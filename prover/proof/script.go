// script.go is the Script: the state a proof file runs on, and the
// constructors a chapter body reaches through it.
//
// The Script type bundles three pieces of state every script needs:
//
//   - Env: the ProverEnv that owns the kernel cache (env.ThmCache),
//     library thms (env.LibraryThms), const-meta service, and the CNF
//     refuter timeout.
//   - Proof: the accumulating Proof object whose section list ends up
//     in the returned *Proof.
//   - LocalThmCache: per-script cache passed to env.ClaimProved so each
//     section's Thm is visible to subsequent sections' cites.
//
// The step constructors here (InductStep, ByCaseStep, AssertStep,
// ExistentialConstDefStep, Lemma, TypeInst, the strips and splits …)
// build the MINISTEPS a proof records; the chapter verbs in derive.go
// (a.Induct, a.Cases, a.Have, Cite) and the session tactics call the
// same constructors, so both surfaces record one tree. The Action-level
// macros that once wrapped these with a post-simplification (Induct,
// Use, DefExpand, ByCase, TypeInstFrom …) are gone — see macro.go's
// header; `Auto` / `CloseByAuto` (the refuter closer) are the two
// Macro-valued constructors that remain.

package proof

import (
	"context"
	"fmt"
	"maps"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// Script is the per-file proof state passed through a build function.
// All fields are public so emit-time and hand-written scripts can poke
// at the underlying state for unusual cases that the helper methods
// don't cover (e.g. ad-hoc tactics applied directly via env).
type Script struct {
	Env           *ProverEnv
	Proof         Proof
	LocalThmCache *ThmCache
	Scope         *ProofScope

	// ParseScope tracks proof-declared symbols for the text-form parser
	// used by MakePropText / SectionText. Const declarations made via
	// `Script.Const` register here automatically; emit-output scripts
	// don't touch this field directly.
	ParseScope dsl.ParseScope

	// curArg is the innermost Argument block currently executing. The
	// block forms (Derive / Given / ByInduction) wire each new block into
	// this dynamic chain so a nested block inherits the enclosing block's
	// surface-name aliases (derive.go §"Surface names"). Proof building
	// is single-threaded per Script; enterArgument restores the previous
	// value on block exit.
	curArg *Argument
}

// NewScript returns a Script bound to env. The returned value owns a
// fresh local ThmCache; the script is single-use (don't share across
// build functions).
//
// ParseScope is pre-populated with metas for the special ext consts
// (COND today; extend as new patterns surface). Sections rendered as
// ctx.SectionText can reference these without an explicit ctx.Const
// declaration — emit's buildParseScope mirrors this preload.
func NewScript(env *ProverEnv) *Script {
	return newScript(env, nil)
}

// NewScriptForEntry creates a Script whose proof identity (target key +
// family exclusions) comes from env.Scope, armed by the harness from the
// registry entry. Member proofs use this constructor: the
// proof file never spells its own key — identity lives in the ProofEntry,
// the harness injects it, and the harness's post-Build identity
// cross-check verifies it. A hand-written key in proof text was the one
// input the circularity gate had to TRUST; this removes the channel.
// Panics when env.Scope is nil: a Build must only run under an
// armed harness.
func NewScriptForEntry(env *ProverEnv) *Script {
	if env.Scope == nil {
		panic("NewScriptForEntry: env.Scope is nil — the harness must arm proof identity (NewProofScope from the registry entry) before Build")
	}
	s := newScript(env, env.Scope)
	// Member scripts are a statement door: section/goal texts
	// resolve strictly — an undeclared name errors instead of
	// freshening. Claims and terms keep their own post-parse contracts
	// (parseScopeWithAliases clears the flag for them).
	s.ParseScope.StrictResolution = true
	s.ParseScope.FreshenMetaLetters = true
	return s
}

func newScript(env *ProverEnv, scope *ProofScope) *Script {
	s := &Script{
		Env:           env,
		LocalThmCache: &ThmCache{},
		Scope:         scope,
		ParseScope: dsl.ParseScope{
			Consts:     map[string]core.ConstTerm{},
			ConstMetas: map[string]core.ConstTermMeta{},
			Vars:       map[string]core.HolType{},
		},
	}
	// Special consts whose metas the parser needs for SectionText
	// round-trip. Mirrors emit's specialConstsForScope.
	s.ParseScope.ConstMetas[string(ext.COND.Name())] = ext.COND.Meta()
	// Registry-const fallback for names the emitted scope didn't declare —
	// the replay-side mirror of the engine session's registryConstResolver
	// (engine.go). Resolution through here yields the process-global
	// ConstMetaManager's meta (def-carrying, identity-canonical), so any
	// const the text mentions carries the SAME meta instance the
	// def-expansion machinery is keyed on — never a synthesized impostor.
	// Names bound by a quantifier or declared in the scope are never
	// queried (dsl.seedResolverConsts skips them), so free-var inference
	// for declared/annotated names is unaffected.
	if env.ProofService != nil && env.ProofService.Syntax != nil {
		s.ParseScope.Syntax = env.ProofService.Syntax
	}
	if env.ProofService != nil && env.ProofService.TypeArity != nil {
		s.ParseScope.TypeResolver = env.ProofService.TypeArity
	}
	if env.ProofService != nil && env.ProofService.LoadConstMeta != nil {
		load := env.ProofService.LoadConstMeta
		s.ParseScope.ConstResolver = func(name string) core.ConstTermMeta {
			meta, ok := load(core.TermName(name))
			if !ok {
				return core.ConstTermMeta{}
			}
			return meta
		}
	}
	if scope != nil {
		scope.cite = s.depByName
	}
	return s
}

// ----- Section management ---------------------------------------------------

// Section delegates to s.Proof.AddSection — the entry point a script uses
// to introduce a new top-level claim. Identical to writing
// `proof.AddSection(p)` directly; provided so a Script-using file never
// needs to mention `s.Proof` by name.
//
// The returned root carries a back-pointer to s so a downstream
// `<root>.Apply(...).Apply(...).Qed()` chain can close the section
// without the caller needing to thread `s` (or `ctx`) into the tail.
func (s *Script) Section(p Prop) *GoalStackNode {
	root := s.Proof.AddSection(p)
	root.script = s
	root.proofScope = s.Scope
	return root
}

// ClaimProved closes the section, propagating the proved thm into both
// the script's local cache and env.ThmCache so later sections (and
// later scripts within the same env) can resolve LemmaActions against
// it.
func (s *Script) ClaimProved(g *GoalStackNode) {
	s.Env.ClaimProved(g, s.LocalThmCache)
}

// ClaimProvedThm registers an already-derived Thm into the script's
// local cache and env.ThmCache so downstream sections / KnownThm leaves
// can resolve against it. Used by sections whose Thm is recovered
// structurally (e.g. TypeDefExpand outputs) rather than via a
// GoalStackNode-based tactic proof — there's no GoalStackNode to
// hand to ClaimProved.
//
// Idempotent: re-registering an already-cached thm is a no-op.
// Trivial-true thms (⊢ ⊤) are intentionally skipped, matching the
// guard in ReconstructSections / ReconstructProof.
func (s *Script) ClaimProvedThm(thm Prop) {
	if thm == nil {
		panic("Script.ClaimProvedThm: nil thm")
	}
	normalized, held := heldThm(thm, s.LocalThmCache, &s.Env.ThmCache)
	if held {
		return
	}
	if normalized.Conclusion().Equals(ext.T) {
		return
	}
	s.LocalThmCache.SaveThm(thm, normalized)
	s.Env.ThmCache.SaveThm(thm, normalized)
}

// ----- Symbol resolution ----------------------------------------------------

// ConstMeta loads a const meta from the underlying ProofService. Panics
// if the const is not registered — registration is the responsibility
// of the caller's bootstrap (the registry's constant manager, populated
// at env startup).
// Use this when an action helper needs a meta directly (Induct's _0/suc
// lookups go through here).
func (s *Script) ConstMeta(name string) core.ConstTermMeta {
	meta, ok := s.Env.ProofService.LoadConstMeta(core.TermName(name))
	if !ok || meta.IsZero() {
		panic(fmt.Sprintf("Script.ConstMeta: const %q not registered in ProofService", name))
	}
	return meta
}

// Const returns the const term for name at the given instantiated type.
// Wraps ConstMeta + ext.Const; used at the top of a script to declare
// every const it references, mirroring the Variables block. The
// resulting ConstTerm is registered into s.ParseScope.Consts so
// later MakePropText / SectionText calls can resolve the name in
// text-form proofs. Polymorphic consts at multiple types in the same
// script: only the first declaration wins for ParseScope purposes;
// subsequent inline uses still construct correct terms via ext.Const
// but won't be reachable by bare name from MakePropText. Those rare
// shapes fall back to the Go-expression section form at emit time.
func (s *Script) Const(name string, instType core.HolType) *ext.TermWrapper {
	meta := s.ConstMeta(name)
	w := ext.Const(meta, instType)
	if s.ParseScope.Consts != nil {
		if _, exists := s.ParseScope.Consts[name]; !exists {
			s.ParseScope.Consts[name] = w.Core().(core.ConstTerm)
		}
	}
	if s.ParseScope.ConstMetas != nil {
		// Always register the meta — even if a fixed Consts entry
		// already exists, ConstMetas's polymorphic-aware path lets
		// later sections instantiate at a different type.
		s.ParseScope.ConstMetas[name] = meta
	}
	return w
}

// Consts declares a batch of monomorphic consts in one call — the
// map form of Const, for the statement-vocabulary preamble at the top
// of a script. Each name goes through Const; map iteration order is
// irrelevant because per-name registration is independent.
func (s *Script) Consts(consts map[string]core.HolType) {
	for name, ty := range consts {
		s.Const(name, ty)
	}
}

// Var declares a proof-level free variable (typically a section Skolem)
// and registers its type into s.ParseScope.Vars, the Var-side mirror of
// Const's ParseScope registration. Later MakePropText / SectionText
// calls resolve the name without a pre-⊢ decls prefix — a claim text
// states only its mathematical content. (Subscript display forms reach
// the registered name through the parser's symbol normalization:
// `m₀` in text resolves the declaration `Var("m_0", …)`.)
//
// Idempotent at the same type. A re-declaration at a DIFFERENT type
// panics: two proof-level frees sharing a name is a proof bug, and
// absorbing it would leave claim texts resolving against whichever
// declaration ran first. Quantifier-bound occurrences in a text are
// unaffected — binders introduce their own types and shadow this scope.
func (s *Script) Var(name string, holType core.HolType) *ext.TermWrapper {
	if s.ParseScope.Vars == nil {
		s.ParseScope.Vars = map[string]core.HolType{}
	}
	if prev, ok := s.ParseScope.Vars[name]; ok && !prev.Equals(holType) {
		panic(fmt.Sprintf(
			"Script.Var: %q re-declared at %s (previously %s) — proof-level frees must have one type per name",
			name, ext.FormatType(holType), ext.FormatType(prev)))
	}
	s.ParseScope.Vars[name] = holType
	return ext.Var(core.TermName(name), holType)
}

// declaredOtherwise reports whether the parse scope declares v's name
// at a type other than v's: the declaration Var refuses. A block's
// strip fixes no such variable (Argument.Fix, the Unpack and Obtain
// family) — the name is fresh for the leaf where the leaf does not
// mention the variable an enclosing block declared, and that variable
// is still one a claim of this block may spell.
func (s *Script) declaredOtherwise(v core.VarTerm) bool {
	declared, ok := s.ParseScope.Vars[string(v.Name())]
	return ok && !declared.Equals(v.Type())
}

// Numeral returns the canonical numeral term for n — the bare BIT
// tower (`_0`, `bit1(_0)`, `bit0(bit1(_0))`, …) that the engine's
// normalized statements use for `num` literals — declaring the tower
// alphabet via Const on the way, so the consts also resolve in later
// text-form statements. Negative n maps to _0, same as
// ext.MakeNumeral; the recursion mirrors it exactly but builds from
// this script's const metas.
func (s *Script) Numeral(n int64) *ext.TermWrapper {
	if n <= 0 {
		return s.Const("_0", ext.NumType)
	}
	bit := "bit0"
	if n%2 == 1 {
		bit = "bit1"
	}
	return s.Const(bit, core.MakeFun(ext.NumType, ext.NumType)).Apply(s.Numeral(n / 2))
}

// PolyConst declares a polymorphic constant by its abstract type,
// carrying type-variable placeholders (VarType instances from
// core.MakeVarType). Unlike Const, which binds ONE monomorphic instance,
// PolyConst returns a PolyConstWrapper that auto-instantiates on each
// .Apply call: the argument types drive type-variable unification, the
// resulting concrete-type instance is cached, and the parse-scope
// registrations (Consts + ConstMetas) are threaded automatically. A
// single declaration replaces the twin-Const pattern (`card` /
// `card_2` handles) needed for polymorphic constants consumed at
// multiple type instances in the same proof.
//
// The abstract signature is passed variadically — the same convention
// as core.MakeFun. `PolyConst("F", A, B, C)` denotes `F: A → B → C`
// (right-associated curry, matches MakeFun's own semantics), and any
// of A/B/C may contain MakeVarType placeholders. A single trailing
// arg is treated as the fully-built signature. Multi-typevar consts
// (e.g. `image: (α → β) → set(α) → set(β)`) put multiple placeholders
// in one signature; the abs-domain-vs-arg matching accumulates
// substitutions across all binder positions, so both α and β get
// pinned from the first Apply that supplies enough context.
//
// See engine/xugo-engine.md §Polymorphic constants for the pattern
// this wrapper replaces + when explicit ⟨⟩ annotations are still
// needed (bare-head references, multi-free-typevar heads).
func (s *Script) PolyConst(name string, absTypeSeq ...core.HolType) *PolyConstWrapper {
	if len(absTypeSeq) == 0 {
		panic(fmt.Sprintf("PolyConst %q: empty abstract signature", name))
	}
	var absType core.HolType
	if len(absTypeSeq) == 1 {
		absType = absTypeSeq[0]
	} else {
		absType = core.MakeFun(absTypeSeq[0], absTypeSeq[1], absTypeSeq[2:]...)
	}
	meta := s.ConstMeta(name)
	// The meta path is what lets ⟨⟩-free polymorphic uses in
	// section text resolve to the right instance — register it
	// once, upfront.
	if s.ParseScope.ConstMetas != nil {
		s.ParseScope.ConstMetas[name] = meta
	}
	return &PolyConstWrapper{
		script:  s,
		name:    name,
		meta:    meta,
		absType: absType,
		cache:   make(map[string]*ext.TermWrapper),
	}
}

// PolyConstWrapper is a polymorphic const handle produced by
// Script.PolyConst. Its .Apply auto-selects the monomorphic instance
// from the arg types via the same abs-type-vs-arg-domain matching the
// DSL parser uses (buildAppViaMeta in ext/dsl/build.go). Instances are
// cached per concrete-type key so a proof reusing the same instance
// (`finite(s)` twice) does not build multiple ConstTerm values.
type PolyConstWrapper struct {
	script  *Script
	name    string
	meta    core.ConstTermMeta
	absType core.HolType
	cache   map[string]*ext.TermWrapper
}

// At returns the monomorphic *TermWrapper for a specific concrete
// instance of the abstract type. Callers producing bare-head references
// (a `SectionText("∀_var:(var:B → bool). …finite(_var)…")` where the
// meta path can't infer without applied args) use At to build the
// wrapper explicitly and pass it into SectionText's varargs. Apply
// callers rarely need it directly.
func (p *PolyConstWrapper) At(instType core.HolType) *ext.TermWrapper {
	key := ext.FormatType(instType)
	if w, ok := p.cache[key]; ok {
		return w
	}
	w := ext.Const(p.meta, instType)
	// Fixed-Consts scope is set-once (mirrors Script.Const's guard);
	// the first instance built becomes the bare-name resolver. Later
	// instances rely on the meta path in scopeConstMetas.
	if p.script.ParseScope.Consts != nil {
		if _, exists := p.script.ParseScope.Consts[p.name]; !exists {
			p.script.ParseScope.Consts[p.name] = w.Core().(core.ConstTerm)
		}
	}
	p.cache[key] = w
	return w
}

// Apply builds an applied term at the monomorphic instance inferred
// from arg types. Panics if the abstract signature doesn't unify with
// the arg types — arity mismatch (more args than the abs sig has
// domains), or a type-variable clash (two different concrete types
// binding the same abstract type-var).
func (p *PolyConstWrapper) Apply(args ...core.Term) *ext.TermWrapper {
	instType, err := inferPolyInstType(p.absType, args)
	if err != nil {
		panic(fmt.Sprintf("PolyConst %q: %v", p.name, err))
	}
	return ext.WrapTerm(ext.Apply(p.At(instType), args...))
}

// inferPolyInstType walks the abstract signature and args in lockstep,
// accumulating type substitutions via the same absDomain.Matches(argType)
// step the DSL parser's buildAppViaMeta uses, then applies them to the
// full abstract type to yield the concrete instantiation. Returns an
// error (rather than panicking) so PolyConstWrapper.Apply can add the
// const name to the message for callsite localization.
func inferPolyInstType(absType core.HolType, args []core.Term) (core.HolType, error) {
	var substs []core.TypeSubst
	cur := absType
	for i, arg := range args {
		curResolved := cur.Substitute(substs...)
		ft, ok := curResolved.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return nil, fmt.Errorf(
				"arg %d: signature %s has no more domains to consume (already fully applied)",
				i, ext.FormatType(absType.Substitute(substs...)))
		}
		domain := ft.SubType(0)
		more, ok := domain.Matches(arg.Type(), fullTypePredicate)
		if !ok {
			return nil, fmt.Errorf(
				"arg %d: type %s does not match abs-domain %s (post-σ)",
				i, ext.FormatType(arg.Type()), ext.FormatType(domain))
		}
		substs = append(substs, more...)
		cur = ft.SubType(1)
	}
	return absType.Substitute(substs...), nil
}

// fullTypePredicate mirrors utils.FullPredicate for VarType — accept
// any type variable in matching. Duplicated here to avoid a utils
// import in the Script's polymorphic-const path.
func fullTypePredicate(core.VarType) bool { return true }

// MakePropText parses a FOL text form against the script's ParseScope
// and returns the resulting Prop. Panics on parse failure with caller
// `file:line` and the diagnostic message. Use this in hand-written
// proofs when constructing a section's goal in text form reads better
// than the nested Go-expression form; emit uses it via SectionText.
//
// The scope carries proof-declared consts (from Script.Const calls)
// so non-well-known names (subset, int_of_num, ==, …) resolve to
// ConstTerm rather than VarTerm — matching the alpha-key compare a
// caller will run against an existing Prop.
//
// The text is read as every door reads one (dsl.ParsePropTextAtDoor): a
// closed text — a section's statement binding its own structure — with
// the script's variables set aside, so a record a section's strips
// declare (`ctx.Var("R_0", …)`) is never read beside the structure the
// text binds; any other text at the script's scope.
//
// Variadic overrides pin a name for this parse. A constant overrides
// its s.ParseScope.Consts entry — needed when the script registers a
// polymorphic instance of a const (e.g. `injective` at the abstract
// `(A→B)→bool`) and a section uses a more-specific instantiation (e.g.
// `injective` at `(ind→ind)→bool`). Without the override, the parser
// would see only the polymorphic instance and infer free arg types as
// polymorphic TyVars, breaking alpha-equality with the entry's
// concrete-typed statement. A variable overrides its s.ParseScope.Vars
// entry: a proof whose disjoint branches each mint a free of one name
// at a different type cannot register both (Var refuses the second),
// so a text spelling that name passes the variable it means. Each
// entry's underlying name is the override key.
func (s *Script) MakePropText(raw string, overrides ...Term) Prop {
	scope := s.parseScopeWithOverrides(overrides)
	res := dsl.ParsePropTextAtDoor(raw, scope)
	if len(res.Errors) > 0 {
		panic(fmt.Sprintf("Script.MakePropText: %q: %s",
			raw, res.Errors[0].Message))
	}
	return res.Prop
}

// UseAbbreviations installs a statement's abbreviation table on the
// script (dsl.ParseScope.Abbreviations): every section, claim and
// term text the script parses from here on spells the table's names as
// «Name». binders names the statement's leading ∀-binders, the names
// the entries are written over, which the statement text may bind
// without capturing them; a claim text binds none of them. A member's
// constructor installs its table before its sections open
// (registry.BuildSpec.installAbbreviations).
func (s *Script) UseAbbreviations(table *dsl.AbbreviationTable, binders map[string]bool) {
	s.ParseScope.Abbreviations = table
	s.ParseScope.AbbreviationBinders = binders
}

// CoerceDomain declares the script's ambient numeric domain for the
// type-directed `&` coercion in statement/claim/term texts: an
// unanchored `&` lowers into this domain instead of the global
// real_of_num default. Anchored operands keep winning, so mixed-domain
// bridge statements cost nothing. A numeric chapter's vocabulary
// declares it once, like Const and Var:
//
//	s.CoerceDomain(proof.IntDomain)
func (s *Script) CoerceDomain(ty core.HolType) {
	s.ParseScope.CoerceDomain = ty
}

// RealDomain / IntDomain are CoerceDomain's arguments — aliases of the
// DSL's runtime numeric types, so a family vocabulary declares its
// ambient domain without importing the DSL package.
var (
	RealDomain = dsl.RealType
	IntDomain  = dsl.IntType
)

// TermText parses a TERM text form against the script's ParseScope —
// MakePropText's term-level counterpart, for the places the Script API
// takes a Term rather than a Prop (`Trans`'s bridge, a `Leg`'s target,
// a `Witness`).
//
// Names resolve exactly as they do in a statement text: constants from
// the script's Const registrations (a family's vocabulary included),
// free variables from Script.Var — which is what `a.Binder`, the
// section-boundary parameters and `a.Obtain`'s Skolems each register
// as they mint. So the term is READ against the scope the leaf
// actually has, where the Go-expression form (`v.Add(v.Mul(m, n0),
// ...)`) re-spells it against names the author must keep aligned with
// the mint by hand — and then writes the readable form a second time
// in a comment, which nothing checks.
//
// A free name the scope does not declare is a typo or a missing
// `Script.Var`, never an intent to introduce a fresh variable: the
// term would denote something the surrounding goal has never heard
// of. TermText panics naming it. Names the text binds itself (a λ's
// own variable) are its own business and are not checked.
//
// Variadic overrides: see MakePropText.
func (s *Script) TermText(raw string, overrides ...Term) *ext.TermWrapper {
	scope := s.parseScopeWithOverrides(overrides)
	res := dsl.ParseTermTextInScope(raw, nil, scope, nil)
	if len(res.Errors) > 0 {
		panic(fmt.Sprintf("Script.TermText: %q: %s",
			raw, res.Errors[0].Message))
	}
	assertFreesDeclared(raw, res.Term, scope)
	return ext.WrapTerm(res.Term)
}

// assertFreesDeclared panics if `t` has a free variable the parse
// scope does not declare — the TermText contract above. Argument's
// claim path (derive.go's parseClaim) runs the same check with its
// own verb-labeled panic.
func assertFreesDeclared(raw string, t core.Term, scope *dsl.ParseScope) {
	undeclared := undeclaredFrees(t, scope)
	if len(undeclared) == 0 {
		return
	}
	panic(fmt.Sprintf(
		"Script.TermText: %q: undeclared free %v — declare via Script.Var, or check the spelling against the minted name (declared: %v)",
		raw, undeclared, declaredNames(scope)))
}

// undeclaredFrees lists `t`'s free variables the parse scope does not
// declare, sorted as "name:type" strings. `CollectVars` gathers bound
// occurrences too, so each candidate is re-tested with HasFreeName: a
// λ-bound name is not a free one.
func undeclaredFrees(t core.Term, scope *dsl.ParseScope) []string {
	vars := map[core.TermKey]core.VarTerm{}
	ext.CollectVars(t, vars)
	var undeclared []string
	for _, v := range vars {
		name := string(v.Name())
		if _, ok := scope.Vars[name]; ok {
			continue
		}
		if !t.HasFreeName(v.Name()) {
			continue // bound by the text itself
		}
		undeclared = append(undeclared, fmt.Sprintf("%s:%s", name, ext.FormatType(v.Type())))
	}
	slices.Sort(undeclared)
	return undeclared
}

// declaredNames is the scope's variable names, sorted — the "what CAN
// be written" half of an undeclared-free panic.
func declaredNames(scope *dsl.ParseScope) []string {
	declared := make([]string, 0, len(scope.Vars))
	for name := range scope.Vars {
		declared = append(declared, name)
	}
	slices.Sort(declared)
	return declared
}

// parseScopeWithOverrides returns s.ParseScope if no overrides are
// supplied; otherwise a copy with each constant overlaid on Consts and
// each variable on Vars. The override is by name — each term's
// underlying ConstTerm or VarTerm .Name() determines which key it
// replaces. ConstMetas carry over from s.ParseScope unchanged (the
// parser's polymorphic-fallback path stays available via ConstMetas),
// and so do the script's coercion domain, its guard on an unanchored
// `&` and its reading of a polymorphic constant's type letters as the
// constant's own.
func (s *Script) parseScopeWithOverrides(overrides []Term) *dsl.ParseScope {
	if len(overrides) == 0 {
		return &s.ParseScope
	}
	consts := make(map[string]core.ConstTerm, len(s.ParseScope.Consts)+len(overrides))
	for k, v := range s.ParseScope.Consts {
		consts[k] = v
	}
	vars, copied := s.ParseScope.Vars, false
	for _, w := range overrides {
		switch t := w.Core().(type) {
		case core.ConstTerm:
			consts[string(t.Name())] = t
		case core.VarTerm:
			if !copied {
				vars = make(map[string]core.HolType, len(s.ParseScope.Vars)+1)
				maps.Copy(vars, s.ParseScope.Vars)
				copied = true
			}
			vars[string(t.Name())] = t.Type()
		default:
			panic(fmt.Sprintf("Script: a scope override is a constant or a variable, not %s", ext.PrintTerm(w)))
		}
	}
	return &dsl.ParseScope{
		Consts:              consts,
		ConstMetas:          s.ParseScope.ConstMetas,
		Vars:                vars,
		ConstResolver:       s.ParseScope.ConstResolver,
		Syntax:              s.ParseScope.Syntax,
		ImplicitBindings:    s.ParseScope.ImplicitBindings,
		CoerceDomain:        s.ParseScope.CoerceDomain,
		StrictCoercion:      s.ParseScope.StrictResolution || s.ParseScope.StrictCoercion,
		FreshenMetaLetters:  s.ParseScope.FreshenMetaLetters,
		Abbreviations:       s.ParseScope.Abbreviations,
		AbbreviationBinders: s.ParseScope.AbbreviationBinders,
	}
}

// parseScopeWithAliases returns the parse scope for a claim carrying
// surface-name aliases (derive.go §"Surface names"): each alias name is
// declared at its minted variable's type — overriding a same-named Vars
// entry, so the innermost binding shadows the chapter vocabulary — plus
// the substitution list that renames the parsed frees to the minted
// variables. A nil/empty alias map returns the scope unchanged with no
// substitutions.
//
// Either way the claim is read under the script's coercion domain, the
// script's guard on an unanchored `&` and the script's reading of a
// polymorphic constant's type letters (FreshenMetaLetters): a claim and
// the statement it serves resolve `&` and a constant's letters by one
// rule, whether or not the block has minted a name.
func (s *Script) parseScopeWithAliases(aliases map[string]core.VarTerm) (*dsl.ParseScope, []core.TermSubst) {
	strictCoercion := s.ParseScope.StrictResolution || s.ParseScope.StrictCoercion
	if len(aliases) == 0 {
		// A claim is read under the statement's abbreviations but binds
		// none of the statement's binders itself: a claim that rebinds
		// a name an entry spells is refused (dsl.ParseScope.
		// AbbreviationBinders).
		scope := s.ParseScope
		scope.AbbreviationBinders = nil
		if s.ParseScope.StrictResolution {
			// The claim/term paths enforce the same undeclared-free
			// contract post-parse (parseClaim, assertFreesDeclared)
			// with the alias legend in the message — clear the
			// parse-level switch so the better diagnostic is the one
			// that fires. The guard on `&` has no post-parse twin and
			// stays.
			scope.StrictResolution = false
			scope.StrictCoercion = strictCoercion
		}
		return &scope, nil
	}
	vars := make(map[string]core.HolType, len(s.ParseScope.Vars)+len(aliases))
	for k, v := range s.ParseScope.Vars {
		vars[k] = v
	}
	substs := make([]core.TermSubst, 0, len(aliases))
	surfaces := make(map[string]string, len(aliases))
	for n, v := range aliases {
		vars[n] = v.Type()
		if n != string(v.Name()) {
			substs = append(substs, core.MakeTermSubst(core.Var(core.TermName(n), v.Type()), v))
			surfaces[string(v.Name())] = n
		}
	}
	scope := &dsl.ParseScope{
		Consts:             s.ParseScope.Consts,
		ConstMetas:         s.ParseScope.ConstMetas,
		Vars:               vars,
		ResidentNames:      surfaces,
		ConstResolver:      s.ParseScope.ConstResolver,
		Syntax:             s.ParseScope.Syntax,
		ImplicitBindings:   s.ParseScope.ImplicitBindings,
		CoerceDomain:       s.ParseScope.CoerceDomain,
		StrictCoercion:     strictCoercion,
		FreshenMetaLetters: s.ParseScope.FreshenMetaLetters,
		Abbreviations:      s.ParseScope.Abbreviations,
	}
	return scope, substs
}

// SectionText delegates to s.Proof.AddSection on the parsed text. The
// returned *GoalStackNode behaves exactly like Section's, including
// downstream .Apply / ClaimProved.
//
// A section states a closed theorem: a text with hypotheses left of ⊢
// panics, naming the closed spelling.
//
// Variadic overrides: see MakePropText.
func (s *Script) SectionText(raw string, overrides ...Term) *GoalStackNode {
	p := s.MakePropText(raw, overrides...)
	if p.NumHyps() > 0 {
		panic(fmt.Sprintf("Script.SectionText(%q): the statement has hypotheses left of ⊢, and a section "+
			"states a closed theorem — ∀-bind its variables and ⇒ its premises, one antecedent per Fact "+
			"parameter: %s", raw, ClosedSpelling(p)))
	}
	return s.Section(p)
}

// ClosedSpelling is the closed reading of a statement with hypotheses,
// as parser text: its free variables ∀-bound, its hypotheses curried
// ⇒-antecedents (in the kernel's hypothesis order, which need not be the
// order the text wrote them in). The statement doors that refuse a
// sequent name it.
func ClosedSpelling(p Prop) string {
	t := p.Conclusion()
	for i := p.NumHyps() - 1; i >= 0; i-- {
		t = WrapTerm(p.Hyp(i)).Imply(t).Core()
	}
	for _, v := range slices.Backward(t.Frees(nil)) {
		t = ForAll(v)(t).Core()
	}
	return prop.FormatPropForParser(core.MakeProp(t))
}

// LibraryThm returns the library theorem the env binds under name
// (ProverEnv.LookupLibraryThm) or panics with a clear message. A cite
// of a corpus entry reads its theorem here, by the entry's registered
// name.
func (s *Script) LibraryThm(name string) Thm {
	thm, ok := s.Env.LookupLibraryThm(name)
	if !ok {
		panic(fmt.Sprintf("Script.LibraryThm: no library theorem %q is bound in this env", name))
	}
	return thm
}

// Dep is the claiming dep verb for proofs: LibraryThm lookup +
// ClaimProvedThm in one call, returning the realized ThmCert — no
// per-dep ladder (lookup, type assertion, claim). It takes the entry
// itself — the typed wrapper var, or any NamedDep — so a dep is
// spelled by the name that registers it and never by a string. A
// proof either hoists the cert once
//
//	addSymThm := ctx.Dep(nat_arith.AddSym)
//
// or cites at use (`CiteSpecialize(ctx.Dep(set_basic.InDelete), …)`); both
// are safe because ClaimProvedThm is idempotent.
//
// Panics when the name isn't preloaded (same fail-fast contract as
// LibraryThm) or when the preloaded value isn't a realized ThmCert —
// the replay harness always stores realized certs, so a
// non-cert value means the env wasn't set up by the harness path this
// verb is for.
func (s *Script) Dep(dep NamedDep) ThmCert { return s.depByName(dep.DepName()) }

// depByName is Dep by the registered name: what Dep reads an entry
// through, and the parse scope's cite lookup.
func (s *Script) depByName(name string) ThmCert {
	cert, ok := s.LibraryThm(name).(ThmCert)
	if !ok {
		panic(fmt.Sprintf("Script.Dep: the library theorem %q is not a realized *ThmCert", name))
	}
	s.ClaimProvedThm(cert)
	return cert
}

// ConstDef returns the def thm of the named const. The thm is the
// ⊢ c = body equation that NewConstDef stamped onto the const's meta
// when it was first introduced; (ConstTerm).DefThm() recovers it
// once the meta is loaded from the ProofService.
//
// Used by emit to resolve external-leaf references whose source is a
// const definition. The
// returned ThmCert feeds a Cite or a TypeInst step, depending on how
// the proof step consumes it.
func (s *Script) ConstDef(name string) ThmCert {
	meta := s.ConstMeta(name)
	if t := meta.Term(); !t.IsZero() {
		// Use the const term to drive type instantiation when the
		// def thm is parametrically typed. For monomorphic consts
		// this is identical to meta.DefThm(), but going through
		// ConstTerm.DefThm() handles the polymorphic case correctly.
		if def := t.DefThm(); !def.IsZero() {
			return s.registerKnownThm(def).AsThmCert()
		}
	}
	if def := meta.DefThm(); !def.IsZero() {
		return s.registerKnownThm(def).AsThmCert()
	}
	panic(fmt.Sprintf("Script.ConstDef: const %q has no def thm "+
		"(meta.def is nil — was it introduced via NewConstDef?)", name))
}

// ConstDefNormalized returns the NORMALIZED def thm of the named const —
// the applied/iff form (e.g. set_member's `∀P,x.(P(x)⇔set_member(x,P))`) rather than the
// raw lambda equation `set_member = λ_._( _)` that ConstDef returns.
//
// emit uses this for a Lemma whose recorded rule resolves to a
// const-def-classified theorem. The session applied the definition in its
// NORMALIZED form (the form the registry's const-def index keys), so
// replay must apply the same form.
// The raw equation only UNFOLDS the const (`set_member(…)→…`); the normalized iff
// also FOLDS into it (`P(x)→set_member(x,P)` by first-order match), which is what
// proofs that introduce membership need. Both thms are kernel-proved —
// Normalize preserves provability, so the result is a genuine Thm.
// Returns ThmCert (not the Thm interface): the input is a realized const-def,
// so the normalized form is realized too, and the consumer (UseThm) wants the
// concrete cert. NormalizedThm differs — it is fed a (possibly promise-backed)
// typed dep, so it must stay promise-transparent (Thm).
func (s *Script) ConstDefNormalized(name string) ThmCert {
	norm, _ := Normalize(s.ConstDef(name))
	return s.registerKnownThm(norm).AsThmCert()
}

// NormalizedThm returns the NORMALIZED form of `t`, registered in the thm
// caches. emit uses it for a TypeInst whose recorded source is a normalized
// prop (the engine's auto-match closes a lemma-reproduction leaf via
// ApplyTypeInst(leaf, Normalize(source)), so the recorded source is already
// normalized) — but emit resolves that to the cited member's raw theorem. _TypeInstStep
// compares the normalized goal against its source assuming the source is
// normalized, so a raw source fails NormalizedPropTypeMatch. Re-normalizing
// here reproduces exactly what record fed the matcher. Same shape as
// ConstDefNormalized.
//
// A proof uses it to install a fact in its closed canonical form with
// zero pinned text — `UseLemmaExact(ctx.NormalizedThm(dep))` /
// `CiteSpecialize(ctx.NormalizedThm(dep), w…)`; a sequent handed to it
// comes back ∀-closed, its hypotheses folded into antecedents (a raw
// sequent cert cannot be installed as a hyp:
// ApplyLemmaPreserveExactWithSource refuses hyps-carrying props). A
// named dep's stated form installs directly — no wrapper needed.
//
// The install form's ∀-prefix is in t's OWN binder order, and its
// clauses share binders as t shares them. Normalize orders a prefix by
// the canonical labeling and has the clauses of a block share binders
// by canonical rank — functions of the statement's α-class that no
// author controls, and ones that a change to the normalizer moves —
// while a consumer that grounds the install form positionally
// (CiteSpecialize, the calc kits' transitivity certificates, the
// conditioning stage) reads a witness tuple in the order the statement
// was written, like every other ground cite, and reads each clause in
// the roles the statement gave its binders: `∀x y. x ≤ max(x,y) ∧ y ≤
// max(x,y)` at (x₀, s) must say s ≤ max(x₀, s), which the canonical
// form `∀y x. y ≤ max(y,x) ∧ y ≤ max(x,y)` under the stated prefix no
// longer does. So the closed clause form is computed by
// prop.NormalizeKeepingSharing and its prefix is then put back into
// the stated order (statedPrefixOrder). The canonical form is what the
// caches register: the bare-cite tier answers "is the leaf this fact
// modulo Normalize" by key, and that key is the canonical one.
func (s *Script) NormalizedThm(t Thm) Thm {
	s.registerKnownThm(s.normalForm(t))
	return s.registerKnownThm(statedPrefixOrder(t, InstallForm(t)))
}

// NormalizedForm is the statement NormalizedThm serves for `stated`,
// computed without a Script: the closed clause form
// prop.NormalizeKeepingSharing gives it, its ∀-prefix put back into the
// stated order. It is the one function
// both faces of "cite a dep in its normalized orientation" read — the
// Go `ctx.DepNormalized(name)` above and the session's per-rule
// `normalized: true` (engine resolveSimpWithRules) — so a rule the
// session fired in this form is the rule the emitted Go fires, and the
// recorded rule prop is byte-for-byte what replay resolves.
func NormalizedForm(stated Prop) Prop {
	return statedPrefixOrder(stated, InstallForm(stated))
}

// InstallForm is the clause form a consumer installs and grounds: the
// statement's closed clause form with its own binder sharing
// (prop.NormalizeKeepingSharing). Normalize is the KEY: it has the
// clauses of a block share binders by canonical rank, so a tuple that
// grounds the statement's binders by name would read a clause in roles
// the author never wrote (`∀s t. s ∩ t ⊆ s ∧ t ∩ s ⊆ s` at (T₀, S₀)
// must supply T₀ ∩ S₀ ⊆ T₀). Every install — a named dep, a typed
// instance's install half, a simp rule's normalized orientation — is
// this one function of the statement, so the session and the emitted
// Go install byte-identical forms (library/emit's atTypesInstance
// rebuilds the half with it).
func InstallForm(t Prop) Prop {
	install, _ := prop.NormalizeKeepingSharing(t)
	return install
}

// statedPrefixOrder returns norm — the closed clause form of stated —
// with its outer ∀-prefix in the order stated's own ∀-prefix binds it,
// when stated is exactly such a prefix over a body. The prefix is
// permuted by the kernel (ReorderForAll); nothing below it moves.
func statedPrefixOrder(stated, norm Prop) Prop {
	// Only a statement that IS a ∀-prefix over a body — no hypotheses,
	// no binder pulled up from inside, no free variable closed — has a
	// stated order for the whole prefix. A nested or sequent-shaped
	// statement keeps Normalize's order: its consumers wrote their
	// witness tuples against that order, which the canonical labeling
	// leaves alone wherever the block has one fixed point.
	if stated.NumHyps() != 0 {
		return norm
	}
	statedVars, _ := DecomposesFORALL(stated.Conclusion())
	vars, body := DecomposesFORALL(norm.Conclusion())
	if vars.Size() < 2 || !statedVars.ElementEquals(&vars) {
		return norm
	}
	ordered := statedVars.Section(0, statedVars.Size())
	rebuilt := ForAll(varsAsTerms(ordered)...)(body).Core()
	if rebuilt.Equals(norm.Conclusion()) {
		return norm
	}
	return prop.ReorderForAll(norm.Conclusion(), rebuilt).EqMP(norm)
}

func varsAsTerms(vs []VarTerm) []Term {
	out := make([]Term, len(vs))
	for i, v := range vs {
		out[i] = v
	}
	return out
}

// DepNormalized is Dep + NormalizedThm in one call — the standard
// compute-route spelling for citing a named dep (see
// NormalizedThm above for why the normalization is needed).
func (s *Script) DepNormalized(dep NamedDep) Thm {
	return s.NormalizedThm(s.Dep(dep))
}

// TypedThm is AtTypes' return value: a cross-type INSTANCE of a dep,
// carrying both forms the cite family needs. The embedded Thm is the
// INSTALL form — Normalize(dep) type-instantiated, the closed canonical
// form the cite installs (so a TypedThm used as a plain Prop/Thm is
// exactly the instance itself). ref is the dep's RAW stated form at the
// same instance: the statement whose binder order a witness tuple
// follows (witness_order.go) and whose implication shape ByInduction
// reads case obligations off — both of which Normalize destroys (the
// clause form reorders the ∀-prefix and dissolves the ⇒).
//
// Carrying the pair is what makes an `At(ctx.AtTypes(dep, τ…), w…)`
// witness tuple read in the dep's OWN stated binder order, like every
// other ground cite: an AtTypes cite does not fall to the positional
// witness path.
type TypedThm struct {
	Thm     // the install form: InstallForm(dep) at the instance types
	ref Thm // the dep's raw stated form at the same instance
}

// Reference returns the dep's raw stated form at the instance types —
// the statement a witness tuple's order follows.
func (t *TypedThm) Reference() Thm { return t.ref }

// AtTypes returns a theorem or proved local section at the given types, in
// its install form: InstallForm(t) — an identity for a ∀-form
// statement, the closed clause form of a sequent handed in, the
// statement's own binder sharing kept — with its type variables
// substituted by `at` POSITIONALLY, in order of first occurrence in
// that form. The canonical form is registered beside it, for the key
// tier. The instance is
// kernel-derived from `t` itself (core.PropTypeInst — statement-level
// type instantiation, promise-transparent) and registered in the script's thm
// caches, so citing it (UseLemmaExact / CiteSpecialize / Cite) closes
// by known-thm lookup.
//
// The returned TypedThm additionally carries the dep's RAW stated form
// at the same instance, so the cite family reads witness tuples in the
// dep's stated binder order (witness_order.go) and ByInduction can read
// obligations through a cross-type cite; used as a plain Prop/Thm the
// value is the install form.
//
// A local section supplies its stated binder names and unforced certificate.
// Both forms are computed from that certificate; no text, no machine names.
// A cross-type install pair of pinned texts — LemmaPreserve(<CNF text
// at the target type>) + TypeInst(ExactFrom(dep, <CNF text at the row's
// own type var>)) — would force the row's machine type-var name, e.g.
// ?83488, into blessed Go.
//
// The positional convention is checked: len(at) must equal the number
// of distinct type variables in the normalized statement, and the
// panic message lists them in positional order. Passing a type equal
// to the row's own var is a no-op substitution and is fine (the
// canonical form itself is returned).
func (s *Script) AtTypes(target any, at ...core.HolType) *TypedThm {
	t := typeInstanceSource(target)
	norm := InstallForm(t)
	vars := orderedPropTypeVars(norm)
	if len(vars) == 0 {
		panic(fmt.Sprintf("Script.AtTypes: dep has no type variables: %s",
			prop.PrintProp(norm)))
	}
	if len(at) != len(vars) {
		names := make([]string, len(vars))
		for i, v := range vars {
			names[i] = string(v.Name())
		}
		panic(fmt.Sprintf("Script.AtTypes: %d type arg(s) for %d type var(s) %v in %s",
			len(at), len(vars), names, prop.PrintProp(norm)))
	}
	return s.atTypeInstance(t, norm, vars, at)
}

// AtTypeVars is AtTypes keyed by the statement's OWN type-variable
// names instead of by position: each binding pairs a type variable the
// dep's stated form spells with the type it takes, so the author reads
// the names off the statement and the list order carries no meaning.
// The bindings must cover the statement's type variables exactly — a
// missing, unknown or doubly-bound name panics, listing the variables
// the statement actually has.
//
// Both spellings funnel into the one install pipeline below
// (atTypeInstance), so a named instance and its positional twin install
// byte-identical forms; the positional first-occurrence convention
// survives only in there, derived from the normalized statement itself
// rather than authored at any call site.
func (s *Script) AtTypeVars(target any, bind ...TypeBinding) *TypedThm {
	t := typeInstanceSource(target)
	norm := InstallForm(t)
	vars := orderedPropTypeVars(norm)
	if len(vars) == 0 {
		panic(fmt.Sprintf("Script.AtTypeVars: dep has no type variables: %s",
			prop.PrintProp(norm)))
	}
	names := make([]string, len(vars))
	inStatement := make(map[core.TypeName]bool, len(vars))
	for i, v := range vars {
		names[i] = string(v.Name())
		inStatement[v.Name()] = true
	}
	byName := make(map[core.TypeName]core.HolType, len(bind))
	var unknown []string
	for _, b := range bind {
		if _, dup := byName[b.name]; dup {
			panic(fmt.Sprintf("Script.AtTypeVars: type variable %s bound twice in %s",
				b.name, prop.PrintProp(norm)))
		}
		byName[b.name] = b.to
		if !inStatement[b.name] {
			unknown = append(unknown, string(b.name))
		}
	}
	at := make([]core.HolType, len(vars))
	var missing []string
	for i, v := range vars {
		bound, ok := byName[v.Name()]
		if !ok {
			missing = append(missing, string(v.Name()))
			continue
		}
		at[i] = bound
	}
	if len(missing) > 0 || len(unknown) > 0 {
		panic(fmt.Sprintf(
			"Script.AtTypeVars: bindings do not match the statement's type variables %v"+
				" (missing %v, unknown %v) in %s",
			names, missing, unknown, prop.PrintProp(norm)))
	}
	return s.atTypeInstance(t, norm, vars, at)
}

// AtSoleType is the third spelling, for a statement with exactly ONE
// type variable: the sole variable is bound without being named —
// there is no pairing to misstate, so the spelling needs neither the
// positional convention nor the variable's name. Besides being the
// natural form for the corpus's single-letter majority, it is the
// clean cite for a raw row whose one variable has a machine name
// (the ?110583 case), which naming would force into blessed Go.
// Panics unless the statement's type-variable count is one, listing
// the variables it actually has — the loud exit for a restatement
// that grows a second letter under an existing sole cite.
func (s *Script) AtSoleType(target any, to core.HolType) *TypedThm {
	t := typeInstanceSource(target)
	norm := InstallForm(t)
	vars := orderedPropTypeVars(norm)
	if len(vars) != 1 {
		names := make([]string, len(vars))
		for i, v := range vars {
			names[i] = string(v.Name())
		}
		panic(fmt.Sprintf(
			"Script.AtSoleType: statement has %d type variable(s) %v, need exactly one: %s",
			len(vars), names, prop.PrintProp(norm)))
	}
	return s.atTypeInstance(t, norm, vars, []core.HolType{to})
}

// typeInstanceSource preserves a local section's declaration at the typed
// citation boundary. An explicit certificate keeps its own statement.
func typeInstanceSource(target any) Thm {
	switch t := target.(type) {
	case *GoalStackNode:
		return core.AsThm(sectionReferenceForm(t))
	case Thm:
		return t
	default:
		panic(fmt.Sprintf("typed instance: expected a theorem or proved section, got %T", target))
	}
}

// atTypeInstance is the one install pipeline behind AtTypes and
// AtTypeVars: at[i] instantiates vars[i], with norm the already-built
// normalized form of t. A single tail is what makes the two spellings
// install byte-identical forms.
func (s *Script) atTypeInstance(t Thm, norm Prop, vars []core.VarType, at []core.HolType) *TypedThm {
	subst := make([]core.TypeSubst, len(vars))
	for i := range vars {
		subst[i] = core.MakeTypeSubst(vars[i], at[i])
	}
	s.registerKnownThm(s.normalForm(t))
	s.registerKnownThm(norm)
	install, rawInst := typedInstallForm(t, norm, subst)
	inst := s.registerKnownThm(install)
	return &TypedThm{Thm: inst, ref: core.AsThm(rawInst)}
}

// typedInstallForm is a typed instance's two forms at subst: the
// install form, t's install form norm (InstallForm) taken at the
// instance — the clause form first, the types after, since the two do
// not commute — and t's stated form at the instance (rawInst).
//
// InstallForm is the install form for closed statements — an
// identity for ∀-form rows, the hyp-folding closure for sequent rows
// (whose frees MUST fold; the SequentRow test pins that). A HYP-FREE
// statement with free term variables — a spec-parametric member, stated
// over its family's declared frees — has no such identity: Normalize
// ∀-closes the frees and Skolemizes the antecedents into a shape whose
// prefix no longer matches the stated binders (so a witness tuple cannot
// ground) and whose closure re-opens the very spec variables the
// consumer's context pins (so the refuter pays for re-finding them). The
// stated form IS the install form there.
func typedInstallForm(t Thm, norm Prop, subst []core.TypeSubst) (install, rawInst Prop) {
	rawInst = core.PropTypeInst(t, subst...)
	install = core.PropTypeInst(norm, subst...)
	if rawInst.NumHyps() == 0 && len(rawInst.Conclusion().Frees(nil)) > 0 {
		install = rawInst
	}
	return install, rawInst
}

// ExplicitInstanceClause is the clause form Go's typed instance of
// source installs (Script.AtTypes; a law's `.At` whose witnesses pin
// every type variable) for the instance a session premise names
// explicitly: source's normalized statement at the type instance that
// takes source's stated form to instance, by the install pipeline
// atTypeInstance runs. A theorem, source being one. A session `by`
// premise that is an explicit instance carries it as its clause form,
// so the session's close installs what the Go spelling of the same
// premise installs. Panics when instance is not a type instance of
// source's stated form: the session builds instance as one.
func ExplicitInstanceClause(source Thm, instance Prop) Prop {
	subst, ok := prop.IsTypeMatchOf(source, instance, utils.FullPredicate[core.VarType])
	if !ok {
		panic(fmt.Sprintf("ExplicitInstanceClause: %s is not a type instance of %s",
			prop.PrintProp(instance), prop.PrintProp(source)))
	}
	install, _ := typedInstallForm(source, InstallForm(source), subst)
	return install
}

// ExplicitReadingClause is the clause form Go's By gives a law read at
// an instance entry (premiseClauseForm: the reading's NormalizedThm —
// Normalize, the ∀-prefix in the stated order), at the type instance
// that takes the reading's statement to instance: the clause a session
// premise grounding that reading at every binder carries, its witnesses
// having pinned the law's loose type letters. A theorem, reading being
// one. Panics when instance is not a type instance of reading's
// statement: the session builds instance as one.
func ExplicitReadingClause(reading Thm, instance Prop) Prop {
	subst, ok := prop.IsTypeMatchOf(reading, instance, utils.FullPredicate[core.VarType])
	if !ok {
		panic(fmt.Sprintf("ExplicitReadingClause: %s is not a type instance of %s",
			prop.PrintProp(instance), prop.PrintProp(reading)))
	}
	return core.PropTypeInst(NormalizedForm(reading), subst...)
}

// OrderedPropTypeVars exposes AtTypes's positional convention to
// callers that must PRODUCE a type-argument list — emit's curate
// transport, which renders the `ctx.AtTypes(dep, τ…)` cross-type cite
// from a recorded install pair and has to put the types in the order
// AtTypes will read them back. The convention needs exactly one
// definition: a second traversal that merely agreed today would be a
// silent mis-instantiation the moment either drifted.
func OrderedPropTypeVars(p Prop) []core.VarType { return orderedPropTypeVars(p) }

// orderedPropTypeVars collects the distinct type variables of p's
// conclusion (then hyps) in first-occurrence order — the positional
// order Script.AtTypes matches its type args against. Deterministic:
// pure structural traversal (function before argument, binder variable
// before body).
func orderedPropTypeVars(p Prop) []core.VarType {
	var order []core.VarType
	seen := map[core.TypeName]bool{}
	collect := func(t core.Term) {
		ext.TermAnyTypeVar(t, func(v core.VarType) bool {
			if !seen[v.Name()] {
				seen[v.Name()] = true
				order = append(order, v)
			}
			return false
		})
	}
	collect(p.Conclusion())
	for h := range p.HypIter() {
		collect(h)
	}
	return order
}

// TypeInstSource prepares a dep thm as a _TypeInstStep source: it performs
// NormalizedThm's cache-registration side effect (downstream cites /
// RecallCached / ClaimProved integrity checks need the normalized form
// known) but returns the thm in its OWN (raw / Stmt) form. The raw form is
// what the step's FIRST (structural, raw-vs-raw) match needs: Normalize's
// ∀-binder order is TYPE-dependent and does not commute with type
// instantiation (a polymorphic source whose conjuncts live at distinct type
// vars keeps per-conjunct binders that MERGE at a concrete instance —
// the distribution of ∩ over ⋃, cited inside a cardinality-of-a-union proof), so the normalized source can be
// structurally unreachable from the normalized goal while the raw forms
// match directly. The step's normalized fallback re-normalizes the source
// internally, so nothing is lost by not passing the normalized form.
func (s *Script) TypeInstSource(t Thm) Thm {
	norm := s.normalForm(t)
	s.registerKnownThm(norm)
	return t
}

// TypeInstSourceExact is TypeInstSource for the viaNormalize resolution:
// the recorded TypeInst source's α-form differs from the dep thm's own
// statement (the two only normalize-coincide), and the recorded form is
// the only one guaranteed to match the recorded goal. Normalize does not
// commute with type instantiation in two independent ways — funext
// expansion of type-var equalities at function-type instances, and
// ∀-binder MERGE when a multi-type-var source's conjuncts collapse to one
// concrete type (both at once in one comprehension-membership cite) — so
// handing _TypeInstStep the dep's own form can be structurally
// unrecoverable at every fallback tier. Performs TypeInstSource's
// normalized-registration side effect, then returns the dep thm REBUILT
// into the recorded exact α-form via ExactFrom (BridgeNormalize —
// kernel-faithful, loud on drift).
func (s *Script) TypeInstSourceExact(t Thm, exact Prop) Prop {
	norm := s.normalForm(t)
	s.registerKnownThm(norm)
	return s.ExactFrom(t, exact)
}

// ExactFrom rebuilds `t` (a proved/promise-backed thm — typically a
// dep) into the EXACT α-form `exact`, for replay sites where the
// recorded proof consumed a normalize-equivalent VARIANT of the dep's
// statement (flipped equation orientation, different binder
// order/names) rather than its own form — applying the dep's own form
// there diverges from the recording. ExactFrom bridges via
// prop.BridgeNormalize, which is kernel-faithful and nil only when the
// two forms do NOT normalize-coincide — a drift worth a loud stop. The bridged thm registers in the script's caches (same
// rationale as NormalizedThm: a cited leaf must be "known" for
// ClaimProved's integrity check).
func (s *Script) ExactFrom(t Thm, exact Prop) Prop {
	bridged := prop.BridgeNormalize(exact, t)
	if bridged == nil {
		panic(fmt.Sprintf(
			"Script.ExactFrom: thm does not normalize-coincide with the "+
				"recorded exact form.\n  thm:   %s\n  exact: %s",
			prop.PrintProp(t), prop.PrintProp(exact)))
	}
	// BridgeNormalize guarantees α-equality with `exact` only — its
	// α-equal early return hands back `t` VERBATIM, so a thm that is a
	// pure bound-variable rename of the recorded form would flow through
	// in its own spelling. Binder NAMES are load-bearing downstream:
	// StripQuant Skolemizes a stripped binder into a session-level FREE
	// variable named after it, so a binder-renamed cite diverges from the
	// recording several steps later (an
	// int_congruent cite in the words chapters: recorded `∃z…` Skolemizes to z₀, the corpus
	// statement's `∃d…` to d₁). Finish the cast to `exact`'s spelling via
	// EqMP against Refl of the exact conclusion — EqMP matches its minor
	// premise up to α, so this is the kernel's α-cast (hyps unchanged).
	if !bridged.Conclusion().Equals(exact.Conclusion()) {
		bridged = core.EqMP(core.Refl(exact.Conclusion()), bridged)
	}
	s.registerKnownThm(bridged)
	return bridged
}

// registerKnownThm records `t` (a kernel-proved, axiomatically-known thm —
// e.g. a const def or its normalized form) in the script's thm caches under
// both its raw and normalized keys. A const-def CITED as a Lemma /
// CloseByNormalize source becomes a thm-leaf that ClaimProved's integrity
// check verifies is "known"; unlike a prior Section it was never Qed-cached,
// so without this the check (prover.go) panics ("Should not happen.") even
// though the cite is sound. Idempotent. HasThm matches on raw OR normalized
// key, so a type-instance / α-variant of a registered def still resolves.
func (s *Script) registerKnownThm(t Prop) Thm {
	norm := s.normalForm(t)
	s.LocalThmCache.SaveThm(t, norm)
	s.Env.ThmCache.SaveThm(t, norm)
	return core.AsThm(t)
}

// normalForm is t's normal form, read from the script's thm caches when
// a thm of t's statement, names included, is held there (normalForm).
func (s *Script) normalForm(t Prop) Prop {
	return normalForm(t, s.LocalThmCache, &s.Env.ThmCache)
}

// TypeDefExpand applies the kernel's TypeDefExpand primitive to source,
// returning the two type-def axiom Thm outputs of the named const's
// abs/rep pair:
//
//	out1 = ⊢ abs(rep a) = a
//	out2 = ⊢ P(r) ⇔ rep(abs r) = r
//
// constName may be either half of the type-def pair — meta.TypeDefExpand
// recovers the orientation from the meta's stored pair pointers. source
// must alpha-equal the const's stored DefSource (the ⊢ P(_) existence
// theorem) — typically a previously-proved section's Thm.
//
// Reconstructs type-def axioms inline rather than relying on
// env.ThmCache preload (quotient.DeriveTypedef builds on it), mirroring the
// LeafConstDef external-leaf helper (ConstDef) for the other
// kernel-external thm source.
func (s *Script) TypeDefExpand(constName string, source Prop) (Thm, Thm) {
	meta := s.ConstMeta(constName)
	if meta.DefSource() == nil {
		panic(fmt.Sprintf("Script.TypeDefExpand: const %q has nil DefSource "+
			"(meta is not from NewTypeDef)", constName))
	}
	out1, out2 := meta.TypeDefExpand(alignTypeDefSource(meta.DefSource(), source))
	// core.AsThm re-types each output into the graph's Thm currency
	// without forcing, so a promise-backed source threads through as
	// derived promises.
	return core.AsThm(out1), core.AsThm(out2)
}

// alignTypeDefSource lifts a proved existence claim to the defSource
// α-form the kernel's TypeDefExpand precondition demands
// (p.AlphaEquals(defSource)). A claim threaded from a prior section or
// a typed dep carries the statement that section stated, which may be
// a Normalize-variant of the stored defSource rather than its α-form;
// when Normalize(defSource) and Normalize(source) coincide, Normalize's
// reconstruct callback lifts the proved normalized source back to
// defSource's exact α-form (kernel-derived and promise-transparent).
//
// Returns source unchanged when no lift applies (already α-equal,
// hyp-bearing shapes, or a genuine mismatch — the kernel's own assert
// then reports it).
func alignTypeDefSource(defSource, source Prop) Prop {
	if defSource == nil || source == nil || source.AlphaEquals(defSource) {
		return source
	}
	if defSource.NumHyps() != 0 || source.NumHyps() != 0 {
		return source
	}
	ndef, reconstruct := prop.Normalize(defSource)
	nsrc, _ := prop.Normalize(source)
	if ndef.AlphaEquals(nsrc) {
		if bridged := reconstruct(nsrc); bridged != nil && bridged.AlphaEquals(defSource) {
			return bridged
		}
	}
	return source
}

// TypeDefSource returns a trusted Thm of the named NewTypeDef const's
// stored existence source (⊢ ∃x. P x), suitable as the `source`
// argument to TypeDefExpand. By construction it α-equals
// meta.DefSource(), so the kernel's TypeDefExpand precondition holds.
//
// The existence claim is the one the type definition recorded on the
// meta: a certificate when the inhabitation was proved at registration,
// the promise of the inhabitation entry otherwise.
// ext.TypeDefSourceThm returns it as a certificate
// (forcing a promise) — nothing is trusted. Used by emit when
// the existence claim is not available as a proved prior section (it
// routinely Normalizes to ⊤ and lands in the shared ⊤-bucket node, which
// can't be threaded as a real sub-proof).
func (s *Script) TypeDefSource(constName string) ThmCert {
	meta := s.ConstMeta(constName)
	if meta.DefSource() == nil {
		panic(fmt.Sprintf("Script.TypeDefSource: const %q has nil DefSource "+
			"(meta is not from NewTypeDef)", constName))
	}
	if s.Env.Forcer != nil {
		return ext.TypeDefSourceThm(meta, *s.Env.Forcer)
	}
	return ext.TypeDefSourceThm(meta, core.NewForcer(context.Background()))
}

// IntOfRealDerive lifts a proven theorem over ℝ to its ℤ analogue
// (omega.IntOfRealThm) — the
// whole body of a registry.Lifted member.
//
// realThm is the source — typically the ℝ twin's entry as a typed dep
// (`ctx.Dep(source)`). Its SURFACE FORM is whatever the ℝ
// entry is stated in — the normalized ∀-form, or any other spelling
// (free-var sequent, reordered binders, …). The lift is made
// surface-agnostic by normalize-first: prop.Normalize canonicalizes the
// source as a kernel-sound derivation (∀-closure is one of its steps),
// and omega.IntOfRealThm lifts that canonical form only. Do NOT teach
// the lift about individual surface shapes — a ∀-strip-only variant
// breaks (on five order lemmas over ℤ, max and min among them) as soon as
// an ℝ source is stated in another spelling.
//
// expected is the member's headline statement (the prop the entry
// registers and a citing consumer is served). The lift output is
// bridged into expected's exact α-form via prop.BridgeNormalize; nil
// (not normalize-equivalent) panics on the spot, so a missing bridge or
// wrong-typed source surfaces at the call site rather than as a
// downstream cite's cache miss or a promise-settle α-mismatch.
//
// The bridge set is installed process-globally via omega.SetIntBridges
// (typically by serve.InstallIntBundle at startup). When unset,
// this method panics with a pointed message — that path catches the
// "bundle not installed" misconfiguration cleanly instead of letting
// the bridge-free lift produce a real_of_int-littered output that
// would silently miss the bridge check.
func (s *Script) IntOfRealDerive(realThm Prop, expected Prop) Thm {
	if s.Scope != nil {
		// The lift's capability is the SOURCE's own key — the chapter
		// source entry's Key, which is its statement's normalized key
		// (the minting rule); the capability was installed under that
		// name from the constructor that lifts it (registry.Lifted).
		sourceNorm, _ := Normalize(realThm)
		s.Scope.RequireCapability(CapabilityIntOfReal + string(sourceNorm.AlphaKey()))
	}
	br := omega.CurrentIntBridges()
	if br == nil {
		panic("Script.IntOfRealDerive: no IntBridges installed. " +
			"Call serve.InstallIntBundle() (or omega.SetIntBridges(...)) " +
			"before forcing any int_of_real-derived theorem.")
	}
	// Canonicalize the source surface. Statement-level and
	// promise-transparent (same family as BridgeNormalize below), so a
	// LazyBuild statement-promise source threads through unforced.
	normSrc, _ := prop.Normalize(realThm)
	out := omega.IntOfRealThm(prop.WrapProp(normSrc), br)
	bridged := prop.BridgeNormalize(expected, out.Core())
	if bridged == nil {
		gotNorm, _ := prop.Normalize(out.Core())
		wantNorm, _ := prop.Normalize(expected)
		panic(fmt.Sprintf("Script.IntOfRealDerive: lift output is not "+
			"normalize-equivalent to the expected statement.\n"+
			"  source thm: %s\n  lifted concl: %s\n  expected:  %s\n"+
			"  normalized key: %s\n  expected key:  %s\n"+
			"This usually means the IntBridges set is incomplete (missing "+
			"Eq/Le/Lt/OfNum/Add/Mul/Neg/Sub for the operators the source "+
			"theorem over ℝ uses), so the lift left some real_of_int residue.",
			prop.PrintProp(realThm), prop.PrintProp(out.Core()),
			prop.PrintProp(expected),
			gotNorm.AlphaKey(), wantNorm.AlphaKey()))
	}
	return core.AsThm(bridged)
}

// TypeDefAxiomSel picks which of the two outputs of
// (ConstTermMeta).TypeDefExpand the TypeDefAxiom helper returns.
// Threaded by emit through the `ctx.TypeDefAxiom(name, which)` call
// sites it renders for LeafTypeDefAxiom external leaves; mirror of
// library/emit.TypeDefAxiomSel.
type TypeDefAxiomSel int

const (
	// TypeDefAbsRep selects ⊢ abs(rep a) = a (TypeDefExpand's first
	// output).
	TypeDefAbsRep TypeDefAxiomSel = iota
	// TypeDefPredRep selects ⊢ P(r) ⇔ rep(abs r) = r (TypeDefExpand's
	// second output).
	TypeDefPredRep
)

// TypeDefAxiom returns one of the two type-def axioms a NewTypeDef
// abs/rep pair makes available via TypeDefExpand, identified by `which`
// — TypeDefAbsRep for ⊢ abs(rep a) = a, TypeDefPredRep for
// ⊢ P(r) ⇔ rep(abs r) = r. constName may be either half of the pair
// (meta.TypeDefExpand recovers orientation from the pair pointer).
//
// Mirrors the LeafConstDef → ConstDef external-leaf helper for the
// NewTypeDef case. The
// source ⊢ ∃x. P(x) is rebuilt via TypeDefSource
// (ext.TypeDefSourceThm); meta.TypeDefExpand's
// deriveProp then lifts both outputs to ThmCerts under that Proved
// source.
//
// The chosen output is Normalize'd before return (mirroring
// ConstDefNormalized): these axioms are keyed by their normalized form
// (e.g. `∀a. a = mk(dest a)`, not the raw kernel form `mk(dest a) = a`
// that TypeDefExpand emits), so a cite of the axiom lines up against the
// normalized α-key. registerKnownThm caches
// the result under both raw and normalized keys, matching the pattern
// every other external-leaf helper uses for cite resolution.
func (s *Script) TypeDefAxiom(constName string, which TypeDefAxiomSel) ThmCert {
	meta := s.ConstMeta(constName)
	srcThm := s.TypeDefSource(constName)
	out1, out2 := meta.TypeDefExpand(srcThm)
	var raw Prop
	switch which {
	case TypeDefAbsRep:
		raw = out1
	case TypeDefPredRep:
		raw = out2
	default:
		panic(fmt.Sprintf("Script.TypeDefAxiom: invalid which=%d for const %q",
			which, constName))
	}
	// raw is ThmCert under a Proved srcThm — deriveProp lifts when all
	// deps are Proved.
	rawCert, ok := raw.(ThmCert)
	if !ok {
		panic(fmt.Sprintf("Script.TypeDefAxiom: TypeDefExpand output for const %q "+
			"(which=%d) is not *ThmCert (got %T) — TypeDefSource returned a "+
			"Proved cert so deriveProp should have lifted both outputs",
			constName, which, raw))
	}
	norm, _ := Normalize(rawCert)
	return s.registerKnownThm(norm).AsThmCert()
}

// ----- The auto closers ----------------------------------------------------
//
// The two Macro-valued constructors that remain: the `auto` closer and
// its Normalize→⊤-first variant. Every other Action-level constructor
// this block once held (Induct, Use, UseThm, DefExpand, ByCase, Assert,
// TypeInstFrom, CloseByNormalize, RecallCached) wrapped a ministep with
// a post-simplification the chapter form never records; see macro.go's
// header for why none exists. The ministep
// constructors below (InductStep, ByCaseStep, AssertStep,
// ExistentialConstDefStep, Lemma, TypeInst…) are the whole surface.

// Auto runs the CNF refuter on the current goal. Wraps env.AutoExpand().
func (s *Script) Auto() Macro {
	return s.Env.AutoExpand()
}

// CloseByAuto returns an Action that mirrors the *GoalStackNode method
// of the same name — Normalize→⊤ first, fall back to AutoExpand. Used
// as a Step expression inside Case bodies. See prover.CloseByAuto for
// the recording-side rationale.
func (s *Script) CloseByAuto() Macro {
	return _CloseByAutoAction{env: s.Env}
}

type _CloseByAutoAction struct {
	env *ProverEnv
}

func (_CloseByAutoAction) String() string { return "CloseByAuto" }

func (a _CloseByAutoAction) Apply(n *GoalStackNode) bool {
	return CloseByAuto(n, a.env)
}

func (a _CloseByAutoAction) applyAction(_ *Script, root *GoalStackNode) {
	applyMacro(root, a)
}

// inductionTemplateFor resolves the induction principle for v's type
// from env.LibraryThms and parses it into a template — the SAME name
// convention + polymorphic type-instantiation the engine's tactic
// dispatch uses at record time (tactic.PrincipleNameCandidates /
// tactic.AnalyzePrincipleForType), so a recorded Induct replays
// against the identical template. Panics on a missing / malformed
// principle, matching the fail-fast policy of Script.LibraryThm.
func (s *Script) inductionTemplateFor(v core.VarTerm) *tactic.InductionTemplate {
	t := v.Type()
	candidates := tactic.PrincipleNameCandidates(t)
	if len(candidates) == 0 {
		panic(fmt.Sprintf("Script: induction on %s: type %s is not an inductive composite type",
			ext.PrintTerm(v), t.Key()))
	}
	for _, name := range candidates {
		thm, ok := s.Env.LookupLibraryThm(name)
		if !ok || thm == nil {
			continue
		}
		tmpl, err := tactic.AnalyzePrincipleForType(thm, t)
		if err != nil {
			panic(fmt.Sprintf("Script: induction principle %q has unsupported shape: %v", name, err))
		}
		if tmpl == nil {
			// Principle exists but its index type can't be unified
			// with v's type. Try the next candidate.
			continue
		}
		return tmpl
	}
	panic(fmt.Sprintf("Script: induction on %s: no principle for type %s preloaded into env.LibraryThms (looked for %v)",
		ext.PrintTerm(v), t.Key(), candidates))
}

// ----- Ministep API --------------------------------------------------------
//
// The MiniStep API runs at one level finer than Action: each ministep is a
// pure function from a goal Prop to a SubGoals tree. Used by members emitted
// from a session's DetailedProofProto (ministep-level tactics like
// strip_quant / witness / specialize / subst / lean_rw).
//
// Hand-written scripts can mix the two styles: an Action-level section uses
// `g.Apply(ctx.Foo())`, while a ministep-level section uses
// `ctx.Do(g, ctx.FooStep())` for each ministep in preorder.

// Step is the exported alias for the package-private _MiniStep
// interface. Exported so emitted members in other packages can pass
// ministep values around if needed; in practice callers just chain
// `ctx.Do(g, ctx.Foo())` and never name the type directly.
type Step = _Step

// Do applies one Step to the first unsolved leaf reachable from
// `focus` in preorder (DFS): each StepProto in a recorded section's
// preorder list corresponds to one `ctx.Do(section, step)` call.
//
// Special handling for _KnownThmStep: first try the theorem carried by the
// step itself, then fall back to cache lookup (LocalThmCache → env.ThmCache).
// The direct path keeps Script.Do aligned with GoalStackNode.runStep and the
// recorder's _KnownThmStep.apply semantics: if the recorded stronger theorem is
// already available as a realized cert or promise, replay should use that exact
// theorem instead of rediscovering one through cache state. The cache fallback
// serves a step whose payload is only a lookup key.
//
// Panics on failure (no matching cached thm, or runStep refuses the
// step). An emitted member is not expected to fail; if it does,
// the panic carries the offending leaf goal for diagnostics.
func (s *Script) Do(focus *GoalStackNode, step _Step) {
	leaf := focus.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("Script.Do: focus has no unsolved leaves remaining "+
			"(section already proved — extra Do call?) step=%v", step) + closedLeafNote(focus))
	}
	// Env injection for state-carrying Steps: the package-level (and
	// Script-method) constructors return nil-env values; env must come
	// from the Script actually running them, threaded here. A non-nil env
	// at this point means the step was constructed against a different
	// Script's env — that's a bug (silently preserving the old env would
	// yield replay divergence at the tryCNFRefute cache-key), so assert
	// instead of a soft mismatch. Internal call sites that build these
	// steps with an env explicitly (AutoExpand.Apply, CloseByCNFRefute,
	// set_tac.apply, tactic_apply) bypass Script.Do and call runStep
	// directly, so this switch never fires for them.
	switch cur := step.(type) {
	case _CNFRefute:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _SetTacStep:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _SetTacDoor:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _ByStep:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _DefineStep:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _DefineDataStep:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _DefineSpecStep:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _DefineInductiveStep:
		// Pure kernel derivation over the record: no env to inject.
		step = cur
	case _DefineQuotientStep:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	case _ElementarityStep:
		Assert(cur.env == nil)
		cur.env = s.Env
		step = cur
	}
	if known, ok := step.(_KnownThmStep); ok {
		if known.strongerGoal != nil &&
			(known.strongerGoal.Proved() || core.IsPromised(known.strongerGoal)) &&
			IsStronger(known.strongerGoal, leaf.Goal) {
			s.ClaimProvedThm(known.strongerGoal)
			if !leaf.runStep(known) {
				panic(fmt.Sprintf("Script.Do: ministep %v failed", step))
			}
			return
		}
		if !TryMatchKnownThm(s.LocalThmCache, leaf) &&
			!TryMatchKnownThm(&s.Env.ThmCache, leaf) {
			panic(fmt.Sprintf("Script.Do(KnownThm): no matching cached thm " +
				"for leaf goal — local + env caches both miss"))
		}
		return
	}
	if !leaf.runStep(step) {
		// Per-tactic diagnostics augment the generic message when the
		// failure mode is identifiable — kernel refusal reasons that a
		// naked "ministep %v failed" swallows. Extend this switch when
		// a new tactic gains a corresponding Analyze* single-source-of-
		// truth (see tactic.AnalyzeByCase for the pattern).
		var extra string
		switch cur := step.(type) {
		case _AssertStep:
			// The assert declines exactly two claims (tactic.AssertTactic):
			// one that is the goal's conclusion and one that is resident.
			claim := cur.claim.Conclusion()
			switch {
			case leaf.Goal.Conclusion().AlphaEquals(claim):
				extra = "\n  reason: the claim is the goal's conclusion (α-equal) — proving it is proving the goal, " +
					"so an assert of it adds nothing and leaves the same goal. Close the goal with the proof " +
					"the claim carried: Show in place of Have or Obtain, with the same actions."
			case goalHasHypAlpha(leaf.Goal, claim):
				extra = "\n  reason: the claim is already a hypothesis (α-equal) — an assert adds nothing; cite the hypothesis."
				if !ext.MatchesEXISTS(claim).IsZero() {
					extra += " A resident ∃-fact is opened with Unpack, which takes the witness's name " +
						"(Unpack(fact, \"a\")); Obtain is for an ∃-claim still to be proved."
				}
			}
		case _ByCaseStep:
			kind, _, _ := tactic.AnalyzeByCase(leaf.Goal, cur.caseTerm)
			switch kind {
			case tactic.ByCaseConclIsPositive:
				extra = "\n  reason: case term α-equals the goal's conclusion — ByCase would produce trivial (assume φ ⊢ φ) + original-shape branches. Use AssertStep((φ) ∨ (¬φ)) + SplitDisj instead."
			case tactic.ByCaseConclIsNegative:
				extra = "\n  reason: ¬(case term) α-equals the goal's conclusion — symmetric no-op. Use AssertStep((φ) ∨ (¬φ)) + SplitDisj instead."
			case tactic.ByCaseHypIsPositive:
				extra = "\n  reason: case term is already a hypothesis — true-branch would just restate it."
			case tactic.ByCaseHypIsNegative:
				extra = "\n  reason: ¬(case term) is already a hypothesis — false-branch would just restate it."
			}
		}
		panic(fmt.Sprintf("Script.Do: ministep %v failed%s\n  on leaf goal: %s",
			step, extra, prop.PrintProp(leaf.Goal)))
	}
	// If the ministep value carries Case bodies (case-eligible
	// multi-residual types: _SplitConj / _SplitDisj / _SplitIff /
	// _SplitHypIff / _SplitHypImply / _ByCaseStep / _InductionStep /
	// _LemmaTactic / _AssertStep), dispatch each body against the
	// corresponding child positionally. Empty cases is the legacy
	// form — no dispatch.
	if cc, ok := step.(caseCarrier); ok {
		dispatchCases(s, leaf, step, cc.caseBodies())
	}
}

// ----- Parameterless ministep constructors ---------------------------------
//
// The Script-method form is kept so hand-written `ctx.Basic()` etc.
// stay compiling; the package-level form is what emit-output bodies
// use to drop the `ctx.` prefix.

func (s *Script) Basic() Step             { return Basic() }
func (s *Script) TrivialSimplify() Step   { return TrivialSimplify() }
func (s *Script) TrivialNormalized() Step { return TrivialNormalized() }
func (s *Script) CondRewrite() Step       { return CondRewrite() }

// Rewrite at the Script level is the no-arg rewrite ministep
// (renamed to RewriteAuto at package level to free `Rewrite` for the
// fused 2-arg `Rewrite(d Prop, c Term) Step` constructor used inside
// Case bodies). Kept on Script so hand-written scripts can write
// `ctx.Rewrite()` per the existing convention.
func (s *Script) Rewrite() Step                   { return RewriteAuto() }
func (s *Script) SplitConj(cases ...Case) Step    { return SplitConj(cases...) }
func (s *Script) SplitConjAll(cases ...Case) Step { return SplitConjAll(cases...) }
func (s *Script) SplitDisj(left DisjLeftHolds, right DisjRightHolds) Step {
	return SplitDisj(left, right)
}
func (s *Script) StripImp() Step                   { return StripImp() }
func (s *Script) StripQuant() Step                 { return StripQuant() }
func (s *Script) StripQuant1() Step                { return StripQuant1() }
func (s *Script) SplitHypImply(cases ...Case) Step { return SplitHypImply(cases...) }
func (s *Script) SplitIff(forward IffForward, backward IffBackward) Step {
	return SplitIff(forward, backward)
}
func (s *Script) SplitHypIff(both IffBothHold, neither IffNeitherHolds) Step {
	return SplitHypIff(both, neither)
}
func (s *Script) Assumption() Step { return Assumption() }
func (s *Script) Refl() Step       { return Refl() }
func (s *Script) Left() Step       { return Left() }
func (s *Script) Right() Step      { return Right() }
func (s *Script) Funext() Step     { return Funext() }
func (s *Script) ByContra() Step   { return ByContra() }
func (s *Script) Symm() Step       { return Symm() }
func (s *Script) Congr() Step      { return Congr() }

// Arith is the unified arithmetic-automation ministep (prover/solver/omega,
// run through tactic.ArithTactic): the conclusion is decided under the
// hypotheses and each hypothesis under the others, every atom by its operand
// type (num, int, real), through the identity folds, ring and linarith over
// the monomial basis, the integer layer and the case-split handlers; agents
// call it without predicting which procedure fires. Parameterless — the
// proof is determined by the goal — so replay re-runs the same dispatch.
// Kept on Script so hand-written scripts can write `ctx.Arith()`.
func (s *Script) Arith() Step { return Arith() }

// RingNf is the ring-normal-form rewrite (prover/solver/omega ring_nf.go):
// every arithmetic subterm of the goal — conclusion and hypotheses — to the
// sum of monomials the ring normalizer reads, unit coefficients and a zero
// constant elided. The rewrite beside Arith's closer: where Arith proves
// `l = r` and says nothing about a term that is not one side of an
// equation, RingNf puts every polynomial in one spelling. Parameterless.
func RingNf() Step             { return _RingNormalize{} }
func (s *Script) RingNf() Step { return RingNf() }

func Basic() Step             { return _BasicTactic{} }
func TrivialSimplify() Step   { return _TrivialSimplify{} }
func TrivialNormalized() Step { return _TrivialNormalizedStep{} }
func CondRewrite() Step       { return _CondRewrite{} }

// RewriteAuto is the no-arg ministep that runs the kernel's
// auto-rewrite tactic. The `Rewrite` identifier is the 2-arg fused
// `Rewrite(d Prop, c Term)` constructor's (the `LeanRw(d) +
// AxiomDefStep(c)` idiom as a runtime value, for use inside Case
// bodies and the unified Prove API).
func RewriteAuto() Step { return _Rewrite{} }

// SplitConj / SplitDisj / SplitIff / SplitHypIff / SplitHypImply are
// case-eligible multi-residual ministeps. Variadic Case args populate
// the embedded `cases []Case` slice; Script.Do dispatches each body
// positionally against the matching child subgoal after the kernel
// ministep produces children. Empty Case args = legacy form (no
// dispatch), preserving back-compat with proto-deserialized and
// hand-written `SplitConj()` call sites.
func SplitConj(cases ...Case) Step      { return _SplitConj{cases: cases} }
func SplitConjAll(cases ...Case) Step   { return _SplitConjAll{cases: cases} }
func SplitDisjCases(cases ...Case) Step { return _SplitDisj{cases: cases} }
func StripImp() Step                    { return _StripImp{} }
func StripQuant() Step                  { return _StripQuant{} }

// StripQuantAt is ∃-elimination on the hypothesis AT hypIdx: its
// leading ∃-prefix is Skolemized and nothing else moves — the
// conclusion keeps its ∀-prefix. StripQuant's pick-first form strips
// the conclusion first and otherwise opens the first ∃-hyp it scans
// to. This is the step a session records when `strip_quant` names a
// hyp_index, and emit renders it back through this factory so the
// index round-trips. A chapter author eliminates an established
// existential with a.Unpack or a.Obtain, which name the fact rather
// than its slot and record this step at the slot they resolve.
func StripQuantAt(hypIdx int) Step { return _StripQuant{hypIndex: &hypIdx} }

// StripQuant1 is the bounded single-binder strip ministep: peel
// EXACTLY ONE leading conclusion ∀ (Skolemizing that binder only),
// leaving inner quantifiers intact. Conclusion side only — it never
// Skolemizes ∃-hyps (use StripQuant for that). Fails (Script.Do
// panics) when the conclusion is not ∀-headed. For "strip exactly n"
// with an up-front binder-count check, use the StripQuantN Action.
func StripQuant1() Step                { return _StripQuant1{} }
func SplitHypImply(cases ...Case) Step { return _SplitHypImply{cases: cases} }

// SplitIff splits an ⇔ GOAL into its two directions, each named by the
// half it proves rather than by the slot it sits in (iff_direction.go).
// The tactic emits the ⇐ child first; that is this constructor's
// business, not the author's.
func SplitIff(forward IffForward, backward IffBackward) Step {
	return SplitIffCases(backward.c, forward.c)
}

// SplitHypIff splits an ⇔ HYPOTHESIS into the branch where both sides
// hold and the branch where neither does — not into directions.
func SplitHypIff(both IffBothHold, neither IffNeitherHolds) Step {
	return SplitHypIffCases(both.c, neither.c)
}

// SplitIffCases / SplitHypIffCases / SplitHypIffAtCases are the
// positional bottoms the named forms are built on. emit renders the
// CASELESS form through them when a split's children did not become a
// Case block; a chapter body authors neither (the labeled call is a
// lint error — TestLintNoPositionalIffCases).
func SplitIffCases(cases ...Case) Step    { return _SplitIff{cases: cases} }
func SplitHypIffCases(cases ...Case) Step { return _SplitHypIff{cases: cases} }
func SplitHypIffAtCases(hypIdx int, cases ...Case) Step {
	return _SplitHypIff{cases: cases, hypIndex: &hypIdx}
}

// SplitDisjAt / SplitHypIffAt / SplitHypImplyAt are the index-targeted
// variants: split the hyp AT hypIdx, not the first ∨/⇔/⇒-shaped one.
// The pick-first factories (SplitDisj / SplitHypIff / SplitHypImply)
// remain for existing call sites and pre-payload proto records that
// deserialize with hypIndex=nil — semantics identical to before.
//
// emit renders a ministep with an explicit index through these
// factories so a recorded hyp_index round-trips into the emitted
// member without silent drop.
func SplitDisjAtCases(hypIdx int, cases ...Case) Step {
	return _SplitDisj{cases: cases, hypIndex: &hypIdx}
}
func SplitHypIffAt(hypIdx int, both IffBothHold, neither IffNeitherHolds) Step {
	return SplitHypIffAtCases(hypIdx, both.c, neither.c)
}
func SplitHypImplyAt(hypIdx int, cases ...Case) Step {
	return _SplitHypImply{cases: cases, hypIndex: &hypIdx}
}
func Assumption() Step { return _Assumption{} }
func Refl() Step       { return _Refl{} }
func Left() Step       { return _Left{} }
func Right() Step      { return _Right{} }
func Funext() Step     { return _Funext{} }
func ByContra() Step   { return _ByContra{} }
func Symm() Step       { return _Symm{} }
func Congr() Step      { return _Congr{} }

// Arith is the unified num-arithmetic ministep: tries the commutative-
// semiring normalizer (omega.RingProveFull via tactic.RingTactic) first, then
// falls back to ℚ-Farkas + integer extension (the strongest sound integer
// procedure, tactic.OmegaTactic). Parameterless — determined by the goal, so
// replay re-runs the same dispatch. emit renders it as the bare `Arith()`
// ministep form (via `<sx>.Do(Arith())`).
func Arith() Step { return _Arith{} }

// CnfRefute returns a nil-env step; env is injected by Script.Do at
// execution time (see the env-injection switch there). This lets emit
// render bare `CnfRefute()` inside `.Do(...)` instead of `ctx.CnfRefute()`.
// The Script-method form is kept as a delegating alias so hand-written
// `ctx.CnfRefute()` calls still compile — under the same nil-env-then-
// inject contract.
func CnfRefute() Step             { return _CNFRefute{ctx: context.Background()} }
func (s *Script) CnfRefute() Step { return CnfRefute() }

// ----- Parameterized ministep constructors ---------------------------------

// Witness / Instantiate / Subst / Trans — all pure struct-literal sugar
// around the corresponding ministep types. Methods delegate to the
// package-level form; emit prefers the bare form.
//
// Index-targeted instantiation is `SpecializeKeep(InstHyp(i, t))` — the
// batch composite peeling one binder with keepSources=true.

func (s *Script) Witness(t TermLike) Step       { return Witness(t) }
func (s *Script) Instantiate(t core.Term) Step  { return Instantiate(t) }
func (s *Script) Subst(hypIdx int) Step         { return Subst(hypIdx) }
func (s *Script) Rw(hypIdx int, flip bool) Step { return Rw(hypIdx, flip) }
func (s *Script) Trans(t core.Term) Step        { return Trans(t) }

// Witness supplies the witness t: ⊢ ∃x.P(x) becomes ⊢ P(t), and
// ⊢ ∃!x.P(x) becomes ⊢ P(t) ∧ (∀y. P(y) ⇒ y = t).
func Witness(t TermLike) Step { return _WitnessStep{witness: ext.CoreOf(t)} }

// Instantiate adds P(t) to the hyps when a ∀-headed hyp ∀x.P(x) exists
// whose binder type matches t. Picks the first such hyp.
//
// Go-only (the step has no wire form): a session grounds through
// Specialize/SpecializeKeep, the composite `specialize` step.
func Instantiate(t core.Term) Step { return _InstantiateStep{witness: t} }

// SpecializeHyp names one entry of a Specialize step: ground the ∀-hyp
// at hypIdx by peeling one leading binder per term, in binder order.
type SpecializeHyp = tactic.SpecializeSpec

// InstHyp builds one Specialize entry: hyps[hypIdx] is ∀-headed;
// peel its leading binders at terms (one binder per term, in order).
func InstHyp(hypIdx int, terms ...core.Term) SpecializeHyp {
	return SpecializeHyp{HypIndex: hypIdx, Witnesses: terms}
}

// Specialize grounds one or more ∀-hyps in ONE step: for each entry the
// final ground instance is added as a new hyp (intermediate partial
// instantiations never materialize) and the source ∀-hyp is dropped —
// the Lean `specialize h a b c` semantics. All entries' hyp indices
// refer to this step's own input goal (ClearHyps' atomic-set
// convention). Use SpecializeKeep to keep the sources available.
//
// The composite records the whole net transition as ONE ministep, so
// N-witness grounding is one recorded step, not N+1.
func Specialize(hyps ...SpecializeHyp) Step {
	return _SpecializeStep{specs: hyps}
}

// SpecializeKeep is Specialize with the grounded source ∀-hyps kept in
// place (the ematch contract: only ADD hyps — one wide ∀-hyp may serve
// several witness tuples).
func SpecializeKeep(hyps ...SpecializeHyp) Step {
	return _SpecializeStep{specs: hyps, keepSources: true}
}

func (s *Script) Specialize(hyps ...SpecializeHyp) Step     { return Specialize(hyps...) }
func (s *Script) SpecializeKeep(hyps ...SpecializeHyp) Step { return SpecializeKeep(hyps...) }

// Subst substitutes using the equality at hyps[hypIdx] (must be an
// equality between a free variable and a term).
func Subst(hypIdx int) Step { return _SubstStep{hypIndex: hypIdx} }

// Rw rewrites with the equality at hyps[hypIdx] to fixpoint across the
// conclusion and all other hyps, in the hyp's written direction
// (flip=false) or reversed (flip=true). The fixpoint,
// direction-controlled counterpart of Subst.
func Rw(hypIdx int, flip bool) Step { return _RwStep{hypIndex: hypIdx, flip: flip} }

// CongrArg / CongrFun — forward congruence on an equality hyp.
// CongrArg supplies the function fn: hyps[hypIdx] `a = b`
// yields the added hyp `fn(a) = fn(b)`. CongrFun supplies the argument
// arg: hyps[hypIdx] `f = g` yields `f(arg) = g(arg)`. emit
// renders both from StepProto_Congr{Arg,Fun}.
func CongrArg(fn core.Term, hypIdx int) Step  { return _CongrArgStep{fn: fn, hypIndex: hypIdx} }
func CongrFun(arg core.Term, hypIdx int) Step { return _CongrFunStep{arg: arg, hypIndex: hypIdx} }

// ClearHyps drops the SET of hyps at hypIndices in one step (Lean's
// `clear`; proto tag `clear_hyps`). All indices refer to
// the same goal's hyp list — removed atomically, no sequential shifting.
func ClearHyps(hypIndices ...int) Step { return _ClearHypsStep{hypIndices: hypIndices} }

func (s *Script) CongrArg(fn core.Term, hypIdx int) Step  { return CongrArg(fn, hypIdx) }
func (s *Script) CongrFun(arg core.Term, hypIdx int) Step { return CongrFun(arg, hypIdx) }
func (s *Script) ClearHyps(hypIndices ...int) Step        { return ClearHyps(hypIndices...) }

// Trans splits ⊢ a = c via the middle term b, producing subgoals
// ⊢ a = b and ⊢ b = c.
func Trans(t core.Term) Step { return _TransStep{middle: t} }

// Denote is the SEARCH form of the denote ministep: it names whichever
// subterm the heuristic picks (ext.FrequentSubTerms above
// sizeThreshold), under a minted α₀.
//
// It is NOT part of the authoring surface — the alias
// generator excludes the name, so a file writing `Denote(8)`
// does not compile, and `Denote` inside a chapter package means
// Argument.Denote. It stays exported because it is (a) the stage auto /
// expand run and (b) what emit renders for a recorded denote that
// carries no explicit choice (a size-only record).
//
// A hand-written denote is DenoteTerm(name, term) — say what you are
// naming and what you are calling it.
//
// The threshold is OPTIONAL: omitted, it is the engine's own denote
// threshold — the one `auto` and `expand` run at — so no proof copies
// the number. Pass a size only to denote at a threshold that is
// deliberately not the engine's.
func (s *Script) Denote(sizeThreshold ...int) Step { return Denote(sizeThreshold...) }
func Denote(sizeThreshold ...int) Step {
	return _AutoDenote{sizeThreshold: denoteSize(sizeThreshold)}
}

// DenoteTerm is the EXPLICIT denote ministep — "let name = term". It
// names THAT subterm by THAT variable, so the script says what was
// abbreviated and the record carries the decision instead of a recipe
// replay must re-derive.
//
//	DenoteTerm("d", v.sum(v.at(x, n), v.at(y, n)))
//
// Panics at this step when the goal's hypotheses / negated conclusion do
// not contain the term, or when the name is already free in them.
func (s *Script) DenoteTerm(name string, term core.Term) Step {
	return DenoteTerm(name, term)
}
func DenoteTerm(name string, term core.Term) Step {
	return _AutoDenote{term: term, name: name}
}

// LetTerm is the DEFINITIONAL ministep — "let name := term": the
// equation `name = term` joins the hypotheses, every occurrence of the
// term in the goal becomes the name, and the goal keeps its form; the
// term need not occur. DenoteTerm's twin for a definition rather than
// an abbreviation — see Argument.Let, the verb.
//
//	LetTerm("w", a.Term("vsub(vsmul(‖v‖_n, u), vsmul(‖u‖_n, v))"))
//
// Panics at this step when the name is already free in the goal.
func (s *Script) LetTerm(name string, term core.Term) Step {
	return LetTerm(name, term)
}
func LetTerm(name string, term core.Term) Step {
	return _AutoDenote{term: term, name: name, let: true}
}

// denoteTermOptional is DenoteTerm that declines rather than panics when
// the leaf does not contain the term — the By shaping preamble's flavor
// (see ByShape and _AutoDenote.optional). Unexported: an authoring verb
// that silently does nothing is exactly what this change is retiring.
func denoteTermOptional(name string, term core.Term, hilbert bool) Step {
	return _AutoDenote{term: term, name: name, hilbert: hilbert, optional: true}
}

// denoteSize resolves the optional threshold shared by Denote, Denoted
// and DenoteRefute.
func denoteSize(size []int) int {
	switch len(size) {
	case 0:
		return _DENOTE_SIZE_THRES
	case 1:
		return size[0]
	default:
		panic(fmt.Sprintf("proof.Denote: at most one size threshold, got %d", len(size)))
	}
}

// HilbertDenote is the SEARCH form for ε-terms: it abstracts whichever
// ε-subterm the scan finds first (hypotheses, then conclusion) under a
// minted α₀, adding the ε's defining existential as a hypothesis.
// Explicit twin: HilbertDenoteTerm.
func (s *Script) HilbertDenote() Step { return HilbertDenote() }
func HilbertDenote() Step             { return _AutoDenote{hilbert: true} }

// HilbertDenoteTerm is the EXPLICIT ε-denote — "let name = εx.P(x)".
// Same transform as HilbertDenote (the ε-term is replaced by the named
// variable and its defining existential joins the hypotheses), with the
// ε-term given rather than searched for.
//
// Panics when the term is not an ε-term, when neither the hypotheses nor
// the conclusion contain it, or when the name is already free in them.
func (s *Script) HilbertDenoteTerm(name string, term core.Term) Step {
	return HilbertDenoteTerm(name, term)
}
func HilbertDenoteTerm(name string, term core.Term) Step {
	return _AutoDenote{hilbert: true, term: term, name: name}
}

// LeanRw / TypeInst / Cite / ByCaseStep / AssertStep are pure
// struct-literal sugar — methods delegate to package-level forms.
//
// (There is no `Script.Lemma` ministep method: `Script.Lemma` is the
// SECTION verb — see section.go. The package-level `Lemma(…)`
// is the ministep form emit renders.)

func (s *Script) LeanRw(lemma Prop) Step         { return LeanRw(lemma) }
func (s *Script) LemmaPreserve(lemma Prop) Step  { return LemmaPreserve(lemma) }
func (s *Script) TypeInst(source Prop) Step      { return TypeInst(source) }
func (s *Script) CiteKnown(stronger Prop) Step   { return CiteKnown(stronger) }
func (s *Script) CiteNode(n *GoalStackNode) Step { return CiteNode(n) }
func (s *Script) ByCaseStep(t core.Term, cases ...Case) Step {
	return ByCaseStep(t, cases...)
}
func (s *Script) AssertStep(claim Prop, cases ...Case) Step {
	return AssertStep(claim, cases...)
}

// Lemma applies a lemma at the ministep level. Creates 1 child (the
// lemma itself) when the goal exactly matches, or 2 children (lemma +
// residual) when matching is partial. Downstream ministeps in the proto
// preorder close each child in turn — typically a _KnownThmStep on
// child(0) and _TrivialSimplify on child(1).
//
// The Prop argument should be a proved Prop (a Thm value satisfies
// this); the kernel checks the Proved() bit at apply time. Variadic
// Case args (used by emitted members in the 2-child branching
// shape; ignored when fusion produces a Cite call site) populate
// the embedded `cases []Case` slice for Script.Do dispatch.
func Lemma(lemma Prop, cases ...Case) Step {
	return _LemmaTactic{lemma: lemma, cases: cases}
}

// LeanRw is the rewrite-only counterpart of Lemma. Bypasses eqSimplify's
// size-decrease guard, so expansion-style equational rewrites are
// admitted. No fallback to lemmaConclMatch/lemmaHypMatch.
func LeanRw(lemma Prop) Step { return _LeanRwTactic{lemma: lemma} }

// LemmaPreserve is the hypothesis-preserving counterpart of Lemma —
// the replay form of the agent-facing session `lemma` dispatch (proto
// tag `lemma_preserve`). Runs the full LemmaTactic chain but accepts
// its result only when every pre-existing goal hyp survives; otherwise
// adds the lemma's conclusion as a new hypothesis with no
// whole-context simplify. See tactic.LemmaPreserveTactic.
func LemmaPreserve(lemma Prop) Step { return _LemmaPreserveTactic{lemma: lemma} }

// TypeInst closes a goal that is a type-variable instantiation of a
// polymorphic source theorem. The source must be a proved Prop.
func TypeInst(source Prop) Step { return _TypeInstStep{source: source} }

// Cite closes a leaf by citing `stronger` — an already-proved theorem
// or promise that is stronger than the leaf goal (α-equal after
// Normalize, or an ∀-generalized form). Pure cache lookup: no
// adaptation, no lemma tactic — the leaf must match the cited fact
// exactly. Contrast with UseLemma(target) (package Action) which runs
// ApplyLemma first for polymorphic type-adaptation before the same
// KnownThm-style cache close.
//
// Script.Do falls back to local/env cache lookup when `stronger` is
// only a lookup-shaped payload from proto replay (the emitted `CiteKnown(L)`
// call site's arg is informational; the resolver finds the actual
// promise/cert by α-key).
//
// The underlying Step type is _KnownThmStep (proto tag `known_thm`) —
// unchanged, since the proto contract is stable.
func CiteKnown(stronger Prop) Step { return _KnownThmStep{strongerGoal: stronger} }

// CiteNode is CiteKnown's section-node shorthand — replaces the
// boilerplate `CiteKnown(section.PromisedThm())` at emit call sites. The section's
// promise-Thm is threaded so the citation stays lazy (no force here).
func CiteNode(n *GoalStackNode) Step { return CiteKnown(n.PromisedThm()) }

// ByCaseStep performs boolean case analysis on t at the ministep level,
// producing exactly 2 children on the term under one leading ¬ — child
// 0 holds it, child 1 its negation (ByCaseBranch names the child on
// which t itself holds) — the bare split the proto records, with no
// simplification on either branch. Variadic Case args populate the
// embedded `cases []Case` slice for Script.Do dispatch.
func ByCaseStep(t core.Term, cases ...Case) Step {
	return _ByCaseStep{caseTerm: t, cases: cases}
}

// AssertStep introduces a hyp-free boolean claim φ at the ministep level,
// producing exactly 2 children: [Γ ⊢ φ, Γ, φ ⊢ G]. Mirrors Script.Assert
// at the ministep level for use inside DetailedProofProto-style proofs.
// Variadic Case args populate the embedded `cases []Case` slice for
// Script.Do dispatch.
func AssertStep(claim Prop, cases ...Case) Step {
	return _AssertStep{claim: claim, cases: cases}
}

// InductStep applies induction on v at the ministep level. Like
// ByCaseStep this stops at the bare 2-child split; the Action-level
// `Induct` runs _TrivialSimplify on the inductive-step branch.
// Variadic Case args populate the embedded `cases []Case` slice for
// Script.Do dispatch.
func (s *Script) InductStep(v core.Term, cases ...Case) Step {
	iv := v.Core().(core.VarTerm)
	return _InductionStep{
		inductVar: iv,
		template:  s.inductionTemplateFor(iv),
		cases:     cases,
	}
}

// AxiomDefStep — pure struct-literal sugar; method delegates to bare form.
func (s *Script) AxiomDefStep(c core.Term) Step { return AxiomDefStep(c) }

// AxiomDefStep unfolds a const definition at the ministep level. c
// must resolve to a ConstTerm via .Core(). For NewConstDef consts the
// def thm is the single ⊢ c = body equation; for NewTypeDef consts the
// abs / rep axiom is selected based on which half of the pair `c` is.
func AxiomDefStep(c core.Term) Step {
	return _AxiomDefStep{constTerm: c.Core().(core.ConstTerm)}
}

// ExistentialConstDefStep — ministep-level form of ExistentialConstDef,
// the case-bearing counterpart of the ExistentialConstDef Action. The
// action auto-closes the residual (child(1)) via _TrivialSimplify and
// reads as a single-residual chain; this Step leaves both children open
// for explicit Case dispatch (child(0) = existence claim `∃F.P(F)`,
// child(1) = residual carrying `P(c)`). Used by emit for the
// ministep schema.
func (s *Script) ExistentialConstDefStep(c core.Term, cases ...Case) Step {
	return ExistentialConstDefStep(c, cases...)
}

func ExistentialConstDefStep(c core.Term, cases ...Case) Step {
	return _ExistentialConstDefStep{constTerm: c.Core().(core.ConstTerm), cases: cases}
}
