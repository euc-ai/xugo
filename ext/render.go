package ext

import (
	"fmt"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/core"
)

// GoTermPrinter renders Term / Prop / HolType as Go source. Callers
// configure the symbol resolution callbacks; the printer owns the
// shape-recognition / connective dispatch.
type GoTermPrinter struct {
	// VarIdent returns the Go identifier that has been declared at the
	// emit-target's function scope for v. If "" / false, the printer
	// emits an inline ext.Var(name, type) expression.
	VarIdent func(v core.VarTerm) (string, bool)

	// WrapperlessIdent reports that VarIdent's identifier for v is not a
	// *TermWrapper: a closure parameter the section's signature binds, a
	// typed wrapper (*Expr, *Arrow, *Arrow2) or a core Term. The
	// identifier stands where the printed term is an argument a method
	// takes as a TermLike; where the term must be a *TermWrapper or a
	// core Term — a method chain's receiver, a quantifier's binder or
	// body, a Not, Cond or MakeProp operand — v prints as the inline
	// ext.Var(name, type), the same variable.
	WrapperlessIdent func(v core.VarTerm) bool

	// ConstIdent returns the Go identifier declared for c, plus the
	// HolType used at that binding site. When the use-site type differs
	// from declType, the printer emits an inline ext.Const(metaIdent,
	// useType) wrapped in WrapTerm — using the metaIdent returned by
	// ConstMetaIdent. Returns ok=false for consts that have no
	// pre-declared binding (the printer falls back to a defensive
	// inline form for diagnostics).
	ConstIdent func(c core.ConstTerm) (ident string, declType core.HolType, ok bool)

	// ConstMetaIdent returns the Go identifier for the const's *Meta*
	// binding (typically `<ident>Meta`). Required only when ConstIdent
	// returns a binding whose declared type differs from the use-site
	// AND ConstAtType is nil (the legacy `Const(metaIdent, useType)`
	// fallback path).
	ConstMetaIdent func(c core.ConstTerm) string

	// ConstAtType, when non-nil, replaces the legacy
	// `Const(<ident>Meta, useType)` fallback for the off-type case
	// with whatever expression the caller wants. Used by the
	// Script-based emit (library/emit/emit.go) to produce
	// `ctx.Const("name", useType)` — script files don't expose a
	// `<ident>Meta` symbol, so the legacy template wouldn't compile.
	ConstAtType func(c core.ConstTerm) string

	// BareNames omits the `core.` and `ext.` package qualifiers from
	// emitted output (so MakeFun / TypeBool / Var / Const / WrapTerm /
	// ForAll / Exists / Unique / Not / T / F / NOT / AND / OR / IMPLY /
	// FORALL / EXISTS / UNIQUE / COND / MakeVarType / MakeCompositeType
	// / MakeMetaType appear bare). The caller is responsible for
	// declaring matching package-level aliases in the emitted file —
	// see library/emit/emit.go's render() preamble for the
	// canonical alias block.
	BareNames bool

	// StrictConsts makes printConstRef PANIC on a const it cannot
	// resolve (no ConstIdent resolver, or the resolver returns ok=false)
	// instead of emitting the defensive `/* unresolved const */
	// WrapTerm(nil)` placeholder. emit sets this: an unresolved const is
	// always a symbol-collection bug, and the placeholder is a nil term
	// that compiles fine but nil-derefs deep in TestReplayAll — far from
	// the cause. Failing at emit time pins it to the offending proof.
	// Left false for diagnostic / test printers that legitimately have no
	// const resolver wired.
	StrictConsts bool
}

// extQ / coreQ produce a qualified or bare reference depending on
// BareNames. e.g. extQ("Var") → "ext.Var" or "Var".
func (p *GoTermPrinter) extQ(name string) string {
	if p.BareNames {
		return name
	}
	return "ext." + name
}

func (p *GoTermPrinter) coreQ(name string) string {
	if p.BareNames {
		return name
	}
	return "core." + name
}

// dslQ qualifies a symbol that lives in the ext/dsl package (the text
// DSL surface, which also owns the nat-arithmetic vocabulary — NumType
// and the numeric-literal metas). In BareNames mode it collapses to the
// bare identifier, like the other *Q helpers.
func (p *GoTermPrinter) dslQ(name string) string {
	if p.BareNames {
		return name
	}
	return "dsl." + name
}

// PrintTerm produces a Go source expression of static type
// *ext.TermWrapper for t.
func (p *GoTermPrinter) PrintTerm(t core.Term) string {
	// Multi-binder quantifier flattening: ∀x.∀y.…body → ForAll(x,y,…)(body).
	// Same for ∃. Done before the structural switch so deeply nested
	// quantifier chains collapse into one call.
	if vars, body := DecomposesFORALL(t); !vars.Empty() {
		return p.printQuantifierChain(p.extQ("ForAll"), vars, body)
	}
	if vars, body := DecomposesEXISTS(t); !vars.Empty() {
		return p.printQuantifierChain(p.extQ("Exists"), vars, body)
	}
	switch t := t.Core().(type) {
	case core.VarTerm:
		if id, ok := p.VarIdent(t); ok {
			return id
		}
		return p.inlineVar(t)
	case core.ConstTerm:
		return p.printConstRef(t)
	case core.AppliedTerm:
		if s, ok := p.tryPrintConnective(t); ok {
			return s
		}
		// Generic application: flatten App(App(...App(f, x1)...), xN)
		// into one f.Apply(x1, …, xN) call via MatchesApply.
		head, args := MatchesApply(t)
		// COND is the only polymorphic special const printed in applied
		// position. The bare `ext.COND` global (specialConstGoAlias) is a
		// single fixed type-var instance, so `WrapTerm(COND).Apply(args)`
		// panics in the kernel whenever the use-site is a different
		// instance (a law moving a function through a COND applies it at both `A` and `B`;
		// one applying a COND of functions has it at a function type `A→B`). Render the
		// 3-arg COND via the ext.Cond constructor, which instantiates at
		// args[1].Type() so the kernel Apply type-checks. Extra args
		// (COND at a function type, then applied: `COND(b,f,g)(x)`) ride
		// a trailing `.Apply(...)`. Mirrors how ∀/∃/= print structurally.
		if hc, ok := head.Core().(core.ConstTerm); ok &&
			string(hc.Meta().Name()) == string(CondStr) && len(args) >= 3 {
			cond := fmt.Sprintf("%s(%s, %s, %s)", p.extQ("Cond"),
				p.printWrapped(args[0]), p.printWrapped(args[1]), p.printWrapped(args[2]))
			if len(args) == 3 {
				return cond
			}
			return fmt.Sprintf("%s.Apply(%s)", cond, p.printTermList(args[3:]))
		}
		// A Hilbert ε-term that is itself applied: `(εx. P(x))(arg…)`.
		// MatchesApply over-flattens App(App(ε, λx.P), arg) into
		// head=ε, args=[λx.P, arg…], so the immediate-app MatchesHilbert
		// check (printSpecialBinder) never fires and ε prints as a bare
		// unresolved const → WrapTerm(nil) (nil-derefs at replay). Detect
		// the Hilbert head + abstraction first-arg here and render the ε
		// structurally via `.SuchThat`, trailing-applying any extra args.
		if hc, ok := head.AsConst(); ok && hc.Meta().Equals(core.MetaHilbert()) &&
			len(args) >= 1 {
			if abs, ok := args[0].AsAbsTerm(); ok {
				hil := fmt.Sprintf("%s.SuchThat(%s)",
					p.printReceiver(abs.Var()), p.PrintTerm(abs.Body()))
				if len(args) == 1 {
					return hil
				}
				return fmt.Sprintf("%s.Apply(%s)", hil, p.printTermList(args[1:]))
			}
		}
		return fmt.Sprintf("%s.Apply(%s)", p.printReceiver(head), p.printTermList(args))
	case core.AbsTerm:
		// Bare λ outside any quantifier.
		return fmt.Sprintf("%s.To(%s)", p.printReceiver(t.Var()), p.PrintTerm(t.Body()))
	}
	panic(fmt.Sprintf("GoTermPrinter.PrintTerm: unknown term shape %T", t))
}

// PrintProp produces `prop.MakeProp(<concl>, <hyps>...)` (or bare
// `MakeProp(...)` when BareNames is set; the alias is the caller's
// responsibility to declare).
func (p *GoTermPrinter) PrintProp(pr core.Prop) string {
	callee := "prop.MakeProp"
	if p.BareNames {
		callee = "MakeProp"
	}
	parts := []string{p.printWrapped(pr.Conclusion())}
	for i := range pr.NumHyps() {
		parts = append(parts, p.printWrapped(pr.Hyp(i)))
	}
	return fmt.Sprintf("%s(%s)", callee, strings.Join(parts, ", "))
}

// PrintType produces a Go expression of static type core.HolType.
func (p *GoTermPrinter) PrintType(t core.HolType) string {
	switch t := t.(type) {
	case core.VarType:
		return fmt.Sprintf("%s(%q)", p.coreQ("MakeVarType"), string(t.Name()))
	case core.CompositeType:
		return p.printCompositeType(t)
	}
	panic(fmt.Sprintf("GoTermPrinter.PrintType: unknown HolType %T", t))
}

func (p *GoTermPrinter) printCompositeType(t core.CompositeType) string {
	metaName := string(t.Meta().Name())
	arity := t.Meta().Arity()
	// High-frequency aliases (opt-in shortcuts; the generic
	// MakeType fallback below already renders all of these in a
	// readable form). The aliases just save a few characters in
	// the dominant cases.
	switch metaName {
	case "bool":
		return p.coreQ("TypeBool")
	case "num":
		// NumType lives in ext/dsl (next to the nat arithmetic metas in
		// ext/dsl/arith.go), not core. dslQ is the right qualifier in
		// non-BareNames mode; in BareNames mode both qualifiers
		// collapse to the bare identifier.
		return p.dslQ("NumType")
	case "fun":
		// Function types stay on MakeFun: it's a core HOL primitive
		// with curry-aware printing and matches the deserialization
		// convention in core/basic_defs.go.
		if arity == 2 {
			return fmt.Sprintf("%s(%s, %s)", p.coreQ("MakeFun"),
				p.PrintType(t.SubType(0)), p.PrintType(t.SubType(1)))
		}
	}
	// Generic fallback for every other composite type: `MakeType("name", subs...)`.
	// Replaces the previous double-wrapped `MakeCompositeType(MakeMetaType("name", n), …)`
	// form (~40 chars per 0-ary type → 14). Works without per-type
	// configuration; new types added to the corpus render readably
	// the moment they appear.
	args := []string{fmt.Sprintf("%q", metaName)}
	for i := 0; i < arity; i++ {
		args = append(args, p.PrintType(t.SubType(i)))
	}
	return fmt.Sprintf("%s(%s)", p.extQ("MakeType"), strings.Join(args, ", "))
}

// inlineVar is v as the inline ext.Var(name, type), a *TermWrapper.
func (p *GoTermPrinter) inlineVar(v core.VarTerm) string {
	return fmt.Sprintf("%s(%q, %s)", p.extQ("Var"), string(v.Name()), p.PrintType(v.Type()))
}

// printWrapped is PrintTerm where the printed expression must be a
// *TermWrapper or a core Term: a variable whose identifier is neither
// (WrapperlessIdent) prints inline.
func (p *GoTermPrinter) printWrapped(t core.Term) string {
	if v, ok := t.Core().(core.VarTerm); ok && p.WrapperlessIdent != nil && p.WrapperlessIdent(v) {
		return p.inlineVar(v)
	}
	return p.PrintTerm(t)
}

// printReceiver is t printed as a method chain's receiver.
func (p *GoTermPrinter) printReceiver(t core.Term) string {
	return p.ensureChainSafe(p.printWrapped(t))
}

// ensureChainSafe wraps a printed term expression so it can act as the
// receiver of a TermWrapper method chain (.Apply/.Eq/.And/.Or/.Imply/
// .To/.SuchThat). Bare `T`/`F` idents (returned by printConstRef for
// ⊤/⊥ since specialConstGoAlias elides the WrapTerm on those two) are
// core.ConstTerm and thus have no method surface — wrap them back
// into WrapTerm(T)/WrapTerm(F) here. Applied forms already produce
// *TermWrapper via their constructors (Not/Cond/Exists/... — or the
// generic `f.Apply(...)` fallback), and Var idents are *TermWrapper-
// typed by construction (Var returns *TermWrapper), so both classes
// need no wrapping.
func (p *GoTermPrinter) ensureChainSafe(expr string) string {
	switch expr {
	case p.extQ("T"), p.extQ("F"):
		return fmt.Sprintf("%s(%s)", p.extQ("WrapTerm"), expr)
	}
	return expr
}

// tryPrintConnective recognizes the standard logical / equality patterns
// using the standard matchers, then emits the corresponding
// TermWrapper method or function form. Returns false on shapes that
// aren't a known connective; the caller falls back to f.Apply(args...).
//
// Single-binder quantifier patterns (∀/∃) never reach this point —
// PrintTerm's DecomposesFORALL/DecomposesEXISTS pass catches them
// (including the n=1 case).
func (p *GoTermPrinter) tryPrintConnective(app core.AppliedTerm) (string, bool) {
	if l, r, ok := MatchesEQ(app); ok {
		return fmt.Sprintf("%s.Eq(%s)", p.printReceiver(l), p.PrintTerm(r)), true
	}
	if l, r, ok := MatchesAND(app); ok {
		return fmt.Sprintf("%s.And(%s)", p.printReceiver(l), p.PrintTerm(r)), true
	}
	if l, r, ok := MatchesOR(app); ok {
		return fmt.Sprintf("%s.Or(%s)", p.printReceiver(l), p.PrintTerm(r)), true
	}
	if l, r, ok := MatchesIMPLY(app); ok {
		return fmt.Sprintf("%s.Imply(%s)", p.printReceiver(l), p.PrintTerm(r)), true
	}
	if s := MatchesNOT(app); s != nil {
		return fmt.Sprintf("%s(%s)", p.extQ("Not"), p.printWrapped(s)), true
	}
	if abs := MatchesUNIQUE(app); !abs.IsZero() {
		return fmt.Sprintf("%s(%s)(%s)", p.extQ("Unique"),
			p.printWrapped(abs.Var()), p.printWrapped(abs.Body())), true
	}
	if abs := core.MatchesHilbert(app); !abs.IsZero() {
		return fmt.Sprintf("%s.SuchThat(%s)",
			p.printReceiver(abs.Var()), p.PrintTerm(abs.Body())), true
	}
	return "", false
}

func (p *GoTermPrinter) printQuantifierChain(callee string, vars VarList, body core.Term) string {
	parts := make([]string, 0, vars.Size())
	for v := range vars.Iter() {
		parts = append(parts, p.printWrapped(v))
	}
	return fmt.Sprintf("%s(%s)(%s)", callee, strings.Join(parts, ", "), p.printWrapped(body))
}

func (p *GoTermPrinter) printTermList(ts []core.Term) string {
	parts := make([]string, len(ts))
	for i, t := range ts {
		parts[i] = p.PrintTerm(t)
	}
	return strings.Join(parts, ", ")
}

// printConstRef emits a const reference. Special consts (T/F/NOT/AND/
// …/COND) get hand-written aliases that wrap to *TermWrapper for
// uniform method-chain compatibility. Registered consts go through
// ConstIdent; the use-site type may differ from the declared one
// (polymorphic instantiation), in which case we emit an inline
// ext.Const(metaIdent, useType) wrapped in WrapTerm.
func (p *GoTermPrinter) printConstRef(c core.ConstTerm) string {
	if alias, ok := p.specialConstGoAlias(c); ok {
		return alias
	}
	// Kernel-primitive consts with no registered const-meta: `=` and
	// Hilbert-ε. Their FULL applications never reach here
	// (tryPrintConnective renders .Eq / .SuchThat), but a LEAF or
	// PARTIAL application — e.g. the eta-contracted equality operands
	// `=(c) = =(COND(…))` that the def_expand of a constant c defined by
	// a conditional produces — must be rebuilt kernel-direct at its exact
	// instance type. A
	// ctx.Const("=") lookup would panic at replay: ProofService
	// const-meta carries only registered consts (ext/proto.go's
	// deserializer special-cases the same two names for the same
	// reason). ext.Const returns a *TermWrapper, so chaining works.
	if c.Meta().Equals(core.MetaEq()) {
		return fmt.Sprintf("%s(%s, %s)",
			p.extQ("Const"), p.coreQ("MetaEq"), p.PrintType(c.Type()))
	}
	if c.Meta().Equals(core.MetaHilbert()) {
		return fmt.Sprintf("%s(%s, %s)",
			p.extQ("Const"), p.coreQ("MetaHilbert"), p.PrintType(c.Type()))
	}
	if p.ConstIdent == nil {
		if p.StrictConsts {
			panic(fmt.Sprintf("emit: unresolved const %q — GoTermPrinter "+
				"has no ConstIdent resolver. A WrapTerm(nil) here would "+
				"nil-deref at replay.", c.Meta().Name()))
		}
		return fmt.Sprintf("/* unresolved const %q */ %s(nil)",
			c.Meta().Name(), p.extQ("WrapTerm"))
	}
	ident, declType, ok := p.ConstIdent(c)
	if !ok {
		if p.StrictConsts {
			panic(fmt.Sprintf("emit: unresolved const %q (type %s) — not "+
				"registered by the symbol-collection pass (walkTerm / "+
				"recordConst). Add the missing walk so a ctx.Const decl is "+
				"emitted; a WrapTerm(nil) here would nil-deref at replay.",
				c.Meta().Name(), c.Type().Key()))
		}
		return fmt.Sprintf("/* unresolved const %q */ %s(nil)",
			c.Meta().Name(), p.extQ("WrapTerm"))
	}
	if declType != nil && c.Type().Equals(declType) {
		return ident
	}
	if p.ConstAtType != nil {
		return p.ConstAtType(c)
	}
	metaIdent := ident + "Meta"
	if p.ConstMetaIdent != nil {
		metaIdent = p.ConstMetaIdent(c)
	}
	return fmt.Sprintf("%s(%s, %s)", p.extQ("Const"), metaIdent, p.PrintType(c.Type()))
}

// specialConstGoAlias returns the Go expression for a "special" const
// that has a hand-written rendering in the ext package. Most returns
// are *TermWrapper-typed (`WrapTerm(NAME)`) so .Apply/.Eq/.To chaining
// works uniformly. The two bool constants ⊤/⊥ return the bare `T`/`F`
// idents (core.ConstTerm) — they can never be applied as function
// heads (bool-typed) and in leaf position `Term`-accepting callers
// consume them directly, which is where they appear >99% of the time
// in practice. The tryPrintConnective chain-head sites (LHS of Eq/
// And/Or/Imply) re-wrap via ensureChainSafe if a bare T/F somehow
// lands there, so the elision is transparent to correctness — worst
// case is one WrapTerm restored at emit time, never a compile break.
//
// The set kept here mirrors the matchers used by tryPrintConnective:
// changing one without the other would create a wire-form
// inconsistency between proof emit and engine RPC. If you add a new
// special const, also add its Matches* primitive in basic_defs.go.
func (p *GoTermPrinter) specialConstGoAlias(c core.ConstTerm) (string, bool) {
	wrap := func(name string) string {
		return fmt.Sprintf("%s(%s)", p.extQ("WrapTerm"), p.extQ(name))
	}
	// The polymorphic specials' package-level globals carry the GENERIC
	// definition type (TypeA-based). A leaf / partial (eta-contracted)
	// occurrence at any other instance type — e.g. `∃!(COND(…))` where
	// the binder-form matcher doesn't apply — must be rebuilt at its
	// exact type, or the emitted .Apply chain type-asserts at replay.
	poly := func(name string, global ConstTerm) string {
		if c.Type().Equals(global.Type()) {
			return wrap(name)
		}
		return fmt.Sprintf("%s(%s.Meta(), %s)",
			p.extQ("Const"), p.extQ(name), p.PrintType(c.Type()))
	}
	// The monomorphic specials have exactly one legal instance type —
	// the global's. An occurrence at any other type means the alias
	// rendering would silently lose the instance type and crash deep
	// in replay, so under StrictConsts it fails AT emit time instead
	// (same principle as the unresolved-const guard in printConstRef).
	mono := func(expr string, global ConstTerm) string {
		if p.StrictConsts && !c.Type().Equals(global.Type()) {
			panic(fmt.Sprintf("emit: special const %q at type %s ≠ its "+
				"alias's fixed type %s — the bare alias would lose the "+
				"instance type and fail at replay",
				c.Meta().Name(), c.Type().Key(), global.Type().Key()))
		}
		return expr
	}
	switch string(c.Meta().Name()) {
	case "⊤":
		return mono(p.extQ("T"), T), true
	case "⊥":
		return mono(p.extQ("F"), F), true
	case "¬":
		return mono(wrap("NOT"), NOT), true
	case "∧":
		return mono(wrap("AND"), AND), true
	case "∨":
		return mono(wrap("OR"), OR), true
	case "⇒":
		return mono(wrap("IMPLY"), IMPLY), true
	case "∀":
		return poly("FORALL", FORALL), true
	case "∃":
		return poly("EXISTS", EXISTS), true
	case "∃!":
		return poly("UNIQUE", UNIQUE), true
	case "COND":
		return poly("COND", COND), true
	}
	return "", false
}

// A large proof often runs on a recurring concept with no constant
// behind it — "r_fn is the numerical-max function of P" in the slope
// completeness proof is a ~200-character formula restated in every
// section statement and every displayed goal. Promoting such a concept
// to a DEFINED constant is not an abbreviation in HOL: the fold/unfold
// crossings are proof steps, the constant needs a home in a shared
// definitional layer, and the name enters the checked text with no
// oracle behind it. The display abbreviation gives the reader the name
// at zero kernel cost: the TERM is untouched everywhere — statements,
// keys, CNF trajectories, payload round-trips — and only the rendered
// string folds.
//
// The iron rule of the set-builder sugar: sugar goes into DISPLAY,
// never into payload text. The fold
// is gated to the display profiles (binderNone — PrintTerm/PrintProp,
// panics, String(); binderPoly — the session inspect surface) and never
// fires in the parser round-trip profiles (binderAll /
// binderAllNameFaithful), so emit payloads and replay-parsed texts are
// byte-identical to a registry-free build.
//
// Folded output is marked: `⟦attainable(P₀, r, n)⟧`. The ⟦⟧ say "this
// is a registered display name, not parseable syntax": the DSL's ⟦…⟧
// is the closed interval, two arguments, so a fold pasted into a tactic
// text — one argument — fails loudly at the parser rather than silently
// meaning something else. The definition lives wherever the registration lives
// (for families: next to the statement builders that generate
// the same formula, so pattern and statement cannot drift).

// DisplayAbbrev is one registered fold: when a displayed subterm
// matches Pattern (α-equivalence on binders; Params match arbitrary
// subterms of their declared type), it renders as ⟦Name(args…)⟧ with
// the captured Params formatted recursively in declaration order.
type DisplayAbbrev struct {
	Name    string
	Params  []VarTerm
	Pattern Term
}

var (
	displayAbbrevMu sync.RWMutex
	displayAbbrevs  []DisplayAbbrev
)

// RegisterDisplayAbbrev registers a fold. Patterns are tried in
// registration order at every displayed subterm, first match wins —
// register the most specific (largest) patterns first. Panics on a
// duplicate name, on a param that never occurs in the pattern (it
// could never be captured), and on a param name colliding with a
// binder inside the pattern (the binder would shadow it).
func RegisterDisplayAbbrev(name string, params []VarTerm, pattern Term) {
	displayAbbrevMu.Lock()
	defer displayAbbrevMu.Unlock()
	for _, a := range displayAbbrevs {
		if a.Name == name {
			panic(fmt.Sprintf("RegisterDisplayAbbrev: duplicate name %q", name))
		}
	}
	for _, p := range params {
		if !pattern.HasName(p.Name()) {
			panic(fmt.Sprintf("RegisterDisplayAbbrev(%q): param %s does not occur in the pattern", name, p.Name()))
		}
		if patternBindsName(pattern, p.Name()) {
			panic(fmt.Sprintf("RegisterDisplayAbbrev(%q): param %s collides with a binder inside the pattern", name, p.Name()))
		}
	}
	displayAbbrevs = append(displayAbbrevs, DisplayAbbrev{Name: name, Params: params, Pattern: pattern})
}

// patternBindsName reports whether any binder inside t is named n.
func patternBindsName(t Term, n TermName) bool {
	switch t := t.Core().(type) {
	case AppliedTerm:
		return patternBindsName(t.Fun(), n) || patternBindsName(t.Arg(), n)
	case AbsTerm:
		return t.Var().Name() == n || patternBindsName(t.Body(), n)
	}
	return false
}

// abbrevMatch is one match attempt's state: the param set, the
// captures, and the binder correspondence built while descending.
type abbrevMatch struct {
	params map[TermName]VarTerm
	capt   map[TermName]Term
	pbind  []VarTerm // pattern-side binders, innermost last
	abind  []VarTerm // actual-side binders, positionally parallel
}

// matchAbbrevTerm matches pattern p against actual t. One-sided,
// syntactic, α-aware on binders: a pattern binder corresponds to the
// actual binder introduced at the same position (types must agree), a
// param captures any actual subterm of its declared type that does not
// reference an actual-side binder in scope (the capture must remain
// meaningful outside the fold site), and everything else must agree
// nodewise (consts by name + type, so pattern consts need not share
// metas with the corpus terms they match).
func matchAbbrevTerm(p, t Term, st *abbrevMatch) bool {
	switch p := p.Core().(type) {
	case VarTerm:
		for i := len(st.pbind) - 1; i >= 0; i-- {
			if st.pbind[i].Name() == p.Name() && st.pbind[i].Type().Equals(p.Type()) {
				tv, ok := t.Core().(VarTerm)
				return ok && tv.Name() == st.abind[i].Name() && tv.Type().Equals(st.abind[i].Type())
			}
		}
		if _, isParam := st.params[p.Name()]; isParam {
			if !p.Type().Equals(t.Type()) {
				return false
			}
			if prev, ok := st.capt[p.Name()]; ok {
				return prev.Equals(t)
			}
			for _, av := range st.abind {
				if t.HasName(av.Name()) {
					return false // capture would escape its binder
				}
			}
			st.capt[p.Name()] = t
			return true
		}
		tv, ok := t.Core().(VarTerm)
		return ok && tv.Name() == p.Name() && tv.Type().Equals(p.Type())
	case ConstTerm:
		tc, ok := t.Core().(ConstTerm)
		return ok && tc.Name() == p.Name() && tc.Type().Equals(p.Type())
	case AppliedTerm:
		ta, ok := t.Core().(AppliedTerm)
		return ok && matchAbbrevTerm(p.Fun(), ta.Fun(), st) && matchAbbrevTerm(p.Arg(), ta.Arg(), st)
	case AbsTerm:
		ta, ok := t.Core().(AbsTerm)
		if !ok || !p.Var().Type().Equals(ta.Var().Type()) {
			return false
		}
		st.pbind = append(st.pbind, p.Var())
		st.abind = append(st.abind, ta.Var())
		matched := matchAbbrevTerm(p.Body(), ta.Body(), st)
		st.pbind = st.pbind[:len(st.pbind)-1]
		st.abind = st.abind[:len(st.abind)-1]
		return matched
	}
	return false
}

// isSingleDisplayFold reports whether s is exactly one ⟦…⟧ fold —
// self-delimiting, so the bracket the quantifier branch would add
// around a structured body is noise. Nested folds inside the args are
// handled by depth counting; `⟦a(x)⟧ ∧ ⟦b(y)⟧` is NOT single. The
// intervals share the fold's opening and closing glyphs and mix them
// (`⟦a, b⟭`), so the count takes every interval delimiter: an opening
// ⟦ or ⟬ deepens, a closing ⟧ or ⟭ rises, and `⟦a, b⟭ ∪ ⟬c, d⟧` is
// NOT single either.
func isSingleDisplayFold(s string) bool {
	runes := []rune(s)
	if len(runes) == 0 || runes[0] != '⟦' {
		return false
	}
	depth := 0
	for i, r := range runes {
		switch r {
		case '⟦', '⟬':
			depth++
		case '⟧', '⟭':
			depth--
			if depth == 0 {
				return i == len(runes)-1
			}
		}
	}
	return false
}

// anyDisplayAbbrevs reports whether the registry is non-empty — the
// cheap guard the quantifier-decomposition stop hook keys on.
func anyDisplayAbbrevs() bool {
	displayAbbrevMu.RLock()
	defer displayAbbrevMu.RUnlock()
	return len(displayAbbrevs) > 0
}

// matchesAnyDisplayAbbrev is the match-only probe (no formatting):
// decomposeQuantifiers' stop hook, so a fold nested under outer
// quantifiers surfaces as a standalone body node.
func matchesAnyDisplayAbbrev(t Term) bool {
	displayAbbrevMu.RLock()
	abbrevs := displayAbbrevs
	displayAbbrevMu.RUnlock()
	for _, a := range abbrevs {
		st := &abbrevMatch{params: map[TermName]VarTerm{}, capt: map[TermName]Term{}}
		for _, p := range a.Params {
			st.params[p.Name()] = p
		}
		if matchAbbrevTerm(a.Pattern, t, st) {
			return true
		}
	}
	return false
}

// formatDisplayAbbrev tries every registered fold at t. Called by
// formatTermImpl on the display profiles only.
func formatDisplayAbbrev(t Term, latex bool, conflicts map[TermName]bool, binderTypes binderTypeMode) (string, bool) {
	displayAbbrevMu.RLock()
	abbrevs := displayAbbrevs
	displayAbbrevMu.RUnlock()
	for _, a := range abbrevs {
		st := &abbrevMatch{params: map[TermName]VarTerm{}, capt: map[TermName]Term{}}
		for _, p := range a.Params {
			st.params[p.Name()] = p
		}
		if !matchAbbrevTerm(a.Pattern, t, st) {
			continue
		}
		args := make([]string, len(a.Params))
		complete := true
		for i, p := range a.Params {
			c, ok := st.capt[p.Name()]
			if !ok {
				complete = false
				break
			}
			args[i] = formatTermImpl(c, latex, conflicts, binderTypes)
		}
		if !complete {
			continue
		}
		return fmt.Sprintf("⟦%s(%s)⟧", a.Name, strings.Join(args, ", ")), true
	}
	return "", false
}
