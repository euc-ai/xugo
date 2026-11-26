// Lowering: turn a type-annotated AST into kernel core.Term / core.Prop
// values (buildProp / buildTerm and their helpers).

package dsl

import (
	"fmt"
	"slices"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// formatHolTypes renders a comma-separated list of types for diagnostics.
func formatHolTypes(ts []core.HolType) string {
	parts := make([]string, len(ts))
	for i, t := range ts {
		parts[i] = ext.FormatType(t)
	}
	return strings.Join(parts, ", ")
}

// buildProp converts an AST prop into a core.Prop. What the build has to
// say of a statement it built (numeralWarnings) is added to warnings.
func buildProp(ast *astProp, scope *ParseScope, warnings *[]InputDiagnostic) (core.Prop, []InputDiagnostic) {
	env := newTypeEnv()
	if scope != nil {
		// Caller scope merges onto the env's seeded default nat encoders
		// (newTypeEnv pre-fills scopeConsts/scopeConstMetas). Default
		// entries win on name collision: a well-known name beats caller
		// scope.
		for name, c := range scope.Consts {
			if _, ok := env.scopeConsts[name]; !ok {
				env.scopeConsts[name] = c
			}
		}
		for name, m := range scope.ConstMetas {
			if _, ok := env.scopeConstMetas[name]; !ok {
				env.scopeConstMetas[name] = m
			}
		}
		// Caller-supplied free-var types behave like in-source decls.
		// Bound vars introduced by ∀/∃ override per the existing
		// bound-stack precedence in lookupType.
		for name, ty := range scope.Vars {
			env.declared[name] = ty
		}
		env.strict = scope.StrictResolution
		env.strictMint = scope.StrictMint
		env.coerceDomain = scope.CoerceDomain
		env.strictCoerce = scope.StrictResolution || scope.StrictCoercion
		env.freshenMeta = scope.FreshenMetaLetters
		env.syntax = scope.Syntax
		env.implicitBindings = scope.ImplicitBindings
		env.residentNames = scope.ResidentNames
		env.resolver = scope.ConstResolver
	}
	// Process declarations: type annotations and hypothesis ASTs.
	var hypASTs []astNode
	for _, decl := range ast.decls {
		if decl.name != "" && decl.typeStr != nil {
			// Type declaration.
			env.declared[decl.name] = resolveType(decl.typeStr)
		} else if decl.hyp != nil {
			hypASTs = append(hypASTs, decl.hyp)
		}
	}

	// Resolver pre-seed: registry-scope const fallback (run before any
	// collect pass / build pass). For every applied head and bare name
	// not already known to env — not in scopeConsts/scopeConstMetas, not
	// declared by scope.Vars or in-source decls, not quantifier-bound —
	// ask scope.ConstResolver for a ConstTermMeta and inject any hit into
	// scopeConstMetas. From that point on the inference + lowering passes
	// treat the resolved name identically to a same-named entry
	// the caller had threaded through ConstMetas itself, so claim text
	// can reference registered constants the surrounding goal happens not to
	// mention (e.g. `dest_nadd` in an `assert.text` whose goal is over a
	// `nadd` variable but never applies `dest_nadd`).
	// A notation names its constant before the resolver pre-seed asks
	// after the names (outfix.go).
	notationRoots := []*astNode{&ast.body}
	for i := range hypASTs {
		notationRoots = append(notationRoots, &hypASTs[i])
	}
	if diag := resolveNotationRoots(scope, notationRoots); diag != nil {
		return nil, []InputDiagnostic{*diag}
	}
	// Bundles are written out as the components they stand for before
	// anything reads the text's names (bundle.go).
	if diag := expandBundleRoots(scope, env.declared, notationRoots); diag != nil {
		return nil, []InputDiagnostic{*diag}
	}
	if scope != nil && scope.ConstResolver != nil {
		seedResolverConsts(ast.body, env, scope.ConstResolver)
		for _, h := range hypASTs {
			seedResolverConsts(h, env, scope.ConstResolver)
		}
	}
	// Implicit structure arguments are completed before the type
	// collectors read argument positions off the head's type (implicit.go).
	roots := []*astNode{&ast.body}
	for i := range hypASTs {
		roots = append(roots, &hypASTs[i])
	}
	if diag := completeImplicitArgs(scope, env, roots); diag != nil {
		return nil, []InputDiagnostic{*diag}
	}
	// A structure fact in the text or resident in the goal binds the
	// symbols its components declare (structure.go).
	if scope != nil {
		rootNodes := make([]astNode, len(roots))
		for i, r := range roots {
			rootNodes[i] = *r
		}
		env.structureOps = structureOperators(scope.Syntax, rootNodes, scope.ResidentFacts, env.declared)
	}
	// Set-theory surface metas are seeded LAST — after the caller-scope
	// merge and the resolver pre-seed — so caller-provided canonical
	// corpus metas win on collision and a resolver hit wins over the
	// DSL-side meta; only a name nothing above supplied (a scope-less
	// bare parse in tests / agent surfaces) falls through to the
	// setops.go metas, so the set-theory surface (∅, {a,b}, x ∈ s, …)
	// still resolves there. See seedSetScopeConstFallback.
	seedSetScopeConstFallback(env.scopeConstMetas)

	// First pass: collect type information from the body and hypotheses
	// so we can infer types for undeclared variables.
	collectAstTypes(ast.body, env)
	for _, h := range hypASTs {
		collectAstTypes(h, env)
	}

	// Second pass: guess types for remaining unresolved variables
	// (equality partners, transitive function arg inference).
	collectTypeGuesses(ast.body, env)
	for _, h := range hypASTs {
		collectTypeGuesses(h, env)
	}

	// Third pass: fallback scope-const polymorphic leak. The pass-1
	// guard in collectAstTypes deliberately skips assigning a free arg
	// var the polymorphic type from a scope-const meta — so a later
	// concrete use can pin the var without colliding with already-
	// leaked free type-vars (the lemma10 case: `f` in `injective(f)` AND
	// `f(x)≠z` with z:ind — concrete wins via propagateEqAppResultType).
	// For free vars that have NO concrete use anywhere AND no `=`/`≠`
	// constraint (the lemma11 case: `f` appears ONLY as arg of scope-
	// const injective/¬surjective), there's nothing else to pin them; this
	// fallback restores the leak so they don't stay untyped. Equivalent
	// to the legacy pre-guard behavior, just deferred so concrete
	// inference wins when both are possible.
	collectScopeConstPolyLeak(ast.body, env)
	for _, h := range hypASTs {
		collectScopeConstPolyLeak(h, env)
	}

	// Build conclusion term.
	prop, diag, buildErr := safeBuildProp(func() (core.Prop, error) {
		concl, err := buildTerm(ast.body, env, true)
		if err != nil {
			return nil, err
		}
		if !core.IsBool(concl) {
			return nil, fmt.Errorf("conclusion must be boolean, got type %s", ext.FormatType(concl.Type()))
		}

		// Build hypothesis terms.
		hyps := make([]core.Term, 0, len(hypASTs))
		for _, h := range hypASTs {
			ht, err := buildTerm(h, env, true)
			if err != nil {
				return nil, err
			}
			if !core.IsBool(ht) {
				return nil, fmt.Errorf("hypothesis must be boolean, got type %s", ext.FormatType(ht.Type()))
			}
			hyps = append(hyps, ht)
		}

		if env.strictCoerce && len(env.defaultedCoerces) > 0 {
			if err := checkStrictDefaultedCoerces(env, append([]core.Term{concl}, hyps...)); err != nil {
				return nil, err
			}
		}
		if env.strictMint {
			if err := checkStrictMint(env, append([]core.Term{concl}, hyps...)); err != nil {
				return nil, err
			}
		}
		*warnings = append(*warnings, env.numeralWarnings(append([]core.Term{concl}, hyps...))...)
		return core.MakeProp(concl, hyps...), nil
	})

	if diag != nil {
		// Enrich typeMissingError diagnostics with suggested types.
		enrichTypeDiagnostic(diag, env, buildErr)
		return nil, append(env.errors, *diag)
	}
	if len(env.errors) > 0 {
		return nil, env.errors
	}
	return prop, nil
}

// buildTerm converts an AST node to a core.Term.
// If boolCtx is true, the result must be boolean.
func buildTerm(node astNode, env *typeEnv, boolCtx bool) (core.Term, error) {
	switch n := node.(type) {
	case *astVar:
		if len(n.typeAnnot) > 0 {
			return buildAnnotatedVarTerm(n, env)
		}
		return buildVarTerm(n.name, env, boolCtx)

	case *astConst:
		if n.name == utils.TrueStr {
			return ext.T, nil
		}
		return ext.F, nil

	case *astNumLit:
		return ext.MakeNumeral(n.value), nil

	case *astTermLit:
		// A completed implicit argument: the instance component's own term.
		return n.term, nil

	case *astOutfix:
		return nil, fmt.Errorf("%s…%s: notation left unresolved (no constant in scope declares it)", n.open, n.close)

	case *astBigOp:
		var expected core.HolType
		if boolCtx {
			expected = core.TypeBool()
		}
		return buildBigOp(n, env, expected)

	case *astNotNode:
		body, err := buildTerm(n.body, env, true)
		if err != nil {
			return nil, err
		}
		if !core.IsBool(body) {
			return nil, fmt.Errorf("¬ requires boolean operand, got %s", ext.FormatType(body.Type()))
		}
		return ext.Not(body), nil

	case *astCoerce:
		return buildCoerce(n, env, nil) // no context: defaults to real_of_num

	case *astNeg:
		return buildNeg(n, env, nil)

	case *astBinOp:
		return buildBinOp(n, env)

	case *astCong:
		return buildCong(n, env)

	case *astTendsAt:
		return buildTendsAt(n, env)

	case *astField:
		return buildStructField(n, env)
	case *astApp:
		// In a boolean context the application's result must be bool;
		// otherwise we have no constraint from here (nil = unknown). A
		// known constraint lets buildApp type an undeclared head by its
		// result type instead of the bool-default. See buildApp.
		var expected core.HolType
		if boolCtx {
			expected = core.TypeBool()
		}
		return buildApp(n, env, expected)

	case *astQuantNode:
		return buildQuant(n, env)

	case *astAbsNode:
		// buildTerm carries no expected type (only the bool-context flag),
		// and a lambda is never bool-typed, so there is nothing to thread
		// here. Callers with a known expected type reach buildAbs via
		// buildExpected instead.
		return buildAbs(n, env, nil)

	case *astPatternAbs:
		return buildPatternAbs(n, env, nil)

	default:
		return nil, fmt.Errorf("unknown AST node type at position %d", node.nodePos())
	}
}

// resolveTypeAnnotation converts a parsed `⟨V:T,...⟩` annotation into a
// slice of core.TypeSubst by resolving each binding's type via
// resolveType. The `varName` is used verbatim as the abstract type-var
// name (mirroring the formatter's ConstInstPairs output: the raw abstract
// type-var name from the const's meta, no `var:` prefix).
func resolveTypeAnnotation(annot []typeAnnotBinding) []core.TypeSubst {
	if len(annot) == 0 {
		return nil
	}
	substs := make([]core.TypeSubst, 0, len(annot))
	for _, b := range annot {
		v := core.MakeVarType(core.TermName(b.varName))
		substs = append(substs, core.MakeTypeSubst(v, resolveType(b.ty)))
	}
	return substs
}

// applyTypeAnnotToMeta instantiates a scope-const meta with an explicit
// `⟨V:T⟩` type-substitution annotation and returns a bare 0-arg
// ConstTerm at the instantiated type. Used when the parser sees
// `Name⟨A:T⟩` NOT followed by an argument list — the annotation still
// pins the polymorphic const's instance, so the printer's
// `formatConstTypeAnnotation` output round-trips.
//
// A binding whose varName is not among the meta's abstract type-vars
// silently no-ops (Substitute is name-keyed and drops non-matching
// entries). We return an error only when the binding produces a type
// that fails MakeConstTerm's Matches assertion — that only fires when
// the annotation contradicts the meta's shape.
func applyTypeAnnotToMeta(env *typeEnv, meta core.ConstTermMeta, annot []typeAnnotBinding) (core.Term, error) {
	substs := resolveTypeAnnotation(annot)
	if err := validateAnnotAgainstMeta(meta, annot); err != nil {
		return nil, err
	}
	env.recordAnnotTyVars(substs)
	abs, freshMap := env.freshAbs(meta)
	substs = translateSeedThroughFresh(substs, freshMap)
	instType := abs.Substitute(substs...)
	return core.MakeConstTerm(meta, instType), nil
}

// recordAnnotTyVars marks the type variables an author spelled inside a
// `⟨V:T⟩` annotation's TARGET types as intentionally pinned — the
// strict-mint check treats them as anchored.
func (env *typeEnv) recordAnnotTyVars(substs []core.TypeSubst) {
	for _, s := range substs {
		for _, tv := range s.HolType.TypeVars() {
			env.annotTyVars[tv.Key()] = true
		}
	}
}

// collectTypeVarNames returns the set of abstract type-variable names
// occurring in `t`. Used to validate that an annotation binding names
// a real type-var of the const's meta — an annotation like
// `finite⟨X:bool⟩` where `X` is not a type-var of finite is likely a
// typo or a stale annotation, and we surface it as an explicit error
// rather than silently no-op'ing.
func collectTypeVarNames(t core.HolType) map[string]bool {
	seen := map[string]bool{}
	var walk func(core.HolType)
	walk = func(t core.HolType) {
		switch x := t.(type) {
		case core.VarType:
			seen[string(x.Name())] = true
		case core.CompositeType:
			for i := 0; i < x.Meta().Arity(); i++ {
				walk(x.SubType(i))
			}
		}
	}
	walk(t)
	return seen
}

// validateAnnotAgainstMeta reports an error when an annotation names a
// type-variable not present in the meta's abstract type. This catches
// typo'd or stale annotations at parse time with a clear message
// instead of a silent no-op deep inside MakeConstTerm.
func validateAnnotAgainstMeta(meta core.ConstTermMeta, annot []typeAnnotBinding) error {
	if len(annot) == 0 {
		return nil
	}
	vars := collectTypeVarNames(meta.AbsType())
	for _, b := range annot {
		if !vars[b.varName] {
			return fmt.Errorf(
				"const %q has no type variable %q in abstract type %s",
				meta.Name(), b.varName, ext.FormatType(meta.AbsType()))
		}
	}
	return nil
}

// buildAnnotatedVarTerm lowers a bare `Name⟨V:T,...⟩` occurrence — an
// identifier atom carrying a polymorphic type-substitution annotation
// with no following argument list. Requires `Name` to resolve as a
// scope-const (in scopeConstMetas or scopeConsts). The annotation
// bypasses the fixed-instance fast path in `env.scopeConsts`, forcing
// re-instantiation from the meta so the annotation's type-vars win.
// Bound-name shadowing is honored: a `∀Name:T.…Name⟨A:U⟩…` inside the
// binder still treats Name as the bound var (and rejects the annotation
// there, since bound vars are not polymorphic consts).
func buildAnnotatedVarTerm(n *astVar, env *typeEnv) (core.Term, error) {
	if _, isBound := env.bound[n.name]; isBound {
		return nil, fmt.Errorf(
			"type annotation ⟨...⟩ on %q: bound variables are not polymorphic",
			n.name)
	}
	// Prefer the meta path when available (it carries the abstract type
	// with named type-vars). scopeConsts's fixed instance has already
	// been substituted, so its type-var names no longer match the
	// annotation's — fall through only when there's no meta.
	if meta, ok := env.scopeConstMetas[n.name]; ok {
		return applyTypeAnnotToMeta(env, meta, n.typeAnnot)
	}
	if c, ok := env.scopeConsts[n.name]; ok {
		return applyTypeAnnotToMeta(env, c.Meta(), n.typeAnnot)
	}
	return nil, fmt.Errorf(
		"type annotation ⟨...⟩ on %q: not a scope constant "+
			"(annotations are only valid on polymorphic constants)",
		n.name)
}

func buildVarTerm(name string, env *typeEnv, boolCtx bool) (core.Term, error) {
	// Resolve via the env's const scope: newTypeEnv pre-seeds the
	// nat-encoding consts (_0/bit0/bit1/suc) so they always
	// resolve here without a caller-supplied scope; caller scope merges
	// emit's proof-declared consts (subset, int_of_num, …) and the
	// engine's goalConstScope on top of that base. Bound binders shadow
	// scope consts — e.g. `∃real_pow:T.…real_pow…` is a fresh local
	// name, not the global `real_pow` const — so skip the const path
	// when env.bound has the name.
	if _, isBound := env.bound[name]; !isBound {
		if c, ok := env.scopeConsts[name]; ok {
			// The pinned instance, unless this occurrence expects another
			// the constant's meta can take (buildExpected's stash): then
			// the meta at the expected type — a pin names the instance
			// a statement reads a constant at by default, not the only
			// one it may be read at (the session elaborator unifies
			// here, and registration must read what a session stated).
			// Only a MONOMORPHIC expectation re-reads the pin, and the
			// bound is load-bearing rather than cautious. A pin is a
			// chapter saying "this constant means ONE instance here"
			// (`sets/num_segment` pins its element type to num), and a
			// premise installed at the pin must still meet a goal built
			// from the same text. Letting an expectation written in a
			// type VARIABLE re-read the pin splits those two apart — it
			// was tried twice, and both times it broke
			// `num_segment.HasSizeBelowStrict` and `num_segment.Card`,
			// whose `card(∅)` premise installs at num while the re-read
			// conclusion stood at the abstract letter: `card` is pinned
			// too, at its generic instance, so the expectation it hands
			// `∅` is `A → bool` in a plain letter, indistinguishable by
			// spelling from one an author wrote. What DOES tell them
			// apart is the path — see rereadPinnedAtom, which re-reads
			// a pin only where an application is read through its meta
			// and the earlier arguments have fixed the domain.
			if target, known := env.inferred[name]; known && !c.Type().Equals(target) &&
				!ext.TermAnyTypeVar(ext.Var("_", target).Core(), utils.FullPredicate) {
				abs, _ := env.freshAbs(c.Meta())
				if substs, ok := abs.Matches(target, utils.FullPredicate); ok {
					return core.MakeConstTerm(c.Meta(), abs.Substitute(substs...)), nil
				}
			}
			return c, nil
		}
		// scopeConstMetas-only path for 0-arity polymorphic consts (the
		// bare-atom case for empty_set, nil, etc.). buildApp already consults
		// scopeConstMetas for applied heads, but a bare `empty_set` is a
		// 0-arg occurrence and never reaches buildApp — so without this
		// branch, a meta seeded into scopeConstMetas by seedResolverConsts
		// (the ConstResolver fallback) is unreachable from a
		// bare-atom site and empty_set stays a free variable.
		//
		// The instance type is specialized from context when one is
		// available: buildExpected stashes the expected type into
		// env.inferred before delegating here (application-arg position —
		// `set_member(x_0:num, empty_set)` reaches us with inferred[empty_set]=num→bool),
		// and collectTypeGuesses records the `=`-partner's type into
		// env.guesses (`s_0:num→bool = empty_set`). Nothing downstream
		// re-specializes the returned ConstTerm — buildArgsAgainstFunType's
		// domain.Matches and buildBinOp's Equals check both treat a
		// still-abstract `var:A→bool` as a mismatch — so the meta must be
		// instantiated HERE or the polymorphism escapes as a parse error.
		// When no contextual type is known (or it contradicts the meta's
		// shape, e.g. a bool-atom guess), fall back to the abstract type
		// and let buildAppViaMeta-style unification handle applied sites.
		if meta, ok := env.scopeConstMetas[name]; ok {
			abs, _ := env.freshAbs(meta)
			target, known := env.lookupType(name)
			if !known {
				target, known = env.guesses[name]
			}
			if known {
				if substs, ok := abs.Matches(target, utils.FullPredicate); ok {
					return core.MakeConstTerm(meta, abs.Substitute(substs...)), nil
				}
			}
			return core.MakeConstTerm(meta, abs), nil
		}
	}
	// An overloaded word written bare (overload.go's bareOverloadedWord):
	// the nullary constant declaring it (`π`), or — where the position's
	// type is known, an application argument against the head's domain
	// (`real_derivative_at(sin, c, cos(c))` reads `sin` at `real → real`)
	// — the one constant declaring the word at that type. A bound or
	// declared variable of the word's spelling shadows it, as a binder
	// shadows a constant.
	if _, isBound := env.bound[name]; !isBound {
		if _, isDeclared := env.declared[name]; !isDeclared && !env.untypedAbsVars[name] {
			if c, err := env.bareOverloadedWord(name); c != nil || err != nil {
				return c, err
			}
		}
	}
	ty, ok := env.lookupType(name)
	if !ok {
		if boolCtx {
			// In boolean context, a bare variable is boolean.
			ty = core.TypeBool()
			env.inferred[name] = ty
		} else if env.untypedAbsVars[name] {
			// Plain-var use of an untyped λ binder with no other
			// constraint reaching here. Assign the type variable the
			// enclosing domain handed the binder (binderFallback) or a
			// fresh `_<name>`, and pin it as the binder's type — buildAbs
			// will then read env.inferred[name] after the body walk
			// and use the same var, so the abstraction binds the
			// body's free var by name+type as usual.
			if fb, ok := env.binderFallback[name]; ok {
				ty = fb
			} else {
				ty = core.MakeVarType(core.TermName("_" + name))
			}
			env.inferred[name] = ty
		} else {
			// An overloaded word that resolved to no constant here (no
			// position type, several fits) is not a variable waiting for
			// a declaration: say what it is.
			if hint := env.overloadHint(name); hint != "" {
				return nil, fmt.Errorf("%q names no variable here%s", name, hint)
			}
			// Check if we have a guess from context.
			if guess, ok := env.guesses[name]; ok {
				return nil, &typeMissingError{
					varName: name,
					guess:   guess,
					reason:  env.guessReasons[name],
				}
			}
			return nil, &typeMissingError{varName: name}
		}
	}
	if env.strict {
		if err := env.strictFreshenCheck(name); err != nil {
			return nil, err
		}
	}
	return core.Var(core.TermName(name), ty), nil
}

// checkStrictMint enforces ParseScope.StrictMint on a built statement:
// every type variable must be ANCHORED — spelled by the author through
// a binder/variable type or a `⟨V:T⟩` tie — never inherited from a
// bare polymorphic head's own abstract letters. buildAppViaMeta
// instantiates meta.AbsType verbatim, so an unpinned head freezes its
// letters into the statement; the result is a DIFFERENT theorem that
// prints identically to the intended one (the class-2 false-mint
// receipts). The message names each offender and the tie spelling
// that pins it.
func checkStrictMint(env *typeEnv, terms []core.Term) error {
	vars := map[core.TermKey]core.VarTerm{}
	consts := map[core.TermKey]core.ConstTerm{}
	for _, t := range terms {
		ext.CollectVars(t, vars)
		ext.CollectConstTerms(t, consts)
	}
	anchored := make(map[core.TypeKey]bool, len(env.annotTyVars))
	for k := range env.annotTyVars {
		anchored[k] = true
	}
	for _, v := range vars {
		for _, tv := range v.Type().TypeVars() {
			anchored[tv.Key()] = true
		}
	}
	offenders := map[string]map[string]bool{} // tyvar name → head descriptions
	for _, c := range consts {
		for _, tv := range c.Type().TypeVars() {
			if anchored[tv.Key()] {
				continue
			}
			name := string(tv.Name())
			if offenders[name] == nil {
				offenders[name] = map[string]bool{}
			}
			offenders[name][describeUnpinnedHead(c, tv)] = true
		}
	}
	if len(offenders) == 0 {
		return nil
	}
	tyNames := make([]string, 0, len(offenders))
	for n := range offenders {
		tyNames = append(tyNames, n)
	}
	sort.Strings(tyNames)
	var b strings.Builder
	for _, n := range tyNames {
		heads := make([]string, 0, len(offenders[n]))
		for h := range offenders[n] {
			heads = append(heads, h)
		}
		sort.Strings(heads)
		fmt.Fprintf(&b, "\n  type variable %s entered through: %s", n, strings.Join(heads, "; "))
	}
	return fmt.Errorf(
		"strict mint: the statement carries type variables no binder mentions and no ⟨⟩ tie "+
			"names — a bare polymorphic head froze its own abstract letters, so this would mint "+
			"a different theorem than the text suggests.%s\n  Pin each instance with a type tie "+
			"(concrete: universe⟨A:num⟩; or tie heads to one letter: card(𝕌⟨A:N⟩)), or bind a "+
			"variable whose type mentions the variable",
		b.String())
}

// describeUnpinnedHead renders one offending const occurrence with the
// meta letter that landed on the unpinned type variable, so the message
// can spell the exact tie.
func describeUnpinnedHead(c core.ConstTerm, tv core.VarType) string {
	letter := ""
	if meta := c.Meta(); !meta.IsZero() {
		if substs, ok := meta.AbsType().Matches(c.Type(), utils.FullPredicate); ok {
			for _, s := range substs {
				for _, stv := range s.HolType.TypeVars() {
					if stv.Key() == tv.Key() {
						letter = string(s.VarType.Name())
					}
				}
			}
		}
	}
	if letter == "" {
		// Identity substitutions are stripped by Matches, so a head
		// still at its own abstract letters reports the variable itself.
		letter = string(tv.Name())
	}
	return fmt.Sprintf("%s (instance %s — spell %s⟨%s:<type>⟩)",
		c.Name(), ext.FormatType(c.Type()), c.Name(), letter)
}

// checkStrictDefaultedCoerces errors when a `&` coercion that took the
// global real default SURVIVED into the final statement — no anchoring
// operand, no declared domain, and no reconcile retarget replaced it.
// Survival is pointer identity: buildCoerce records the exact node it
// built, and a retarget builds a new one.
func checkStrictDefaultedCoerces(env *typeEnv, terms []core.Term) error {
	present := map[core.Term]bool{}
	for _, t := range terms {
		collectTermNodes(t, present)
	}
	var poss []int
	for _, d := range env.defaultedCoerces {
		if present[d.term] {
			poss = append(poss, d.pos)
		}
	}
	if len(poss) == 0 {
		return nil
	}
	sort.Ints(poss)
	return fmt.Errorf(
		"strict resolution: %d unanchored `&` coercion(s) at position %v defaulted to real_of_num — "+
			"no neighbouring operand pins the embedding and the scope declares no coercion domain. "+
			"Declare the chapter's domain (a CoerceDomain row of its vocabulary, or WithCoerceDomain on "+
			"the family of a chapter with none — a session reads the domain of the family it is bound "+
			"to), anchor an operand, or spell the embedding longhand (real_of_num(…) / int_of_num(…))",
		len(poss), poss)
}

// exoneratePartnerAnchoredCoerces clears pending pure-default `&`
// records on ONE side of a real=real junction when the OTHER side
// carries none: the defaults agreed with an author-typed real
// neighbour rather than deciding alone (`&0 + x` with x:real — the
// default and the anchor coincide, so no reconcile rebuild marks it).
// When BOTH sides carry defaults (`&m = &n`, `&(nat_pow(2,k)) ≤ &(val(w))`)
// nothing is exonerated — that is exactly the silent-ℝ receipt shape
// the strict guard exists to flag.
func (env *typeEnv) exoneratePartnerAnchoredCoerces(left, right core.Term) {
	if len(env.defaultedCoerces) == 0 {
		return
	}
	if !left.Type().Equals(RealType) || !right.Type().Equals(RealType) {
		return
	}
	pending := map[core.Term]bool{}
	for _, d := range env.defaultedCoerces {
		pending[d.term] = true
	}
	lNodes := map[core.Term]bool{}
	collectTermNodes(left, lNodes)
	rNodes := map[core.Term]bool{}
	collectTermNodes(right, rNodes)
	lHas, rHas := nodesIntersect(lNodes, pending), nodesIntersect(rNodes, pending)
	var clear map[core.Term]bool
	switch {
	case lHas && !rHas:
		clear = lNodes
	case rHas && !lHas:
		clear = rNodes
	default:
		return
	}
	kept := env.defaultedCoerces[:0]
	for _, d := range env.defaultedCoerces {
		if !clear[d.term] {
			kept = append(kept, d)
		}
	}
	env.defaultedCoerces = kept
}

func nodesIntersect(nodes, pending map[core.Term]bool) bool {
	for t := range pending {
		if nodes[t] {
			return true
		}
	}
	return false
}

// collectTermNodes gathers every node of t into seen, by pointer.
func collectTermNodes(t core.Term, seen map[core.Term]bool) {
	if seen[t] {
		return
	}
	seen[t] = true
	switch x := t.Core().(type) {
	case core.AppliedTerm:
		collectTermNodes(x.Fun(), seen)
		collectTermNodes(x.Arg(), seen)
	case core.AbsTerm:
		collectTermNodes(x.Body(), seen)
	}
}

// strictFreshenCheck is ParseScope.StrictResolution's verdict for a
// name about to become a free VarTerm: quantifier-bound names, declared
// names (scope Vars or an in-text decl), and untyped λ binders pass;
// anything else is the silent-freshening event strict mode forbids. The
// message names the repair — the consumers are mostly agents, for whom
// the error text is the prompt.
func (env *typeEnv) strictFreshenCheck(name string) error {
	if _, ok := env.bound[name]; ok {
		return nil
	}
	if _, ok := env.declared[name]; ok {
		return nil
	}
	if env.untypedAbsVars[name] {
		return nil
	}
	declared := make([]string, 0, len(env.declared))
	for n := range env.declared {
		declared = append(declared, n)
	}
	sort.Strings(declared)
	return fmt.Errorf(
		"strict resolution: %q is neither a declared variable nor quantified, "+
			"and resolves to no constant in scope — quantify it, declare it "+
			"(a `%s:<type>` decl before ⊢, or the scope's Vars), or fix the "+
			"spelling if a constant was intended (declared vars: %v)%s",
		name, name, declared, env.overloadHint(name))
}

// buildEqOperands builds the two operands of an `=` / `≠`, propagating type
// across the connective. Both are built in non-bool context (so num operands
// aren't coerced to bool). Because buildApp now FAILS FAST on an undeclared-head
// application with no contextual type (rather than defaulting its result to
// bool), an operand whose type is recoverable only from its partner — e.g.
// `nat_pow(a,n)` in `nat_pow(a,n) = 1`, where the literal `1` is the only thing fixing
// nat_pow's result to num — would otherwise error. So when exactly one side builds,
// its type is imposed on the other via buildExpected. (The =-partner inference in
// infer.go already seeds this when the partner is a typed VARIABLE — `nat_pow(a,n) =
// a` — but not when it is a literal, which carries no var to guess from.) When
// BOTH sides fail (e.g. both undeclared heads), the goal is genuinely ambiguous
// and the first error is returned.
func buildEqOperands(n *astBinOp, env *typeEnv) (left, right core.Term, err error) {
	left, lerr := buildTerm(n.left, env, false)
	right, rerr := buildTerm(n.right, env, false)
	switch {
	case lerr == nil && rerr == nil:
		// An int partner embeds a num or retargets a real-defaulted `&`,
		// so both `2 = x:int` and `&2 = x:int` build int_of_num.
		left, right = reconcileNumericDomain(n.left, n.right, left, right, env)
		env.exoneratePartnerAnchoredCoerces(left, right)
		// A BARE polymorphic const builds at whatever instance context
		// offered — and with no expected type of its own, that context is
		// the name-keyed guess a DIFFERENT occurrence left behind. In
		// `⋃∅ = ∅` the two ∅'s are at different instances (the empty
		// family and the empty set), so the guess is simply the other
		// occurrence's answer and the sides disagree. Rebuild the bare
		// side against its partner's type, which is the constraint that
		// actually applies to it. Only a bare const-meta atom is retried:
		// anything else disagreeing is a real mismatch and must still be
		// reported.
		if !left.Type().Equals(right.Type()) {
			if isBareConstMetaAtom(n.right, env) {
				if t, err := buildExpected(n.right, env, left.Type()); err == nil {
					return left, t, nil
				}
			}
			if isBareConstMetaAtom(n.left, env) {
				if t, err := buildExpected(n.left, env, right.Type()); err == nil {
					return t, right, nil
				}
			}
			return reconcileFreshLetters(env, left, right)
		}
		return left, right, nil
	case lerr == nil && rerr != nil:
		right, err = buildExpected(n.right, env, left.Type())
		return left, right, err
	case rerr == nil && lerr != nil:
		left, err = buildExpected(n.left, env, right.Type())
		return left, right, err
	default:
		return nil, nil, lerr
	}
}

// rereadPinnedAtom re-reads a bare PINNED constant through its meta at
// the domain an application demands of it. It is asked only where the
// application is read through its head's meta — the last reading an
// application has — and the pinned instance has just FAILED to unify
// with the domain: `cons(x, nil)` with `x : prod(A, bool)` in a chapter
// whose vocabulary pins nil at list(A), where x has fixed the domain at
// list(prod(A, bool)); `⁅nil⁆` under a class map over
// list(prod(?f, bool)), which no instance of list(A) at a rigid A is.
// The pin says which instance a statement reads by default, the domain
// says which this occurrence is, and nothing but an error stood between
// them (the session, which pins nothing, read the same text). Where the
// pin DOES unify it is what instantiates the domain and this is never
// reached — `card(∅)` in a chapter pinning ∅ at num reads at num, the
// boundary buildVarTerm's pinned branch documents. nil when node is not
// such an atom or the constant's meta cannot take the domain either (an
// honest mismatch, reported as before).
func rereadPinnedAtom(node astNode, env *typeEnv, domain core.HolType) core.Term {
	v, ok := node.(*astVar)
	if !ok || len(v.typeAnnot) > 0 {
		return nil
	}
	if _, isBound := env.bound[v.name]; isBound {
		return nil
	}
	c, pinned := env.scopeConsts[v.name]
	if !pinned {
		return nil
	}
	abs, _ := env.freshAbs(c.Meta())
	substs, ok := abs.Matches(domain, utils.FullPredicate)
	if !ok {
		return nil
	}
	return core.MakeConstTerm(c.Meta(), abs.Substitute(substs...))
}

// reconcileFreshLetters unifies two operands' types where they differ by
// a constant's occurrence-local stand-ins alone: a bare polymorphic
// nullary beside a typed partner — `free_one * x`, a definiendum typed
// `free_group(A)` beside `⁅nil⁆` at `free_group(?f…)` — reads at the
// partner's instance, exactly as an argument reads at its domain. Only
// the stand-ins move (unifyDomainArg's freshOnly predicate); an author's
// letter is rigid, so two sides written at different letters still
// disagree and are reported as they were. A reading that would retype a
// variable bound outside the operands is refused (substituteFreshInArgs).
func reconcileFreshLetters(env *typeEnv, left, right core.Term) (core.Term, core.Term, error) {
	lt, rt := left.Type(), right.Type()
	if lt.Equals(rt) || !env.freshenMeta {
		return left, right, nil
	}
	substs, ok := unifyDomainArg(env, lt, rt, nil)
	if !ok {
		return left, right, nil
	}
	out, err := substituteFreshInArgs([]core.Term{left, right}, resolveSubstTargets(substs))
	if err != nil {
		return nil, nil, err
	}
	return out[0], out[1], nil
}

// isBareConstMetaAtom reports whether node is an unannotated atom naming
// a polymorphic const meta that no binder shadows — the one shape whose
// type is decided entirely by context, and so the one worth rebuilding
// when a partner's type contradicts the instance it happened to get.
func isBareConstMetaAtom(node astNode, env *typeEnv) bool {
	v, ok := node.(*astVar)
	if !ok || len(v.typeAnnot) > 0 {
		return false
	}
	if _, isBound := env.bound[v.name]; isBound {
		return false
	}
	_, isMeta := env.scopeConstMetas[v.name]
	return isMeta
}

// imposeBareConstOperand re-types the BARE polymorphic-const operand of a
// two-operand polymorphic head (the set infixes, ∘) against the domain
// its partner grounds. buildAppViaMeta unifies from the argument types
// alone, so a bare `∅` under `x ∈ ∅` was built at its generic instance
// and the head's domain check failed at num; at a type variable other
// than the meta's own letter the unifier bound the operand's letter
// instead and the kernel rejected the application. The `=` arm has
// always rebuilt a bare const-meta atom against its partner
// (buildEqOperands); this is the same retry for a head with a known
// meta: unify the head's abstract domains with the partner, and rebuild
// the bare operand against its own domain once every letter of that
// domain is bound. Two bare operands (`∅ ⊆ ∅`) or none leave both
// untouched, and a rebuild that fails leaves the original for
// buildAppViaMeta's own diagnostic.
func imposeBareConstOperand(n *astBinOp, env *typeEnv, meta core.ConstTermMeta, left, right core.Term) (core.Term, core.Term) {
	leftBare, rightBare := isBareConstMetaAtom(n.left, env), isBareConstMetaAtom(n.right, env)
	if leftBare == rightBare {
		return left, right
	}
	absType, _ := env.freshAbs(meta)
	first, ok := absType.(core.CompositeType)
	if !ok || !first.Meta().Equals(core.MetaTypeFun()) {
		return left, right
	}
	second, ok := first.SubType(1).(core.CompositeType)
	if !ok || !second.Meta().Equals(core.MetaTypeFun()) {
		return left, right
	}
	partnerDomain, bareDomain, partner, bare := first.SubType(0), second.SubType(0), left, n.right
	if leftBare {
		partnerDomain, bareDomain, partner, bare = second.SubType(0), first.SubType(0), right, n.left
	}
	substs, ok := unifyDomainArg(env, partnerDomain, partner.Type(), nil)
	if !ok {
		return left, right
	}
	for name := range collectTypeVarNames(bareDomain) {
		if !annotBinds(substs, core.MakeVarType(core.TermName(name))) {
			return left, right
		}
	}
	rebuilt, err := buildExpected(bare, env, bareDomain.Substitute(substs...))
	if err != nil {
		return left, right
	}
	if leftBare {
		return rebuilt, right
	}
	return left, rebuilt
}

func buildBinOp(n *astBinOp, env *typeEnv) (core.Term, error) {
	if n.op == "=" {
		// Equality: both sides must have the same type, not necessarily bool.
		left, right, err := buildEqOperands(n, env)
		if err != nil {
			return nil, err
		}
		if !left.Type().Equals(right.Type()) {
			return nil, fmt.Errorf("equality type mismatch: left is %s, right is %s%s",
				ext.FormatType(left.Type()), ext.FormatType(right.Type()), pairForSetHint(left.Type(), right.Type()))
		}
		env.noteNumeralRelation(n.op, n.pos, left, right)
		return core.Eq(left, right), nil
	}

	// Inequality is sugar for ¬(a = b). Build both sides in non-bool
	// context so num-typed operands aren't coerced to bool.
	if n.op == utils.NeqStr {
		left, right, err := buildEqOperands(n, env)
		if err != nil {
			return nil, err
		}
		if !left.Type().Equals(right.Type()) {
			return nil, fmt.Errorf("inequality type mismatch: left is %s, right is %s%s",
				ext.FormatType(left.Type()), ext.FormatType(right.Type()), pairForSetHint(left.Type(), right.Type()))
		}
		env.noteNumeralRelation(n.op, n.pos, left, right)
		return ext.Not(core.Eq(left, right)), nil
	}

	// Non-membership is sugar for ¬(x ∈ s): the membership builds through
	// the set-theory arm below, which picks its meta and types its operands.
	if n.op == "∉" {
		member, err := buildBinOp(&astBinOp{op: "∈", left: n.left, right: n.right, pos: n.pos}, env)
		if err != nil {
			return nil, err
		}
		return ext.Not(member), nil
	}

	// Set-theory infix: ∈, ⊆, ⊊, ∪, ∩, ∖. Each maps to a single polymorphic
	// const meta (setOperator dispatch) whose element type A is unified from
	// the operands by buildAppViaMeta. Operands build in non-boolean context —
	// the LHS of ∈ is an A-typed element (typically not bool), and the LHS/RHS
	// of ⊆/∪/∩/∖ are set-typed (A → bool). A bare nullary operand (`x ∈ ∅`,
	// `s ⊆ 𝕌`) takes its instance from its partner (imposeBareConstOperand).
	// buildAppViaMeta rejects a genuine type mismatch (`x ∈ 3` — right is
	// num, not A→bool).
	//
	// Scope-first: setOperator names the const; the meta POINTER must come
	// from env.scopeConstMetas, which seedSetScopeConstFallback has filled
	// with the highest-precedence producer available (caller scope >
	// const resolver > DSL surface meta). Binding the package-level
	// surface meta directly here would mint def-less α-variant metas into
	// sessions whose registry carries the canonical meta — the
	// SetTacExpand-silent-skip / cnfKey-drift bug, and the
	// ConstTermMeta.Equals mixed-meta panic.
	if meta := setOperator(n.op); !meta.IsZero() {
		if m, ok := env.scopeConstMetas[string(meta.Name())]; ok {
			meta = m
		}
		left, right, err := buildSetOperands(n, env, meta)
		if err != nil {
			return nil, err
		}
		left, right = imposeBareConstOperand(n, env, meta, left, right)
		return buildAppViaMeta(env, meta, []core.Term{left, right})
	}

	// Function-space infix: ∘. Same scope-first rule as the set path above
	// — funcOperator names the const, the meta POINTER comes from
	// env.scopeConstMetas when anything better than the def-less surface
	// meta is available. `f ∘ g` is a PARTIAL application of `o`'s
	// three-argument type, which buildAppViaMeta instantiates from the two
	// arguments given.
	if meta := funcOperator(n.op); !meta.IsZero() {
		if m, ok := env.scopeConstMetas[string(meta.Name())]; ok {
			meta = m
		}
		left, err := buildTerm(n.left, env, false)
		if err != nil {
			return nil, err
		}
		right, err := buildTerm(n.right, env, false)
		if err != nil {
			return nil, err
		}
		left, right = imposeBareConstOperand(n, env, meta, left, right)
		return buildAppViaMeta(env, meta, []core.Term{left, right})
	}

	// Overloaded arith / comparison: +, -, *, <, ≤, >, ≥. The operator is
	// resolved by OPERAND TYPE, never by const name — both num ⇒ nat, both real
	// ⇒ real, both int ⇒ int, and likewise for the three real-construction-tower
	// layers (hreal, nadd, treal = hreal × hreal). The result type is the
	// operand type for arithmetic and bool for comparison. `-` is monus on num,
	// real_sub on real, int_sub on int, and has no instance at all in the tower.
	// Each operand is resolved by its OWN inferred type, so a statement mixing
	// domains (`hreal_of_num(m + n) ≤ x`, num inside, hreal outside) dispatches
	// each operator independently; only the two operands of ONE operator have to
	// agree. Genuinely mismatched operands are rejected.
	if isArithOperator(n.op) {
		left, right, err := buildArithOperands(n, env)
		if err != nil {
			return nil, err
		}
		lt, rt := left.Type(), right.Type()
		if !lt.Equals(rt) {
			return nil, fmt.Errorf("operator %s requires both operands in the same arithmetic domain (%s), got %s and %s",
				n.op, arithDomainNames, ext.FormatType(lt), ext.FormatType(rt))
		}
		meta := arithDomainOperator(n.op, lt)
		if meta.IsZero() {
			// No built-in domain serves the operands: a chapter's
			// constant declaring the symbol may — `vadd` at `num → A`
			// (operator.go) — or a resident structure's component may,
			// at its carrier (structure.go).
			if t, ok, err := buildChapterOperator(env, n.op, []core.Term{left, right}); ok || err != nil {
				return t, err
			}
			return nil, fmt.Errorf("operator %s has no instance for operand type %s", n.op, ext.FormatType(lt))
		}
		// Scope-first, mirroring the setOperator path above: when the
		// caller's scope carries a meta for the same const name at the
		// same shape, its POINTER wins over the DSL surface meta. The
		// surface metas are def-less α-variants of the registered metas;
		// binding them into a session whose registry carries the canonical
		// meta silently defeats def-sensitive consumers (def_expand's
		// DefThm gate — the SetTacExpand class; `∣` lowers to
		// nat_divides/int_divides, whose def IS the integer closer's
		// entry point). The AbsType guard keeps an unrelated same-name
		// scope meta from hijacking the operator.
		if m, ok := env.scopeConstMetas[string(meta.Name())]; ok &&
			m.AbsType().Equals(meta.AbsType()) {
			meta = m
		}
		applied := core.Apply(core.Apply(meta.Term(), left), right)
		if isValueArithOp(n.op) {
			return env.typedByNumerals(applied, left, right), nil
		}
		env.noteNumeralRelation(n.op, n.pos, left, right)
		return applied, nil
	}

	// The scalar action `c • u` and the limit relation `a ⟶ l` have no
	// built-in domain, so their operands need not agree in type: they
	// are built as they are and the declared constant is instantiated
	// from them (operator.go) — or, the declared constants declining, a
	// resident structure's component is read at the operands' types
	// (structure.go: a module's `smul : A → B → B`).
	// The power `x ^ n`: the BASE's domain picks the constant — nat_pow
	// at num, real_pow at real, int_pow at int (arith.go's
	// powDomainOperator), the exponent num in each. A base in no
	// built-in domain (a type variable, ℂ) falls through to the constant
	// declaring `^`, as for `•` and `⟶` below.
	if n.op == "^" {
		if t, ok, err := buildPower(n, env); ok || err != nil {
			return t, err
		}
	}

	if isDeclaredOnlyOperator(n.op) {
		left, err := buildTerm(n.left, env, false)
		if err != nil {
			return nil, err
		}
		right, err := buildTerm(n.right, env, false)
		if err != nil {
			return nil, err
		}
		if t, ok, err := buildChapterOperator(env, n.op, []core.Term{left, right}); ok || err != nil {
			return t, err
		}
		return nil, fmt.Errorf("operator %s has no instance for operand types %s and %s (no constant in scope declares it, and no resident structure binds it there)",
			n.op, ext.FormatType(left.Type()), ext.FormatType(right.Type()))
	}

	// All remaining binary ops are logical and require boolean operands.
	left, err := buildTerm(n.left, env, true)
	if err != nil {
		return nil, err
	}
	right, err := buildTerm(n.right, env, true)
	if err != nil {
		return nil, err
	}
	if !core.IsBool(left) {
		return nil, fmt.Errorf("operator %s requires boolean left operand, got %s", n.op, ext.FormatType(left.Type()))
	}
	if !core.IsBool(right) {
		return nil, fmt.Errorf("operator %s requires boolean right operand, got %s", n.op, ext.FormatType(right.Type()))
	}

	wl := ext.WrapTerm(left)
	switch n.op {
	case utils.AndStr:
		return wl.And(right), nil
	case utils.OrStr:
		return wl.Or(right), nil
	case utils.ImplyStr:
		return wl.Imply(right), nil
	case utils.IffStr:
		return wl.Eq(right), nil // ⇔ is = on booleans
	default:
		return nil, fmt.Errorf("unknown binary operator %q", n.op)
	}
}

// buildExpected builds `node` carrying a known expected type (nil =
// unknown). It threads the expectation into the two node shapes where an
// undeclared head would otherwise fall back to buildApp's bool-default:
//   - application: hand `expected` to buildApp as the result type, so
//     an undeclared head like predecessor in `predecessor(g(c))` is typed `…→<expected>`.
//   - lambda: peel one arrow off a function-typed `expected` and recurse
//     into the body with the codomain. This is what reaches the body of
//     `λg b c. predecessor(g(c))` — without it the body builds with no constraint
//     and the head bool-defaults. Nested lambdas peel one arrow per level.
//
// Bare variables receive the expected type when no stronger binding exists.
// A num at an int position is embedded with int_of_num. An arithmetic
// expression that types naturally keeps its operators and embeds as a whole:
// `a - b` with natural operands remains natural monus, including at int.
// Context still resolves explicit `&` syntax whose target is unanchored.
func buildExpected(node astNode, env *typeEnv, expected core.HolType) (core.Term, error) {
	t, err := buildExpectedNode(node, env, expected)
	if err == nil && !env.suppressImplicitInt && expected != nil && expected.Equals(IntType) && t.Type().Equals(NumType) {
		return core.Apply(IntOfNumMeta.Term(), t), nil
	}
	return t, err
}

// buildExpectedNode reads the syntax at its expected type before inserting
// the num-to-int embedding at that position.
func buildExpectedNode(node astNode, env *typeEnv, expected core.HolType) (core.Term, error) {
	if expected == nil {
		return buildTerm(node, env, false)
	}
	switch n := node.(type) {
	case *astVar:
		if len(n.typeAnnot) > 0 {
			return buildAnnotatedVarTerm(n, env)
		}
		// A polymorphic CONST may legitimately occur at several instances
		// in one statement — `⋃∅ = ∅` names the empty family and the
		// empty set — so the expected type this occurrence is handed must
		// not outlive it. env.inferred is keyed by NAME and is the right
		// memo for a VARIABLE (whose type must agree statement-wide); for
		// a const meta it would pin every later occurrence to the first
		// one's instance, and the statement fails to type. Scope the
		// stash to this occurrence, using the same save/restore the
		// binder builders already use for shadowed names.
		if _, isBound := env.bound[n.name]; !isBound {
			_, isMeta := env.scopeConstMetas[n.name]
			// A PINNED constant answers at one instance; where this
			// occurrence's expected type is another — a monomorphic
			// function applied to a polymorphic constructor,
			// `list_sum(nil)` with nil pinned at list(A) — the expected
			// type is stashed for this occurrence exactly as for a meta,
			// and buildVarTerm falls through to the constant's meta at
			// that instance (the applied-head fallthrough buildApp makes,
			// for the bare-atom site).
			pinnedElsewhere := false
			if c, isPinned := env.scopeConsts[n.name]; isPinned && !c.Type().Equals(expected) {
				pinnedElsewhere = true
			}
			if isMeta || pinnedElsewhere {
				prev, had := env.inferred[n.name]
				env.inferred[n.name] = expected
				t, err := buildVarTerm(n.name, env, expected.Equals(core.TypeBool()))
				if had {
					env.inferred[n.name] = prev
				} else {
					delete(env.inferred, n.name)
				}
				return t, err
			}
		}
		if _, ok := env.lookupType(n.name); !ok {
			env.inferred[n.name] = expected
		}
		return buildVarTerm(n.name, env, expected.Equals(core.TypeBool()))
	case *astApp:
		return buildApp(n, env, expected)
	case *astAbsNode:
		return buildAbs(n, env, expected)
	case *astPatternAbs:
		return buildPatternAbs(n, env, expected)
	case *astTermLit:
		return n.term, nil
	case *astCoerce:
		return buildCoerce(n, env, expected)
	case *astNeg:
		return buildNeg(n, env, expected)
	case *astBigOp:
		return buildBigOp(n, env, expected)
	case *astBinOp:
		// A natural computation owns its domain before an enclosing int
		// position embeds its result. Only syntax needing a numeric domain
		// (`&a * &b`, for example) is read under the expectation below.
		if expected.Equals(IntType) && (isValueArithOp(n.op) || n.op == powerSymbol) {
			if t, err := buildTerm(n, env, false); err == nil && (t.Type().Equals(NumType) || t.Type().Equals(IntType)) {
				return t, nil
			}
		}
		if t, ok, err := buildArithExpected(n, env, expected); ok {
			return t, err
		}
		if t, ok, err := buildPowerExpected(n, env, expected); ok {
			return t, err
		}
		return buildTerm(node, env, expected.Equals(core.TypeBool()))
	default:
		return buildTerm(node, env, expected.Equals(core.TypeBool()))
	}
}

// buildCoerce lowers a `&t` coercion — the build half of the type-directed `&`.
// The operand is a num (`&` is the num→{real,int} embedding) or a real,
// which only a DECLARED lift can take (a chapter's constant marked
// Coercion — complex_of_real into ℂ — syntax.go; a num reaches it through
// the real line). Target resolution, in order: an anchoring `expected`
// type (an operand the author typed — intent; a lift's codomain among
// them), then the scope's declared CoerceDomain, and only then the
// global real_of_num default. Under the declared domain a REAL lifts
// into it (a chapter that declared ℂ reads `&x` as complex_of_real(x),
// and `&exp(x)` likewise), while a NUM is read on the real line — int
// under a declared ℤ — and lifts further only where a position or a
// partner asks (`exp(i * &π) + &1`): a chapter's literals stay its
// field's. A pure-default coercion is recorded under the strict guard
// (StrictResolution, or StrictCoercion by itself): if it SURVIVES into the
// final statement (the reconcile may still retarget it), the parse errors
// instead of silently meaning ℝ.
func buildCoerce(n *astCoerce, env *typeEnv, expected core.HolType) (core.Term, error) {
	operand, err := buildTerm(n.operand, env, false)
	if err != nil {
		return nil, err
	}
	isNum, isReal := operand.Type().Equals(NumType), operand.Type().Equals(RealType)
	if !isNum && !isReal {
		return nil, fmt.Errorf("& coercion requires a num or real operand, got %s", ext.FormatType(operand.Type()))
	}
	// lift is the declared embedding into a codomain, applied to the
	// operand read on the real line.
	lift := func(into core.HolType) (core.Term, bool, error) {
		name := env.coercionConst(into)
		if name == "" {
			return nil, false, nil
		}
		if syn := env.syntax.ConstSyntax(name); isReal && syn != nil && syn.Coercion != nil && syn.Coercion.NumeralsOnly {
			return nil, true, fmt.Errorf("& of a real operand into %s: %s lifts numerals only — spell %s(…) where the real may be negative", ext.FormatType(into), name, name)
		}
		meta, err := env.constMeta(name)
		if err != nil {
			return nil, true, fmt.Errorf("& coercion into %s: %v", ext.FormatType(into), err)
		}
		base := operand
		if isNum {
			base = core.Apply(RealOfNumMeta.Term(), operand)
		}
		return core.Apply(meta.Term(), base), true, nil
	}
	switch {
	case expected != nil && isNum && expected.Equals(IntType):
		return core.Apply(IntOfNumMeta.Term(), operand), nil
	case expected != nil && isNum && expected.Equals(RealType):
		return core.Apply(RealOfNumMeta.Term(), operand), nil
	case expected != nil && !expected.Equals(NumType):
		if t, ok, err := lift(expected); ok || err != nil {
			return t, err
		}
	}
	// The declared domain is real, int, or a type some constant is the
	// declared coercion into — checked at the `&` that reads it, since a
	// chapter declares its domain before it mints the lift.
	if env.coerceDomain != nil && !env.coerceDomain.Equals(RealType) && !env.coerceDomain.Equals(IntType) && env.coercionConst(env.coerceDomain) == "" {
		return nil, fmt.Errorf("ParseScope.CoerceDomain must be real, int, or a type some constant is the declared coercion into, got %s", ext.FormatType(env.coerceDomain))
	}
	if isReal {
		if env.coerceDomain != nil {
			if t, ok, err := lift(env.coerceDomain); ok || err != nil {
				return t, err
			}
		}
		return nil, fmt.Errorf("& of a real operand needs a domain that lifts it — a position of that type, or the chapter's declared domain being one some constant is the coercion into")
	}
	switch {
	case env.coerceDomain != nil && env.coerceDomain.Equals(IntType):
		return env.typedByNumeral(core.Apply(IntOfNumMeta.Term(), operand)), nil
	case env.coerceDomain != nil:
		return env.typedByNumeral(core.Apply(RealOfNumMeta.Term(), operand)), nil
	}
	t := env.typedByNumeral(core.Apply(RealOfNumMeta.Term(), operand))
	if env.strictCoerce {
		env.defaultedCoerces = append(env.defaultedCoerces, defaultedCoerce{term: t, pos: n.pos})
	}
	return t, nil
}

// typedByNumeral marks t as a term whose type an `&` numeral decided
// alone (typeEnv.numeralTyped) and returns it.
func (env *typeEnv) typedByNumeral(t core.Term) core.Term {
	if env.numeralTyped == nil {
		env.numeralTyped = map[core.Term]bool{}
	}
	env.numeralTyped[t] = true
	return t
}

// typedByNumerals marks result as typed by numerals alone where each
// of operands is, and returns it: an arithmetic combination of such
// terms has the type they have.
func (env *typeEnv) typedByNumerals(result core.Term, operands ...core.Term) core.Term {
	for _, operand := range operands {
		if !env.numeralTyped[operand] {
			return result
		}
	}
	return env.typedByNumeral(result)
}

// noteNumeralRelation records the relation op at pos when both of its
// sides are typed by numerals alone: nothing in it says which type it
// is stated at.
func (env *typeEnv) noteNumeralRelation(op string, pos int, left, right core.Term) {
	if env.numeralTyped[left] && env.numeralTyped[right] {
		env.numeralRelations = append(env.numeralRelations, numeralRelation{left: left, op: op, pos: pos})
	}
}

// numeralWarnings are the relations between numerals alone that
// survived into the statement, one warning each in the text's order:
// the type the relation was read at and why, and how the author states
// it at another. A relation an outer rebuild replaced is not in the
// statement and is not reported.
func (env *typeEnv) numeralWarnings(terms []core.Term) []InputDiagnostic {
	if len(env.numeralRelations) == 0 {
		return nil
	}
	present := map[core.Term]bool{}
	for _, t := range terms {
		collectTermNodes(t, present)
	}
	reason := "the scope declares no `&` domain, and a bare numeral is then real"
	switch {
	case env.coerceDomain != nil && env.coerceDomain.Equals(IntType):
		reason = "the scope's `&` domain is int"
	case env.coerceDomain != nil && env.coerceDomain.Equals(RealType):
		reason = "the scope's `&` domain is real"
	case env.coerceDomain != nil:
		reason = fmt.Sprintf("the scope's `&` domain is %s, under which a bare numeral stays on the real line and lifts "+
			"only where a position or a partner asks", ext.FormatType(env.coerceDomain))
	}
	suggestion := "to state it at another type, type one side: spell its embedding longhand, or name a term of that type"
	if lift := env.coercionConst(env.coerceDomain); lift != "" {
		suggestion = fmt.Sprintf("to state it at %s, lift one side, `%s(&…)`: the other side follows it",
			ext.FormatType(env.coerceDomain), lift)
	}
	seen := map[int]bool{}
	var warnings []InputDiagnostic
	for _, r := range env.numeralRelations {
		if !present[r.left] || seen[r.pos] {
			continue
		}
		seen[r.pos] = true
		warnings = append(warnings, InputDiagnostic{
			Position: r.pos,
			Length:   len(r.op),
			Code:     CodeNumeralDomain,
			Message: fmt.Sprintf("the relation `%s` at position %d stands between numerals alone and is read at %s: "+
				"nothing in it names a type, and %s", r.op, r.pos, ext.FormatType(r.left.Type()), reason),
			Suggestion: suggestion,
		})
	}
	sort.SliceStable(warnings, func(i, j int) bool { return warnings[i].Position < warnings[j].Position })
	return warnings
}

// buildNeg lowers a unary `-x`. The result is real_neg or int_neg, chosen by the
// operand's own type (num has no negation). An int expectation embeds a
// num operand; other expectations guide an explicit `&` coercion.
func buildNeg(n *astNeg, env *typeEnv, expected core.HolType) (core.Term, error) {
	operand, err := buildExpected(n.operand, env, expected)
	if err != nil {
		return nil, err
	}
	switch {
	case operand.Type().Equals(RealType):
		return env.typedByNumerals(core.Apply(RealNegMeta.Term(), operand), operand), nil
	case operand.Type().Equals(IntType):
		return env.typedByNumerals(core.Apply(IntNegMeta.Term(), operand), operand), nil
	}
	// A chapter's constant declaring the prefix `-` at the operand's
	// type — `vneg` at `num → A` (operator.go) — or a resident
	// structure's component at its carrier (structure.go).
	if t, ok, err := buildChapterOperator(env, "-", []core.Term{operand}); ok || err != nil {
		return t, err
	}
	return nil, fmt.Errorf("unary - requires a real or int operand, got %s", ext.FormatType(operand.Type()))
}

// isValueArithOp reports whether op is a value-producing arithmetic operator
// (result type = operand type), as opposed to a comparison (result bool).
func isValueArithOp(op string) bool { return op == "+" || op == "-" || op == "*" }

// buildArithExpected builds a value arith astBinOp (`+`/`-`/`*`) forced to the
// `expected` domain (real or int), threading that domain into both operands so a
// nested `&` coercion resolves there and num operands embed at int. Returns
// ok=false for the default build when expected isn't real/int, the op isn't
// a value arith op, the domain has no instance, or an operand can't be coerced.
func buildArithExpected(n *astBinOp, env *typeEnv, expected core.HolType) (core.Term, bool, error) {
	if !expected.Equals(RealType) && !expected.Equals(IntType) {
		return nil, false, nil
	}
	if !isValueArithOp(n.op) {
		return nil, false, nil
	}
	meta := arithDomainOperator(n.op, expected)
	if meta.IsZero() {
		return nil, false, nil
	}
	left, err := buildExpected(n.left, env, expected)
	if err != nil {
		return nil, false, nil
	}
	right, err := buildExpected(n.right, env, expected)
	if err != nil {
		return nil, false, nil
	}
	if !left.Type().Equals(expected) || !right.Type().Equals(expected) {
		return nil, false, nil
	}
	return core.Apply(core.Apply(meta.Term(), left), right), true, nil
}

// buildArithOperands builds both operands of an overloaded arith/comparison op,
// then reads a num or a real-defaulted `&` at an int partner's domain:
// both `x:int + 2` and `x:int + &2` embed the numeral with int_of_num.
// An operand whose type is recoverable only from its PARTNER gets the
// partner's type imposed on it, exactly as buildEqOperands does across `=`.
// This is what keeps the infix surface as expressive as the prefix spelling
// it sugars: `hreal_add(snd(y), d)` types the free `d` from hreal_add's
// declared domain, so `snd(y) + d` must type it from the partner — otherwise
// the sugar would be strictly weaker than the form it replaces, and
// "surface-only" would be false. An operand that already builds keeps its
// type except for numeric reconciliation against its partner.
func buildArithOperands(n *astBinOp, env *typeEnv) (core.Term, core.Term, error) {
	left, lerr := buildTerm(n.left, env, false)
	right, rerr := buildTerm(n.right, env, false)
	switch {
	case lerr == nil && rerr == nil:
		left, right = reconcileNumericDomain(n.left, n.right, left, right, env)
		env.exoneratePartnerAnchoredCoerces(left, right)
		return reconcileFreshLetters(env, left, right)
	case lerr == nil && rerr != nil:
		right, err := buildExpected(n.right, env, left.Type())
		if err != nil {
			return nil, nil, err
		}
		return left, right, nil
	case rerr == nil && lerr != nil:
		left, err := buildExpected(n.left, env, right.Type())
		if err != nil {
			return nil, nil, err
		}
		return left, right, nil
	default:
		return nil, nil, lerr
	}
}

// reconcileNumericDomain reads a num operand at int when its partner is int,
// and retargets a real-defaulted operand to int for the type-directed `&`. A
// genuine real operand fails the int rebuild and is left real, so the caller's
// type-mismatch error still surfaces. An operand the real line typed beside
// a partner whose arrows end in a domain some constant is the declared
// coercion into (liftsAtResult) is rebuilt at the partner's type the same
// way, the expectation reaching every λ body on the way: `exp(i * &π) + &1`
// reads `&1` as complex_of_real(&1) because its partner is complex,
// `f = λx. &0` at a complex-valued f reads the body at ℂ, and a genuine
// real — a variable, or a λ whose body is one — fails the rebuild and is
// left real.
func reconcileNumericDomain(ln, rn astNode, left, right core.Term, env *typeEnv) (core.Term, core.Term) {
	lt, rt := left.Type(), right.Type()
	switch {
	case lt.Equals(IntType) && rt.Equals(NumType):
		if r2, e := buildExpected(rn, env, IntType); e == nil && r2.Type().Equals(IntType) {
			return left, r2
		}
	case rt.Equals(IntType) && lt.Equals(NumType):
		if l2, e := buildExpected(ln, env, IntType); e == nil && l2.Type().Equals(IntType) {
			return l2, right
		}
	case env.liftsAtResult(rt, lt):
		if r2, e := buildExpected(rn, env, lt); e == nil && r2.Type().Equals(lt) {
			return left, r2
		}
	case env.liftsAtResult(lt, rt):
		if l2, e := buildExpected(ln, env, rt); e == nil && l2.Type().Equals(rt) {
			return l2, right
		}
	case lt.Equals(IntType) && rt.Equals(RealType):
		if r2, e := buildExpected(rn, env, IntType); e == nil && r2.Type().Equals(IntType) {
			return left, r2
		}
		// The symmetric direction: a declared-default int coercion
		// yields to a genuine real partner. Only a `&`-built term can
		// rebuild at real (variables and longhand consts fail), so
		// anchors stay authoritative; in a scope with no declared
		// domain an int operand is never a bare coercion, so this arm
		// cannot fire there and legacy behavior is unchanged.
		if l2, e := buildExpected(ln, env, RealType); e == nil && l2.Type().Equals(RealType) {
			return l2, right
		}
	case rt.Equals(IntType) && lt.Equals(RealType):
		if l2, e := buildExpected(ln, env, IntType); e == nil && l2.Type().Equals(IntType) {
			return l2, right
		}
		if r2, e := buildExpected(rn, env, RealType); e == nil && r2.Type().Equals(RealType) {
			return left, r2
		}
	}
	return left, right
}

// liftsAtResult reports whether an operand of type side may be the
// real line's reading of an operand its partner, of type partner,
// types: partner's arrows end in a type a declared coercion lifts into
// (liftResult, the type the chapter spelling folds a lift against), and
// side takes as many arguments and ends in ℝ. That is the type the `&`
// default gives a `&`, a negation of one or a λ whose body is one, where
// the partner would have read it at the lift; the rebuild at the
// partner's type decides, and a side it does not bring to that type is
// a genuine mismatch.
func (env *typeEnv) liftsAtResult(side, partner core.HolType) bool {
	return liftResult(env.syntax, partner) != nil &&
		spineResult(side).Equals(RealType) &&
		len(argumentSlots(side)) == len(argumentSlots(partner))
}

// buildArg builds an argument term, given the expected type that the
// enclosing function's domain imposes on this position (nil = no constraint).
// Threading the domain through every argument shape lets known constants pin
// nested lambdas, undeclared applications, and bare variables before the kernel
// application check runs.
func buildArg(node astNode, env *typeEnv, expected core.HolType) (core.Term, error) {
	if expected != nil {
		return buildExpected(node, env, expected)
	}
	return buildTerm(node, env, false)
}

// buildSetOperands builds a set infix's two operands. A bare use of a
// binder deferred to its uses — `{w | w ∈ s}`'s w at its only use — is
// built after its partner, against the domain the partner instantiates
// (the element type of s), as an application's arguments are ordered
// (buildArgsAgainstFunType); otherwise both are built as they stand.
func buildSetOperands(n *astBinOp, env *typeEnv, meta core.ConstTermMeta) (left, right core.Term, err error) {
	leftDeferred, rightDeferred := env.deferredBinderVar(n.left), env.deferredBinderVar(n.right)
	if leftDeferred == rightDeferred {
		if left, err = buildTerm(n.left, env, false); err != nil {
			return nil, nil, err
		}
		if right, err = buildTerm(n.right, env, false); err != nil {
			return nil, nil, err
		}
		return left, right, nil
	}
	absType, _ := env.freshAbs(meta)
	domains := decomposeFunType(absType, 2)
	if len(domains) < 2 {
		return nil, nil, fmt.Errorf("const %q: not a binary operator (%s)", meta.Name(), ext.FormatType(absType))
	}
	// The partner first; the deferred binder against the domain it
	// instantiates, where that domain is concrete.
	partnerAST, deferredAST, partnerDomain, deferredDomain := n.right, n.left, domains[1], domains[0]
	if rightDeferred {
		partnerAST, deferredAST, partnerDomain, deferredDomain = n.left, n.right, domains[0], domains[1]
	}
	partner, err := buildTerm(partnerAST, env, false)
	if err != nil {
		return nil, nil, err
	}
	var expected core.HolType
	if substs, ok := unifyDomainArg(env, partnerDomain, partner.Type(), nil); ok {
		if d := deferredDomain.Substitute(substs...); !ext.TypeAnyVar(d, env.constLetter) {
			expected = d
		}
	}
	deferred, err := buildArg(deferredAST, env, expected)
	if err != nil {
		return nil, nil, err
	}
	if rightDeferred {
		return partner, deferred, nil
	}
	return deferred, partner, nil
}

// buildArgsAgainstFunType builds application arguments left-to-right while
// threading each known function-domain type into the corresponding argument.
// For polymorphic constants, each successfully-built argument refines later
// domains, so `COND(c, λx. ..., λx. ..., y)` and `set_comprehension(λv. ...)` can push the
// instantiated lambda-binder type into nested bodies before core.Apply checks.
//
// The arguments are built in their order but for a bare use of a binder
// deferred to its uses (untypedAbsVars, no type yet): it is built as
// soon as its domain is concrete — before the arguments still to come,
// which may be the binder's only other uses — and, while its domain
// stays polymorphic, after every other argument, against the domain
// they instantiate.
//
// A `&` has no type of its own, and one in a slot still polymorphic
// takes the default where it stands and so decides the slot for the
// arguments after it. Where that reading does not build — the other
// arguments do not fit the default — the arguments are read again with
// every such `&` waiting as a deferred binder waits, for the type the
// others give its slot: `COND(c, &0, z)` reads its `&0` at z's type as
// `COND(c, z, &0)` does. It is the operators' rule, a default and then
// a rebuild at the partner's type (reconcileNumericDomain), for an
// application's arguments. A text the first reading builds is built
// by it alone. So the set-builder's `comprehension_spec(v, φ, t)`
// types v from t (the three-part form `{ x + x | x | x ∈ s }` builds
// although its output is no bare binder the collect pass can read a
// type off), and with v typed by the context it types the binder x from
// v before φ asks the word `abs` to pick a constant by x's type. The
// order of the other arguments is kept as written: building a typed
// variable ahead of its place changes the unification order, and under
// a scope that does not freshen a constant's letters an author's `B`
// beside image's `B` unifies in one order and not the other.
func buildArgsAgainstFunType(argsAST []astNode, env *typeEnv, funType core.HolType) ([]core.Term, error) {
	return buildArgsAgainst(argsAST, env, funType, false)
}

// buildPinnedArgs tries a polymorphic pin with a meta fallback without
// implicit embeddings. A natural argument can then select the natural
// instance through that fallback. A head without such a fallback supplies
// its fixed domain and allows the embedding immediately.
func buildPinnedArgs(argsAST []astNode, env *typeEnv, c core.ConstTerm) ([]core.Term, error) {
	prev := env.suppressImplicitInt
	if meta, ok := env.scopeConstMetas[string(c.Name())]; ok && len(meta.AbsType().TypeVars()) > 0 {
		env.suppressImplicitInt = true
	}
	defer func() { env.suppressImplicitInt = prev }()
	return buildArgsAgainstFunType(argsAST, env, c.Type())
}

// buildArgsAgainstMeta is buildArgsAgainstFunType for a head read
// through its META — the last reading an application has — where a
// bare pinned constant the fixed domain rejects is re-read at that
// domain (rereadPinnedAtom) instead of failing the application.
func buildArgsAgainstMeta(argsAST []astNode, env *typeEnv, funType core.HolType) ([]core.Term, error) {
	return buildArgsAgainst(argsAST, env, funType, true)
}

func buildArgsAgainst(argsAST []astNode, env *typeEnv, funType core.HolType, rereadPins bool) ([]core.Term, error) {
	args, defaulted, err := buildArgsReading(argsAST, env, funType, rereadPins, false)
	if err == nil || !defaulted {
		return args, err
	}
	if late, _, lateErr := buildArgsReading(argsAST, env, funType, rereadPins, true); lateErr == nil {
		return late, nil
	}
	return nil, err
}

// buildArgsReading is one reading of an application's arguments
// (buildArgsAgainstFunType). late says a `&` in a slot still
// polymorphic waits for the other arguments; otherwise it is built in
// its place, and defaulted reports that one was.
func buildArgsReading(
	argsAST []astNode, env *typeEnv, funType core.HolType, rereadPins, late bool,
) (out []core.Term, defaulted bool, err error) {
	args := make([]core.Term, len(argsAST))
	built := make([]bool, len(argsAST))
	var substs []core.TypeSubst
	open := func(d core.HolType) bool { return ext.TypeAnyVar(d, utils.FullPredicate[core.VarType]) }
	waits := func(i int) bool { return late && positionTyped(argsAST[i]) }
	// domain is the i-th domain of the function type under the
	// substitutions so far — peeled afresh each time, since an earlier
	// argument may instantiate a type variable to a function type and
	// so expose the later domains (`vec_add(add, P, Q, i, j)` at a
	// carrier that is itself `num → A`). ok is false while the depth is
	// not yet exposed.
	domain := func(i int) (core.HolType, bool) {
		cur := funType.Substitute(env.slotSubsts(substs)...)
		for k := 0; ; k++ {
			ft, ok := cur.(core.CompositeType)
			if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
				return nil, false
			}
			if k == i {
				return ft.SubType(0), true
			}
			cur = ft.SubType(1)
		}
	}
	buildAt := func(i int) error {
		d, ok := domain(i)
		if !ok {
			return fmt.Errorf(
				"argument count %d exceeds curry depth of type %s",
				len(argsAST), ext.FormatType(funType))
		}
		if positionTyped(argsAST[i]) && open(d) {
			defaulted = true
		}
		arg, err := buildArg(argsAST[i], env, d)
		if err != nil {
			return err
		}
		args[i] = arg
		built[i] = true
		more, ok := unifyDomainArg(env, d, arg.Type(), substs)
		if !ok && rereadPins {
			if reread := rereadPinnedAtom(argsAST[i], env, d); reread != nil {
				arg, args[i] = reread, reread
				more, ok = unifyDomainArg(env, d, arg.Type(), substs)
			}
		}
		if !ok {
			return slotMismatch(arg.Type(), d)
		}
		substs = append(substs, more...)
		return nil
	}
	// pinDeferred builds every deferred binder and every waiting `&`
	// whose domain has become concrete, until none has.
	pinDeferred := func() error {
		for progress := true; progress; {
			progress = false
			for i := range argsAST {
				if built[i] || !(env.deferredBinderVar(argsAST[i]) || waits(i)) {
					continue
				}
				if d, ok := domain(i); !ok || open(d) {
					continue
				}
				if err := buildAt(i); err != nil {
					return err
				}
				progress = true
			}
		}
		return nil
	}
	if err := pinDeferred(); err != nil {
		return nil, defaulted, err
	}
	for i, argAST := range argsAST {
		if built[i] {
			continue
		}
		if d, exposed := domain(i); exposed && (env.deferredBinderVar(argAST) || waits(i) && open(d)) {
			continue
		}
		if err := buildAt(i); err != nil {
			return nil, defaulted, err
		}
		if err := pinDeferred(); err != nil {
			return nil, defaulted, err
		}
	}
	for i := range argsAST {
		if !built[i] {
			if err := buildAt(i); err != nil {
				return nil, defaulted, err
			}
		}
	}
	return args, defaulted, nil
}

// positionTyped says whether node is a `&` coercion, bare or under a
// prefix `-`: a term with no type of its own, read at the type its
// position gives it (astCoerce).
func positionTyped(node astNode) bool {
	switch n := node.(type) {
	case *astCoerce:
		return true
	case *astNeg:
		return positionTyped(n.operand)
	}
	return false
}

// deferredBinderVar says whether node is a bare use of a binder whose
// type is deferred to its uses (buildAbs / buildQuant's untypedAbsVars)
// and that nothing has typed yet.
func (env *typeEnv) deferredBinderVar(node astNode) bool {
	v, ok := node.(*astVar)
	if !ok || len(v.typeAnnot) > 0 || !env.untypedAbsVars[v.name] {
		return false
	}
	_, typed := env.lookupType(v.name)
	return !typed
}

// buildApp lowers a function application. `expected`, when non-nil, is
// the type this application must produce (bool in a logical-atom
// position, or a domain type when nested as another function's
// argument). It is used only to type an *undeclared* head by its result
// type — declared/known heads already carry their type. When `expected`
// is nil the head defaults to a bool result, preserving the original
// behavior for standalone undeclared predicates.
func buildApp(n *astApp, env *typeEnv, expected core.HolType) (core.Term, error) {
	// A constant applied in stages, `ring_add(R)(a, b)` — the bundle
	// pass's reading of a record field `R.add(a, b)` — is the constant
	// applied to every argument, and is built as `ring_add(R, a, b)` is:
	// each argument read at the constant's domain.
	if spine := appSpine(n); spine != n {
		if head, isVar := spine.fun.(*astVar); isVar {
			_, isBound := env.bound[head.name]
			_, isConst := env.scopeConsts[head.name]
			_, hasMeta := env.scopeConstMetas[head.name]
			if !isBound && (isConst || hasMeta) {
				n = spine
			}
		}
	}
	// Nat-encoding consts (_0/bit0/bit1/suc) are seeded into
	// env.scopeConsts by newTypeEnv, so heads like `bit0` resolve
	// through the regular scopeConsts path below.
	//
	// Caller-supplied scope. When the function is a
	// bare name resolvable in env.scopeConstMetas, instantiate it from
	// arguments built under the meta's domain constraints. If only a
	// fixed env.scopeConsts instance is available, build against that
	// instance and curry-apply it. This makes emit-output text props
	// produce ConstTerm for proof-declared consts (subset, int_of_num,
	// …) instead of VarTerm, matching the original prop for alpha-key
	// compare.
	// Bound binders shadow scope consts — `∃real_pow:T.…real_pow(x)…` is
	// a local Skolem function name, not the global `real_pow` const — so
	// skip both scope-const paths when env.bound has the head name and
	// let the buildVarTerm path below treat it as a bound var.
	if funVar, isVar := n.fun.(*astVar); isVar {
		if _, isBound := env.bound[funVar.name]; !isBound {
			// Annotation path: `Name⟨V:T⟩(args)` — the annotation forces
			// meta-based instantiation and its type-var bindings win over
			// any scope-fixed instance. Fall through to the meta lookup
			// (scopeConstMetas first, then scopeConsts.Meta()).
			if len(funVar.typeAnnot) > 0 {
				var meta core.ConstTermMeta
				if m, ok := env.scopeConstMetas[funVar.name]; ok {
					meta = m
				} else if c, ok := env.scopeConsts[funVar.name]; ok {
					meta = c.Meta()
				} else {
					return nil, fmt.Errorf(
						"type annotation ⟨...⟩ on %q: not a scope constant "+
							"(annotations are only valid on polymorphic constants)%s",
						funVar.name, env.overloadHint(funVar.name))
				}
				if err := validateAnnotAgainstMeta(meta, funVar.typeAnnot); err != nil {
					return nil, err
				}
				// Pre-substitute the meta's abstract type with the
				// annotation before argument-domain unification, so
				// nested arg builds see the concrete domain types.
				annotSubsts := resolveTypeAnnotation(funVar.typeAnnot)
				env.recordAnnotTyVars(annotSubsts)
				annotAbs, annotFresh := env.freshAbs(meta)
				preInst := annotAbs.Substitute(translateSeedThroughFresh(annotSubsts, annotFresh)...)
				args, err := buildArgsAgainstMeta(n.args, env, preInst)
				if err != nil {
					return nil, err
				}
				return buildAppViaMetaSeeded(env, meta, args, annotSubsts)
			}
			// Scope fixed-instance FAST PATH first (before the meta path).
			// When the prop uses this const at a single instance the section
			// captured, `scopeConsts` carries the exact concrete instance —
			// including any polymorphic type-vars named as they appear in
			// this prop (e.g. `c : (num → T(var:N))`).
			// The meta path would re-instantiate from the meta's ABSTRACT
			// type-vars (fresh `var:A`), producing a term whose type is
			// syntactically distinct from — and therefore fails to unify
			// with — a sibling use that pins the type via a bound-var
			// annotation (e.g. `∀Q:(T(var:N) → bool). … Q(c(i)) …`).
			// If the fixed instance's curry-prefix types agree with the
			// argument types (applyTypesMatch), we use it directly and
			// preserve the shared type-var name. If not — the current call
			// site is at a DIFFERENT instance from what scopeConsts pinned
			// (multi-instance within the prop) — we fall through to the
			// meta path, which unifies from the args' actual types.
			if c, ok := env.scopeConsts[funVar.name]; ok {
				args, err := buildPinnedArgs(n.args, env, c)
				if err == nil && applyTypesMatch(c.Type(), args) {
					var result core.Term = c
					for _, arg := range args {
						result = core.Apply(result, arg)
					}
					return result, nil
				}
			}
			if meta, ok := env.scopeConstMetas[funVar.name]; ok {
				// Thread the FRESHENED domains into the arguments — the
				// verbatim abstract letters here were a capture bypass
				// (an argument built against the meta's own `A` ties to
				// a same-named author letter). The builder re-freshens
				// for its own unify; var-to-var bindings between the
				// two occurrence alphabets resolve in its chain pass.
				abs, _ := env.freshAbs(meta)
				args, err := buildArgsAgainstMeta(n.args, env, abs)
				if err != nil {
					return nil, err
				}
				return buildAppViaMeta(env, meta, args)
			}
			// An overloaded word the scope does not declare as anything
			// else: the constant its arguments pick (overload.go).
			if _, isDeclared := env.declared[funVar.name]; !isDeclared {
				if cands, ok := env.overloadWord(funVar.name); ok {
					return buildOverload(n, funVar.name, cands, env)
				}
			}
		}
	}

	// Resolve the head's type up front when it is already known (declared
	// or inferred in an earlier pass). A known head lets us hand each
	// argument the domain type it must satisfy — essential for nested
	// undeclared applications like P(g(x)) where P : num→bool: g's result
	// type has to come from P's domain (num), not the bool-default.
	funVar, isVar := n.fun.(*astVar)
	var knownFunTy core.HolType
	if isVar {
		if ty, ok := env.lookupType(funVar.name); ok {
			knownFunTy = ty
		}
	}
	var domTypes []core.HolType
	if knownFunTy != nil {
		domTypes = decomposeFunType(knownFunTy, len(n.args))
	}

	// Build argument terms. When the head type is unknown we still build
	// args first (with no constraint) so their types can drive the
	// head-type inference below.
	args := make([]core.Term, len(n.args))
	for i, arg := range n.args {
		var argExpected core.HolType
		if i < len(domTypes) {
			argExpected = domTypes[i]
		}
		t, err := buildArg(arg, env, argExpected)
		if err != nil {
			return nil, err
		}
		args[i] = t
	}

	if isVar {
		ty := knownFunTy
		if ty == nil {
			// Undeclared head: infer F : argTypes → result. The result type comes
			// from the caller-imposed `expected` when known (a bool-atom position
			// passes bool; a known function-arg domain passes its domain; an =/≠
			// partner reaches here via buildEqOperands with the partner's type).
			// When `expected` is nil the result type is genuinely unconstrained —
			// FAIL FAST naming F, rather than silently defaulting to bool. The old
			// bool-default only ever fired in value positions (bool-atom positions
			// already pass expected=bool), where bool is almost always wrong: it
			// mis-typed uses like `nat_pow(a,n) = 1` and surfaced far away as a baffling
			// "left is bool" mismatch instead of pointing at the undeclared F.
			argTypes := make([]core.HolType, len(args))
			for i, a := range args {
				argTypes[i] = a.Type()
			}
			if expected == nil {
				return nil, fmt.Errorf(
					"cannot infer result type of undeclared function %q applied to (%s); "+
						"declare it (e.g. `%s : <type>`) or constrain its result",
					funVar.name, formatHolTypes(argTypes), funVar.name)
			}
			ty = buildFunType(argTypes, expected)
			env.inferred[funVar.name] = ty
		}

		if env.strict {
			if err := env.strictFreshenCheck(funVar.name); err != nil {
				return nil, err
			}
		}
		return applyArgs(env, core.Var(core.TermName(funVar.name), ty), args, false)
	}

	// A head that is no name: a field read off a record (`P(n).add`), a
	// λ applied in place. Its stand-ins are its own, and the arguments
	// may bind them. An abbreviation's λ reads the letters its arguments
	// fix off the arguments, before it is built (entryLetterTypes).
	if n.reduced && len(n.letters) > 0 {
		retypeEntryLetters(n.fun, entryLetterTypes(n.fun, args, n.letters))
	}
	funTerm, err := buildTerm(n.fun, env, false)
	if err != nil {
		return nil, err
	}
	applied, err := applyArgs(env, funTerm, args, true)
	if err != nil {
		return nil, err
	}
	if n.reduced {
		return reduceHead(applied, len(args)), nil
	}
	return applied, nil
}

// entryLetterTypes is the types an abbreviation's use, the λ head, is
// read at for letters, the letters its arguments fix (abbreviation.go,
// instantiateLetters): each written binder type the arguments fill
// matched against its argument's type. A letter matched at a type that
// still holds a constant's stand-in, or at itself, stays as written,
// and the application reads it as before; a binder untyped, or an
// argument whose type the binder's cannot match, leaves its letters to
// the application to refuse.
func entryLetterTypes(head astNode, args []core.Term, letters []string) []core.TypeSubst {
	instantiable := func(v core.VarType) bool { return slices.Contains(letters, string(v.Name())) }
	var σ []core.TypeSubst
	for _, arg := range args {
		abs, ok := head.(*astAbsNode)
		if !ok || abs.varType == nil {
			break
		}
		held := slices.Clone(σ)
		if !core.MatchTypeInto(resolveType(abs.varType), arg.Type(), instantiable, &σ) {
			σ = held
		}
		head = abs.body
	}
	return slices.DeleteFunc(σ, func(s core.TypeSubst) bool {
		return s.HolType.Equals(s.VarType) || ext.TypeAnyVar(s.HolType, isStandIn)
	})
}

// retypeEntryLetters writes σ into head, the λ of an abbreviation's
// use: every type its AST carries — the types written at its binders
// and ties, the ones the collect pass stashed, the terms a pass spliced
// in — at σ's types for the use's letters, which only the entry's text
// spells there (instantiateLetters leaves out a letter a free name
// types).
func retypeEntryLetters(head astNode, σ []core.TypeSubst) {
	if len(σ) == 0 {
		return
	}
	at := make(map[string]astType, len(σ))
	for _, s := range σ {
		at[string(s.VarType.Name())] = holTypeToAst(s.HolType)
	}
	retypeLetters(head, at)
	walkAST(head, func(n astNode) {
		switch n := n.(type) {
		case *astQuantNode:
			if n.resolvedVarType != nil {
				n.resolvedVarType = n.resolvedVarType.Substitute(σ...)
			}
		case *astAbsNode:
			if n.resolvedVarType != nil {
				n.resolvedVarType = n.resolvedVarType.Substitute(σ...)
			}
		case *astPatternAbs:
			for _, lf := range n.pat.leaves(nil) {
				if lf.resolvedTy != nil {
					lf.resolvedTy = lf.resolvedTy.Substitute(σ...)
				}
			}
		case *astTermLit:
			n.term = n.term.TypeSubstitute(σ...)
		}
	})
}

// reduceHead is t with the redexes on its application spine reduced,
// at most depth of them from the head: `(λx. λy. body)(m, w)` is
// body[m/x][w/y], each step the kernel's capture-avoiding substitution
// (SubstituteReducing: a λ substituted where the body applies its binder
// is applied in turn). An argument beyond the λs stays applied to what
// the body became.
func reduceHead(t core.Term, depth int) core.Term {
	app, ok := t.AsAppliedTerm()
	if !ok || depth == 0 {
		return t
	}
	fun := reduceHead(app.Fun(), depth-1)
	if abs, isAbs := fun.AsAbsTerm(); isAbs {
		return SubstituteReducing(abs.Body(), abs.Var(), app.Arg())
	}
	if fun == app.Fun() {
		return t
	}
	return core.Apply(fun, app.Arg())
}

// SubstituteReducing is body[arg/x] with every redex the substitution
// makes reduced: where body applies x, `x(a)`, and arg is a λ, the
// result is arg's body at a, reduced the same way — so an abbreviation
// applied to a λ reads as the term the author abbreviated, written out
// at it, with no `(λi. …)(i)` left where the entry applied its binder.
// A redex body or arg spells as written is kept.
func SubstituteReducing(body core.Term, x core.VarTerm, arg core.Term) core.Term {
	return substituteAllReducing(body, []core.VarTerm{x}, []core.Term{arg})
}

// substituteAllReducing is SubstituteReducing for the simultaneous
// substitution of args for xs.
func substituteAllReducing(body core.Term, xs []core.VarTerm, args []core.Term) core.Term {
	substs := make([]core.TermSubst, len(xs))
	var lams []int
	for i, x := range xs {
		substs[i] = core.MakeTermSubst(x, args[i])
		if _, isAbs := args[i].AsAbsTerm(); isAbs {
			lams = append(lams, i)
		}
	}
	out := body.Substitute(substs...)
	if len(lams) == 0 {
		return out
	}
	made := make(map[core.VarTerm]core.Term, len(lams))
	for _, i := range lams {
		made[xs[i]] = args[i]
	}
	return reduceMade(body, out, made)
}

// reduceMade walks before (a body) and after (it with the λs of made
// for their variables) in step, and reduces at each application of
// such a variable in before the redex its image in after is. The two
// have one shape outside the variables' occurrences, the substitution
// renaming at most a binder.
func reduceMade(before, after core.Term, made map[core.VarTerm]core.Term) core.Term {
	lambdaOf := func(t core.Term) (core.Term, bool) {
		v, isVar := t.AsVar()
		if !isVar {
			return nil, false
		}
		for x, arg := range made {
			if v.EqualsVar(x) {
				return arg, true
			}
		}
		return nil, false
	}
	switch b := before.Core().(type) {
	case core.AppliedTerm:
		head, bargs := ext.MatchesApply(before)
		if lam, isMade := lambdaOf(head); isMade {
			_, aargs := ext.MatchesApply(after)
			if len(aargs) != len(bargs) {
				return after
			}
			out := lam
			for i := range bargs {
				a := reduceMade(bargs[i], aargs[i], made)
				if abs, isAbs := out.AsAbsTerm(); isAbs {
					out = SubstituteReducing(abs.Body(), abs.Var(), a)
				} else {
					out = core.Apply(out, a)
				}
			}
			return out
		}
		app, ok := after.AsAppliedTerm()
		if !ok {
			return after
		}
		fun, a := reduceMade(b.Fun(), app.Fun(), made), reduceMade(b.Arg(), app.Arg(), made)
		if fun == app.Fun() && a == app.Arg() {
			return after
		}
		return core.Apply(fun, a)
	case core.AbsTerm:
		abs, ok := after.AsAbsTerm()
		if !ok {
			return after
		}
		inner := made
		if _, shadows := lambdaOf(b.Var()); shadows {
			inner = make(map[core.VarTerm]core.Term, len(made))
			for x, arg := range made {
				if !b.Var().EqualsVar(x) {
					inner[x] = arg
				}
			}
		}
		body := reduceMade(b.Body(), abs.Body(), inner)
		if body == abs.Body() {
			return after
		}
		return core.Abs(abs.Var(), body)
	}
	return after
}

func buildQuant(n *astQuantNode, env *typeEnv) (core.Term, error) {
	// Resolve binder type. Source priority (mirrors absBinderType +
	// buildAbs):
	//   1. explicit `∀x:T.` from the parser (n.varType non-nil);
	//   2. stash from the collect pass (n.resolvedVarType — set by
	//      walkQuantScopeCollect when the body's usage pinned the type);
	//   3. defer to body inference here via the untypedAbsVars channel.
	// (3) only fires for `∀x. T` style inputs where x is unused in T —
	// the body walk then doesn't pin anything, and the final fallback
	// is a fresh `var:_x`.
	varType := quantBinderType(n)
	// A bare type variable the collect pass stashed for a binder the
	// author did not type is a fallback, not a binding — as for a λ
	// binder (buildAbs): the body may still make it concrete.
	var fallback core.HolType
	if _, bare := varType.(core.VarType); bare && n.varType == nil {
		fallback, varType = varType, nil
	}

	prevBound, hadBound := env.bound[n.varName]
	prevDeclared, hadDeclared := env.declared[n.varName]
	prevInferred, hadInferred := env.inferred[n.varName]
	prevUntyped, hadUntyped := env.untypedAbsVars[n.varName]
	prevFallback, hadFallback := env.binderFallback[n.varName]

	if varType != nil {
		env.bound[n.varName] = varType
	} else {
		// A deferred binder shadows a declared variable of its name as a
		// typed one does: the body's uses are the binder's.
		delete(env.bound, n.varName)
		delete(env.declared, n.varName)
		delete(env.inferred, n.varName)
		env.untypedAbsVars[n.varName] = true
	}
	if fallback != nil {
		env.binderFallback[n.varName] = fallback
	} else {
		delete(env.binderFallback, n.varName)
	}

	body, err := buildTerm(n.body, env, true)

	// On a successful body walk with a deferred binder, read the
	// inferred type; then the fallback; then a fresh type variable as a
	// last resort so that `∀x. T` (with x unused in T — degenerate but
	// well-formed) still produces a valid term.
	if err == nil && varType == nil {
		if t, ok := env.inferred[n.varName]; ok {
			varType = t
		} else if t, ok := env.guesses[n.varName]; ok {
			varType = t
		} else if fallback != nil {
			varType = fallback
		} else {
			varType = core.MakeVarType(core.TermName("_" + n.varName))
		}
	}

	// Restore outer-scope state for this name (bound / inferred /
	// untypedAbsVars). Symmetric on success and error paths.
	if hadBound {
		env.bound[n.varName] = prevBound
	} else {
		delete(env.bound, n.varName)
	}
	if hadDeclared {
		env.declared[n.varName] = prevDeclared
	}
	if hadInferred {
		env.inferred[n.varName] = prevInferred
	} else {
		delete(env.inferred, n.varName)
	}
	if hadUntyped {
		env.untypedAbsVars[n.varName] = prevUntyped
	} else {
		delete(env.untypedAbsVars, n.varName)
	}
	if hadFallback {
		env.binderFallback[n.varName] = prevFallback
	} else {
		delete(env.binderFallback, n.varName)
	}

	if err != nil {
		return nil, err
	}
	if !core.IsBool(body) {
		return nil, fmt.Errorf("quantifier body must be boolean, got %s", ext.FormatType(body.Type()))
	}

	boundVar := core.Var(core.TermName(n.varName), varType)

	// Build: ∀ (λx:A. body) or ∃ (λx:A. body)

	switch n.quantifier {
	case utils.ForAllStr:
		return ext.ForAll(boundVar)(body), nil
	case utils.ExistsStr:
		return ext.Exists(boundVar)(body), nil
	case utils.UniqueStr:
		return ext.Unique(boundVar)(body), nil
	case utils.HilbertStr:
		return core.Hilbert(boundVar, body), nil
	default:
		return nil, fmt.Errorf("unknown quantifier %q", n.quantifier)
	}
}

// buildAbs lowers a bare lambda `λx:T. body` to core.Abs(x, body).
// `expected`, when a function type, supplies the body's expected type:
// one arrow is peeled off (its codomain is the body's expectation), so a
// known result type reaches the body. Without this, the body builds with
// no constraint and an undeclared head there bool-defaults — the
// `λg b c. predecessor(g(c))` failure. When `expected` is nil or not a function
// type, the body is built unconstrained, as before, and any genuine type
// mismatch surfaces at the caller's final type check. The bound var is
// pushed into env.bound for the body walk; the binding is restored /
// removed on exit so a shadowed outer binding survives the lambda.
func buildAbs(n *astAbsNode, env *typeEnv, expected core.HolType) (core.Term, error) {
	var bodyExpected core.HolType
	if expected != nil {
		if _, cod, ok := splitFunType(expected); ok {
			bodyExpected = cod
		}
	}

	// Resolve the binder type. Source priority:
	//   1. explicit `λx:T.` from the parser (n.varType non-nil);
	//   2. stash from a prior collect pass (n.resolvedVarType);
	//   3. domain peeled off enclosing `expected` (`λx. body` with
	//      caller-supplied result type).
	// If none of those pin a type, we DEFER to the body walk: leave
	// the binder name absent from env.bound and mark it in
	// untypedAbsVars, so:
	//   * buildApp's undeclared-head branch infers the binder's type
	//     when the body uses it as a function head (e.g., `r 0`
	//     → `r : num→num` when `r 0` sits in a num-domain position);
	//   * buildVarTerm's untyped-abs fallback assigns a fresh type
	//     variable for plain-var uses (e.g., `λi. i`).
	// After the walk we read env.inferred[varName] for the binder
	// type; the body's free uses of varName already carry that type,
	// so core.Abs binds them by name+type as usual.
	varType := absBinderType(n)
	// A bare type variable the binder was not WRITTEN at — the collect
	// pass's stash, or the domain peeled off `expected`, both carrying
	// the fresh variable of the polymorphic constant this λ is an
	// argument of (`set_comprehension(λv. …)` at `A → bool`) — is no
	// type to bind the binder at: the body's uses, or a later argument
	// of an application inside the body (`comprehension_spec(v, φ, t)`
	// types v from t, buildArgsAgainstFunType), may still make it
	// concrete. It is kept as the fallback the binder takes when nothing
	// does, so a binder nothing pins builds exactly as before.
	var fallback core.HolType
	if _, bare := varType.(core.VarType); bare && n.varType == nil {
		fallback, varType = varType, nil
	}
	if varType == nil && expected != nil {
		if dom, _, ok := splitFunType(expected); ok {
			if _, bare := dom.(core.VarType); bare {
				if fallback == nil {
					fallback = dom
				}
			} else {
				varType = dom
			}
		}
	}

	prevBound, hadBound := env.bound[n.varName]
	prevDeclared, hadDeclared := env.declared[n.varName]
	prevInferred, hadInferred := env.inferred[n.varName]
	prevUntyped, hadUntyped := env.untypedAbsVars[n.varName]
	prevFallback, hadFallback := env.binderFallback[n.varName]

	if varType != nil {
		env.bound[n.varName] = varType
	} else {
		// A deferred binder shadows a declared variable of its name as a
		// typed one does: the body's uses are the binder's.
		delete(env.bound, n.varName)
		delete(env.declared, n.varName)
		delete(env.inferred, n.varName)
		env.untypedAbsVars[n.varName] = true
	}
	if fallback != nil {
		env.binderFallback[n.varName] = fallback
	} else {
		delete(env.binderFallback, n.varName)
	}

	body, err := buildExpected(n.body, env, bodyExpected)

	// On a successful body walk with a deferred binder, read the
	// inferred type; then the fallback; then a fresh type variable as
	// a last resort so that `λx. body` (with no usage of x) still
	// produces a well-formed term.
	if err == nil && varType == nil {
		if t, ok := env.inferred[n.varName]; ok {
			varType = t
		} else if t, ok := env.guesses[n.varName]; ok {
			varType = t
		} else if fallback != nil {
			varType = fallback
		} else {
			varType = core.MakeVarType(core.TermName("_" + n.varName))
		}
	}

	// Restore outer-scope state for this name (bound / inferred /
	// untypedAbsVars). The save/restore is symmetric on success and
	// error paths.
	if hadBound {
		env.bound[n.varName] = prevBound
	} else {
		delete(env.bound, n.varName)
	}
	if hadDeclared {
		env.declared[n.varName] = prevDeclared
	}
	if hadInferred {
		env.inferred[n.varName] = prevInferred
	} else {
		delete(env.inferred, n.varName)
	}
	if hadUntyped {
		env.untypedAbsVars[n.varName] = prevUntyped
	} else {
		delete(env.untypedAbsVars, n.varName)
	}
	if hadFallback {
		env.binderFallback[n.varName] = prevFallback
	} else {
		delete(env.binderFallback, n.varName)
	}

	if err != nil {
		return nil, err
	}
	return core.Abs(core.Var(core.TermName(n.varName), varType), body), nil
}

// buildPatternAbs lowers a pair-pattern lambda `λ(u:T₁, x:T₂). body` to
// the canonical pattern_abstraction encoding
//
//	pattern_abstraction(λf:(prod(T₁,T₂)→R). ∀u:T₁. ∀x:T₂. f((u, x)) = body)
//
// with a FRESH internal binder f chosen to avoid every name occurring in
// the built body or pattern — so the same-name shadow capture that makes
// the explicit encoding unprintable can never re-enter via this surface.
//
// Construction is deliberately term-level rather than a desugar to
// existing AST shapes: the internal binder's type (prod → R) is only
// known once the body is built, and routing the un-annotated lambda
// through buildApp's abstract meta path would pin the binder to pattern_abstraction's
// abstract `var:A` domain. Building the body first (with the pattern
// leaves pushed as bound vars, untyped leaves deferred exactly like
// buildAbs) yields R and the leaf types, after which the pattern_abstraction instance
// is fully determined and resolved per-occurrence via buildAppViaMeta —
// no `⟨…⟩` annotation needed even when the surrounding prop uses pattern_abstraction
// at multiple instances.
func buildPatternAbs(n *astPatternAbs, env *typeEnv, expected core.HolType) (core.Term, error) {
	leaves := n.pat.leaves(nil)
	seen := map[string]bool{}
	for _, lf := range leaves {
		if seen[lf.name] {
			return nil, fmt.Errorf(
				"duplicate binder %q in λ-pattern (pattern components must be distinct)", lf.name)
		}
		seen[lf.name] = true
	}

	// The caller's expected type (prod(..) → R) types the body by its
	// codomain and seeds untyped leaves from the matching domain
	// components.
	var bodyExpected core.HolType
	if expected != nil {
		if dom, cod, ok := splitFunType(expected); ok {
			bodyExpected = cod
			seedPatTypesFromDomain(n.pat, dom)
		}
	}

	// Push the leaf binders for the body walk; untyped leaves use the
	// deferred protocol shared with buildAbs (cleared from bound/inferred,
	// marked in untypedAbsVars, read back from env.inferred after).
	type savedState struct {
		bound, inferred       core.HolType
		hadBound, hadInferred bool
		untyped, hadUntyped   bool
	}
	saved := make([]savedState, len(leaves))
	for i, lf := range leaves {
		s := &saved[i]
		s.bound, s.hadBound = env.bound[lf.name]
		s.inferred, s.hadInferred = env.inferred[lf.name]
		s.untyped, s.hadUntyped = env.untypedAbsVars[lf.name]
		if ty := patLeafType(lf); ty != nil {
			env.bound[lf.name] = ty
		} else {
			delete(env.bound, lf.name)
			delete(env.inferred, lf.name)
			env.untypedAbsVars[lf.name] = true
		}
	}

	body, err := buildExpected(n.body, env, bodyExpected)

	var leafTypes []core.HolType
	if err == nil {
		leafTypes = make([]core.HolType, len(leaves))
		for i, lf := range leaves {
			ty := patLeafType(lf)
			if ty == nil {
				if t, ok := env.inferred[lf.name]; ok {
					ty = t
				} else if t, ok := env.guesses[lf.name]; ok {
					ty = t
				} else {
					ty = core.MakeVarType(core.TermName("_" + lf.name))
				}
			}
			leafTypes[i] = ty
		}
	}

	for i, lf := range leaves {
		s := &saved[i]
		if s.hadBound {
			env.bound[lf.name] = s.bound
		} else {
			delete(env.bound, lf.name)
		}
		if s.hadInferred {
			env.inferred[lf.name] = s.inferred
		} else {
			delete(env.inferred, lf.name)
		}
		if s.hadUntyped {
			env.untypedAbsVars[lf.name] = s.untyped
		} else {
			delete(env.untypedAbsVars, lf.name)
		}
	}
	if err != nil {
		return nil, err
	}

	// Scope-first metas (see buildBinOp's setOperator discipline): the
	// caller scope's `,` meta when present, the DSL surface meta as
	// fallback. pattern_abstraction has no DSL surface meta — it must come from the
	// scope or its resolver.
	commaMeta := ext.CommaConstMeta
	if m, ok := env.scopeConstMetas[","]; ok {
		commaMeta = m
	}
	var patternAbstractionMeta core.ConstTermMeta
	if m, ok := env.scopeConstMetas["pattern_abstraction"]; ok {
		patternAbstractionMeta = m
	} else if c, ok := env.scopeConsts["pattern_abstraction"]; ok {
		patternAbstractionMeta = c.Meta()
	} else {
		return nil, fmt.Errorf(
			"λ-pattern at position %d requires the pattern_abstraction constant in scope "+
				"(pair-pattern lambdas lower to the pattern_abstraction encoding)", n.pos)
	}

	// Pattern term over the resolved leaf vars.
	idx := 0
	var leafVars []core.Term
	var buildPat func(p *astPat) (core.Term, error)
	buildPat = func(p *astPat) (core.Term, error) {
		if p.isLeaf() {
			v := core.Var(core.TermName(p.name), leafTypes[idx])
			idx++
			leafVars = append(leafVars, v)
			return v, nil
		}
		l, err := buildPat(p.left)
		if err != nil {
			return nil, err
		}
		r, err := buildPat(p.right)
		if err != nil {
			return nil, err
		}
		return buildAppViaMeta(env, commaMeta, []core.Term{l, r})
	}
	patTerm, err := buildPat(n.pat)
	if err != nil {
		return nil, err
	}

	fname := core.TermName("f")
	for body.HasName(fname) || patTerm.HasName(fname) {
		fname = utils.NextName(fname)
	}
	fVar := core.Var(fname, core.MakeFun(patTerm.Type(), body.Type()))
	quantified := ext.ForAll(leafVars...)(core.Eq(core.Apply(fVar, patTerm), body))
	return buildAppViaMeta(env, patternAbstractionMeta, []core.Term{core.Abs(fVar, quantified)})
}

// patLeafType resolves a pattern leaf's binder type: explicit parser
// type first, then the collect-pass / expected-domain stash. Nil when
// still unknown (deferred to the body walk).
func patLeafType(lf *astPat) core.HolType {
	if lf.ty != nil {
		return resolveType(lf.ty)
	}
	return lf.resolvedTy
}

// seedPatTypesFromDomain distributes an expected pattern type (a prod
// tree) onto untyped pattern leaves whose shape lines up. Mismatched
// shapes just stop seeding — the deferred-binder protocol still covers
// the leaves.
func seedPatTypesFromDomain(p *astPat, dom core.HolType) {
	if p.isLeaf() {
		if p.ty == nil && p.resolvedTy == nil {
			p.resolvedTy = dom
		}
		return
	}
	ct, ok := dom.(core.CompositeType)
	if !ok || !ct.Meta().Equals(ext.MetaTypeProd) {
		return
	}
	seedPatTypesFromDomain(p.left, ct.SubType(0))
	seedPatTypesFromDomain(p.right, ct.SubType(1))
}

// buildFunType constructs a curried function type from argument types and result type.
// buildFunType([A, B], C) → A → B → C
func buildFunType(argTypes []core.HolType, result core.HolType) core.HolType {
	t := result
	for i := len(argTypes) - 1; i >= 0; i-- {
		t = core.MakeFun(argTypes[i], t)
	}
	return t
}

// applyTypesMatch reports whether a fun term of type `funType` can be
// curry-applied to args whose actual types are `args[i].Type()`. Used
// by buildApp's scope-fast-path to decide whether the scope's
// pre-instantiated ConstTerm is a good fit or whether we need to fall
// through to meta-based instantiation.
func applyTypesMatch(funType core.HolType, args []core.Term) bool {
	cur := funType
	for _, arg := range args {
		ft, ok := cur.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return false
		}
		if !ft.SubType(0).Equals(arg.Type()) {
			return false
		}
		cur = ft.SubType(1)
	}
	return true
}

// buildAppViaMeta instantiates a polymorphic const meta from
// application argument types, then curry-applies. Implements the
// type-unification path needed when scopeConsts's fixed instance
// doesn't match (or no fixed instance exists, e.g. for the special
// const COND that emit doesn't record).
//
// Algorithm: walk meta.AbsType's curry chain, peeling one fun arrow
// per supplied argument. At each step, unify the (substitution-
// applied) domain type with the argument's actual type via the
// existing core.HolType.Matches pattern matcher. Accumulate the
// substitutions and apply them to the full absType to produce the
// instantiated type. Build a ConstTerm at that type and curry-apply
// the args.
//
// Returns an error when the curry chain runs out before all args are
// consumed or when a domain doesn't unify with its arg's type. The
// caller (buildApp) treats this as "not a match" and falls through
// to variable-treatment.
// buildAppViaMetaSeeded is buildAppViaMeta with a pre-seeded substitution
// list from a `⟨V:T,...⟩` annotation. The annotation-substs are applied
// first (they win over any argument-driven unification for the same
// type-var, matching the semantic that an explicit annotation is
// authoritative). Argument-driven substs on OTHER type-vars still
// accumulate normally, so `set_member⟨A:B⟩(y, t)` still lets the second arg
// pin any remaining free type-var in set_member's shape.
// freshMetaPrefix marks occurrence-local letters minted by freshAbs.
// The namespace is the machine-reserved `?`, with an `f` no imported
// machine letter carries, so a fresh name collides with nothing an
// author or the trace ever writes.
const freshMetaPrefix = "?f"

// An UnpinnedLetter is a type letter of a polymorphic constant that a
// parse under FreshenMetaLetters left at its occurrence-local stand-in:
// no argument, no neighbour and no `⟨⟩` tie fixed the instance, so the
// text does not say at which type the constant is meant.
type UnpinnedLetter struct {
	Const  string // the constant whose instance carries the letter
	Letter string // the constant's own name for it (A, B, …)
}

// Repair is the edit that pins the letter, in the words every door that
// refuses an unpinned letter uses.
func (u UnpinnedLetter) Repair() string {
	return fmt.Sprintf("%s's %s — write %s⟨%s:%s⟩, or the type it is meant at",
		u.Const, u.Letter, u.Const, u.Letter, u.Letter)
}

// UnpinnedLetters lists the letters p's constants carry unpinned, in
// order of first occurrence (conclusion before hypotheses), one row per
// constant and letter. A statement with a row is polymorphic in a
// letter its author never wrote: its type variable is the parser's
// stand-in, which no binder of the statement and no letter of the
// family names.
func UnpinnedLetters(p core.Prop) []UnpinnedLetter {
	return UnpinnedLettersIn(append([]core.Term{p.Conclusion()}, p.Hyps()...)...)
}

// UnpinnedLettersIn is UnpinnedLetters over terms — a tactic's term
// parameter, a term_specialize witness — in order of first occurrence.
func UnpinnedLettersIn(terms ...core.Term) []UnpinnedLetter {
	var out []UnpinnedLetter
	seen := map[UnpinnedLetter]bool{}
	var walk func(t core.Term)
	walk = func(t core.Term) {
		switch x := t.Core().(type) {
		case core.ConstTerm:
			for _, v := range x.Type().TypeVars() {
				name := string(v.Name())
				if !strings.HasPrefix(name, freshMetaPrefix) {
					continue
				}
				row := UnpinnedLetter{
					Const:  string(x.Name()),
					Letter: strings.TrimLeft(strings.TrimPrefix(name, freshMetaPrefix), "0123456789"),
				}
				if !seen[row] {
					seen[row] = true
					out = append(out, row)
				}
			}
		case core.AppliedTerm:
			walk(x.Fun())
			walk(x.Arg())
		case core.AbsTerm:
			walk(x.Body())
		}
	}
	for _, t := range terms {
		walk(t)
	}
	return out
}

// ReadBackMetaLetters reads every occurrence-local stand-in in t back
// to the letter it stands for (?f3A → A): the reading of a text that
// names no binder of its own — a quotient's relation, spelled by a
// constant — whose only letters are the constants' own. Two stand-ins
// for one letter, or a stand-in whose letter the term already carries,
// is an ambiguity the text must settle with a ⟨⟩ tie, reported by
// name.
func ReadBackMetaLetters(t core.Term) (core.Term, error) {
	standIns := map[string]string{} // stand-in → the letter it reads back to
	var order []string
	letters := map[string]bool{} // the letters the term carries outright
	collect := func(typ core.HolType) {
		for _, v := range typ.TypeVars() {
			name := string(v.Name())
			if !strings.HasPrefix(name, freshMetaPrefix) {
				letters[name] = true
				continue
			}
			if _, seen := standIns[name]; seen {
				continue
			}
			standIns[name] = strings.TrimLeft(strings.TrimPrefix(name, freshMetaPrefix), "0123456789")
			order = append(order, name)
		}
	}
	var walk func(core.Term)
	walk = func(x core.Term) {
		switch y := x.Core().(type) {
		case core.ConstTerm:
			collect(y.Type())
		case core.VarTerm:
			collect(y.Type())
		case core.AppliedTerm:
			walk(y.Fun())
			walk(y.Arg())
		case core.AbsTerm:
			collect(y.Var().Type())
			walk(y.Body())
		}
	}
	walk(t)
	if len(order) == 0 {
		return t, nil
	}
	readBack := map[string]string{} // letter → the stand-in that reads back to it
	substs := make([]core.TypeSubst, 0, len(order))
	for _, name := range order {
		letter := standIns[name]
		if letters[letter] {
			return nil, fmt.Errorf("type letter %s is both written and a constant's unpinned letter — tie the constant's with ⟨%s:…⟩", letter, letter)
		}
		if other, taken := readBack[letter]; taken {
			return nil, fmt.Errorf("two constants' unpinned letters both read back to %s (%s, %s) — tie one with ⟨%s:…⟩", letter, other, name, letter)
		}
		readBack[letter] = name
		substs = append(substs, core.MakeTypeSubst(core.MakeVarType(name), core.MakeVarType(letter)))
	}
	return t.TypeSubstitute(substs...), nil
}

// freshAbs returns the meta's abstract type for ONE occurrence. Under
// FreshenMetaLetters every letter is renamed `?f<k><letter>` (k = the
// occurrence counter), and the returned map lets `⟨⟩` ties keep
// addressing the canonical names. Without the flag it is AbsType
// verbatim — the legacy capture-prone behavior.
func (env *typeEnv) freshAbs(meta core.ConstTermMeta) (core.HolType, map[string]core.VarType) {
	abs := meta.AbsType()
	if !env.freshenMeta {
		return abs, nil
	}
	letters := collectTypeVarNames(abs)
	if len(letters) == 0 {
		return abs, nil
	}
	env.freshCounter++
	fresh := make(map[string]core.VarType, len(letters))
	substs := make([]core.TypeSubst, 0, len(letters))
	for name := range letters {
		fv := core.MakeVarType(fmt.Sprintf("%s%d%s", freshMetaPrefix, env.freshCounter, name))
		fresh[name] = fv
		substs = append(substs, core.MakeTypeSubst(core.MakeVarType(name), fv))
	}
	return abs.Substitute(substs...), fresh
}

// translateSeedThroughFresh rewrites tie/seed bindings addressed at the
// meta's CANONICAL letters onto this occurrence's fresh stand-ins.
func translateSeedThroughFresh(seed []core.TypeSubst, fresh map[string]core.VarType) []core.TypeSubst {
	if len(fresh) == 0 || len(seed) == 0 {
		return seed
	}
	out := make([]core.TypeSubst, 0, len(seed))
	for _, s := range seed {
		if fv, ok := fresh[string(s.VarType.Name())]; ok {
			out = append(out, core.MakeTypeSubst(fv, s.HolType))
		} else {
			out = append(out, s)
		}
	}
	return out
}

// resolveSubstTargets closes substitution chains (S := ?f1A, ?f1A := A
// ⇒ S := A). Chains only materialize under freshening — verbatim
// letters collapse them by name collision. The bindings are acyclic,
// unifyDomainArg admitting none that would close a cycle, so a chain
// ends within as many rounds as there are bindings; a cycle here is a
// unifier's fault and panics, spelled out, before the targets grow
// without bound.
func resolveSubstTargets(substs []core.TypeSubst) []core.TypeSubst {
	if cyclicBinding(substs) {
		var sb strings.Builder
		for _, s := range substs {
			fmt.Fprintf(&sb, " %s := %s", s.VarType.Name(), ext.FormatType(s.HolType))
		}
		panic("cyclic type substitution:" + sb.String())
	}
	out := make([]core.TypeSubst, len(substs))
	copy(out, substs)
	for iter := 0; iter <= len(out); iter++ {
		changed := false
		for i, s := range out {
			nt := s.HolType.Substitute(out...)
			if !nt.Equals(s.HolType) {
				out[i] = core.MakeTypeSubst(s.VarType, nt)
				changed = true
			}
		}
		if !changed {
			break
		}
	}
	return out
}

// cyclicBinding reports whether a letter's binding reaches the letter
// itself through the bindings — `?a := ?b → ?b, ?b := ?a` — the first
// binding of a letter being the one Substitute applies. Such a letter
// has no type, and resolving the chains through it would not end.
func cyclicBinding(substs []core.TypeSubst) bool {
	target := map[core.TypeName]core.HolType{}
	for _, s := range substs {
		if _, bound := target[s.VarType.Name()]; !bound {
			target[s.VarType.Name()] = s.HolType
		}
	}
	const onPath, closed = 1, 2
	state := map[core.TypeName]int{}
	var reaches func(letter core.TypeName) bool
	reaches = func(letter core.TypeName) bool {
		if state[letter] != 0 {
			return state[letter] == onPath
		}
		state[letter] = onPath
		if t, bound := target[letter]; bound {
			for _, v := range t.TypeVars() {
				if reaches(v.Name()) {
					return true
				}
			}
		}
		state[letter] = closed
		return false
	}
	for letter := range target {
		if reaches(letter) {
			return true
		}
	}
	return false
}

// substituteFreshInArgs applies the unifier's bindings for
// occurrence-local fresh letters INTO already-built argument terms.
// Cross-occurrence resolution (`∅ ⊆ s` — ∅'s fresh letter is bound to
// s's author letter by the head's unify) is exactly what verbatim
// letters get by name capture; substituting is safe precisely
// BECAUSE fresh letters are occurrence-local — an author letter is
// never rewritten. A variable free in the arguments is not
// occurrence-local: one whose type carries a bound stand-in was typed
// by its first use elsewhere, and is refused (retypedVarError) rather
// than rewritten here alone. No-op without the flag (no fresh letters
// exist).
func substituteFreshInArgs(args []core.Term, substs []core.TypeSubst) ([]core.Term, error) {
	var freshOnly []core.TypeSubst
	for _, s := range substs {
		if isStandIn(s.VarType) {
			freshOnly = append(freshOnly, s)
		}
	}
	if len(freshOnly) == 0 {
		return args, nil
	}
	if err := retypedFreeVar(freshOnly, args...); err != nil {
		return nil, err
	}
	out := make([]core.Term, len(args))
	for i, a := range args {
		out[i] = a.TypeSubstitute(freshOnly...)
	}
	return out, nil
}

// unifyDomainArg matches a (possibly substitution-resolved) domain
// against a built argument's type, under the bindings the occurrence
// holds so far. Under freshening the binding direction is disciplined:
// only occurrence-local fresh letters may bind — an author letter
// surfacing on the domain side (a bound target of an earlier argument)
// must not be re-pointed at a fresh one; when the fresh letter sits on
// the ARG side instead (`s ∖ ∅` — the bare second operand), the reverse
// match binds it. Where stand-ins on both sides must bind — the slot
// `U → ?B` of injective_on beside `fun_zero(z) : ?D → num`, whose letter
// only the slot fixes — the two are unified (unifyStandIns). The one-way
// matches are tried first, so a text either of them reads keeps its
// reading. A match is a reading only when its bindings, with those held,
// bind no letter to a type that reaches the letter itself: a stand-in
// that typed a variable at one slot and meets a function over itself at
// the next (`c(x, x)` with `c : A → (A → A) → A`) has no type, and the
// chains resolveSubstTargets closes through it would not end.
// unifyStandIns refuses such a binding as it makes it; a one-way match,
// which reads the other side's letters as rigid, is read back for it.
// Without the flag this is exactly the legacy FullPredicate match.
func unifyDomainArg(env *typeEnv, domain, argType core.HolType, held []core.TypeSubst) ([]core.TypeSubst, bool) {
	if !env.freshenMeta {
		return domain.Matches(argType, utils.FullPredicate)
	}
	acyclic := func(substs []core.TypeSubst) bool {
		return !cyclicBinding(slices.Concat(held, substs))
	}
	if substs, ok := domain.Matches(argType, isStandIn); ok && acyclic(substs) {
		return substs, true
	}
	if substs, ok := argType.Matches(domain, isStandIn); ok && acyclic(substs) {
		return substs, true
	}
	if substs, ok := unifyStandIns(domain, argType, isStandIn); ok && acyclic(substs) {
		return substs, true
	}
	return nil, false
}

// isStandIn reports whether v is an occurrence-local stand-in freshAbs
// minted for a constant's letter.
func isStandIn(v core.VarType) bool {
	return strings.HasPrefix(string(v.Name()), freshMetaPrefix)
}

// constLetter reports whether v may be a polymorphic constant's own
// letter, still open for an occurrence to fix: under freshening a
// stand-in alone, the author's letters being as fixed as num; without
// it every letter, the constant's and the author's being spelled alike.
func (env *typeEnv) constLetter(v core.VarType) bool {
	return !env.freshenMeta || isStandIn(v)
}

// unifyStandIns unifies a and b, binding the letters flexible admits
// on either side; every other letter is rigid. The substitution is
// resolved — no binding's target mentions a letter it binds — and
// lists the bindings in the order they were made.
func unifyStandIns(a, b core.HolType, flexible core.VarTypePredicate) ([]core.TypeSubst, bool) {
	var substs []core.TypeSubst
	bind := func(v core.VarType, t core.HolType) bool {
		if ext.TypeHasVar(t, v) {
			return false
		}
		s := core.MakeTypeSubst(v, t)
		for i := range substs {
			substs[i] = core.MakeTypeSubst(substs[i].VarType, substs[i].HolType.Substitute(s))
		}
		substs = append(substs, s)
		return true
	}
	pairs := [][2]core.HolType{{a, b}}
	for len(pairs) > 0 {
		x, y := pairs[0][0].Substitute(substs...), pairs[0][1].Substitute(substs...)
		pairs = pairs[1:]
		if x.Equals(y) {
			continue
		}
		if v, ok := x.(core.VarType); ok && flexible(v) {
			if !bind(v, y) {
				return nil, false
			}
			continue
		}
		if v, ok := y.(core.VarType); ok && flexible(v) {
			if !bind(v, x) {
				return nil, false
			}
			continue
		}
		xc, xok := x.(core.CompositeType)
		yc, yok := y.(core.CompositeType)
		if !xok || !yok || !xc.Meta().Equals(yc.Meta()) {
			return nil, false
		}
		for i := range xc.Meta().Arity() {
			pairs = append(pairs, [2]core.HolType{xc.SubType(i), yc.SubType(i)})
		}
	}
	return substs, true
}

// slotSubsts is the substitution a curried head's next slot is read
// under. Under freshening the bindings so far are resolved first: two
// sibling arguments at one letter chain it (?f1U := ?f2U, ?f2U :=
// ?f3U), and a slot read one link short binds the middle letter a
// second time, a binding the first one shadows — the pin a later
// argument makes never reaches the letter the siblings were left at.
func (env *typeEnv) slotSubsts(substs []core.TypeSubst) []core.TypeSubst {
	if !env.freshenMeta {
		return substs
	}
	return resolveSubstTargets(substs)
}

// applyArgs applies a head the builder holds as a term — a variable,
// a field read off a record — to its arguments. Where an argument's
// type and its slot differ by stand-ins, the two are unified and the
// bindings are written into the arguments, and into a built head
// (headBinds), whose stand-ins are its own; a variable's type is never
// rewritten. Any other difference is refused by name, before the
// kernel sees the application.
func applyArgs(env *typeEnv, head core.Term, args []core.Term, headBinds bool) (core.Term, error) {
	rigid := map[core.TypeName]bool{}
	if !headBinds {
		for _, v := range head.Type().TypeVars() {
			rigid[v.Name()] = true
		}
	}
	flexible := func(v core.VarType) bool { return isStandIn(v) && !rigid[v.Name()] }
	args = append([]core.Term(nil), args...)
	result := head
	for i := range args {
		ft, ok := result.Type().(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return nil, fmt.Errorf("argument count %d exceeds curry depth of type %s",
				len(args), ext.FormatType(head.Type()))
		}
		domain := ft.SubType(0)
		if env.freshenMeta && !domain.Equals(args[i].Type()) {
			if substs, ok := unifyStandIns(domain, args[i].Type(), flexible); ok {
				if err := retypedFreeVar(substs, append([]core.Term{result}, args[i:]...)...); err != nil {
					return nil, err
				}
				result = result.TypeSubstitute(substs...)
				for j := i; j < len(args); j++ {
					args[j] = args[j].TypeSubstitute(substs...)
				}
				domain = result.Type().(core.CompositeType).SubType(0)
			}
		}
		if !domain.Equals(args[i].Type()) {
			return nil, slotMismatch(args[i].Type(), domain)
		}
		result = core.Apply(result, args[i])
	}
	return result, nil
}

// readAtExpected reads a built term at the type its door expects where
// the two differ by the term's own stand-ins: a constant whose letter
// only its result mentions (`fun_zero(z)` at `num → num`) takes the
// letter from the expectation, as an argument takes it from its slot.
// The expectation is the caller's and stays as it is; a term it cannot
// be read at is returned unchanged, for the door to refuse.
func readAtExpected(t core.Term, expected core.HolType) core.Term {
	if t.Type().Equals(expected) {
		return t
	}
	rigid := map[core.TypeName]bool{}
	for _, v := range expected.TypeVars() {
		rigid[v.Name()] = true
	}
	flexible := func(v core.VarType) bool { return isStandIn(v) && !rigid[v.Name()] }
	substs, ok := unifyStandIns(expected, t.Type(), flexible)
	if !ok || retypedFreeVar(substs, t) != nil {
		return t
	}
	return t.TypeSubstitute(substs...)
}

// ReadTermAt reads a built term at a binder's type where the two differ
// by the term's own stand-ins — the fresh letters a bare polymorphic
// constant is read with (`∅`, `𝕌`, `identity_map`) which no argument,
// partner or expected type pinned — the binder's type being the
// expectation a term_specialize witness or a reading's witness is read
// at. The stand-ins unify with the binder's type, the binder's letters
// that instantiable admits (a lemma's own, which the witness may fix)
// binding on their side; every other letter is rigid. The term comes
// back retyped at its stand-ins' bindings only — the binder's bindings
// are the door's to make, by its own match on the retyped term. A term
// carrying no stand-in in its type is returned as it is: the door's
// match alone reads it. ok is false where no reading exists, or where
// a binder letter would take a type holding a stand-in — the binder
// then fixes nothing about that letter, and the text must.
func ReadTermAt(t core.Term, binder core.HolType, instantiable core.VarTypePredicate) (core.Term, bool) {
	standIns := false
	for _, v := range t.Type().TypeVars() {
		if isStandIn(v) {
			standIns = true
			break
		}
	}
	if !standIns || t.Type().Equals(binder) {
		return t, true
	}
	flexible := func(v core.VarType) bool { return isStandIn(v) || instantiable(v) }
	substs, ok := unifyStandIns(t.Type(), binder, flexible)
	if !ok {
		return t, false
	}
	var own []core.TypeSubst
	for _, s := range substs {
		if isStandIn(s.VarType) {
			own = append(own, s)
			continue
		}
		if ext.TypeAnyVar(s.HolType, isStandIn) {
			return t, false
		}
	}
	if retypedFreeVar(own, t) != nil {
		return t, false
	}
	return t.TypeSubstitute(own...), true
}

// retypedFreeVar refuses substs where it rewrites the type of a
// variable free in one of terms, nil when it rewrites none: a binder
// outside them that its first use typed at a constant's stand-in
// (`∀x. fun_zero(z, x) = z ∧ x ∈ s`). Its binder and its other
// occurrences keep the stand-in, so rewriting this occurrence would
// make it another variable, free in the statement.
func retypedFreeVar(substs []core.TypeSubst, terms ...core.Term) *retypedVarError {
	for _, t := range terms {
		for _, v := range t.Frees(nil) {
			if to := v.Type().Substitute(substs...); !to.Equals(v.Type()) {
				return &retypedVarError{v, to}
			}
		}
	}
	return nil
}

// A retypedVarError is a variable a later use reads at another type
// than the constant's stand-in its first use gave it: a type mismatch,
// repaired by typing the variable where it is bound.
type retypedVarError struct {
	v  core.VarTerm
	to core.HolType
}

func (e *retypedVarError) Error() string {
	return fmt.Sprintf("%s took the type %s from a constant at an earlier use, and is read at %s here — write its type at its binder",
		e.v.Name(), ext.FormatType(e.v.Type()), ext.FormatType(e.to))
}

// A slotMismatchError is an argument its slot cannot take, refused by
// the builder before the kernel sees the application: a type mismatch,
// reported with both types.
type slotMismatchError struct{ argType, domain core.HolType }

func slotMismatch(argType, domain core.HolType) error {
	return &slotMismatchError{argType, domain}
}

func (e *slotMismatchError) Error() string {
	return fmt.Sprintf("argument type %s does not match domain %s%s",
		ext.FormatType(e.argType), ext.FormatType(e.domain), pairForSetHint(e.argType, e.domain))
}

// pairForSetHint is what a type refusal adds where a pair of reals
// stands where a set is expected — `x ∈ (a, b)`, `s = (a, b)`: the
// round parentheses are the pair, and the open interval is written
// with the white tortoise shell brackets. Empty for any other pair of
// types; the two may come in either order.
func pairForSetHint(a, b core.HolType) string {
	if !(isRealPair(a) && isSetType(b) || isRealPair(b) && isSetType(a)) {
		return ""
	}
	return " — (a, b) is a pair: the open interval is written ⟬a, b⟭ (U+27EC, U+27ED)"
}

// isRealPair reports whether t is real # real.
func isRealPair(t core.HolType) bool {
	c, ok := t.(core.CompositeType)
	return ok && c.Meta().Equals(ext.MetaTypeProd) && c.SubType(0).Equals(RealType) && c.SubType(1).Equals(RealType)
}

// isSetType reports whether t is a set, τ → bool.
func isSetType(t core.HolType) bool {
	c, ok := t.(core.CompositeType)
	return ok && c.Meta().Equals(core.MetaTypeFun()) && c.SubType(1).Equals(core.TypeBool())
}

func buildAppViaMetaSeeded(env *typeEnv, meta core.ConstTermMeta, args []core.Term, seed []core.TypeSubst) (core.Term, error) {
	absType, freshMap := env.freshAbs(meta)
	seed = translateSeedThroughFresh(seed, freshMap)
	substs := append([]core.TypeSubst(nil), seed...)
	cur := absType
	for _, arg := range args {
		curResolved := cur.Substitute(env.slotSubsts(substs)...)
		ft, ok := curResolved.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return nil, fmt.Errorf(
				"const %q: arg count %d exceeds curry depth of type %s",
				meta.Name(), len(args), ext.FormatType(meta.AbsType()))
		}
		domain := ft.SubType(0)
		more, ok := unifyDomainArg(env, domain, arg.Type(), substs)
		if !ok {
			return nil, fmt.Errorf(
				"const %q: arg type %s does not match domain %s%s",
				meta.Name(), ext.FormatType(arg.Type()), ext.FormatType(domain), pairForSetHint(arg.Type(), domain))
		}
		// Only accept "more" substs for vars NOT already bound by the
		// seed — the annotation is authoritative for the vars it names.
		for _, m := range more {
			if !annotBinds(seed, m.VarType) {
				substs = append(substs, m)
			}
		}
		if cc, ok := cur.(core.CompositeType); ok && cc.Meta().Equals(core.MetaTypeFun()) {
			cur = cc.SubType(1)
		} else {
			cur = ft.SubType(1)
		}
	}
	if env.freshenMeta {
		substs = resolveSubstTargets(substs)
		var err error
		if args, err = substituteFreshInArgs(args, substs); err != nil {
			return nil, err
		}
	}
	instType := absType.Substitute(substs...)
	c := core.MakeConstTerm(meta, instType)
	var result core.Term = c
	for _, arg := range args {
		result = core.Apply(result, arg)
	}
	return result, nil
}

// annotBinds reports whether the annotation-seed already carries a
// binding for `v`. Used by buildAppViaMetaSeeded to keep the annotation
// authoritative when a later argument-driven unifier would otherwise
// bind the same type-var to something else.
func annotBinds(seed []core.TypeSubst, v core.VarType) bool {
	for _, s := range seed {
		if s.VarType.Equals(v) {
			return true
		}
	}
	return false
}

func buildAppViaMeta(env *typeEnv, meta core.ConstTermMeta, args []core.Term) (core.Term, error) {
	absType, _ := env.freshAbs(meta)
	var substs []core.TypeSubst
	cur := absType
	for _, arg := range args {
		// Resolve the running result type against accumulated substitutions
		// BEFORE the function-type check. This is what makes over-application
		// work: e.g. COND : bool→A→A→A applied to (c, t, e, x) unifies A to a
		// function type from arg t/e, so after the 3rd arg `cur` is the bare
		// type-var A — which only reveals itself as a function (num→num) once
		// the A↦num→num substitution is applied. Without this, the 4th arg
		// trips the "exceeds curry depth" error and buildApp falls through to
		// treating the head as a free var (a replay-only divergence the emit
		// gate's concrete-const path, applyTypesMatch, never sees because its
		// instance type is already fully ground).
		curResolved := cur.Substitute(env.slotSubsts(substs)...)
		ft, ok := curResolved.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return nil, fmt.Errorf(
				"const %q: arg count %d exceeds curry depth of type %s",
				meta.Name(), len(args), ext.FormatType(meta.AbsType()))
		}
		domain := ft.SubType(0)
		more, ok := unifyDomainArg(env, domain, arg.Type(), substs)
		if !ok {
			return nil, fmt.Errorf(
				"const %q: arg type %s does not match domain %s%s",
				meta.Name(), ext.FormatType(arg.Type()), ext.FormatType(domain), pairForSetHint(arg.Type(), domain))
		}
		substs = append(substs, more...)
		// Step cur. Prefer the raw next slot when cur is itself a
		// function type — substituting in the already-substituted
		// ft.SubType(1) double-applies substs to any type-vars whose
		// names collide with newly-bound ones (e.g. COND : bool→A→A→A
		// over user args that contain a type-var named "A" themselves;
		// the first substituted A↦(var:A→bool) would re-substitute the
		// inner var:A on the next iter, producing (var:A→bool)→bool
		// and shifting the curry chain). When cur is a VarType that
		// only revealed itself as a function via substitution (the
		// genuine over-application case), the raw form has nothing left
		// to walk — fall back to ft.SubType(1).
		if cc, ok := cur.(core.CompositeType); ok && cc.Meta().Equals(core.MetaTypeFun()) {
			cur = cc.SubType(1)
		} else {
			cur = ft.SubType(1)
		}
	}
	if env.freshenMeta {
		substs = resolveSubstTargets(substs)
		var err error
		if args, err = substituteFreshInArgs(args, substs); err != nil {
			return nil, err
		}
	}
	instType := absType.Substitute(substs...)
	c := core.MakeConstTerm(meta, instType)
	var result core.Term = c
	for _, arg := range args {
		result = core.Apply(result, arg)
	}
	return result, nil
}

// seedResolverConsts walks `node` and, for every name occurring free in
// it (applied head or bare var) that env doesn't already know, asks
// `resolver` for a ConstTermMeta and injects any hit into
// env.scopeConstMetas. Bound names (∀/∃/ε/λ) are skipped so a binder
// like `∀dest_nadd:T. …` is never shadowed by a registered const. Names
// already present in env.scopeConsts / env.scopeConstMetas / env.declared
// (which absorbs scope.Vars and in-source `name:type` decls earlier in
// buildProp) are also skipped — first-bound wins, just like everywhere
// else in the typeEnv.
//
// The seeded entries land in scopeConstMetas only; buildApp's existing
// meta-instantiation branch (`buildAppViaMeta`) then resolves them at
// build time, identically to a caller-supplied ConstMetas entry.
func seedResolverConsts(node astNode, env *typeEnv, resolver func(string) core.ConstTermMeta) {
	seen := make(map[string]bool)
	bound := make(map[string]int)
	walkResolverNames(node, bound, func(name string) {
		if seen[name] {
			return
		}
		seen[name] = true
		if _, ok := env.scopeConsts[name]; ok {
			return
		}
		if _, ok := env.scopeConstMetas[name]; ok {
			return
		}
		if _, ok := env.declared[name]; ok {
			return
		}
		// An overloaded word outranks the resolver: a resolver constant
		// of the same name is not what the text means (overload.go).
		if _, ok := env.overloadWord(name); ok {
			return
		}
		if meta := resolver(name); !meta.IsZero() {
			env.scopeConstMetas[name] = meta
		}
	})
}

// walkResolverNames visits every free-position *astVar name in `node`,
// tracking the quantifier / abstraction bound-stack so binder names
// don't leak out as "free". Used by seedResolverConsts; kept narrow on
// purpose (no inference state, no env mutation).
func walkResolverNames(node astNode, bound map[string]int, visit func(name string)) {
	switch n := node.(type) {
	case *astVar:
		if bound[n.name] == 0 {
			visit(n.name)
		}
	case *astField:
		walkResolverNames(n.receiver, bound, visit)
	case *astApp:
		if v, ok := n.fun.(*astVar); ok {
			if bound[v.name] == 0 {
				visit(v.name)
			}
		} else {
			walkResolverNames(n.fun, bound, visit)
		}
		for _, a := range n.args {
			walkResolverNames(a, bound, visit)
		}
	case *astBinOp:
		// A `∘` surface never mentions `o` as a source-text name, and a
		// set infix (`x ∈ s`, `x ∉ s`, `s ⊆ t`, `s ∪ t`, …) never mentions set_member /
		// subset / union, so the resolver would never be asked for them
		// and the def-less surface meta would win by default — the
		// mixed-meta hazard setops.go's seedSetScopeConstFallback
		// documents. Surface the lowered name here, the same way a
		// pattern lambda surfaces pattern_abstraction and `,` below. (The other set
		// surface forms — `∅`, `𝕌`, `{a, b}`, `{x | φ}`, `⋃`, `⋂` — are
		// lowered by the parser to astVar / astApp names and are visited
		// as such.)
		if n.op == "∘" {
			visit("o")
		}
		if n.op == "∉" {
			visit(string(InMeta.Name()))
		}
		if meta := setOperator(n.op); !meta.IsZero() {
			visit(string(meta.Name()))
		}
		walkResolverNames(n.left, bound, visit)
		walkResolverNames(n.right, bound, visit)
	case *astCong:
		walkResolverNames(n.left, bound, visit)
		walkResolverNames(n.right, bound, visit)
		walkResolverNames(n.modulus, bound, visit)
	case *astTendsAt:
		walkResolverNames(n.fn, bound, visit)
		walkResolverNames(n.limit, bound, visit)
		walkResolverNames(n.point, bound, visit)
	case *astNotNode:
		walkResolverNames(n.body, bound, visit)
	case *astTermLit:
		// A pre-built term names nothing the resolver could seed.
	case *astOutfix:
		for _, a := range n.args {
			walkResolverNames(a, bound, visit)
		}
		if n.sub != nil {
			walkResolverNames(n.sub, bound, visit)
		}
	case *astCoerce:
		walkResolverNames(n.operand, bound, visit)
	case *astNeg:
		walkResolverNames(n.operand, bound, visit)
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		walkResolverNames(n.body, bound, visit)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		walkResolverNames(n.body, bound, visit)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astBigOp:
		// The constant a big operator lowers to, and the constant a
		// declared operator lowers to, are named by no source-text name;
		// the build resolves them on demand (typeEnv.constMeta). The
		// half-open range `Σ_{i<m}` sums over is a different matter: it
		// lowers to the set-builder `{i | i < m}` (belowRangeAST), whose
		// two set names must reach the resolver like any written
		// set-builder's — otherwise the def-less surface metas fill them,
		// and a session seeds those into every later parse (goal-local
		// constants), where set_tac finds no definition to unfold.
		if n.rel == "<" {
			visit("set_comprehension")
			visit("comprehension_spec")
		}
		walkResolverNames(n.bound, bound, visit)
		bound[n.binder]++
		walkResolverNames(n.body, bound, visit)
		bound[n.binder]--
	case *astPatternAbs:
		// The lowering constructs pattern_abstraction and `,` applications that never
		// appear as astVar names in the tree — surface them to the
		// resolver so a registry-backed scope can seed their metas.
		visit("pattern_abstraction")
		visit(",")
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
		}
		walkResolverNames(n.body, bound, visit)
		for _, lf := range leaves {
			bound[lf.name]--
		}
	}
}

// buildPower builds `x ^ n` at a built-in domain: the base is built on
// its own, its domain picks the power constant (powDomainOperator), and
// the exponent is built at num. ok is false when the base is in no
// built-in domain — the caller then asks the constant declaring `^`.
// The scope's meta pointer wins over the surface meta exactly as for
// `+` (the registered nat_pow carries the definition def-sensitive
// consumers read).
func buildPower(n *astBinOp, env *typeEnv) (core.Term, bool, error) {
	base, err := buildTerm(n.left, env, false)
	if err != nil {
		return nil, false, nil
	}
	meta := powDomainOperator(base.Type())
	if meta.IsZero() {
		return nil, false, nil
	}
	exponent, err := buildExpected(n.right, env, NumType)
	if err != nil {
		return nil, true, err
	}
	if !exponent.Type().Equals(NumType) {
		return nil, true, fmt.Errorf("operator ^: the exponent must be a num, got %s", ext.FormatType(exponent.Type()))
	}
	if m, ok := env.scopeConstMetas[string(meta.Name())]; ok && m.AbsType().Equals(meta.AbsType()) {
		meta = m
	}
	return core.Apply(core.Apply(meta.Term(), base), exponent), true, nil
}

// buildPowerExpected is buildPower under a known result type: the base
// is built at that domain (so `2 ^ n` under a real expectation reads
// `&2 ^ n`), the exponent at num. ok is false when the expectation is
// no power domain or an operand does not build there.
func buildPowerExpected(n *astBinOp, env *typeEnv, expected core.HolType) (core.Term, bool, error) {
	if n.op != "^" {
		return nil, false, nil
	}
	meta := powDomainOperator(expected)
	if meta.IsZero() {
		return nil, false, nil
	}
	base, err := buildExpected(n.left, env, expected)
	if err != nil || !base.Type().Equals(expected) {
		return nil, false, nil
	}
	exponent, err := buildExpected(n.right, env, NumType)
	if err != nil || !exponent.Type().Equals(NumType) {
		return nil, false, nil
	}
	if m, ok := env.scopeConstMetas[string(meta.Name())]; ok && m.AbsType().Equals(meta.AbsType()) {
		meta = m
	}
	return core.Apply(core.Apply(meta.Term(), base), exponent), true, nil
}

// coercionConst is the constant a chapter declared as the embedding of
// the real line into the type (syntax.go's Coercion), "" when none is
// or the scope has no syntax table.
func (env *typeEnv) coercionConst(into core.HolType) string {
	if env.syntax == nil || into == nil {
		return ""
	}
	return env.syntax.CoercionConst(into)
}
