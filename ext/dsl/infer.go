// Type inference for the text DSL: the typeEnv, the type-collection
// passes, and the diagnostics that surface missing/ambiguous types.

package dsl

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// typeEnv tracks variable types during AST → Term conversion.
type typeEnv struct {
	// Explicitly declared types: "P" → "A→bool"
	declared map[string]core.HolType

	// Inferred types: accumulated from usage context.
	inferred map[string]core.HolType

	// Bound variable stack (quantifier scopes).
	bound map[string]core.HolType

	// Guesses for variables whose types could not be fully inferred but
	// can be suggested from usage context (e.g., equality partner type).
	guesses      map[string]core.HolType
	guessReasons map[string]string // varName → reason string

	// scopeConsts is the const-resolution map consulted by buildVarTerm
	// and buildApp. newTypeEnv pre-seeds it with the nat-encoding
	// constants (defaultNatScopeConsts) so every parse path knows
	// _0/bit0/bit1/suc without a caller-supplied scope. Caller
	// scope (ParseScope.Consts — emit's proof-declared consts like
	// subset / int_of_num, engine's goalConstScope-harvested goal consts)
	// merges on top with default-wins precedence. Entries are already-
	// instantiated ConstTerm values; the polymorphic-instantiation
	// fallback lives in scopeConstMetas.
	scopeConsts map[string]core.ConstTerm

	// scopeConstMetas carries the polymorphic-aware fallback. When a
	// scopeConsts entry doesn't match the application's argument types
	// (different instantiation in this section), or the const isn't in
	// scopeConsts at all (special consts like COND), buildApp tries
	// instantiating the meta from arg types via buildAppViaMeta.
	scopeConstMetas map[string]core.ConstTermMeta

	// untypedAbsVars tracks names introduced by untyped λ binders
	// (`λx. body`) that are currently in scope during the body walk
	// of buildAbs. When set, lookupType deliberately does NOT find
	// the name — the body's uses then either:
	//   * fire buildApp's undeclared-head branch (head used as
	//     function with concrete arg types → infer
	//     `argTypes → expected`); or
	//   * fire buildVarTerm's fallback below (plain-var use → assign
	//     a fresh type variable `_<name>` and pin via inferred).
	// In both paths env.inferred[name] is the binder's discovered
	// type by the time buildAbs reads it after the body walk. The
	// set is keyed by name and saved/restored in lockstep with the
	// usual bound/inferred save+restore.
	untypedAbsVars map[string]bool
	// binderFallback holds, for a deferred λ binder, the bare type
	// variable the enclosing polymorphic domain handed it (buildAbs):
	// not a type to bind the binder at — the body's uses, or a later
	// argument of the application the body is, may still make it
	// concrete — but the type it takes when nothing does, a bare use
	// included, as it did before the deferral.
	binderFallback map[string]core.HolType

	// strict mirrors ParseScope.StrictResolution for the prop-parse
	// pass — buildProp sets it; term parses leave it false.
	strict bool

	// strictMint mirrors ParseScope.StrictMint; annotTyVars collects
	// the type variables the author spelled inside `⟨V:T⟩` annotation
	// targets — the strict-mint check treats them as anchored.
	strictMint  bool
	annotTyVars map[core.TypeKey]bool

	// coerceDomain mirrors ParseScope.CoerceDomain; defaultedCoerces
	// records every `&` that took the global real default — neither
	// anchored by an expected type nor covered by a declared domain.
	// The strict check errors on any that SURVIVE into the final
	// statement (the reconcile may retarget and drop them).
	// strictCoerce arms that check: ParseScope.StrictResolution or
	// ParseScope.StrictCoercion, for the prop-parse pass.
	coerceDomain     core.HolType
	strictCoerce     bool
	defaultedCoerces []defaultedCoerce

	// numeralTyped are the terms whose type an `&` numeral decided alone,
	// read where nothing beside it asked for a type (the declared
	// domain's reading, or the real default): such a coercion, its
	// negation, and the sum, difference, product or power of such terms.
	// numeralRelations are the equations, disequations and comparisons
	// both of whose sides are among them, which the parse reports
	// (numeralWarnings).
	numeralTyped     map[core.Term]bool
	numeralRelations []numeralRelation

	// A polymorphic constant's pinned instance is tried without implicit
	// num-to-int embeddings, so its arguments can select another instance.
	suppressImplicitInt bool

	// freshenMeta mirrors ParseScope.FreshenMetaLetters; freshCounter
	// numbers meta occurrences deterministically within one parse.
	freshenMeta  bool
	freshCounter int

	// syntax, implicitBindings and resolver mirror ParseScope.Syntax,
	// ParseScope.ImplicitBindings and ParseScope.ConstResolver for the
	// build passes that lower a declared notation by TYPE — an operator
	// at operand types no built-in domain serves, a big operator at its
	// body's type (operator.go, bigop.go): the constant such a notation
	// names appears under no source-text name, so it is resolved on
	// demand there and its implicit prefix completed at build time.
	syntax           SyntaxTable
	implicitBindings map[string]core.Term
	residentNames    map[string]string
	resolver         func(string) core.ConstTermMeta
	// components are the variables some structure predicate of the text
	// or of a resident fact is applied to (componentVariables).
	components map[string]bool

	// structureOps are the operator symbols the text's structure facts
	// bind to component variables (structure.go): symbol → the bound
	// components, resolved at build by the operands' type.
	structureOps map[string][]structureOperator

	errors []InputDiagnostic
}

func newTypeEnv() *typeEnv {
	// Seed scopeConsts / scopeConstMetas with the default nat encoders
	// (defaultNatScopeConsts/-ConstMetas in arith.go) so every parse
	// path resolves names like bit0/bit1/_0/suc as constants
	// without a caller-supplied scope. Copy into a fresh map so caller-
	// supplied additions (merged later in buildProp / ParseTermTextInScope)
	// don't mutate the package-level default.
	scopeConsts := make(map[string]core.ConstTerm, len(defaultNatScopeConsts))
	for k, v := range defaultNatScopeConsts {
		scopeConsts[k] = v
	}
	scopeConstMetas := make(map[string]core.ConstTermMeta, len(defaultNatScopeConstMetas))
	for k, v := range defaultNatScopeConstMetas {
		scopeConstMetas[k] = v
	}
	// Set-theory consts are seeded via seedSetScopeConstFallback AFTER any
	// caller-supplied scope merges and after the resolver pre-seed, so
	// caller-provided registry metas (which typically carry different
	// abstract type-var names than the DSL-side setops.go metas) and
	// resolver hits win on name collision. Skipping the seed here keeps
	// buildProp / ParseTermTextInScope in charge of the timing.
	return &typeEnv{
		declared:        make(map[string]core.HolType),
		inferred:        make(map[string]core.HolType),
		bound:           make(map[string]core.HolType),
		guesses:         make(map[string]core.HolType),
		guessReasons:    make(map[string]string),
		scopeConsts:     scopeConsts,
		scopeConstMetas: scopeConstMetas,
		untypedAbsVars:  make(map[string]bool),
		binderFallback:  make(map[string]core.HolType),
		annotTyVars:     make(map[core.TypeKey]bool),
	}
}

// defaultedCoerce is one `&` occurrence that took the global real
// default; term is the exact built node (pointer identity — a
// reconcile retarget replaces it), pos its source position.
type defaultedCoerce struct {
	term core.Term
	pos  int
}

// numeralRelation is a relation between numerals alone: its left side,
// by which its survival into the statement is read, its operator and
// where the operator stands in the text.
type numeralRelation struct {
	left core.Term
	op   string
	pos  int
}

func (env *typeEnv) lookupType(name string) (core.HolType, bool) {
	if t, ok := env.bound[name]; ok {
		return t, true
	}
	if t, ok := env.declared[name]; ok {
		return t, true
	}
	if t, ok := env.inferred[name]; ok {
		return t, true
	}
	// Caller-supplied scope consts. Used by the
	// collector pass to propagate scope-const argument types to
	// otherwise-unconstrained args.
	if c, ok := env.scopeConsts[name]; ok {
		return c.Type(), true
	}
	return nil, false
}

// resolveType converts an AST type to a core.HolType.
//
// Type-variable input forms accepted in agent text DSL:
//   - single uppercase letter `A`, `B`, … — the canonical DSL
//     spelling; the parser normalizes `var:A` to this form at AST
//     construction (normalizeTypeVarName), so the statement formatter
//     outputs it too
//   - `var:<name>` — the `ext.FormatType` spelling; required for
//     multi-letter type-var names (`var:Repty`) and produced by the
//     lexer for Skolem type vars (`var:?94099`)
//
// Both produce `VarType`. Multi-letter bare names without the `var:`
// prefix resolve as arity-0 `CompositeType`.
func resolveType(t astType) core.HolType {
	switch t := t.(type) {
	case *astTypeNamed:
		name := t.name
		// The DSL's own alias: `set(τ)` IS `τ → bool` (typenames.go).
		// It lowers here, so nothing downstream — keys, matching, the
		// printers — ever sees a type named set.
		if t.name == typeAliasSet && len(t.args) == 1 {
			return core.MakeFun(resolveType(t.args[0]), core.TypeBool())
		}
		// n-ary composite type application: `name(t1, t2, ...)`.
		// Recursively resolve each arg and assemble the composite.
		if len(t.args) > 0 {
			subs := make([]core.HolType, len(t.args))
			for i, a := range t.args {
				subs[i] = resolveType(a)
			}
			return core.MakeCompositeType(
				core.MakeMetaType(core.TermName(name), len(subs)), subs...)
		}
		// Option D form: `var:<name>` → VarType.
		if rest, ok := strings.CutPrefix(name, "var:"); ok {
			return core.MakeVarType(core.TermName(rest))
		}
		// Single uppercase letter → type variable (DSL convenience).
		if len(name) == 1 && name[0] >= 'A' && name[0] <= 'Z' {
			return core.MakeVarType(core.TermName(name))
		}
		// Known type names.
		switch name {
		case "bool":
			return core.TypeBool()
		default:
			// Treat as nullary composite type.
			return core.MakeCompositeType(core.MakeMetaType(core.TermName(name), 0))
		}

	case *astTypeFun:
		return core.MakeFun(resolveType(t.domain), resolveType(t.codomain))

	case *astTypeVar:
		return core.MakeVarType(core.TermName(t.name))

	default:
		// Should not happen.
		return core.TypeBool()
	}
}

// collectAstTypes performs a first pass to infer variable types from usage.
// It propagates type information in two directions:
// - From declared function types to argument variables (P : A→bool, P(x) → x : A)
// - From argument types to undeclared function variables (x:A, F(x) → F : A→bool)
func collectAstTypes(node astNode, env *typeEnv) {
	switch n := node.(type) {
	case *astField:
		collectAstTypes(n.receiver, env)
	case *astApp:
		// An application whose head is itself an application is the
		// spine's head applied to every argument: a record field
		// `R.add(a, b)`, which the bundle pass writes `ring_add(R)(a, b)`,
		// types its arguments as `ring_add(R, a, b)` does.
		n = appSpine(n)
		// First collect types from arguments.
		for _, arg := range n.args {
			collectAstTypes(arg, env)
		}
		// A field read off a record expression, `P(n).add(x, y)`, types
		// its arguments from the field's type.
		if field, ok := n.fun.(*astField); ok {
			collectAstTypes(field, env)
			if funTy, known := inferStructFieldType(field, env); known {
				collectAppArgTypes(n, env, funTy, nil)
			}
		}
		// If the function has a known type, propagate argument types.
		if v, ok := n.fun.(*astVar); ok {
			if funTy, exists := env.lookupType(v.name); exists {
				// SCOPE-CONST polymorphic leak guard: when funVar comes
				// from a caller-supplied const scope (env.scopeConsts —
				// e.g. emit's `injective` declared via Script.Const at the
				// polymorphic `(A→B)→bool` shape), its free type-vars
				// are INTERNAL to the const's polymorphism, not user-
				// introduced names. Pinning a free arg var (e.g. `f`) to
				// those internal vars (`A→B`) here prevents a later
				// concrete use like `f(x1)` with `x1:ind` from typing
				// `f` as `ind→ind` — core.Apply's strict-equality
				// assert then rejects A≠ind. Leave the arg var untyped
				// in this case so a downstream concrete use can pin it;
				// the const meta is re-instantiated against that
				// concrete type at term-build time.
				//
				// User-declared / quantifier-bound polymorphic types
				// (e.g. `P:A→bool` in the input) are NOT scope consts
				// — there, the user's `A` IS the intended name and
				// leaking it to free arg vars is the correct behavior
				// (and the only way `(∀x:A. P(x)) ⇒ Q(x)`-style inputs
				// typecheck). So we only skip the leak when funVar's
				// type came from scopeConsts.
				var internal core.VarTypePredicate
				if _, fromConstMeta := env.scopeConsts[v.name]; fromConstMeta {
					internal = utils.FullPredicate[core.VarType]
				}
				collectAppArgTypes(n, env, funTy, internal)
			} else if _, isBound := env.bound[v.name]; !isBound {
				if meta, ok := env.scopeConstMetas[v.name]; ok {
					abs, fresh := env.freshAbs(meta)
					collectAppArgTypes(n, env, abs, occurrenceLetters(fresh))
				}
			}
		}
	case *astBinOp:
		collectAstTypes(n.left, env)
		collectAstTypes(n.right, env)
		// `=` / `≠` impose a shared-type constraint on their operands.
		// When one side is a typed bare var (e.g. quantifier-bound `z:ind`)
		// and the other is `F(args)` with `F` undeclared and `args` all
		// typed, the var's type pins F's result type — closing a real
		// inference gap exposed when emit's section text is the picked
		// original of a multi-use free var. Without this, F's first
		// concrete use defaults its result to bool (buildApp's expected=nil
		// branch), and a later concrete use at a non-bool type fails the
		// equality/inequality check with a misleading "bool vs <T>"
		// diagnostic. See `f` in `(f(x1)=f(x2)) ∧ (f(x)≠z)` where `z:ind`.
		if n.op == "=" || n.op == utils.NeqStr {
			propagateEqAppResultType(n.left, n.right, env)
			propagateEqAppResultType(n.right, n.left, env)
		}
	case *astCong:
		collectAstTypes(n.left, env)
		collectAstTypes(n.right, env)
		collectAstTypes(n.modulus, env)
	case *astTendsAt:
		collectAstTypes(n.fn, env)
		collectAstTypes(n.limit, env)
		collectAstTypes(n.point, env)
	case *astNotNode:
		collectAstTypes(n.body, env)
	case *astTermLit:
		// Pre-built: its type is its own.
	case *astCoerce:
		collectAstTypes(n.operand, env)
	case *astNeg:
		collectAstTypes(n.operand, env)
	case *astQuantNode:
		walkQuantScopeCollect(n, env, collectAstTypes)
	case *astAbsNode:
		walkAbsScopeCollect(n, env, collectAstTypes)
	case *astPatternAbs:
		walkPatternAbsScopeCollect(n, env, collectAstTypes)
	case *astBigOp:
		walkBigOpScopeCollect(n, env, collectAstTypes)
	case *astVar:
		// Leaf — nothing to collect yet.
	case *astConst:
		// Leaf.
	}
}

// appSpine is the application n reads as: n itself when its head is no
// application, else the innermost head applied to the arguments of
// every level in order — `f(x)(y, z)` is `f(x, y, z)`. The argument
// nodes are n's own.
func appSpine(n *astApp) *astApp {
	inner, ok := n.fun.(*astApp)
	if !ok {
		return n
	}
	return appSpine(inner).appliedTo(n.args, n.pos)
}

// collectAppArgTypes propagates constraints across a curried application of a
// known function type. Unlike a plain left-to-right domain leak, it first
// unifies domains with already-known argument types, then applies those
// substitutions back to unresolved bare-var arguments. This closes cases such
// as `comprehension_spec(v, p, f(x,y))`, where the third argument pins the first.
// A bare-var argument whose domain still mentions a letter internal to the
// head (nil: none is) is left to the build.
func collectAppArgTypes(n *astApp, env *typeEnv, funTy core.HolType, internal core.VarTypePredicate) {
	domains := make([]core.HolType, len(n.args))
	var substs []core.TypeSubst
	cur := funTy
	for i, arg := range n.args {
		curResolved := cur.Substitute(substs...)
		ft, ok := curResolved.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return
		}
		domain := ft.SubType(0)
		domains[i] = domain
		if argTy, ok := inferAstType(arg, env); ok {
			if more, ok := domain.Matches(argTy, utils.FullPredicate); ok {
				substs = append(substs, more...)
			}
		}
		if cc, ok := cur.(core.CompositeType); ok && cc.Meta().Equals(core.MetaTypeFun()) {
			cur = cc.SubType(1)
		} else {
			cur = ft.SubType(1)
		}
	}
	for i, arg := range n.args {
		av, ok := arg.(*astVar)
		if !ok {
			continue
		}
		if _, exists := env.lookupType(av.name); exists {
			continue
		}
		argTy := domains[i].Substitute(substs...)
		if internal != nil && ext.TypeAnyVar(argTy, internal) {
			continue
		}
		env.inferred[av.name] = argTy
	}
}

// occurrenceLetters is true of the letters freshAbs minted for one
// occurrence of a constant, nil when it minted none. The build mints
// its own for the same occurrence, so a type the collect passes read
// off a constant is theirs to record only where its arguments fixed
// every such letter — a letter they leave open is the build's to fix.
func occurrenceLetters(fresh map[string]core.VarType) core.VarTypePredicate {
	if len(fresh) == 0 {
		return nil
	}
	return func(v core.VarType) bool {
		for _, f := range fresh {
			if f.Equals(v) {
				return true
			}
		}
		return false
	}
}

func inferAstType(node astNode, env *typeEnv) (core.HolType, bool) {
	switch n := node.(type) {
	case *astVar:
		return env.lookupType(n.name)
	case *astConst:
		return core.TypeBool(), true
	case *astNumLit:
		return NumType, true
	case *astTermLit:
		return n.term.Type(), true
	case *astNotNode:
		return core.TypeBool(), true
	case *astBinOp:
		if n.op == "=" || n.op == utils.NeqStr ||
			n.op == utils.AndStr || n.op == utils.OrStr ||
			n.op == utils.ImplyStr || n.op == utils.IffStr {
			return core.TypeBool(), true
		}
		return nil, false
	case *astCong, *astTendsAt:
		return core.TypeBool(), true
	case *astQuantNode:
		if n.quantifier == utils.HilbertStr {
			if t := quantBinderType(n); t != nil {
				return t, true
			}
			if t, ok := env.inferred[n.varName]; ok {
				return t, true
			}
			return nil, false
		}
		return core.TypeBool(), true
	case *astAbsNode:
		varTy := absBinderType(n)
		if varTy == nil {
			if t, ok := env.inferred[n.varName]; ok {
				varTy = t
			} else {
				return nil, false
			}
		}
		bodyTy, ok := inferAstType(n.body, env)
		if !ok {
			return nil, false
		}
		return core.MakeFun(varTy, bodyTy), true
	case *astBigOp:
		// A big operator has its body's type; the body is read with the
		// index bound at the range's type.
		indexTy, ok := bigOpIndexType(n, env)
		if !ok {
			return nil, false
		}
		prev, had := env.bound[n.binder]
		env.bound[n.binder] = indexTy
		bodyTy, ok := inferAstType(n.body, env)
		if had {
			env.bound[n.binder] = prev
		} else {
			delete(env.bound, n.binder)
		}
		return bodyTy, ok
	case *astPatternAbs:
		// A pattern lambda's term type is prod(leafTypes…) → bodyType,
		// with the prod tree mirroring the pattern's nesting.
		domTy, ok := patTreeType(n.pat, env)
		if !ok {
			return nil, false
		}
		bodyTy, ok := inferAstType(n.body, env)
		if !ok {
			return nil, false
		}
		return core.MakeFun(domTy, bodyTy), true
	case *astField:
		return inferStructFieldType(n, env)
	case *astApp:
		fv, ok := n.fun.(*astVar)
		if !ok {
			funTy, known := inferAstType(n.fun, env)
			if !known {
				return nil, false
			}
			return inferAppResultType(n, env, funTy)
		}
		if t, ok := env.lookupType(fv.name); ok {
			return inferAppResultType(n, env, t)
		}
		if _, isBound := env.bound[fv.name]; !isBound {
			if meta, ok := env.scopeConstMetas[fv.name]; ok {
				// The constant's letters are this occurrence's own, as
				// buildAppViaMeta reads the application (freshAbs); a
				// result still spelling one is unknown here.
				abs, fresh := env.freshAbs(meta)
				t, ok := inferAppResultType(n, env, abs)
				if own := occurrenceLetters(fresh); ok && own != nil && ext.TypeAnyVar(t, own) {
					return nil, false
				}
				return t, ok
			}
		}
		return nil, false
	default:
		return nil, false
	}
}

func inferAppResultType(n *astApp, env *typeEnv, funTy core.HolType) (core.HolType, bool) {
	var substs []core.TypeSubst
	cur := funTy
	for _, arg := range n.args {
		curResolved := cur.Substitute(substs...)
		ft, ok := curResolved.(core.CompositeType)
		if !ok || !ft.Meta().Equals(core.MetaTypeFun()) {
			return nil, false
		}
		domain := ft.SubType(0)
		if argTy, ok := inferAstType(arg, env); ok {
			more, ok := domain.Matches(argTy, utils.FullPredicate)
			if !ok {
				return nil, false
			}
			substs = append(substs, more...)
		}
		if cc, ok := cur.(core.CompositeType); ok && cc.Meta().Equals(core.MetaTypeFun()) {
			cur = cc.SubType(1)
		} else {
			cur = ft.SubType(1)
		}
	}
	return cur.Substitute(substs...), true
}

// walkAbsScopeCollect walks an AbsNode's body with the binder pushed into
// env.bound, sharing the pattern used by all three collect passes. For
// typed binders (n.varType != nil) it resolves and pushes that type. For
// untyped binders it first reuses n.resolvedVarType if a previous pass
// pinned it; otherwise it walks the body with bound[varName] cleared so
// usage of the binder propagates into env.inferred[varName], then stashes
// the discovery on n.resolvedVarType for downstream readers. The save/
// restore protocol keeps outer-scope bindings of varName intact.
func walkAbsScopeCollect(n *astAbsNode, env *typeEnv, walk func(astNode, *typeEnv)) {
	if varTy := absBinderType(n); varTy != nil {
		prev, had := env.bound[n.varName]
		env.bound[n.varName] = varTy
		walk(n.body, env)
		if had {
			env.bound[n.varName] = prev
		} else {
			delete(env.bound, n.varName)
		}
		return
	}
	// Untyped + not yet resolved. Clear bound/declared/inferred for
	// varName so the walk can infer the binder type from how the body
	// uses it — the binder shadows a declared variable of its name as a
	// typed one does — restore after, stashing the discovery on
	// n.resolvedVarType.
	prevBound, hadBound := env.bound[n.varName]
	prevDeclared, hadDeclared := env.declared[n.varName]
	prevInferred, hadInferred := env.inferred[n.varName]
	delete(env.bound, n.varName)
	delete(env.declared, n.varName)
	delete(env.inferred, n.varName)
	walk(n.body, env)
	if t, ok := env.inferred[n.varName]; ok {
		n.resolvedVarType = t
	}
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
}

// walkPatternAbsScopeCollect is the astPatternAbs counterpart of
// walkAbsScopeCollect: every typed pattern leaf is pushed into env.bound
// for the body walk; untyped leaves use the clear-and-infer protocol,
// stashing any body-walk discovery on the leaf's resolvedTy. Save/
// restore keeps outer-scope bindings of the leaf names intact.
func walkPatternAbsScopeCollect(n *astPatternAbs, env *typeEnv, walk func(astNode, *typeEnv)) {
	leaves := n.pat.leaves(nil)
	type savedState struct {
		bound, inferred       core.HolType
		hadBound, hadInferred bool
	}
	saved := make([]savedState, len(leaves))
	for i, lf := range leaves {
		s := &saved[i]
		s.bound, s.hadBound = env.bound[lf.name]
		s.inferred, s.hadInferred = env.inferred[lf.name]
		if ty := patLeafType(lf); ty != nil {
			env.bound[lf.name] = ty
		} else {
			delete(env.bound, lf.name)
			delete(env.inferred, lf.name)
		}
	}
	walk(n.body, env)
	for i, lf := range leaves {
		if patLeafType(lf) == nil {
			if t, ok := env.inferred[lf.name]; ok {
				lf.resolvedTy = t
			}
		}
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
	}
}

// patTreeType assembles the prod type of a λ-pattern from its resolved
// leaf types (explicit / stashed / env.inferred), mirroring the leaf
// resolution inferAstType's astAbsNode case uses. False when any leaf
// is still untyped.
func patTreeType(p *astPat, env *typeEnv) (core.HolType, bool) {
	if p.isLeaf() {
		if ty := patLeafType(p); ty != nil {
			return ty, true
		}
		if t, ok := env.inferred[p.name]; ok {
			return t, true
		}
		return nil, false
	}
	l, ok := patTreeType(p.left, env)
	if !ok {
		return nil, false
	}
	r, ok := patTreeType(p.right, env)
	if !ok {
		return nil, false
	}
	return ext.MakeProdType(l, r), true
}

// absBinderType returns the resolved binder type for an AbsNode, or nil
// if no type is known yet. The order is: explicit (n.varType from
// parser), then the lazy stash (n.resolvedVarType from a previous pass).
func absBinderType(n *astAbsNode) core.HolType {
	if n.varType != nil {
		return resolveType(n.varType)
	}
	return n.resolvedVarType
}

// quantBinderType is the astQuantNode counterpart of absBinderType. Same
// resolution order: explicit parser type first, then the lazy stash.
func quantBinderType(n *astQuantNode) core.HolType {
	if n.varType != nil {
		return resolveType(n.varType)
	}
	return n.resolvedVarType
}

// walkQuantScopeCollect mirrors walkAbsScopeCollect for astQuantNode. A
// typed binder pushes its type into env.bound for the body walk; an
// untyped + unresolved binder clears bound/inferred for varName, walks,
// then stashes any discovered type on n.resolvedVarType — the same
// protocol every collect pass shares for lambdas. Without this, the
// untyped quantifier collect cases would call `resolveType(nil)`, which
// silently returns TypeBool (the resolveType default), poisoning binder
// resolution and rejecting any subsequent non-bool use of the binder.
func walkQuantScopeCollect(n *astQuantNode, env *typeEnv, walk func(astNode, *typeEnv)) {
	if varTy := quantBinderType(n); varTy != nil {
		prev, had := env.bound[n.varName]
		env.bound[n.varName] = varTy
		walk(n.body, env)
		if had {
			env.bound[n.varName] = prev
		} else {
			delete(env.bound, n.varName)
		}
		return
	}
	// The binder shadows a declared variable of its name as a typed
	// one does, so its own uses — not the outer variable's type — pin
	// it (buildQuant hides the declaration the same way).
	prevBound, hadBound := env.bound[n.varName]
	prevDeclared, hadDeclared := env.declared[n.varName]
	prevInferred, hadInferred := env.inferred[n.varName]
	delete(env.bound, n.varName)
	delete(env.declared, n.varName)
	delete(env.inferred, n.varName)
	walk(n.body, env)
	if t, ok := env.inferred[n.varName]; ok {
		n.resolvedVarType = t
	}
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
}

// decomposeFunType extracts the first n argument types from a curried function type.
// E.g., decomposeFunType(A → B → bool, 2) returns [A, B].
func decomposeFunType(ty core.HolType, n int) []core.HolType {
	var args []core.HolType
	cur := ty
	for i := 0; i < n; i++ {
		ct, ok := cur.(core.CompositeType)
		if !ok || !ct.Meta().Equals(core.MetaTypeFun()) {
			break
		}
		// Fun type has 2 subtypes: domain (0) and codomain (1).
		args = append(args, ct.SubType(0))
		cur = ct.SubType(1)
	}
	return args
}

// propagateEqAppResultType infers F's result type from the constraint
// imposed by `known = F(args)` or `known ≠ F(args)`: when `known` is a
// bare var with an already-resolvable type and `args` are all typed
// vars, F (undeclared) must have type `argTypes → known.Type()`.
//
// Narrow on purpose — handles the typical "free-var function used at
// the goal level" pattern. Skips when:
//   - `known` isn't a typed bare var (anything else would require
//     recursive type computation we don't do in this pass);
//   - `unknown` isn't a bare-var-headed application (lambdas, nested
//     apps, etc. are out of scope);
//   - F is already in env (declared / bound / inferred) — first inference
//     wins, matching the rest of collectAstTypes;
//   - any arg isn't a typed bare var (we can't synthesize a function
//     type without complete domains).
func propagateEqAppResultType(known, unknown astNode, env *typeEnv) {
	kv, ok := known.(*astVar)
	if !ok {
		return
	}
	kt, ok := env.lookupType(kv.name)
	if !ok {
		return
	}
	ua, ok := unknown.(*astApp)
	if !ok {
		return
	}
	uv, ok := ua.fun.(*astVar)
	if !ok {
		return
	}
	if _, exists := env.lookupType(uv.name); exists {
		return
	}
	// An overloaded word is not an undeclared function variable: the
	// constants declaring it type its arguments, each occurrence on its
	// own (`|a| = a` at int must not make the later `|y|` read y at int).
	if _, isWord := env.overloadWord(uv.name); isWord {
		return
	}
	argTypes := make([]core.HolType, len(ua.args))
	for i, arg := range ua.args {
		av, ok := arg.(*astVar)
		if !ok {
			return
		}
		t, ok := env.lookupType(av.name)
		if !ok {
			return
		}
		argTypes[i] = t
	}
	env.inferred[uv.name] = buildFunType(argTypes, kt)
}

// splitFunType decomposes a function type into (domain, codomain, true).
// For a non-function type it returns (nil, nil, false). Used to peel one
// arrow off an expected type when descending into a lambda body.
func splitFunType(ty core.HolType) (core.HolType, core.HolType, bool) {
	ct, ok := ty.(core.CompositeType)
	if !ok || !ct.Meta().Equals(core.MetaTypeFun()) {
		return nil, nil, false
	}
	return ct.SubType(0), ct.SubType(1), true
}

// collectTypeGuesses runs after collectTypes to guess types for variables that
// were not resolved by the primary inference pass. It handles:
//   - Equality: if one side of a = b has a known type, guess the other's type.
//   - Function args: re-check function applications with the updated env (catches
//     transitive cases where a function type was inferred in the first pass).
func collectTypeGuesses(node astNode, env *typeEnv) {
	switch n := node.(type) {
	case *astCong:
		collectTypeGuesses(n.left, env)
		collectTypeGuesses(n.right, env)
		collectTypeGuesses(n.modulus, env)
	case *astTendsAt:
		collectTypeGuesses(n.fn, env)
		collectTypeGuesses(n.limit, env)
		collectTypeGuesses(n.point, env)
	case *astBinOp:
		collectTypeGuesses(n.left, env)
		collectTypeGuesses(n.right, env)
		if n.op == "=" {
			// If one side is a known-typed var and the other is unknown, guess.
			lv, lok := n.left.(*astVar)
			rv, rok := n.right.(*astVar)
			if lok && rok {
				lt, lhas := env.lookupType(lv.name)
				rt, rhas := env.lookupType(rv.name)
				if lhas && !rhas {
					if _, already := env.guesses[rv.name]; !already {
						env.guesses[rv.name] = lt
						env.guessReasons[rv.name] = fmt.Sprintf("appears in %s = %s where %s : %s",
							lv.name, rv.name, lv.name, ext.FormatType(lt))
					}
				} else if rhas && !lhas {
					if _, already := env.guesses[lv.name]; !already {
						env.guesses[lv.name] = rt
						env.guessReasons[lv.name] = fmt.Sprintf("appears in %s = %s where %s : %s",
							lv.name, rv.name, rv.name, ext.FormatType(rt))
					}
				}
			}
		}
	case *astField:
		collectTypeGuesses(n.receiver, env)
	case *astApp:
		for _, arg := range n.args {
			collectTypeGuesses(arg, env)
		}
		// Re-check: function type may have been inferred in collectTypes.
		if v, ok := n.fun.(*astVar); ok {
			if funTy, exists := env.lookupType(v.name); exists {
				argTypes := decomposeFunType(funTy, len(n.args))
				for i, arg := range n.args {
					if i < len(argTypes) {
						if av, ok := arg.(*astVar); ok {
							if _, exists := env.lookupType(av.name); !exists {
								if _, already := env.guesses[av.name]; !already {
									env.guesses[av.name] = argTypes[i]
									env.guessReasons[av.name] = fmt.Sprintf("appears in %s(...) where %s : %s",
										v.name, v.name, ext.FormatType(funTy))
								}
							}
						}
					}
				}
			}
		}
	case *astNotNode:
		collectTypeGuesses(n.body, env)
	case *astTermLit:
	case *astCoerce:
		collectTypeGuesses(n.operand, env)
	case *astNeg:
		collectTypeGuesses(n.operand, env)
	case *astQuantNode:
		walkQuantScopeCollect(n, env, collectTypeGuesses)
	case *astAbsNode:
		walkAbsScopeCollect(n, env, collectTypeGuesses)
	case *astPatternAbs:
		walkPatternAbsScopeCollect(n, env, collectTypeGuesses)
	case *astBigOp:
		walkBigOpScopeCollect(n, env, collectTypeGuesses)
	case *astVar, *astConst:
		// Leaf — nothing to do.
	}
}

// collectScopeConstPolyLeak is the third typing pass: for every astApp
// whose head is a scope-const meta (env.scopeConsts) with a polymorphic
// type, propagate the (free) polymorphic argument types into UNDECLARED
// free arg vars that pass-1 + pass-2 didn't manage to type. See the
// rationale comment at the call site (buildProp's third-pass block).
func collectScopeConstPolyLeak(node astNode, env *typeEnv) {
	switch n := node.(type) {
	case *astField:
		collectScopeConstPolyLeak(n.receiver, env)
	case *astApp:
		for _, arg := range n.args {
			collectScopeConstPolyLeak(arg, env)
		}
		v, ok := n.fun.(*astVar)
		if !ok {
			return
		}
		if _, fromScopeConst := env.scopeConsts[v.name]; !fromScopeConst {
			return
		}
		funTy, exists := env.lookupType(v.name)
		if !exists {
			return
		}
		argTypes := decomposeFunType(funTy, len(n.args))
		for i, arg := range n.args {
			if i >= len(argTypes) {
				break
			}
			av, ok := arg.(*astVar)
			if !ok {
				continue
			}
			if _, exists := env.lookupType(av.name); exists {
				continue // pinned by pass-1 / pass-2 / `=`/`≠` — leave it
			}
			env.inferred[av.name] = argTypes[i]
		}
	case *astBinOp:
		collectScopeConstPolyLeak(n.left, env)
		collectScopeConstPolyLeak(n.right, env)
	case *astCong:
		collectScopeConstPolyLeak(n.left, env)
		collectScopeConstPolyLeak(n.right, env)
		collectScopeConstPolyLeak(n.modulus, env)
	case *astTendsAt:
		collectScopeConstPolyLeak(n.fn, env)
		collectScopeConstPolyLeak(n.limit, env)
		collectScopeConstPolyLeak(n.point, env)
	case *astNotNode:
		collectScopeConstPolyLeak(n.body, env)
	case *astTermLit:
	case *astCoerce:
		collectScopeConstPolyLeak(n.operand, env)
	case *astNeg:
		collectScopeConstPolyLeak(n.operand, env)
	case *astQuantNode:
		walkQuantScopeCollect(n, env, collectScopeConstPolyLeak)
	case *astAbsNode:
		walkAbsScopeCollect(n, env, collectScopeConstPolyLeak)
	case *astPatternAbs:
		walkPatternAbsScopeCollect(n, env, collectScopeConstPolyLeak)
	case *astBigOp:
		walkBigOpScopeCollect(n, env, collectScopeConstPolyLeak)
	}
}

// typeMissingError carries context about an unresolved variable type so that
// buildProp can construct a rich InputDiagnostic with SuggestedTypes.
type typeMissingError struct {
	varName string
	guess   core.HolType // nil if no guess available
	reason  string       // e.g., "appears in P(x) where P : A→bool"
}

func (e *typeMissingError) Error() string {
	if e.guess != nil {
		return fmt.Sprintf("variable %q has no type declaration; suggest '%s : %s' before ⊢ (%s)",
			e.varName, e.varName, ext.FormatType(e.guess), e.reason)
	}
	return fmt.Sprintf("variable %q has no type declaration; add '%s : <type>' before ⊢", e.varName, e.varName)
}

// buildSuggestedTypes returns a map of all currently known variable types
// (declared + inferred), formatted as strings for agent consumption.
func buildSuggestedTypes(env *typeEnv) map[string]string {
	result := make(map[string]string)
	for name, ty := range env.declared {
		result[name] = ext.FormatType(ty)
	}
	for name, ty := range env.inferred {
		if _, exists := result[name]; !exists {
			result[name] = ext.FormatType(ty)
		}
	}
	return result
}

// enrichTypeDiagnostic upgrades a generic validation diagnostic to a rich
// type-suggestion diagnostic when the underlying error is a typeMissingError,
// and to a type mismatch when it is a slotMismatchError or a retypedVarError.
func enrichTypeDiagnostic(diag *InputDiagnostic, env *typeEnv, origErr error) {
	if origErr == nil {
		return
	}
	switch origErr.(type) {
	case *slotMismatchError:
		diag.Code = CodeTypeMismatch
		diag.Suggestion = illTypedApplicationRepair
		return
	case *retypedVarError:
		diag.Code = CodeTypeMismatch
		return
	}
	tme, ok := origErr.(*typeMissingError)
	if !ok {
		return
	}
	diag.Code = CodeMissingType
	diag.SuggestedTypes = buildSuggestedTypes(env)
	if tme.guess != nil {
		diag.Suggestion = fmt.Sprintf("add '%s : %s' before ⊢ (%s)",
			tme.varName, ext.FormatType(tme.guess), tme.reason)
	} else {
		diag.Suggestion = fmt.Sprintf("add '%s : <type>' before ⊢", tme.varName)
	}
}
