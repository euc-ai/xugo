// Each inductive type's induction principle is paired with a
// RECURSION principle — the existence schema the `define` move's
// equation compiler instantiates:
//
//	⊢ ∃fn. clause₁ ∧ … ∧ clauseₖ        (or ∃!fn. — num_recursion)
//
// one clause per constructor, each an equation
//
//	∀args. fn(Cᵢ(args)) = paramᵢ(slot, …)
//
// where paramᵢ is the clause's target function — a variable the
// principle either ∀-binds ahead of the ∃ or leaves free — and every
// slot is a constructor argument passed through, or a recursive call
// fn(arg) at a carrier-typed argument.
//
// The corpus stores its three bootstrap principles in three surface
// arrangements, and the analyzer accepts all of them as they are
// served (no bridging seam — contrast num_induction, which
// library/serve bridges to its Go-built spelling):
//
//	num_recursion         ∀f e. ∃!fn. ∀n. (e = fn(0)) ∧ (fn(suc n) = f(fn n, n))
//	                  — params ∀-bound, the clause binder HOISTED above
//	                  the conjunction, base equation flipped, ∃! head
//	list_recursion    ∀cons' nil'. ∃fn. ∀a0 a1. (nil' = fn(nil)) ∧
//	                  (fn(cons(a0,a1)) = cons'(a0, a1, fn(a1)))
//	option_recursion  none', some' declared free (sequent decl prefix):
//	                  ⊢ ∃fn. (fn NONE = none') ∧ (∀a. fn(SOME a) = some'(a))
//	                  — per-clause binders, natural orientation
//
// AnalyzeRecursionPrinciple normalizes across those into a
// RecursionTemplate, the structural model DefineRecursive's compiler
// consumes. Statement-level only: a promise-backed principle stays
// unforced here (the AnalyzeInductionPrinciple contract).
//
// Deliberately OUTSIDE this analyzer's shape: the WF family
// (wellfounded_recursion-class principles carry a wellfounded(<<) hypothesis and pass fn
// itself to the functional — a different template, chartered
// separately), and curried extra parameters (fn applied past the
// constructor pattern). The latter is a fact about SCHEMAS, not
// definitions: a definition with curried parameters (primrec v1.1)
// canonizes in the equation compiler (prover/proof/define.go),
// which presents this analyzer an uncurried instance.

package tactic

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// RecursionTemplate is the parsed structural model of a recursion
// principle. Purely a description: every field is derived from
// Principle, and Principle stays the source of truth at
// instantiation time.
type RecursionTemplate struct {
	// Principle is the recursion theorem as served (statement-level;
	// possibly promise-backed — never forced here).
	Principle core.Prop

	// FnVar is the ∃-bound recursion function variable (bound INSIDE
	// Principle; recorded for its name and type).
	FnVar VarTerm

	// CarrierType is fn's domain — the inductive type recursed over.
	CarrierType core.HolType

	// ResultType is fn's codomain — the motive (a type variable in the
	// polymorphic principles; the compiler instantiates it at the
	// definition's result type).
	ResultType core.HolType

	// Unique marks an ∃! head (num_recursion). The compiler weakens to ∃
	// before the Hilbert reduce.
	Unique bool

	// OuterParams is the principle's leading ∀-prefix, in binder
	// order — the parameter functions a compiler instance grounds
	// positionally (num_recursion's f, e; list_recursion's cons', nil').
	// Empty for principles whose parameters are free variables
	// (option_recursion's sequent-decl form).
	OuterParams []VarTerm

	// Cases describes the constructor clauses, in ∧-spine order.
	Cases []RecursionCase
}

// RecursionCase is one constructor's clause in the principle.
type RecursionCase struct {
	// Clause is the literal conjunct as it appears under the ∃
	// (binders included) — diagnostics and instantiation anchoring.
	Clause core.Term

	// Constructor is the clause's constructor constant, at the
	// instance the principle spells (e.g. `suc`, `cons` at list(A)).
	Constructor ConstTerm

	// CtorArgs are the constructor's argument variables, in
	// CONSTRUCTOR argument order (which may differ from the clause's
	// binder order).
	CtorArgs []VarTerm

	// Param is the clause's target function variable — the RHS head.
	Param VarTerm

	// ParamBound: Param is one of the template's OuterParams
	// (grounded positionally); false = Param is free in the principle
	// (grounded by term instantiation).
	ParamBound bool

	// Slots is Param's application spine, in application order. Empty
	// for a bare-parameter clause (num_recursion's `e`).
	Slots []RecursionSlot

	// Flipped: the stored equation carries the fn-application on the
	// RIGHT (`e = fn(0)`); the compiler orients its instance
	// accordingly when aligning against the schema.
	Flipped bool
}

// RecursionSlot is one argument position of a clause's parameter
// application: the constructor argument at ArgIndex, either passed
// through bare or under a recursive call fn(·).
type RecursionSlot struct {
	ArgIndex  int
	Recursive bool
}

// RecArgIndices returns the CtorArgs indices that receive a recursive
// call somewhere in Slots, in first-occurrence order.
func (c *RecursionCase) RecArgIndices() []int {
	var out []int
	for _, s := range c.Slots {
		if s.Recursive && !slices.Contains(out, s.ArgIndex) {
			out = append(out, s.ArgIndex)
		}
	}
	return out
}

// AnalyzeRecursionPrinciple decomposes a recursion principle into a
// RecursionTemplate. Strict: anything outside the shape documented in
// the file comment returns an error, which callers surface verbatim.
// The principle is consumed at the STATEMENT level only.
func AnalyzeRecursionPrinciple(thm core.Prop) (*RecursionTemplate, error) {
	if thm == nil {
		return nil, fmt.Errorf("nil recursion principle")
	}
	if thm.NumHyps() != 0 {
		return nil, fmt.Errorf(
			"recursion principle must be hyp-free (a hyp-carrying principle "+
				"— the wellfounded_recursion family — is a different template); got %d hyps",
			thm.NumHyps())
	}

	outerList, rest := ext.DecomposesFORALL(thm.Conclusion())
	outer := make([]VarTerm, 0, outerList.Size())
	for v := range outerList.Iter() {
		outer = append(outer, v)
	}

	unique := false
	fnAbs := ext.MatchesEXISTS(rest)
	if fnAbs.IsZero() {
		if fnAbs = ext.MatchesUNIQUE(rest); !fnAbs.IsZero() {
			unique = true
		}
	}
	if fnAbs.IsZero() {
		return nil, fmt.Errorf(
			"expected ∃fn / ∃!fn after the ∀-prefix, got %q", ext.PrintTerm(rest))
	}
	fnVar := fnAbs.Var()
	fnType, ok := fnVar.Type().(core.CompositeType)
	if !ok || !ext.IsFunType(fnType) {
		return nil, fmt.Errorf(
			"recursion function %q must have a function type, got %s",
			ext.PrintTerm(fnVar), ext.FormatType(fnVar.Type()))
	}
	carrier, result := fnType.SubType(0), fnType.SubType(1)

	// Clause binders come hoisted above the ∧ (num_recursion, list) or
	// per-clause (option) — collect the hoisted pool here, each
	// clause adds its own.
	sharedList, body := ext.DecomposesFORALL(fnAbs.Body())
	shared := make([]VarTerm, 0, sharedList.Size())
	for v := range sharedList.Iter() {
		shared = append(shared, v)
	}

	conjuncts := ext.DecomposesAND(body)
	cases := make([]RecursionCase, 0, len(conjuncts))
	for _, clause := range conjuncts {
		c, err := analyzeRecursionClause(clause, fnVar, shared, outer, carrier)
		if err != nil {
			return nil, fmt.Errorf("clause %q: %w", ext.PrintTerm(clause), err)
		}
		for _, prev := range cases {
			if prev.Constructor.Name() == c.Constructor.Name() {
				return nil, fmt.Errorf(
					"constructor %q has two clauses — one equation per constructor",
					c.Constructor.Name())
			}
			if prev.Param.EqualsVar(c.Param) {
				return nil, fmt.Errorf(
					"parameter %q serves two clauses — parameters must be distinct",
					ext.PrintTerm(c.Param))
			}
		}
		cases = append(cases, c)
	}

	return &RecursionTemplate{
		Principle:   thm,
		FnVar:       fnVar,
		CarrierType: carrier,
		ResultType:  result,
		Unique:      unique,
		OuterParams: outer,
		Cases:       cases,
	}, nil
}

// analyzeRecursionClause parses one conjunct into its RecursionCase.
// shared is the binder pool hoisted above the ∧; outer the principle's
// ∀-prefix (for the ParamBound classification).
func analyzeRecursionClause(
	clause core.Term, fnVar VarTerm,
	shared, outer []VarTerm, carrier core.HolType) (RecursionCase, error) {

	ownList, eq := ext.DecomposesFORALL(clause)
	pool := slices.Clone(shared)
	for v := range ownList.Iter() {
		pool = append(pool, v)
	}
	inPool := func(v VarTerm) bool {
		return slices.IndexFunc(pool, v.EqualsVar) >= 0
	}

	l, r, ok := MatchesEQ(eq)
	if !ok {
		return RecursionCase{}, fmt.Errorf("clause body must be an equation")
	}
	appSide, paramSide, flipped := l, r, false
	if !isFnApplication(l, fnVar) {
		if !isFnApplication(r, fnVar) {
			return RecursionCase{}, fmt.Errorf(
				"neither equation side is an application of the recursion function %q",
				ext.PrintTerm(fnVar))
		}
		appSide, paramSide, flipped = r, l, true
	}

	// fn(C(args...)) — exactly one fn argument, the constructor pattern.
	_, fnArgs := ext.MatchesApply(appSide)
	if len(fnArgs) != 1 {
		return RecursionCase{}, fmt.Errorf(
			"the recursion function must be applied to exactly the constructor "+
				"pattern (%d arguments found — a curried SCHEMA is outside the "+
				"template; curried definitions canonize before reaching it)", len(fnArgs))
	}
	ctorTerm := fnArgs[0]
	if !ctorTerm.Type().Equals(carrier) {
		return RecursionCase{}, fmt.Errorf(
			"constructor pattern %q has type %s, expected the carrier %s",
			ext.PrintTerm(ctorTerm), ext.FormatType(ctorTerm.Type()), ext.FormatType(carrier))
	}
	ctorHead, ctorArgTerms := ext.MatchesApply(ctorTerm)
	ctorConst, ok := ctorHead.AsConst()
	if !ok {
		return RecursionCase{}, fmt.Errorf(
			"constructor position must be headed by a constant, got %q",
			ext.PrintTerm(ctorHead))
	}
	ctorArgs := make([]VarTerm, len(ctorArgTerms))
	for i, at := range ctorArgTerms {
		v, ok := at.AsVar()
		if !ok {
			return RecursionCase{}, fmt.Errorf(
				"constructor argument %q must be a bound variable", ext.PrintTerm(at))
		}
		if !inPool(v) {
			return RecursionCase{}, fmt.Errorf(
				"constructor argument %q is not among the clause's ∀-binders",
				ext.PrintTerm(v))
		}
		if slices.IndexFunc(ctorArgs[:i], v.EqualsVar) >= 0 {
			return RecursionCase{}, fmt.Errorf(
				"constructor arguments must be distinct variables; %q repeats",
				ext.PrintTerm(v))
		}
		ctorArgs[i] = v
	}

	// param(slot...) — the parameter head with its application spine.
	pHead, pArgs := ext.MatchesApply(paramSide)
	paramVar, ok := pHead.AsVar()
	if !ok {
		return RecursionCase{}, fmt.Errorf(
			"the clause's target side must be an application of a parameter "+
				"variable, got head %q", ext.PrintTerm(pHead))
	}
	if paramVar.EqualsVar(fnVar) {
		return RecursionCase{}, fmt.Errorf(
			"the clause's target head is the recursion function itself — " +
				"a wellfounded_recursion-family shape, not structural recursion")
	}
	if inPool(paramVar) {
		return RecursionCase{}, fmt.Errorf(
			"the clause's target head %q is a clause binder, not a parameter",
			ext.PrintTerm(paramVar))
	}
	slots := make([]RecursionSlot, len(pArgs))
	for i, a := range pArgs {
		if v, ok := a.AsVar(); ok {
			idx := slices.IndexFunc(ctorArgs, v.EqualsVar)
			if idx < 0 {
				return RecursionCase{}, fmt.Errorf(
					"slot %q is not a constructor argument", ext.PrintTerm(v))
			}
			slots[i] = RecursionSlot{ArgIndex: idx}
			continue
		}
		if !isFnApplication(a, fnVar) {
			return RecursionCase{}, fmt.Errorf(
				"slot %q must be a constructor argument or a recursive call fn(arg)",
				ext.PrintTerm(a))
		}
		_, callArgs := ext.MatchesApply(a)
		if len(callArgs) != 1 {
			return RecursionCase{}, fmt.Errorf(
				"recursive call %q must apply fn to exactly one constructor argument",
				ext.PrintTerm(a))
		}
		v, ok := callArgs[0].AsVar()
		if !ok {
			return RecursionCase{}, fmt.Errorf(
				"recursive call argument %q must be a constructor argument variable",
				ext.PrintTerm(callArgs[0]))
		}
		idx := slices.IndexFunc(ctorArgs, v.EqualsVar)
		if idx < 0 {
			return RecursionCase{}, fmt.Errorf(
				"recursive call argument %q is not a constructor argument",
				ext.PrintTerm(v))
		}
		if !v.Type().Equals(carrier) {
			return RecursionCase{}, fmt.Errorf(
				"recursive call at %q whose type %s is not the carrier %s",
				ext.PrintTerm(v), ext.FormatType(v.Type()), ext.FormatType(carrier))
		}
		slots[i] = RecursionSlot{ArgIndex: idx, Recursive: true}
	}

	return RecursionCase{
		Clause:      clause,
		Constructor: ctorConst,
		CtorArgs:    ctorArgs,
		Param:       paramVar,
		ParamBound:  slices.IndexFunc(outer, paramVar.EqualsVar) >= 0,
		Slots:       slots,
		Flipped:     flipped,
	}, nil
}

// isFnApplication reports whether t is fnVar applied to one or more
// arguments.
func isFnApplication(t core.Term, fnVar VarTerm) bool {
	head, args := ext.MatchesApply(t)
	if len(args) == 0 {
		return false
	}
	v, ok := head.AsVar()
	return ok && v.EqualsVar(fnVar)
}

// RecursionPrincipleNameCandidates returns the
// recursion principle names to try for a given inductive type, in
// priority order — the recursion sibling of PrincipleNameCandidates,
// against the same table (env.LibraryThms; the corpus binds every
// serving entry's statement-promise by name, so num_recursion /
// list_recursion / option_recursion resolve wherever
// serve.InductionPrinciples() was loaded).
//
// The convention is `<T>_recursion` for every type; num's is served in
// the ∃! form (peano.Recursion), the datatype door's in the ∃ form.
func RecursionPrincipleNameCandidates(t core.HolType) []string {
	ct, ok := t.(core.CompositeType)
	if !ok {
		return nil
	}
	return []string{string(ct.Meta().Name()) + "_recursion"}
}

// AnalyzeRecursionPrincipleForType parses a recursion principle and,
// if its carrier doesn't match `targetType` directly, attempts to
// type-instantiate it (polymorphic `list_recursion` for `list(A)`
// specialized to `list(num)`). Returns (nil, nil) when the carrier
// can't be unified with `targetType` — the AnalyzePrincipleForType
// contract.
func AnalyzeRecursionPrincipleForType(thm core.Prop, targetType core.HolType) (*RecursionTemplate, error) {
	tmpl, err := AnalyzeRecursionPrinciple(thm)
	if err != nil {
		return nil, err
	}
	if tmpl.CarrierType.Equals(targetType) {
		return tmpl, nil
	}
	substs, ok := tmpl.CarrierType.Matches(targetType, func(core.VarType) bool { return true })
	if !ok {
		return nil, nil
	}
	// PropTypeInst is promise-transparent: a promise-backed principle
	// stays a promise after specialization. Re-analyze at the
	// statement level (no cert collapse, which would force the cone).
	specialized := core.PropTypeInst(thm, substs...)
	return AnalyzeRecursionPrinciple(specialized)
}
