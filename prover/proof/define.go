// define.go — the definition move's shared driver: the pieces of
// `define` that live OUTSIDE the proof tree — equation analysis and
// the kernel mint — plus the characterizing-theorem derivation the
// _DefineStep executor runs inside it. The engine `define` RPC
// (session side) and registry.Family.Define (replay side)
// drive these same functions — the record/emit/replay code-reuse
// principle applied at ENTRY granularity.
//
// This file is the `recursive:` payload's two shapes, both on the one
// mint/derive spine:
//
//   - DIRECT — the zero-recursion degenerate case
//     (the nat_divides vocab-mint pattern promoted to
//     a first-class move).
//   - PRIMREC — schema compilation against a RecursionTemplate:
//     clause analysis, the case witnesses, CompileRecursiveExistence.
//     §"v1.1" carries it past the exact-schema shape (result-type
//     currying and argument reshuffle), in
//     three nested provers.
//
// The other payloads have their own files: `data:` in define_data.go,
// the COND-form well-founded shape in define_wf.go.

package proof

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// ParseDefinitionEquation parses one definition-equation literal with the
// DEFINIENDUM declared as a variable of the author's stated type. This is
// the one door a fresh name may enter (strict resolution's invariant): both
// strict switches are forced on, so any OTHER undeclared name errors with
// the repair named, and an unanchored type letter is rejected with the tie
// spelling — the definiendum is the single deliberate exception, and it
// enters as a declared VARIABLE, never as a freshened constant.
//
// base supplies the ambient resolution — a session's statement scope,
// or the registry's manager-backed scope; it is read, never mutated.
// The definiendum must be a FRESH name: one that base already resolves
// as a constant errors here, before any parse, with the collision
// named (the mint would refuse it anyway; this is the earlier, clearer
// diagnostic).
func ParseDefinitionEquation(equationText, name, typeText string, base *dsl.ParseScope) (Prop, VarTerm, error) {
	typ, err := dsl.ParseTypeTextInScope(typeText, base)
	if err != nil {
		return nil, VarTerm{}, fmt.Errorf("definition type %q: %v", typeText, err)
	}
	if base != nil && scopeResolvesConst(base, name) {
		return nil, VarTerm{}, fmt.Errorf(
			"define: %q already names a constant in scope — a definition mints a "+
				"FRESH name; pick another", name)
	}

	var scope dsl.ParseScope
	if base != nil {
		scope = *base
	}
	vars := make(map[string]HolType, len(scope.Vars)+1)
	for k, v := range scope.Vars {
		vars[k] = v
	}
	vars[name] = typ
	scope.Vars = vars
	scope.StrictResolution = true
	scope.StrictMint = true
	scope.FreshenMetaLetters = true

	res := dsl.ParsePropTextInScope(equationText, &scope)
	if len(res.Errors) > 0 {
		return nil, VarTerm{}, fmt.Errorf("parse definition equation: %s", res.Errors[0].Message)
	}
	defVar := Var(TermName(name), typ).Core().(VarTerm)
	return res.Prop, defVar, nil
}

// scopeResolvesConst reports whether the scope already binds name as a
// constant (fixed instance, meta, or resolver fallback).
func scopeResolvesConst(s *dsl.ParseScope, name string) bool {
	if _, ok := s.Consts[name]; ok {
		return true
	}
	if _, ok := s.ConstMetas[name]; ok {
		return true
	}
	return s.ConstResolver != nil && !s.ConstResolver(name).IsZero()
}

// DirectDefinition is the analyzed form of a non-recursive definition
// equation:
//
//	∀x̄. c(x̄) = body        (⇔ at bool — the same constant)
//
// with c the DEFINIENDUM — a free VARIABLE in the parsed equation,
// because the mint has not happened yet: the parser declares the new
// name as a variable of the author's stated type, so strict
// resolution stays armed and the one-door invariant holds — x̄
// distinct variables, and body free of c (zero recursion) and closed
// apart from x̄.
type DirectDefinition struct {
	// DefVar is the definiendum's variable occurrence in Equation.
	// Its name is the constant's name; its type the constant's type.
	DefVar VarTerm

	// Args are the LHS argument variables, in application order.
	// Empty for a nullary definition (c = body).
	Args []VarTerm

	// Body is the RHS, free only in Args.
	Body Term

	// Lambda is λArgs.Body — the closed term core.NewConstDef consumes.
	Lambda Term

	// Equation is the parsed equation, definiendum-var form.
	Equation Prop
}

// AnalyzeDirectDefinition validates a parsed definition equation
// against the direct (non-recursive) shape and decomposes it. Strict:
// every deviation is an error naming its repair, surfaced verbatim to
// the author (a rejection names its repair).
func AnalyzeDirectDefinition(equation Prop, defVar VarTerm) (*DirectDefinition, error) {
	if equation == nil || defVar.IsZero() {
		return nil, fmt.Errorf("nil definition equation")
	}
	if equation.NumHyps() != 0 {
		return nil, fmt.Errorf("definition equation must be hyp-free; got %d hyps",
			equation.NumHyps())
	}
	concl := equation.Conclusion()

	// The only free variable of the ∀-closed equation is the
	// definiendum itself — anything else is an unbound name the
	// ∀-prefix should have caught.
	for _, v := range concl.Frees(nil) {
		if !v.EqualsVar(defVar) {
			return nil, fmt.Errorf(
				"definition equation has a free variable %q besides the definiendum — "+
					"∀-bind it or fix the spelling", PrintTerm(v))
		}
	}

	binderList, matrix := DecomposesFORALL(concl)
	binders := make([]VarTerm, 0, binderList.Size())
	for v := range binderList.Iter() {
		binders = append(binders, v)
	}

	l, r, ok := MatchesEQ(matrix)
	if !ok {
		return nil, fmt.Errorf("definition body must be an equation (= / ⇔), got %q",
			PrintTerm(matrix))
	}
	head, argTerms := MatchesApply(l)
	headVar, ok := head.AsVar()
	if !ok || !headVar.EqualsVar(defVar) {
		return nil, fmt.Errorf(
			"the definiendum %q must head the LEFT side as %s(args…) = body",
			defVar.Name(), defVar.Name())
	}
	if r.HasFree(defVar) {
		return nil, fmt.Errorf(
			"the definiendum %q occurs on the right side — a recursive definition; "+
				"the direct shape requires a c-free body", defVar.Name())
	}

	args := make([]VarTerm, len(argTerms))
	for i, at := range argTerms {
		v, ok := at.AsVar()
		if !ok {
			return nil, fmt.Errorf(
				"definition argument %q must be a plain ∀-bound variable "+
					"(patterns belong to the recursive shapes)", PrintTerm(at))
		}
		if slices.IndexFunc(binders, v.EqualsVar) < 0 {
			return nil, fmt.Errorf(
				"definition argument %q is not ∀-bound by the equation", PrintTerm(v))
		}
		if slices.IndexFunc(args[:i], v.EqualsVar) >= 0 {
			return nil, fmt.Errorf(
				"definition arguments must be distinct variables; %q repeats",
				PrintTerm(v))
		}
		args[i] = v
	}
	// Every ∀-binder must be consumed as an argument — a binder the
	// LHS does not mention would be silently dropped from the
	// definition (the body cannot use it either: λ-closedness below
	// would fail), so name it loudly.
	for _, b := range binders {
		if slices.IndexFunc(args, b.EqualsVar) < 0 {
			return nil, fmt.Errorf(
				"∀-bound variable %q is not an argument of %s(…) — every bound "+
					"variable of a definition equation must appear on the left",
				PrintTerm(b), defVar.Name())
		}
	}

	lambda := r
	for i := len(args) - 1; i >= 0; i-- {
		lambda = Abs(args[i], lambda)
	}

	return &DirectDefinition{
		DefVar:   defVar,
		Args:     args,
		Body:     r,
		Lambda:   lambda,
		Equation: equation,
	}, nil
}

// MintDirectDefinition performs the kernel mint for an analyzed
// direct definition — c := λx̄.body via core.NewConstDef — and
// registers the const meta through the env's ProofService.
// Registration is EXCLUSIVE (the nat_divides precedent; a session mint is
// process-global): a name already registered errors — a second
// mint, or a collision with an imported constant — and never shadows.
//
// Returns the minted const and the characterizing statement
// ⊢ ∀x̄. c(x̄) = body (the analyzed equation with the definiendum
// variable replaced by the constant) — UNPROVED: proving it is the
// definition section's job, via the _DefineStep executor.
func MintDirectDefinition(env *ProverEnv, d *DirectDefinition) (ConstTerm, Prop, error) {
	return MintDirectDefinitionAs(env, d, d.DefVar.Name())
}

// MintDirectDefinitionAs is MintDirectDefinition minting under name
// rather than the definiendum variable's own — the door for a
// constant the text DSL cannot spell in head position (an operator,
// a name the DSL reserves), whose equations spell a stand-in.
func MintDirectDefinitionAs(env *ProverEnv, d *DirectDefinition, name TermName) (ConstTerm, Prop, error) {
	c, err := mintDefinedConst(env, name, d.Lambda)
	if err != nil {
		return ConstTerm{}, nil, err
	}
	characterizing := core.MakeProp(
		d.Equation.Conclusion().Substitute(MakeTermSubst(d.DefVar, c)))
	return c, characterizing, nil
}

// MintRecursiveDefinition performs the kernel mint for an analyzed
// recursive definition — c := εf. P(f) via core.NewConstDef, the
// specification shape — under the same exclusive registration as
// the direct mint. Returns the minted const and the characterizing
// statement P(c) (the equations' conjunction at the constant) —
// UNPROVED: the definition section proves it through _DefineStep's
// HILBERT branch, whose existence obligation the equation compiler
// (CompileRecursiveExistence) discharges.
//
// Callers mint only AFTER a successful compile: a definition whose
// existence the schema cannot discharge must not register a constant.
func MintRecursiveDefinition(env *ProverEnv, rd *RecursiveDefinition) (ConstTerm, Prop, error) {
	return MintRecursiveDefinitionAs(env, rd, rd.DefVar.Name())
}

// MintRecursiveDefinitionAs is MintRecursiveDefinition minting under
// name rather than the definiendum variable's own (the stand-in
// spelling case, as MintDirectDefinitionAs).
func MintRecursiveDefinitionAs(env *ProverEnv, rd *RecursiveDefinition, name TermName) (ConstTerm, Prop, error) {
	c, err := mintDefinedConst(env, name, rd.EpsTerm)
	if err != nil {
		return ConstTerm{}, nil, err
	}
	characterizing := core.MakeProp(
		rd.Property.Substitute(MakeTermSubst(rd.DefVar, c)))
	return c, characterizing, nil
}

// mintDefinedConst is the shared kernel mint + EXCLUSIVE registration
// (the nat_divides precedent; a session mint is process-global): a name
// already registered errors — a second mint, or a collision with an
// imported constant — and never shadows.
func mintDefinedConst(env *ProverEnv, name TermName, payload Term) (ConstTerm, error) {
	if env == nil || env.ProofService == nil ||
		env.ProofService.LoadOrStoreConstMeta == nil {
		return ConstTerm{}, fmt.Errorf("define: env carries no const-meta registry")
	}
	if env.ProofService.LoadConstMeta != nil {
		if meta, ok := env.ProofService.LoadConstMeta(name); ok && !meta.IsZero() {
			return ConstTerm{}, fmt.Errorf(
				"define: constant %q is already registered — a second mint, or a "+
					"collision with an imported constant; pick a fresh name", name)
		}
	}
	c := core.NewConstDef(payload, name)
	if _, existed := env.ProofService.LoadOrStoreConstMeta(c.Meta()); existed {
		return ConstTerm{}, fmt.Errorf(
			"define: constant %q was registered concurrently — pick a fresh name", name)
	}
	return c, nil
}

// IsCompiledDefinitionEquation reports whether a parsed definition
// equation belongs to the equation compiler rather than the direct
// shape — the classifier the doors route a SINGLE equation on (two or
// more always compile). It does when its right side mentions the
// definiendum (a recursion), or when an argument on its left is not a
// plain variable (a constructor pattern): a one-constructor datatype's
// projection, `re(complex(x, y)) = x`, recurs nowhere and is still a
// definition by cases, which only the compiler reads.
func IsCompiledDefinitionEquation(equation Prop, defVar VarTerm) bool {
	if equation == nil {
		return false
	}
	_, matrix := DecomposesFORALL(equation.Conclusion())
	l, r, ok := MatchesEQ(matrix)
	if !ok {
		return false
	}
	if r.HasFree(defVar) {
		return true
	}
	_, args := MatchesApply(l)
	for _, a := range args {
		if _, isVar := a.AsVar(); !isVar {
			return true
		}
	}
	return false
}

// ---------------------------------------------------------------------------
// The recursive shape — the equation compiler (P4a)
// ---------------------------------------------------------------------------

// RecursiveClause is one analyzed defining equation of a recursive
// definition: fn applied to a constructor pattern (plus any curried
// extra parameters — the v1.1 shape) on the left, an arbitrary term
// over (extra parameters, constructor args, recursive calls) on the
// right.
type RecursiveClause struct {
	// Equation is the parsed equation, definiendum-var form.
	Equation Prop
	// Constructor is the pattern's head constant, at the carrier
	// instance the equation spells.
	Constructor ConstTerm
	// CtorArgs are the pattern's argument variables, constructor
	// argument order.
	CtorArgs []VarTerm
	// ExtraParams are the LHS variables at the non-recursion argument
	// positions, in position order — empty for the v1 single-argument
	// shape.
	ExtraParams []VarTerm
	// Binders is the clause's ∀-binder list in the author's parse
	// order (= CtorArgs ∪ ExtraParams, as spelled).
	Binders []VarTerm
	// Rhs is the right side — free in Binders and the definiendum,
	// the latter ONLY as recursive calls whose recursion-position
	// argument is a pattern argument.
	Rhs Term
}

// RecursiveDefinition is the analyzed form of a recursive definition:
// one equation per constructor of the carrier type, definiendum still
// a VARIABLE (the mint has not happened).
type RecursiveDefinition struct {
	DefVar      VarTerm
	CarrierType HolType
	// ResultType is the CANONICAL MOTIVE the schema's result type
	// instantiates at: the extra argument types (author position
	// order, recursion position removed) folded onto the remaining
	// result type. With no extra parameters this is everything after
	// the carrier — the v1 shape.
	ResultType HolType
	// ArgTypes are the author-position argument types (one per spelled
	// LHS argument); ArgTypes[RecArgPos] is the carrier.
	ArgTypes []HolType
	// RecArgPos is the recursion argument's position on the LHS — 0
	// for the v1/v1.1a shapes, >0 for the reshuffle shapes (v1.1b).
	RecArgPos int
	Clauses   []RecursiveClause // author order

	// Property is P(f): the ∧ of the equations' conclusions in author
	// order, DefVar free.
	Property Term
	// EpsTerm is εf. P(f) — the closed core.NewConstDef payload.
	EpsTerm Term
	// ExistsStmt is ∃f. P(f) — the existence obligation's statement.
	ExistsStmt Prop
}

// curried reports whether the definition carries extra parameters
// beyond the recursion argument — the v1.1 shapes, whose compiled
// existence needs the canonical→author transfer.
func (rd *RecursiveDefinition) curried() bool {
	return len(rd.Clauses) > 0 && len(rd.Clauses[0].ExtraParams) > 0
}

// AnalyzeRecursiveDefinition validates parsed equations against the
// recursive shape (the primrec v1/v1.1 rulings: ONE recursion
// argument position — first or reshuffled — plus curried extra
// parameters, one equation per constructor, RHS arbitrary over extra
// parameters, constructor args and recursive calls) and decomposes
// them. Strict, repair-naming errors.
func AnalyzeRecursiveDefinition(equations []Prop, defVar VarTerm) (*RecursiveDefinition, error) {
	if len(equations) == 0 || defVar.IsZero() {
		return nil, fmt.Errorf("recursive definition needs at least one equation")
	}
	arity, recPos, err := scanRecursionShape(equations, defVar)
	if err != nil {
		return nil, err
	}

	// Peel the spelled arity off the definiendum's type: one type per
	// author position, plus the remaining result.
	argTypes := make([]HolType, arity)
	rest := defVar.Type()
	for i := range arity {
		ct, ok := rest.(CompositeType)
		if !ok || !ext.IsFunType(ct) {
			return nil, fmt.Errorf(
				"the definiendum %q has type %s but the equations apply %d arguments",
				defVar.Name(), FormatType(defVar.Type()), arity)
		}
		argTypes[i], rest = ct.SubType(0), ct.SubType(1)
	}
	carrier := argTypes[recPos]
	// The canonical motive: extra argument types (position order, the
	// recursion position removed) folded onto the remaining result —
	// the result-type currying. With no extras this is everything
	// after the carrier, the v1 shape.
	motive := rest
	for i := arity - 1; i >= 0; i-- {
		if i == recPos {
			continue
		}
		motive = MakeFun(argTypes[i], motive)
	}

	clauses := make([]RecursiveClause, 0, len(equations))
	conj := make([]Term, 0, len(equations))
	for _, equation := range equations {
		c, err := analyzeRecursiveClause(equation, defVar, carrier, arity, recPos)
		if err != nil {
			return nil, err
		}
		for _, prev := range clauses {
			if prev.Constructor.Name() == c.Constructor.Name() {
				return nil, fmt.Errorf(
					"constructor %q has two equations — one equation per constructor",
					c.Constructor.Name())
			}
		}
		clauses = append(clauses, c)
		conj = append(conj, equation.Conclusion())
	}

	property := conj[len(conj)-1]
	for i := len(conj) - 2; i >= 0; i-- {
		property = ext.And(conj[i], property).Core()
	}
	eps := WrapTerm(defVar).SuchThat(WrapTerm(property)).Core()
	exists := core.MakeProp(Exists(WrapTerm(defVar))(WrapTerm(property)).Core())

	return &RecursiveDefinition{
		DefVar:      defVar,
		CarrierType: carrier,
		ResultType:  motive,
		ArgTypes:    argTypes,
		RecArgPos:   recPos,
		Clauses:     clauses,
		Property:    property,
		EpsTerm:     eps,
		ExistsStmt:  exists,
	}, nil
}

// scanRecursionShape reads every equation's LHS application spine and
// pins the two shape-wide facts clause analysis needs: the spelled
// arity (all clauses must agree) and the recursion argument's
// position — the single position where clauses carry constructor
// patterns (non-variable arguments); every other position holds plain
// variables.
func scanRecursionShape(equations []Prop, defVar VarTerm) (arity, recPos int, err error) {
	arity = -1
	patternPositions := make(map[int]bool)
	for _, equation := range equations {
		if equation == nil {
			return 0, 0, fmt.Errorf("nil defining equation")
		}
		_, matrix := DecomposesFORALL(equation.Conclusion())
		l, _, ok := MatchesEQ(matrix)
		if !ok {
			return 0, 0, fmt.Errorf("equation body must be an equation (= / ⇔), got %q",
				PrintTerm(matrix))
		}
		head, fnArgs := MatchesApply(l)
		headVar, ok := head.AsVar()
		if !ok || !headVar.EqualsVar(defVar) {
			return 0, 0, fmt.Errorf(
				"the definiendum %q must head the LEFT side as %s(args…) = body",
				defVar.Name(), defVar.Name())
		}
		if len(fnArgs) == 0 {
			return 0, 0, fmt.Errorf(
				"a recursive defining equation applies %s to its arguments; a bare "+
					"%s = … equation is the direct shape", defVar.Name(), defVar.Name())
		}
		if arity < 0 {
			arity = len(fnArgs)
		} else if arity != len(fnArgs) {
			return 0, 0, fmt.Errorf(
				"the equations apply %s to different argument counts (%d vs %d) — "+
					"every clause spells the same arguments", defVar.Name(), arity, len(fnArgs))
		}
		for i, a := range fnArgs {
			if _, isVar := a.AsVar(); !isVar {
				patternPositions[i] = true
			}
		}
	}
	switch len(patternPositions) {
	case 0:
		return 0, 0, fmt.Errorf(
			"no equation carries a constructor pattern — a recursive definition "+
				"patterns exactly one argument position of %s", defVar.Name())
	case 1:
		for p := range patternPositions {
			recPos = p
		}
		return arity, recPos, nil
	default:
		positions := make([]int, 0, len(patternPositions))
		for p := range patternPositions {
			positions = append(positions, p)
		}
		slices.Sort(positions)
		return 0, 0, fmt.Errorf(
			"constructor patterns appear at %d argument positions %v of %s — "+
				"recursion runs on exactly ONE position",
			len(positions), positions, defVar.Name())
	}
}

func analyzeRecursiveClause(equation Prop, defVar VarTerm, carrier HolType, arity, recPos int) (RecursiveClause, error) {
	if equation == nil || equation.NumHyps() != 0 {
		return RecursiveClause{}, fmt.Errorf("defining equation must be hyp-free")
	}
	concl := equation.Conclusion()
	for _, v := range concl.Frees(nil) {
		if !v.EqualsVar(defVar) {
			return RecursiveClause{}, fmt.Errorf(
				"equation %q has a free variable %q besides the definiendum — "+
					"∀-bind it or fix the spelling", PrintTerm(concl), PrintTerm(v))
		}
	}
	binderList, matrix := DecomposesFORALL(concl)
	binders := make([]VarTerm, 0, binderList.Size())
	for v := range binderList.Iter() {
		binders = append(binders, v)
	}
	l, r, ok := MatchesEQ(matrix)
	if !ok {
		return RecursiveClause{}, fmt.Errorf("equation body must be an equation (= / ⇔), got %q",
			PrintTerm(matrix))
	}
	head, fnArgs := MatchesApply(l)
	headVar, ok := head.AsVar()
	if !ok || !headVar.EqualsVar(defVar) {
		return RecursiveClause{}, fmt.Errorf(
			"the definiendum %q must head the LEFT side as %s(pattern) = body",
			defVar.Name(), defVar.Name())
	}
	if len(fnArgs) != arity {
		// scanRecursionShape pinned the shared arity; defensive.
		return RecursiveClause{}, fmt.Errorf(
			"%s takes %d arguments here but %d elsewhere — every clause spells "+
				"the same arguments", defVar.Name(), len(fnArgs), arity)
	}
	pattern := fnArgs[recPos]
	ctorHead, ctorArgTerms := MatchesApply(pattern)
	ctorConst, ok := ctorHead.AsConst()
	if !ok {
		return RecursiveClause{}, fmt.Errorf(
			"the pattern at the recursion position (%d) must be a constructor "+
				"application, got head %q", recPos, PrintTerm(ctorHead))
	}
	if !pattern.Type().Equals(carrier) {
		return RecursiveClause{}, fmt.Errorf(
			"pattern %q has type %s, but %s recurses over %s",
			PrintTerm(pattern), FormatType(pattern.Type()),
			defVar.Name(), FormatType(carrier))
	}
	ctorArgs := make([]VarTerm, len(ctorArgTerms))
	for i, at := range ctorArgTerms {
		v, ok := at.AsVar()
		if !ok {
			return RecursiveClause{}, fmt.Errorf(
				"pattern argument %q must be a plain variable (nested patterns "+
					"are out of the v1 shape)", PrintTerm(at))
		}
		if slices.IndexFunc(binders, v.EqualsVar) < 0 {
			return RecursiveClause{}, fmt.Errorf(
				"pattern argument %q is not ∀-bound by the equation", PrintTerm(v))
		}
		if slices.IndexFunc(ctorArgs[:i], v.EqualsVar) >= 0 {
			return RecursiveClause{}, fmt.Errorf(
				"pattern arguments must be distinct variables; %q repeats", PrintTerm(v))
		}
		ctorArgs[i] = v
	}
	// The extra parameters: every non-recursion position holds a plain
	// ∀-bound variable, distinct across the whole LHS (v1.1's curried
	// shape; empty at arity 1 — the v1 shape).
	extras := make([]VarTerm, 0, arity-1)
	for i, at := range fnArgs {
		if i == recPos {
			continue
		}
		v, ok := at.AsVar()
		if !ok {
			return RecursiveClause{}, fmt.Errorf(
				"argument %q at position %d must be a plain ∀-bound variable — "+
					"constructor patterns live only at the recursion position (%d)",
				PrintTerm(at), i, recPos)
		}
		if slices.IndexFunc(binders, v.EqualsVar) < 0 {
			return RecursiveClause{}, fmt.Errorf(
				"extra parameter %q is not ∀-bound by the equation", PrintTerm(v))
		}
		if slices.IndexFunc(ctorArgs, v.EqualsVar) >= 0 {
			return RecursiveClause{}, fmt.Errorf(
				"%q is both a pattern argument and an extra parameter — the LHS "+
					"variables must be distinct", PrintTerm(v))
		}
		if slices.IndexFunc(extras, v.EqualsVar) >= 0 {
			return RecursiveClause{}, fmt.Errorf(
				"extra parameters must be distinct variables; %q repeats", PrintTerm(v))
		}
		extras = append(extras, v)
	}
	for _, b := range binders {
		if slices.IndexFunc(ctorArgs, b.EqualsVar) < 0 &&
			slices.IndexFunc(extras, b.EqualsVar) < 0 {
			return RecursiveClause{}, fmt.Errorf(
				"∀-bound variable %q is not an argument of %s(…) — every bound "+
					"variable of a defining equation must appear on the left",
				PrintTerm(b), defVar.Name())
		}
	}
	if err := checkRecursiveCalls(r, defVar, ctorArgs, carrier, recPos); err != nil {
		return RecursiveClause{}, err
	}
	return RecursiveClause{
		Equation:    equation,
		Constructor: ctorConst,
		CtorArgs:    ctorArgs,
		ExtraParams: extras,
		Binders:     binders,
		Rhs:         r,
	}, nil
}

// checkRecursiveCalls walks rhs and validates every occurrence of the
// definiendum: it must head an application that reaches the recursion
// position, whose recursion-position argument is a carrier-typed
// pattern argument — the shape the recursion schemas provide slots
// for. The other call arguments are arbitrary terms (the nth-element class:
// an extra argument may change in the recursive call), themselves
// walked for nested occurrences.
func checkRecursiveCalls(t Term, defVar VarTerm, ctorArgs []VarTerm, carrier HolType, recPos int) error {
	if v, ok := t.AsVar(); ok {
		if v.EqualsVar(defVar) {
			return fmt.Errorf(
				"%q occurs as a bare value on the right — recursive calls must "+
					"apply %s through its recursion argument", defVar.Name(), defVar.Name())
		}
		return nil
	}
	if abs, ok := t.AsAbsTerm(); ok {
		if abs.Var().EqualsVar(defVar) {
			return nil // shadowed — inner occurrences are not the definiendum
		}
		return checkRecursiveCalls(abs.Body(), defVar, ctorArgs, carrier, recPos)
	}
	head, args := MatchesApply(t)
	if len(args) == 0 {
		return nil
	}
	if hv, ok := head.AsVar(); ok && hv.EqualsVar(defVar) {
		if len(args) < recPos+1 {
			return fmt.Errorf(
				"recursive call %q reaches only %d argument(s) — the recursion "+
					"argument sits at position %d and must be present",
				PrintTerm(t), len(args), recPos)
		}
		rv, ok := args[recPos].AsVar()
		if !ok || slices.IndexFunc(ctorArgs, rv.EqualsVar) < 0 {
			return fmt.Errorf(
				"recursive call %q must take a pattern argument at the recursion "+
					"position (nested recursion is out of the v1.1 shape)",
				PrintTerm(t))
		}
		if !rv.Type().Equals(carrier) {
			return fmt.Errorf(
				"recursive call at %q whose type %s is not the carrier %s",
				PrintTerm(rv), FormatType(rv.Type()), FormatType(carrier))
		}
		for i, a := range args {
			if i == recPos {
				continue
			}
			if err := checkRecursiveCalls(a, defVar, ctorArgs, carrier, recPos); err != nil {
				return err
			}
		}
		return nil
	}
	if err := checkRecursiveCalls(head, defVar, ctorArgs, carrier, recPos); err != nil {
		return err
	}
	for _, a := range args {
		if err := checkRecursiveCalls(a, defVar, ctorArgs, carrier, recPos); err != nil {
			return err
		}
	}
	return nil
}

// AnalyzeRecursiveExistence re-derives the RecursiveDefinition from an
// existence obligation ∃f.(eq₁ ∧ … ∧ eqₖ) — the _DefineStep executor's
// entry: the obligation statement is the recorded goal's whole
// self-contained payload, so replay recomputes the compilation from it
// deterministically.
func AnalyzeRecursiveExistence(exists Prop) (*RecursiveDefinition, error) {
	if exists == nil || exists.NumHyps() != 0 {
		return nil, fmt.Errorf("existence obligation must be a hyp-free statement")
	}
	abs := MatchesEXISTS(exists.Conclusion())
	if abs.IsZero() {
		return nil, fmt.Errorf("existence obligation must be ∃-headed, got %q",
			PrintTerm(exists.Conclusion()))
	}
	defVar := abs.Var()
	conjuncts := DecomposesAND(abs.Body())
	equations := make([]Prop, len(conjuncts))
	for i, c := range conjuncts {
		equations[i] = core.MakeProp(c)
	}
	return AnalyzeRecursiveDefinition(equations, defVar)
}

// replaceSubTerm returns t with every occurrence of `from` (α-compared)
// replaced by `to`. It does not descend under a binder that captures a
// free variable of `from` (those occurrences are different terms) or of
// `to` (replacement there would capture; the compiler's `to` is always
// a fresh variable, so this is a guard, not a code path).
func replaceSubTerm(t, from, to Term) Term {
	if t.AlphaEquals(from) {
		return to
	}
	if app, ok := t.AsAppliedTerm(); ok {
		f := replaceSubTerm(app.Fun(), from, to)
		a := replaceSubTerm(app.Arg(), from, to)
		if f == app.Fun() && a == app.Arg() {
			return t
		}
		return Apply(f, a).Core()
	}
	if abs, ok := t.AsAbsTerm(); ok {
		if from.HasFree(abs.Var()) || to.HasFree(abs.Var()) {
			return t
		}
		b := replaceSubTerm(abs.Body(), from, to)
		if b == abs.Body() {
			return t
		}
		return Abs(abs.Var(), b)
	}
	return t
}

// CompileRecursiveExistence proves the existence obligation ∃f.P(f)
// from the carrier's registered recursion schema: resolve the schema
// (RecursionPrincipleNameCandidates against env.LibraryThms),
// type-instantiate carrier and result, build one parameter witness per
// constructor clause, term-instantiate, β-normalize, weaken ∃!→∃ when
// the schema is unique-form, and bridge to the obligation's own
// arrangement. Pure statement-level derivation — deterministic, no
// refuter, promise-transparent (the schema promise forces only when
// the definition's theorem does). Returns the proved obligation and
// the schema's name (the entry's dep).
func CompileRecursiveExistence(env *ProverEnv, rd *RecursiveDefinition) (Prop, string, error) {
	if env == nil {
		return nil, "", fmt.Errorf("compile recursive definition: nil env")
	}
	candidates := tactic.RecursionPrincipleNameCandidates(rd.CarrierType)
	if len(candidates) == 0 {
		return nil, "", fmt.Errorf(
			"type %s is not an inductive composite type — no recursion schema to instantiate",
			FormatType(rd.CarrierType))
	}
	var tmpl *tactic.RecursionTemplate
	var schemaName string
	for _, name := range candidates {
		thm, ok := env.LookupLibraryThm(name)
		if !ok || thm == nil {
			continue
		}
		tm, err := tactic.AnalyzeRecursionPrincipleForType(thm, rd.CarrierType)
		if err != nil || tm == nil {
			continue
		}
		tmpl, schemaName = tm, name
		break
	}
	if tmpl == nil {
		return nil, "", fmt.Errorf(
			"no recursion schema registered for carrier %s (looked for %v in the "+
				"library theorems)", FormatType(rd.CarrierType), candidates)
	}

	// Result-motive instantiation.
	if !tmpl.ResultType.Equals(rd.ResultType) {
		substs, ok := tmpl.ResultType.Matches(rd.ResultType, func(VarType) bool { return true })
		if !ok {
			return nil, "", fmt.Errorf(
				"schema %s's result type %s cannot instantiate at %s",
				schemaName, FormatType(tmpl.ResultType), FormatType(rd.ResultType))
		}
		specialized := core.PropTypeInst(tmpl.Principle, substs...)
		tm, err := tactic.AnalyzeRecursionPrinciple(specialized)
		if err != nil {
			return nil, "", fmt.Errorf("schema %s after result instantiation: %v", schemaName, err)
		}
		tmpl = tm
	}

	// One witness per template case, matched to the user clause by
	// constructor.
	witnessByParam := make(map[VarTerm]Term, len(tmpl.Cases))
	matched := make([]bool, len(rd.Clauses))
	for i := range tmpl.Cases {
		tc := &tmpl.Cases[i]
		idx := slices.IndexFunc(rd.Clauses, func(c RecursiveClause) bool {
			return c.Constructor.Name() == tc.Constructor.Name()
		})
		if idx < 0 {
			return nil, "", fmt.Errorf(
				"missing equation for constructor %q — schema %s needs one equation "+
					"per constructor", tc.Constructor.Name(), schemaName)
		}
		matched[idx] = true
		w, err := buildCaseWitness(rd, &rd.Clauses[idx], tc)
		if err != nil {
			return nil, "", err
		}
		witnessByParam[tc.Param] = w
	}
	for i, m := range matched {
		if !m {
			return nil, "", fmt.Errorf(
				"equation for %q matches no constructor clause of schema %s — "+
					"not a constructor of %s",
				rd.Clauses[i].Constructor.Name(), schemaName, FormatType(rd.CarrierType))
		}
	}

	// Instantiate the schema's parameters: ∀-bound positionally,
	// free ones by term instantiation.
	w := WrapProp(tmpl.Principle)
	if len(tmpl.OuterParams) > 0 {
		args := make([]Term, len(tmpl.OuterParams))
		for i, p := range tmpl.OuterParams {
			wit, ok := witnessByParam[p]
			if !ok {
				return nil, "", fmt.Errorf(
					"schema %s quantifies a parameter %q no clause targets",
					schemaName, PrintTerm(p))
			}
			args[i] = wit
		}
		w = w.ConclForAllInsts(args...)
	}
	var frees []TermSubst
	for i := range tmpl.Cases {
		tc := &tmpl.Cases[i]
		if !tc.ParamBound {
			frees = append(frees, MakeTermSubst(tc.Param, witnessByParam[tc.Param]))
		}
	}
	if len(frees) > 0 {
		w = WrapProp(core.PropTermInst(w, frees...))
	}
	proved := w.Rewrite(DeepBeta)

	if tmpl.Unique {
		proved = prop.UniqueImpliesExists(proved)
		if proved == nil {
			return nil, "", fmt.Errorf(
				"schema %s: ∃!-elimination failed on the instantiated principle — "+
					"engine bug, report this shape", schemaName)
		}
	}
	// The curried shapes (v1.1): the instance speaks the CANONICAL
	// function (carrier → motive, λ-valued clauses); transfer it to
	// the author's spelling — currying uncurried, arguments back in
	// author order — before the final alignment.
	var exists Prop = proved
	if rd.curried() {
		transferred, err := transferCanonicalExistence(rd, proved)
		if err != nil {
			return nil, "", fmt.Errorf("schema %s: %v", schemaName, err)
		}
		exists = transferred
	}
	aligned := BridgeNormalize(rd.ExistsStmt, exists)
	if aligned == nil {
		return nil, "", fmt.Errorf(
			"schema %s's instance is not normalize-equivalent to the equations' "+
				"existence form\n  instance: %s\n  wanted:   %s",
			schemaName, PrintProp(exists), PrintProp(rd.ExistsStmt))
	}
	return aligned, schemaName, nil
}

// buildCaseWitness builds the parameter witness for one template case:
// λ over the case's slots, body = the user clause's canonized RHS with
// each slot's value (a pattern argument, or a recursive call at one)
// replaced by the slot's binder. For the curried shapes the body is
// additionally λ-wrapped over the clause's extra parameters — the
// result-type currying: a recursive slot then carries the MOTIVE type
// (extras → result), and the canonized RHS applies it to whatever the
// author's call passed (the nth-element class rides for free).
func buildCaseWitness(rd *RecursiveDefinition, uc *RecursiveClause, tc *tactic.RecursionCase) (Term, error) {
	if len(tc.CtorArgs) != len(uc.CtorArgs) {
		return nil, fmt.Errorf(
			"constructor %q: pattern has %d arguments, schema clause has %d",
			uc.Constructor.Name(), len(uc.CtorArgs), len(tc.CtorArgs))
	}
	avoid := []Term{uc.Rhs, rd.DefVar}
	for _, a := range uc.CtorArgs {
		avoid = append(avoid, a)
	}
	for _, v := range uc.ExtraParams {
		avoid = append(avoid, v)
	}
	binders := make([]VarTerm, len(tc.Slots))
	for j, slot := range tc.Slots {
		var ty HolType
		if slot.Recursive {
			ty = rd.ResultType
		} else {
			ty = uc.CtorArgs[slot.ArgIndex].Type()
		}
		b := Var(TermName(fmt.Sprintf("b%d", j)), ty).Core().(VarTerm).
			RenameToAvoid(avoid...)
		binders[j] = b
		avoid = append(avoid, b)
	}

	// Canonize: every recursive call spelled with the recursion
	// argument hoisted first (the reshuffle; identity for the
	// recursion-argument-first shapes), so a whole f̂(argᵢ) subterm
	// heads each call. The canonical function variable carries the
	// CANONICAL type (carrier → motive) — the author's f only spells
	// its own argument order.
	fHat := rd.DefVar
	if rd.RecArgPos > 0 {
		fHat = Var("f", MakeFun(rd.CarrierType, rd.ResultType)).
			Core().(VarTerm).RenameToAvoid(avoid...)
		avoid = append(avoid, fHat)
	}
	body := permuteRecCalls(uc.Rhs, rd.DefVar, fHat, rd.RecArgPos)
	// Recursive slots first (they consume whole f̂(argᵢ) subterms), bare
	// argument slots after.
	for j, slot := range tc.Slots {
		if !slot.Recursive {
			continue
		}
		call := Apply(fHat, uc.CtorArgs[slot.ArgIndex]).Core()
		body = replaceSubTerm(body, call, binders[j])
	}
	for j, slot := range tc.Slots {
		if slot.Recursive {
			continue
		}
		body = body.Substitute(MakeTermSubst(uc.CtorArgs[slot.ArgIndex], binders[j]))
	}

	if body.HasFree(rd.DefVar) || body.HasFree(fHat) {
		return nil, fmt.Errorf(
			"constructor %q: a recursive call in %q has no recursion slot in the "+
				"schema clause", uc.Constructor.Name(), PrintTerm(uc.Rhs))
	}
	// The clause's value at the motive: λ extras. body — the currying.
	for j := len(uc.ExtraParams) - 1; j >= 0; j-- {
		body = Abs(uc.ExtraParams[j], body)
	}
	for _, v := range body.Frees(nil) {
		if slices.IndexFunc(binders, v.EqualsVar) < 0 {
			return nil, fmt.Errorf(
				"constructor %q: argument %q is not passed to the schema clause's "+
					"parameter", uc.Constructor.Name(), PrintTerm(v))
		}
	}
	out := body
	for j := len(binders) - 1; j >= 0; j-- {
		out = Abs(binders[j], out)
	}
	return out, nil
}

// deriveDirectCharacterizing derives the characterizing theorem for a
// DIRECT-shape const from its stored definition. Given c with def thm
// ⊢ c = λx̄.body and a goal ∀ḡ. c(ḡ) = body′, it applies both sides
// at the GOAL's own binders (PropRightApply), β-reduces each level, and
// re-generalizes — so the derived form lands on the goal's binder
// names — then bridges any residual arrangement difference
// (prop.BridgeNormalize, the family.Derived alignment). Returns nil
// when the goal is not this const's characterizing shape (wrong head,
// arity past the λ-depth, body not normalize-equivalent).
func deriveDirectCharacterizing(c ConstTerm, goal Prop) Prop {
	return deriveDirect(c, goal, true)
}

// deriveDirectExact is deriveDirectCharacterizing without the
// normalize bridge: the derived form must be α-equal to the goal.
func deriveDirectExact(c ConstTerm, goal Prop) Prop {
	return deriveDirect(c, goal, false)
}

// deriveDirect is the shared derivation; bridge says whether a
// residual arrangement difference may be closed by BridgeNormalize.
func deriveDirect(c ConstTerm, goal Prop, bridge bool) Prop {
	if goal.NumHyps() != 0 {
		return nil
	}
	defThm := getDefThm(c)
	if defThm.IsZero() {
		return nil
	}
	binderList, matrix := DecomposesFORALL(goal.Conclusion())
	l, _, ok := MatchesEQ(matrix)
	if !ok {
		return nil
	}
	head, argTerms := MatchesApply(l)
	headConst, ok := head.AsConst()
	if !ok || headConst.Name() != c.Name() {
		return nil
	}
	// The goal's binders, needed both for the PropRightApply arguments (the
	// LHS application spine) and the re-generalization.
	binders := make([]VarTerm, 0, binderList.Size())
	for v := range binderList.Iter() {
		binders = append(binders, v)
	}
	args := make([]VarTerm, len(argTerms))
	for i, at := range argTerms {
		v, ok := at.AsVar()
		if !ok {
			return nil
		}
		args[i] = v
	}

	w := WrapProp(defThm)
	for _, v := range args {
		_, rhs, ok := MatchesEQ(w.Conclusion())
		if !ok {
			return nil
		}
		abs, isAbs := rhs.AsAbsTerm()
		if !isAbs {
			// Goal arity exceeds the definition's λ-depth.
			return nil
		}
		w = w.RightApply(v)
		w = w.Rewrite(DeepBetaAbs(abs))
	}
	for i := len(binders) - 1; i >= 0; i-- {
		w = w.ConclForAll(binders[i])
	}

	goalStmt := core.MakeProp(goal.Conclusion())
	if w.AlphaEquals(goalStmt) {
		return w
	}
	if !bridge {
		return nil
	}
	return BridgeNormalize(goalStmt, w)
}

// =======================================================================
// v1.1 — curried parameters
// =======================================================================
//
// The v1 compiler serves the single-argument recursion shape exactly.
// v1.1 extends it in two stages
// (three nested provers: raw = v1's exact-schema shape, then
// `canonize`, then `reshuffle`):
//
//   - v1.1a — result-type currying (`canonize`): recursion argument
//     first, extra curried parameters after it. Each clause
//     f(pat, v̄) = rhs canonizes to f(pat) = λv̄.rhs, the schema's
//     result type instantiates at the motive V̄ → R, and the clause
//     witness abstracts the function-typed recursive RESULT rather
//     than the applied call — which covers the nth-element class (the extra
//     argument CHANGES in the recursive call) for free.
//   - v1.1b — argument reshuffle (`reshuffle` + `scrub_def`): the
//     recursion argument is NOT first. The analyzer locates the
//     pattern position, the witness builder canonizes calls with the
//     recursion argument hoisted (permuteRecCalls), and the transfer
//     below re-derives the AUTHOR-order existence through a wrapper
//     witness λx̄. fn(x_p)(x̄ ∖ p) — all at the EXISTENCE level,
//     before any mint, so exactly one constant is ever created and
//     the permutation never reaches kernel state.
//
// The transfer (transferCanonicalExistence) is the blueprint's choose
// dance made explicit with the prop layer's own rules: Assume the
// canonical body, derive each author clause from its canonical
// conjunct (extract → orient → rename pattern vars → uncurry by
// application and β → β-expand onto the author matrix at
// the witness → re-∀-close in the author's binder order), ∧-fold in
// author order, ∃-introduce at the witness (InstExists), discharge
// the assumption (HypExists), and cut against the compiled
// instance (DeriveHypFrom). What persists — the characterizing
// theorem, the simp rules, the emitted DefEntry — speaks the author's
// argument order only.

// permuteRecCalls rewrites every recursive call in an author-form RHS
// into its canonical spelling: f(t₀,…,t_p,…,tⱼ) becomes
// f̂(t_p)(t₀,…,t̂_p,…,tⱼ) — the recursion argument hoisted to the
// front, every other argument (recursively transformed) kept in
// author order — where f̂ is the CANONICAL function variable (type
// carrier → motive; the author's f cannot spell the permuted call:
// its argument types are in author order). The identity when the
// recursion argument already comes first: the author's curried
// application at f itself IS the canonical spelling there.
func permuteRecCalls(t Term, defVar, fHat VarTerm, recPos int) Term {
	if recPos == 0 {
		return t
	}
	if _, ok := t.AsVar(); ok {
		return t
	}
	if abs, ok := t.AsAbsTerm(); ok {
		if abs.Var().EqualsVar(defVar) {
			return t // shadowed — inner occurrences are not the definiendum
		}
		b := permuteRecCalls(abs.Body(), defVar, fHat, recPos)
		if b == abs.Body() {
			return t
		}
		return Abs(abs.Var(), b)
	}
	head, args := MatchesApply(t)
	if len(args) == 0 {
		return t
	}
	if hv, ok := head.AsVar(); ok && hv.EqualsVar(defVar) {
		// Analysis validated len(args) ≥ recPos+1 and args[recPos] a
		// pattern argument.
		newArgs := make([]Term, 0, len(args))
		newArgs = append(newArgs, args[recPos])
		for i, a := range args {
			if i == recPos {
				continue
			}
			newArgs = append(newArgs, permuteRecCalls(a, defVar, fHat, recPos))
		}
		return Apply(fHat, newArgs...).Core()
	}
	newHead := permuteRecCalls(head, defVar, fHat, recPos)
	changed := newHead != head
	newArgs := make([]Term, len(args))
	for i, a := range args {
		newArgs[i] = permuteRecCalls(a, defVar, fHat, recPos)
		changed = changed || newArgs[i] != a
	}
	if !changed {
		return t
	}
	return Apply(newHead, newArgs...).Core()
}

// authorOrderWrapper builds λx₀…xₖ. fn(x_p)(x₀,…,x̂_p,…,xₖ) — the
// author-argument-order face of the canonical function: the reshuffle
// blueprint's assumed wrapper, spelled as an explicit ∃-witness term.
func authorOrderWrapper(rd *RecursiveDefinition, fnVar VarTerm) Term {
	xs := make([]VarTerm, len(rd.ArgTypes))
	avoid := []Term{fnVar}
	for i, ty := range rd.ArgTypes {
		x := Var(TermName(fmt.Sprintf("x%d", i)), ty).Core().(VarTerm).
			RenameToAvoid(avoid...)
		xs[i] = x
		avoid = append(avoid, x)
	}
	callArgs := make([]Term, 0, len(xs))
	callArgs = append(callArgs, xs[rd.RecArgPos])
	for i, x := range xs {
		if i == rd.RecArgPos {
			continue
		}
		callArgs = append(callArgs, x)
	}
	body := Apply(fnVar, callArgs...).Core()
	for i := len(xs) - 1; i >= 0; i-- {
		body = Abs(xs[i], body)
	}
	return body
}

// conjProject splits a conjunction-conclusion wrapper into one
// wrapper per ∧-spine leaf (left to right), each still carrying the
// hyps.
func conjProject(w *PropWrapper) []*PropWrapper {
	l, r, ok := MatchesAND(w.Conclusion())
	if !ok {
		return []*PropWrapper{w}
	}
	left := w.DeriveTrans(HypAND0(l, r))
	right := w.DeriveTrans(HypAND1(l, r))
	return append(conjProject(left), conjProject(right)...)
}

// transferCanonicalExistence turns the compiled CANONICAL existence
// ⊢ ∃fn. Canon(fn) — fn at carrier → motive, clauses λ-valued in the
// schema's arrangement — into the AUTHOR-form existence
// ⊢ ∃f. Property(f) the obligation states. Pure statement-level
// derivation, deterministic, no refuter (the compiler's discipline).
// Every "internal:" error is an engine fault, not an authoring error:
// the analysis accepted the equations and the schema accepted the
// witnesses, so the canonical instance must carry each author clause.
func transferCanonicalExistence(rd *RecursiveDefinition, proved Prop) (Prop, error) {
	abs := MatchesEXISTS(proved.Conclusion())
	if abs.IsZero() {
		return nil, fmt.Errorf("internal: compiled instance is not ∃-headed: %s",
			PrintTerm(proved.Conclusion()))
	}
	// The chosen function, renamed clear of every author name so the
	// ∀-closures and substitutions below can never collide with it.
	fnVar := abs.Var().RenameToAvoid(rd.Property, rd.DefVar)
	body := abs.Body()
	if !fnVar.EqualsVar(abs.Var()) {
		body = body.Substitute(MakeTermSubst(abs.Var(), fnVar))
	}

	// The author-order witness: the chosen function itself when the
	// recursion argument comes first; the reshuffle wrapper otherwise.
	var witness Term = fnVar
	if rd.RecArgPos > 0 {
		witness = authorOrderWrapper(rd, fnVar)
	}

	assumed := prop.Assume(body)
	stripped, _ := assumed.StripConclForAll()
	leaves := conjProject(stripped)
	if len(leaves) != len(rd.Clauses) {
		return nil, fmt.Errorf(
			"internal: canonical instance has %d conjuncts for %d clauses",
			len(leaves), len(rd.Clauses))
	}

	derived := make([]*PropWrapper, len(rd.Clauses))
	for _, leaf := range leaves {
		w, _ := leaf.StripConclForAll()
		l, r, ok := MatchesEQ(w.Conclusion())
		if !ok {
			return nil, fmt.Errorf("internal: canonical conjunct %q is not an equation",
				PrintTerm(w.Conclusion()))
		}
		// Orient: the fn-application side left (the schema may store a
		// clause flipped — num_recursion's base).
		appSide := l
		if !isCanonicalFnApp(l, fnVar) {
			if !isCanonicalFnApp(r, fnVar) {
				return nil, fmt.Errorf(
					"internal: neither side of canonical conjunct %q applies the "+
						"chosen function to a pattern", PrintTerm(w.Conclusion()))
			}
			w, appSide = w.EqSym(), r
		}
		_, fnArgs := MatchesApply(appSide)
		ctorHead, ctorArgTerms := MatchesApply(fnArgs[0])
		ctorConst, ok := ctorHead.AsConst()
		if !ok {
			return nil, fmt.Errorf("internal: canonical pattern %q has no constructor head",
				PrintTerm(fnArgs[0]))
		}
		idx := slices.IndexFunc(rd.Clauses, func(c RecursiveClause) bool {
			return c.Constructor.Name() == ctorConst.Name()
		})
		if idx < 0 || derived[idx] != nil {
			return nil, fmt.Errorf(
				"internal: canonical conjunct for %q matches no unserved author clause",
				ctorConst.Name())
		}
		uc := &rd.Clauses[idx]
		if len(ctorArgTerms) != len(uc.CtorArgs) {
			return nil, fmt.Errorf(
				"internal: constructor %q carries %d arguments in the instance, %d in "+
					"the clause", ctorConst.Name(), len(ctorArgTerms), len(uc.CtorArgs))
		}
		// Rename the schema's pattern variables to the author's.
		var substs []TermSubst
		for i, at := range ctorArgTerms {
			v, ok := at.AsVar()
			if !ok {
				return nil, fmt.Errorf("internal: instance pattern argument %q is not "+
					"a variable", PrintTerm(at))
			}
			if !v.EqualsVar(uc.CtorArgs[i]) {
				substs = append(substs, MakeTermSubst(v, uc.CtorArgs[i]))
			}
		}
		if len(substs) > 0 {
			w = w.TermInst(substs...)
		}
		// Uncurry: apply the clause's extra parameters and β-reduce —
		// PropRightApply per parameter, each followed by its β-step.
		for _, v := range uc.ExtraParams {
			w = w.RightApply(v)
		}
		w = w.RewriteConcl(DeepBeta)
		// Land on the author matrix at the witness. For the reshuffle
		// wrapper (and any author-written redex) the target carries
		// β-redexes the derived form has reduced — expand back through
		// the β-equality.
		_, matrix := DecomposesFORALL(uc.Equation.Conclusion())
		target := matrix.Substitute(MakeTermSubst(rd.DefVar, witness))
		if !w.Conclusion().AlphaEquals(target) {
			eq := DeepBeta(target)
			if eq == nil || !Rhs(eq).AlphaEquals(w.Conclusion()) {
				return nil, fmt.Errorf(
					"internal: clause %q did not land on its author form\n  derived: %s\n"+
						"  wanted:  %s", ctorConst.Name(),
					PrintTerm(w.Conclusion()), PrintTerm(target))
			}
			w = eq.EqSym().EqMP(w)
		}
		derived[idx] = w.ConclForAllList(uc.Binders...)
	}
	for i := range derived {
		if derived[i] == nil {
			return nil, fmt.Errorf("internal: no canonical conjunct served constructor %q",
				rd.Clauses[i].Constructor.Name())
		}
	}

	// ∧-fold in author order, matching Property's right-fold shape.
	acc := derived[len(derived)-1]
	for i := len(derived) - 2; i >= 0; i-- {
		pair := prop.ConclAND(derived[i].Conclusion(), acc.Conclusion())
		acc = acc.DeriveTrans(derived[i].DeriveTrans(pair))
	}
	// ∃-introduce the author statement at the witness, discharge the
	// canonical body (HypExists), and cut against the compiled instance.
	intro := prop.InstExists(rd.ExistsStmt.Conclusion(), witness)
	return acc.DeriveTrans(intro).HypExists(fnVar, body).DeriveHypFrom(proved), nil
}

// isCanonicalFnApp reports whether t is the chosen function applied to
// exactly one argument — the canonical clause's fn(pattern) side.
func isCanonicalFnApp(t Term, fnVar VarTerm) bool {
	head, args := MatchesApply(t)
	if len(args) != 1 {
		return false
	}
	v, ok := head.AsVar()
	return ok && v.EqualsVar(fnVar)
}
