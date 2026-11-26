// Each inductive type has an induction principle stated in the standard
// form every member statement is written in:
//
//   ∀P. ∀x. case_1 ∧ case_2 ∧ … ∧ case_k ⇒ P(x)
//
// where P : τ → bool is the predicate, x : τ the index, and each
// `case_i`, read along the antecedent's left ∧-spine, is a term of one
// of these shapes:
//
//   P(c)                                        -- base constructor, no args
//   ∀a₁ ... aₙ.   P(c(a₁,…,aₙ))                 -- non-recursive constructor with args
//   ∀a₁ ... aₙ.   P(rec₁) ⇒ … ⇒ P(recₘ) ⇒
//                  P(c(a₁,…,aₙ))                -- recursive constructor (each rec_j ∈ args
//                                                  and has type = IndexType)
//
// Examples:
//
//   num:    ∀P n. P(_0) ∧ (∀n. P(n) ⇒ P(suc n))      ⇒ P(n)
//   list:   ∀P l. P([]) ∧ (∀h t. P(t) ⇒ P(cons h t)) ⇒ P(l)
//   option: ∀P o. P(none) ∧ (∀a. P(some a))          ⇒ P(o)
//
// AnalyzeInductionPrinciple parses a Prop in this shape into an
// InductionTemplate that GeneralInductionTactic can drive. The analyzer
// is strict: anything that doesn't fit (a sequent, a prefix binding
// more than the predicate and the index, mixed-type IH args, a
// non-applied case conclusion, sub-conjunctions instead of ⇒-chains)
// returns an error, which the engine layer surfaces verbatim.
//
// The tactic is driven by the InductionTemplate.
// Each constructor of the type contributes one child subgoal whose hypotheses
// include the induction hypotheses for every recursive argument of that constructor.
//
// Examples (single-IH constructors):
//
//   num:    P(_0) | ∀n. P(n) ⇒ P(suc n)
//             child 0:                ⊢ P(_0)
//             child 1:   P(n)         ⊢ P(suc n)
//
//   list:   P([]) | ∀h t. P(t) ⇒ P(cons h t)
//             child 0:                ⊢ P([])
//             child 1:   P(t)         ⊢ P(cons h t)
//
//   option: P(none) | ∀a. P(some a)   (no IH; non-recursive constructor)
//             child 0:                ⊢ P(none)
//             child 1:                ⊢ P(some a)
//
// Hypothesis handling matches the num implementation: hyps that
// mention the induction variable are moved to the conclusion side as
// disjuncts before the split, then restored on the reconstructed
// theorem. Conclusion-quantified induction (`⊢ ∀x. body`) is also
// handled: the ∀x is stripped, induction runs on the body, and the
// reconstructed conclusion is re-quantified (re-ordering universals
// when needed to match the original goal).
//
// Reconstruction opens the principle into the sequent its cases
// discharge one by one (principleSequent):
//
//   case_1, …, case_k ⊢ P(x)
//
// After `TermInst(P := λx.concl, x := inductVar)` and beta-reduction,
// case_i becomes the original case_i with concl substituted in. We
// PromoteHyp each child's IH-hyps and ConclForAll each non-recursive
// argument to produce the matching case hyp, then DeriveHypFrom into
// the instantiated principle.

package tactic

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// InductionTemplate is the parsed structural model of an induction
// principle. It is purely a description (no proof obligation): every
// field is derived from Principle, and Principle stays the source of
// truth used at reconstruction time.
type InductionTemplate struct {
	// Principle is the induction theorem in the standard form,
	// e.g. ∀P x. P(_0) ∧ (∀n. P(n) ⇒ P(suc n)) ⇒ P(x). Typed core.Prop
	// (statement), NOT a realized ThmCert: a promise-backed principle
	// stays unforced here; the reconstruct threads it through
	// promise-transparent kernel ops, so it forces only when an
	// induction-using proof is itself forced.
	Principle core.Prop

	// PredicateVar is the predicate P the principle binds first: the
	// variable its cases and its conclusion apply. Type = IndexType → bool.
	PredicateVar VarTerm

	// IndexVar is the index x the principle binds after P, the variable
	// applied to P in its conclusion P(x). Type = IndexType.
	IndexVar VarTerm

	// IndexType is the inductive type being recursed over.
	IndexType core.HolType

	// Cases describes each case of Principle, in the order its
	// antecedent joins them (constructor order).
	Cases []InductionCase
}

// InductionCase is one constructor's obligation in the principle.
type InductionCase struct {
	// CaseHyp is the literal conjunct of Principle's antecedent.
	// E.g. for the suc case of num: `∀n. P(n) ⇒ P(suc n)`.
	CaseHyp core.Term

	// Args are the outermost ∀-bound variables of CaseHyp.
	// For base cases like `P(_0)` this is empty.
	// For `∀h t. P(t) ⇒ P(cons h t)` this is [h, t].
	Args []VarTerm

	// RecArgIndices index into Args, naming the recursive args (those
	// with type = IndexType that show up in IH hyps).
	// For `∀h t. P(t) ⇒ P(cons h t)` this is [1] (just t).
	// For base cases / non-recursive constructors this is empty.
	RecArgIndices []int

	// Constructor is the term P is applied to in the case-hyp's
	// innermost conclusion: P(Constructor).
	// For num's suc case: `suc(n)`. For list's cons case: `cons(h, t)`.
	// For base cases: `_0`, `[]`, etc.
	Constructor core.Term
}

// RecArgs returns the subset of Args at RecArgIndices.
func (c *InductionCase) RecArgs() []VarTerm {
	out := make([]VarTerm, len(c.RecArgIndices))
	for i, idx := range c.RecArgIndices {
		out[i] = c.Args[idx]
	}
	return out
}

// AnalyzeInductionPrinciple decomposes a HOL induction principle,
// stated in the standard form, into a structural template usable by
// GeneralInductionTactic.
//
// Strict shape requirements (return error on mismatch):
//   - thm states a closed theorem `∀P x. cases ⇒ P(x)`: no hypothesis
//     left of ⊢, a prefix binding exactly P and x, P.Type() = x.Type()
//     → bool, the consequent P(x).
//   - Each conjunct of cases, along its left ∧-spine, must be
//     `∀args. IH₁ ⇒ … ⇒ IHₘ ⇒ P(constructor)` where each IH_j has shape
//     `P(arg_j')` with arg_j' ∈ args of type x.Type().
//
// All non-num args (e.g. `h` in list's cons case) must NOT have type
// = IndexType, and all IH args MUST have type = IndexType — the
// analyzer enforces this so that the constructor's recursive vs
// non-recursive positions are statically identifiable.
// The principle is consumed at the STATEMENT level only (Conclusion /
// NumHyps); thm may therefore be a promise-backed core.Thm whose
// certificate is never forced here.
func AnalyzeInductionPrinciple(thm core.Prop) (*InductionTemplate, error) {
	if thm == nil {
		return nil, fmt.Errorf("nil induction principle")
	}
	if thm.NumHyps() > 0 {
		return nil, fmt.Errorf("principle states a sequent (%d hypotheses left of ⊢); a principle "+
			"is stated closed, ∀P x. case₁ ∧ … ∧ caseₖ ⇒ P(x)", thm.NumHyps())
	}
	prefix, body := ext.DecomposesFORALL(thm.Conclusion())
	antecedent, conclusion, ok := ext.MatchesIMPLY(body)
	if !ok {
		return nil, fmt.Errorf("principle body %q is not an implication; a principle is stated "+
			"∀P x. case₁ ∧ … ∧ caseₖ ⇒ P(x)", ext.PrintTerm(body))
	}
	predVar, indexVar, err := parsePrincipleConclusion(conclusion)
	if err != nil {
		return nil, fmt.Errorf("principle conclusion: %w", err)
	}
	indexType := indexVar.Type()
	binds := func(v VarTerm) bool {
		for b := range prefix.Iter() {
			if b.Equals(v) {
				return true
			}
		}
		return false
	}
	if prefix.Size() != 2 || !binds(predVar) || !binds(indexVar) {
		names := make([]string, 0, prefix.Size())
		for b := range prefix.Iter() {
			names = append(names, string(b.Name()))
		}
		return nil, fmt.Errorf("principle binds %v; a principle binds exactly its predicate %s and "+
			"its index %s", names, ext.PrintTerm(predVar), ext.PrintTerm(indexVar))
	}

	conjuncts := prop.LeftConjuncts(antecedent)
	cases := make([]InductionCase, 0, len(conjuncts))
	for _, h := range conjuncts {
		c, err := analyzeCase(h, predVar, indexType)
		if err != nil {
			return nil, fmt.Errorf("case %q: %w", ext.PrintTerm(h), err)
		}
		cases = append(cases, c)
	}

	return &InductionTemplate{
		Principle:    thm,
		PredicateVar: predVar,
		IndexVar:     indexVar,
		IndexType:    indexType,
		Cases:        cases,
	}, nil
}

// PrincipleNameCandidates returns the library name an inductive type's
// induction principle is served under: `<T>_induction` for every type —
// num, the datatype door's types (list_induction, option_induction,
// btree_induction, …) alike. It must show up in env.LibraryThms to be
// usable.
//
// Shared by the engine's tactic dispatch (record side) and
// Script.InductStep / Script.Induct (replay side) so both resolve a
// goal's induction principle identically.
func PrincipleNameCandidates(t core.HolType) []string {
	ct, ok := t.(core.CompositeType)
	if !ok {
		return nil
	}
	return []string{string(ct.Meta().Name()) + "_induction"}
}

// AnalyzePrincipleForType parses an induction principle and, if its
// index type doesn't match `targetType` directly, attempts to
// type-instantiate it (e.g. polymorphic `list_induction` for `list(A)`
// can be specialized to `list(num)`). Returns (nil, nil) when the
// principle's index type can't be unified with `targetType`.
func AnalyzePrincipleForType(thm core.Prop, targetType core.HolType) (*InductionTemplate, error) {
	tmpl, err := AnalyzeInductionPrinciple(thm)
	if err != nil {
		return nil, err
	}
	if tmpl.IndexType.Equals(targetType) {
		return tmpl, nil
	}
	// Try a type-variable match: principle.IndexType against targetType.
	substs, ok := tmpl.IndexType.Matches(targetType, func(core.VarType) bool { return true })
	if !ok {
		return nil, nil
	}
	// PropTypeInst is promise-transparent: a promise-backed principle stays a
	// promise after specialization. Re-analyze it at the statement level (no
	// .AsThmCert() collapse, which would force the cone here).
	specialized := core.PropTypeInst(thm, substs...)
	return AnalyzeInductionPrinciple(specialized)
}

// parsePrincipleConclusion expects `P(x)` with both P and x free vars
// and P.Type() = x.Type() → bool. Returns (P, x).
func parsePrincipleConclusion(concl core.Term) (VarTerm, VarTerm, error) {
	head, args := ext.MatchesApply(concl)
	if len(args) != 1 {
		return VarTerm{}, VarTerm{}, fmt.Errorf(
			"expected `P(x)`, got %q with %d args", ext.PrintTerm(concl), len(args))
	}
	predVar, ok := head.AsVar()
	if !ok {
		return VarTerm{}, VarTerm{}, fmt.Errorf(
			"expected `P(x)` with P a free var, got head %q", ext.PrintTerm(head))
	}
	indexVar, ok := args[0].AsVar()
	if !ok {
		return VarTerm{}, VarTerm{}, fmt.Errorf(
			"expected `P(x)` with x a free var, got argument %q", ext.PrintTerm(args[0]))
	}
	funTypes := ext.MatchesFun(predVar.Type())
	if len(funTypes) != 2 || !funTypes[1].Equals(core.TypeBool()) {
		return VarTerm{}, VarTerm{}, fmt.Errorf(
			"predicate %q must have type τ → bool, got %s",
			ext.PrintTerm(predVar), ext.FormatType(predVar.Type()))
	}
	if !funTypes[0].Equals(indexVar.Type()) {
		return VarTerm{}, VarTerm{}, fmt.Errorf(
			"predicate %q has domain %s; index %q has type %s",
			ext.PrintTerm(predVar), ext.FormatType(funTypes[0]),
			ext.PrintTerm(indexVar), ext.FormatType(indexVar.Type()))
	}
	return predVar, indexVar, nil
}

// analyzeCase parses one case-hyp into its (Args, RecArgIndices,
// Constructor) decomposition.
func analyzeCase(caseHyp core.Term, predVar VarTerm, indexType core.HolType) (InductionCase, error) {
	argList, body := ext.DecomposesFORALL(caseHyp)
	args := make([]VarTerm, 0, argList.Size())
	for v := range argList.Iter() {
		args = append(args, v)
	}

	// Walk the IH chain: `P(arg) ⇒ rest`.
	var recIndices []int
	for {
		lhs, rhs, ok := ext.MatchesIMPLY(body)
		if !ok {
			break
		}
		ihHead, ihArgs := ext.MatchesApply(lhs)
		if !ihHead.AlphaEquals(predVar) || len(ihArgs) != 1 {
			return InductionCase{}, fmt.Errorf(
				"IH hyp must have shape `P(arg)`, got %q", ext.PrintTerm(lhs))
		}
		ihVar, ok := ihArgs[0].AsVar()
		if !ok {
			return InductionCase{}, fmt.Errorf(
				"IH argument must be a bound variable, got %q", ext.PrintTerm(ihArgs[0]))
		}
		if !ihVar.Type().Equals(indexType) {
			return InductionCase{}, fmt.Errorf(
				"IH argument %q has type %s, expected %s",
				ext.PrintTerm(ihVar), ext.FormatType(ihVar.Type()), ext.FormatType(indexType))
		}
		idx := slices.IndexFunc(args, ihVar.EqualsVar)
		if idx < 0 {
			return InductionCase{}, fmt.Errorf(
				"IH argument %q is not among the ∀-bound args of the case",
				ext.PrintTerm(ihVar))
		}
		recIndices = append(recIndices, idx)
		body = rhs
	}

	// What remains must be `P(constructor)`.
	conclHead, conclArgs := ext.MatchesApply(body)
	if !conclHead.AlphaEquals(predVar) || len(conclArgs) != 1 {
		return InductionCase{}, fmt.Errorf(
			"case conclusion must be `P(constructor)`, got %q", ext.PrintTerm(body))
	}
	constructor := conclArgs[0]

	return InductionCase{
		CaseHyp:       caseHyp,
		Args:          args,
		RecArgIndices: recIndices,
		Constructor:   constructor,
	}, nil
}

// Build num type and related constants for verification.
// This mirrors what the DB would provide.
var (
	numMetaType = core.MakeMetaType("num", 0)
	numType     = core.MakeCompositeType(numMetaType)

	zeroConstMeta = core.MakeConstMeta("_0", numType)
	sucConstMeta  = core.MakeConstMeta("suc", MakeFun(numType, numType))

	_0  = core.MakeConstTerm(zeroConstMeta, numType)
	suc = core.MakeConstTerm(sucConstMeta, MakeFun(numType, numType))
)

// --- Polymorphic principles for the standard inductive types. ---
//
// These mirror the statements a datatype definition produces but
// constructed directly in Go. They're polymorphic over the element
// type (`var:A`); the engine's lookupInductionTemplate type-instantiates
// them per goal var at apply time. A test env serves them as axioms; the
// corpus serves the datatype door's entries, which state the same
// theorems.

// listMetaType, optionMetaType are the standard inductive type
// constructors with their canonical arities.
var (
	listMetaType   = core.MakeMetaType("list", 1)
	optionMetaType = core.MakeMetaType("option", 1)
)

// ListInductProp returns the polymorphic list induction principle:
//
//	∀P l. P([]) ∧ (∀h t. P(t) ⇒ P(cons h t)) ⇒ P(l)
func ListInductProp() Prop {
	elem := core.TypeA()
	listT := core.MakeCompositeType(listMetaType, elem)
	nilMeta := core.MakeConstMeta("nil", listT)
	consMeta := core.MakeConstMeta("cons", MakeFun(elem, MakeFun(listT, listT)))
	nilT := core.MakeConstTerm(nilMeta, listT)
	consT := core.MakeConstTerm(consMeta, MakeFun(elem, MakeFun(listT, listT)))
	P := Var("P", MakeFun(listT, TypeBool))
	l := Var("l", listT)
	h := Var("h", elem)
	t := Var("t", listT)
	Pl := P.Apply(l)
	Pnil := P.Apply(nilT)
	Pt := P.Apply(t)
	Pcons := P.Apply(ext.Apply(consT, h, t))
	step := ForAll(h)(ForAll(t)(Pt.Imply(Pcons)))
	return MakeProp(ForAll(P)(ForAll(l)(Pnil.And(step).Imply(Pl))))
}

// OptionInductProp returns the polymorphic option induction principle:
//
//	∀P o. P(none) ∧ (∀a. P(some a)) ⇒ P(o)
func OptionInductProp() Prop {
	elem := core.TypeA()
	optT := core.MakeCompositeType(optionMetaType, elem)
	noneMeta := core.MakeConstMeta("none", optT)
	someMeta := core.MakeConstMeta("some", MakeFun(elem, optT))
	noneT := core.MakeConstTerm(noneMeta, optT)
	someT := core.MakeConstTerm(someMeta, MakeFun(elem, optT))
	P := Var("P", MakeFun(optT, TypeBool))
	o := Var("o", optT)
	a := Var("a", elem)
	Po := P.Apply(o)
	Pnone := P.Apply(noneT)
	Psome := P.Apply(ext.Apply(someT, a))
	return MakeProp(ForAll(P)(ForAll(o)(Pnone.And(ForAll(a)(Psome)).Imply(Po))))
}

// GeneralInductionTactic applies structural induction on inductVar
// using the given InductionTemplate. The template's IndexType must
// equal inductVar.Type() — callers (engine dispatch) enforce this and
// the tactic asserts it.
//
// Returns nil-producing tactic if inductVar isn't free anywhere in
// the goal AND the goal's conclusion doesn't bind a ∀-variable
// matching inductVar.
func GeneralInductionTactic(inductVar core.VarTerm, tmpl *InductionTemplate) Tactic {
	if tmpl == nil || inductVar.IsZero() {
		return nilTactic
	}
	Assert(inductVar.Type().Equals(tmpl.IndexType))

	return func(goal Prop) *SubGoals {
		target, ok := inductionTargetOf(goal, inductVar)
		if !ok {
			return nil
		}
		concl, movedGoal, movedHyps := target.concl, target.moved, target.movedHyps
		univQuantifiedInductVar := target.univQuantified

		// Per-case data computed at apply time so fresh-var renames
		// can avoid collisions with inductVar and the goal's frees.
		type caseData struct {
			freshArgs   []VarTerm // args after RenameToAvoid (in template order)
			recArgs     []VarTerm // subset of freshArgs at RecArgIndices
			constructor core.Term // template Constructor under args→freshArgs
			ihHyps      []core.Term
			childGoalW  *PropWrapper
		}

		cases := make([]caseData, len(tmpl.Cases))
		for i, c := range tmpl.Cases {
			freshArgs := target.caseArguments(inductVar, c)
			argSubsts := make([]core.TermSubst, 0, len(c.Args))
			for j, a := range c.Args {
				if !freshArgs[j].Equals(a) {
					argSubsts = append(argSubsts, core.MakeTermSubst(a, freshArgs[j]))
				}
			}

			constructor := c.Constructor
			if len(argSubsts) > 0 {
				constructor = constructor.Substitute(argSubsts...)
			}

			recArgs := make([]VarTerm, len(c.RecArgIndices))
			for j, idx := range c.RecArgIndices {
				recArgs[j] = freshArgs[idx]
			}

			// Child concl = concl[constructor / inductVar].
			childConcl := concl.Substitute(core.MakeTermSubst(inductVar, constructor))

			// IH hyps = concl[recArg / inductVar] for each recArg.
			ihHyps := make([]core.Term, len(recArgs))
			for j, r := range recArgs {
				ihHyps[j] = concl.Substitute(core.MakeTermSubst(inductVar, r))
			}

			childHyps := append([]Term{}, ihHyps...)
			childHyps = append(childHyps, movedGoal.Hyps()...)
			cases[i] = caseData{
				freshArgs:   freshArgs,
				recArgs:     recArgs,
				constructor: constructor,
				ihHyps:      ihHyps,
				childGoalW:  WrapProp(core.MakeProp(childConcl, childHyps...)),
			}
		}

		childGoals := make([]Prop, len(cases))
		for i, cd := range cases {
			childGoals[i] = cd.childGoalW.AsProp()
		}

		reconstruct := func(thms ...Prop) Prop {
			// Open the principle into its sequent, instantiate P with
			// λinductVar.concl and the index with inductVar, then
			// beta-reduce. The sequent's hyps then have the shape we
			// expect each case's reconstructed proof to match.
			predicate := core.Abs(inductVar, concl)
			inductionInst := principleSequent(tmpl.Principle).
				TermInst(
					core.MakeTermSubst(tmpl.PredicateVar, predicate),
					core.MakeTermSubst(tmpl.IndexVar, inductVar)).
				Rewrite(prop.DeepBetaAbs(predicate))

			result := inductionInst
			for i, cd := range cases {
				caseProof := prop.WrapProp(prop.WeakenTo(thms[i], cd.childGoalW))
				// PromoteHyp each IH hyp (reverse order so the result's
				// implication chain ends up `IH_1 ⇒ … ⇒ IH_m ⇒ concl`).
				for j := len(cd.ihHyps) - 1; j >= 0; j-- {
					caseProof = caseProof.PromoteHyp(cd.ihHyps[j])
				}
				// ConclForAll each arg (reverse order so outermost
				// quantifier corresponds to the first template arg).
				for j := len(cd.freshArgs) - 1; j >= 0; j-- {
					caseProof = caseProof.ConclForAll(cd.freshArgs[j])
				}
				result = result.DeriveHypFrom(caseProof)
			}

			if univQuantifiedInductVar {
				result = result.ConclForAll(inductVar)
				if !result.Conclusion().AlphaEquals(goal.Conclusion()) {
					// The order of the univ quantifiers might be
					// different; reorder to match the original goal.
					result = prop.ReorderForAll(result.Conclusion(), goal.Conclusion()).
						EqMP(result)
				}
				return result
			}

			// Move the disjunctive ¬h components back to hypothesis side.
			// principle's TermInst with predicate λx.concl + DeepBetaAbs
			// may α-rename bound vars inside h's negation to avoid
			// capture by a case's bound ∀-args. Refresh h to the
			// α-variant actually present in the OR chain; otherwise
			// MoveConclDisjComponentToHyp's post-rearrangement Equals
			// check fails.
			//
			// Pick the *last* ¬h in the disjunct chain, not the first.
			// MoveHypsToConcl appends ¬h to the right (BinaryThms
			// "(p ⇒ q) ⇔ (¬p ∨ q)" then CommuteOR), so the appended
			// copy is always at the rightmost end. If the goal's
			// original concl already contains ¬h as a literal disjunct
			// (e.g. a post-case_split shape `eq ⊢ ¬eq ∨ X`),
			// IndexFunc's first-match would peel the original disjunct
			// instead of the appended one, leaving result.Conclusion()
			// permuted vs goal.Conclusion() and failing IsStronger's
			// α-equals check in MakeSubGoals.
			for _, h := range movedHyps {
				nh := ext.Not(h)
				if result.Conclusion().AlphaEquals(nh) {
					result = result.MoveConclDisjComponentToHyp(h)
					continue
				}
				components := ext.DecomposesOR(result.Conclusion())
				i := -1
				for j := len(components) - 1; j >= 0; j-- {
					if nh.AlphaEquals(components[j]) {
						i = j
						break
					}
				}
				Assert(i >= 0)
				result = prop.ArrangeORChain(result.Conclusion(), -1, i).EqMP(result)
				result = result.MoveConclDisjComponentToHyp(ext.MatchesNOT(components[i]))
			}

			return result
		}

		return MakeSubGoals(goal, reconstruct, childGoals...)
	}
}

// principleSequent opens a principle stated in the standard form into
// the sequent its cases discharge one by one, `case₁, …, caseₖ ⊢ P(x)`
// with P and x free: the prefix instantiated at its own binders, the
// antecedent assumed and split along its left ∧-spine. Promise-
// transparent: a promise-backed principle stays unforced.
func principleSequent(principle core.Prop) *PropWrapper {
	opened, _ := prop.WrapProp(principle).StripConclForAll()
	antecedent, _, ok := ext.MatchesIMPLY(opened.Conclusion())
	Assert(ok)
	cases := prop.LeftConjuncts(antecedent)
	all := make([]int, len(cases))
	for i := range all {
		all[i] = i
	}
	return opened.DemoteHyp().DeriveHypFrom(prop.ConjunctionFromPieces(cases, all))
}

// inductionTarget is what an induction runs over once the goal is
// prepared: the conclusion the predicate is abstracted from, the goal
// with the hypotheses mentioning the induction variable moved to the
// conclusion side, those hypotheses, and whether the induction variable
// was ∀-bound in the conclusion rather than free. Computed once by the
// tactic and once more by whoever asks what a case minted
// (InductionCaseArguments) — the same preparation, so the two agree.
type inductionTarget struct {
	concl          Term
	moved          *PropWrapper
	movedHyps      []Term
	univQuantified bool
}

// inductionTargetOf prepares goal for induction on inductVar. ok is
// false when inductVar occurs nowhere the tactic can induct on: neither
// free in the goal nor ∀-bound in its conclusion.
func inductionTargetOf(goal Prop, inductVar VarTerm) (inductionTarget, bool) {
	concl := goal.Conclusion()

	// Check whether inductVar is free anywhere in the goal
	// (conclusion + hyps).
	isFree := concl.HasFree(inductVar) ||
		goal.AnyHyp(func(h Term) bool { return h.HasFree(inductVar) })

	target := inductionTarget{moved: WrapProp(goal)}
	inductVarInHyp := func(h Term) bool { return h.HasFree(inductVar) }

	if isFree {
		// Free-var path: move hyps containing inductVar to
		// conclusion side, then induct over the extended conclusion.
		// e.g. Q(n) ⊢ P(n) becomes ⊢ P(n) ∨ ¬Q(n)
		// e.g. Q(n), h ⊢ ⊥ becomes h ⊢ ¬Q(n)
		target.moved = target.moved.MoveHypsToConcl(inductVarInHyp)
		for h := range goal.HypIter() {
			if inductVarInHyp(h) {
				target.movedHyps = append(target.movedHyps, h)
			}
		}
		target.concl = target.moved.Conclusion()
	} else {
		// Fallback: inductVar is not free anywhere. Check if the
		// conclusion has a ∀-bound variable matching inductVar.
		// e.g. ⊢ ∀n:num. P(n)
		vars, body := ext.DecomposesFORALL(concl)
		if !body.HasFree(inductVar) {
			return inductionTarget{}, false
		}
		restVars := make([]Term, 0, vars.Size())
		inductVarInd := -1
		for i := range vars.Size() {
			if vars.Ind(i).Equals(inductVar) {
				inductVarInd = i
			} else {
				restVars = append(restVars, vars.Ind(i))
			}
		}
		if inductVarInd == -1 {
			return inductionTarget{}, false
		}
		target.concl = ForAll(restVars...)(body)
		target.univQuantified = true
	}

	Assert(target.concl.HasFree(inductVar))
	return target, true
}

// caseArguments mints the variables one case of the principle
// introduces, in the case's own argument order. The first recursive
// argument IS inductVar (so the induction hypothesis ends up as
// concl[inductVar/inductVar] = concl, the num convention); every other
// argument is the principle's binder renamed away from anything it
// must not collide with — the conclusion, inductVar, the goal's
// remaining hypotheses, and the arguments minted before it.
func (t inductionTarget) caseArguments(inductVar VarTerm, c InductionCase) []VarTerm {
	// Avoid-frontier base: anything an arg's fresh name must NOT
	// collide with. inductVar is reserved for the case's primary
	// recursive arg, so it's included here to push other (non-rec) args
	// away from it. Per-case scoped: each case's args are independent
	// free vars in their own subgoal.
	avoid := []core.Term{t.concl, inductVar}
	for _, h := range t.moved.Hyps() {
		avoid = append(avoid, h)
	}
	primaryRec := -1
	if len(c.RecArgIndices) > 0 {
		primaryRec = c.RecArgIndices[0]
	}
	fresh := make([]VarTerm, len(c.Args))
	for j, a := range c.Args {
		if j == primaryRec {
			fresh[j] = inductVar
		} else {
			fresh[j] = a.RenameToAvoid(avoid...)
		}
		// Subsequent args in this case must also avoid this one.
		avoid = append(avoid, fresh[j])
	}
	return fresh
}

// InductionCaseArguments reports the variables GeneralInductionTactic
// minted for case i of tmpl when it split goal on inductVar: the
// constructor's arguments in the principle's order, the primary
// recursive one being inductVar itself. It runs the tactic's own
// preparation and minting, so what it returns is what the i-th child
// goal carries — the way a proof layer can name a step's head and tail
// without re-deriving the rename. nil when the tactic would not apply
// to goal, or when the case introduces no argument.
func InductionCaseArguments(goal Prop, inductVar VarTerm, tmpl *InductionTemplate, i int) []VarTerm {
	if tmpl == nil || inductVar.IsZero() || i < 0 || i >= len(tmpl.Cases) {
		return nil
	}
	target, ok := inductionTargetOf(goal, inductVar)
	if !ok {
		return nil
	}
	return target.caseArguments(inductVar, tmpl.Cases[i])
}

// InductionCaseHypotheses reports the induction hypotheses
// GeneralInductionTactic grants case i of tmpl when it splits goal on
// inductVar: one per RECURSIVE constructor argument, in the
// constructor's argument order — the conclusion at that argument,
// which is what the i-th child goal carries as a hypothesis. It runs
// the tactic's own preparation and minting (InductionCaseArguments), so
// a proof layer can hand a step's hypotheses to its branch by CONTENT
// rather than by their position among the child's hypotheses. nil when
// the tactic would not apply to goal, or when the case grants none (a
// base case, a constructor with no recursive argument).
func InductionCaseHypotheses(goal Prop, inductVar VarTerm, tmpl *InductionTemplate, i int) []core.Term {
	if tmpl == nil || inductVar.IsZero() || i < 0 || i >= len(tmpl.Cases) {
		return nil
	}
	target, ok := inductionTargetOf(goal, inductVar)
	if !ok {
		return nil
	}
	c := tmpl.Cases[i]
	args := target.caseArguments(inductVar, c)
	out := make([]core.Term, 0, len(c.RecArgIndices))
	for _, idx := range c.RecArgIndices {
		out = append(out, target.concl.Substitute(core.MakeTermSubst(inductVar, args[idx])))
	}
	return out
}
