package omega

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Products on ℕ: a product is zero exactly where a factor is.
//
// To the linear core a product of two unknowns is one more unknown, and ℕ
// has no products pass to say otherwise. ℤ and ℝ read a zero product through
// MulEqZero's hypothesis split and a product's sign through their sign rows;
// on ℕ both are one law, `m * n = 0 ⇔ m = 0 ∨ n = 0` (MulEqZero), since
// there a term is positive exactly where it is not zero:
//
//   - a hypothesis `a * b = 0`, or `0 = a * b`, splits into `a = 0 ∨ b = 0`
//     (natProductZeroSplit, one of hypSplittable's shapes). A square's two
//     guards are one guard, and the split has one case (splitByCases);
//   - a product whose factors are positive is positive: for each product of
//     the sequent — the goal's and the hypotheses' alike — with both factors
//     shown positive, `0 < a * b` joins the enrichment's facts
//     (natPositiveProducts) for one more linear run and for the case
//     split, which read from it `1 ≤ a * b`, `a * b ≠ 0` and, in the
//     branch of its monus, `suc(a * b − 1) = a * b`.
//
// A factor is shown positive by the linear prover, by a resident `t ≠ 0`,
// or, itself a product, by its own factors. Nothing here re-enters the
// decide chain.

// natProductZeroEq matches a hypothesis `a * b = 0` / `0 = a * b`.
func natProductZeroEq(h Term) (a, b Term, ok bool) {
	l, r, isEq := ext.MatchesEQ(h)
	if !isEq || !isNat(l) {
		return nil, nil, false
	}
	if isZeroNum(r) {
		if x, y, ok := MatchesStar(l); ok {
			return x, y, true
		}
	}
	if isZeroNum(l) {
		if x, y, ok := MatchesStar(r); ok {
			return x, y, true
		}
	}
	return nil, nil, false
}

// natMulEqZero is MulEqZero at a and b: `⊢ (a * b = 0) ⇔ (a = 0 ∨ b = 0)`;
// nil where the bundle holds no MulEqZero.
func natMulEqZero(a, b Term) *prop.PropWrapper {
	thm := mulEqZeroThm()
	if thm == nil {
		return nil
	}
	iff := instAll(thm, []Term{a, b})
	want := eqT(eqT(star(a, b), natZero), or(eqT(a, natZero), eqT(b, natZero)))
	if !iff.Conclusion().AlphaEquals(want) {
		panic(fmt.Sprintf("omega: the nat bundle's MulEqZero does not read `%s`: %s",
			ext.PrintTerm(want), ext.PrintTerm(iff.Conclusion())))
	}
	return iff
}

// natProductZeroSplit is the split of a hypothesis h, `a * b = 0` in either
// orientation, into `a = 0 ∨ b = 0`.
func natProductZeroSplit(h Term) (splittableAtom, bool) {
	a, b, ok := natProductZeroEq(h)
	if !ok {
		return splittableAtom{}, false
	}
	iff := natMulEqZero(a, b)
	if iff == nil {
		return splittableAtom{}, false
	}
	product := prop.Assume(h) // {h} ⊢ a * b = 0
	if l, _, _ := ext.MatchesEQ(h); isZeroNum(l) {
		product = product.EqSym()
	}
	za, zb := eqT(a, natZero), eqT(b, natZero)
	return splittableAtom{
		atom:      h,
		disjProof: iff.EqMP(product), // {h} ⊢ a = 0 ∨ b = 0
		branches: [2]splitBranch{
			{guard: za, facts: []*prop.PropWrapper{prop.Assume(za)}},
			{guard: zb, facts: []*prop.PropWrapper{prop.Assume(zb)}},
		},
	}, true
}

// natPositiveProducts lists `Γ ⊢ 0 < t`, Γ ⊆ hyps, for the products of
// the hypotheses and the goal whose factors are shown positive, and for
// their powers of a base shown positive.
func natPositiveProducts(hyps []Term, goal Term) []*prop.PropWrapper {
	if mulEqZeroThm() == nil || posIffNonzeroThm() == nil {
		return nil
	}
	productOrPower := func(t Term) bool { return isNatSymbolicProduct(t) || isNatSymbolicPower(t) }
	var facts []*prop.PropWrapper
	for _, t := range collectBinderFreeSubterms(append(slices.Clone(hyps), goal), productOrPower) {
		if slices.ContainsFunc(hyps, lt(natZero, t).AlphaEquals) {
			continue
		}
		if w := natProvePositive(hyps, t); w != nil {
			facts = append(facts, w)
		}
	}
	return facts
}

// natZeroPowerFacts lists, for each hypothesis `nat_pow(b, e) = 0` in
// either orientation, what it says of the base and the exponent:
// `{h} ⊢ b = 0` and `{h} ⊢ 0 < e` (PowEqZero).
func natZeroPowerFacts(hyps []Term) []*prop.PropWrapper {
	if powEqZeroThm() == nil || posIffNonzeroThm() == nil {
		return nil
	}
	var facts []*prop.PropWrapper
	for _, h := range hyps {
		power, turned, ok := zeroSidedEq(h, isZeroNum)
		if !ok {
			continue
		}
		base, exponent, ok := MatchesExp(power)
		if !ok {
			continue
		}
		isZero := prop.Assume(h) // {h} ⊢ nat_pow(b, e) = 0
		if turned != nil {
			isZero = turned.EqMP(isZero)
		}
		baseZero, exponentNonzero := eqT(base, natZero), not(eqT(exponent, natZero))
		iff := instAll(powEqZeroThm(), []Term{base, exponent})
		if want := eqT(eqT(power, natZero), ext.Apply(prop.AND, baseZero, exponentNonzero)); !iff.Conclusion().AlphaEquals(want) {
			panic(fmt.Sprintf("omega: the nat bundle's PowEqZero does not read `%s`: %s",
				ext.PrintTerm(want), ext.PrintTerm(iff.Conclusion())))
		}
		parts := splitConjuncts(iff.EqMP(isZero)) // {h} ⊢ b = 0, {h} ⊢ ¬(e = 0)
		for _, fact := range []*prop.PropWrapper{parts[0], natPosIffNonzero(exponent).EqMP(parts[1])} {
			if !slices.ContainsFunc(hyps, fact.Conclusion().AlphaEquals) {
				facts = append(facts, fact)
			}
		}
	}
	return facts
}

// isNatSymbolicPower reports whether t is a power whose exponent is no
// numeral: the power the linear core reads as an unknown.
func isNatSymbolicPower(t Term) bool {
	_, exponent, ok := MatchesExp(t)
	return ok && !isNumeralLit(exponent)
}

// isNatSymbolicProduct reports whether t is a product of two terms neither
// of which is a numeral: the product the linear core reads as an unknown.
func isNatSymbolicProduct(t Term) bool {
	a, b, ok := MatchesStar(t)
	return ok && !isNumeralLit(a) && !isNumeralLit(b)
}

// natProvePositive proves `Γ ⊢ 0 < t`, Γ ⊆ hyps: a product by its
// factors, any other term by the linear prover or a resident `t ≠ 0`, and
// a power by its base where neither shows it. nil where t is not shown
// positive.
func natProvePositive(hyps []Term, t Term) *prop.PropWrapper {
	goal := lt(natZero, t)
	if a, b, ok := MatchesStar(t); ok {
		pa, pb := natProvePositive(hyps, a), natProvePositive(hyps, b)
		if pa == nil || pb == nil {
			return nil
		}
		return natProductPositive(a, b, pa, pb)
	}
	if w, ok := proveLinThenInt(slices.Values(hyps), goal); ok {
		return w
	}
	if w := natResidentPositive(hyps, t); w != nil {
		return w
	}
	if base, exponent, ok := MatchesExp(t); ok && powPositiveThm() != nil {
		if positive := natProvePositive(hyps, base); positive != nil {
			return natPowerPositive(base, exponent, positive)
		}
	}
	return nil
}

// natPowerPositive is `Γ ⊢ 0 < nat_pow(base, exponent)` from positive,
// `Γ ⊢ 0 < base` (PowPositive: a power is positive where its base is not
// zero or its exponent is).
func natPowerPositive(base, exponent Term, positive *prop.PropWrapper) *prop.PropWrapper {
	nonzero, exponentZero := not(eqT(base, natZero)), eqT(exponent, natZero)
	power := ext.Apply(natExp, base, exponent)
	iff := instAll(powPositiveThm(), []Term{base, exponent})
	if want := eqT(lt(natZero, power), or(nonzero, exponentZero)); !iff.Conclusion().AlphaEquals(want) {
		panic(fmt.Sprintf("omega: the nat bundle's PowPositive does not read `%s`: %s",
			ext.PrintTerm(want), ext.PrintTerm(iff.Conclusion())))
	}
	either := natNonzero(base, positive).DeriveTrans(prop.ConclOR0(nonzero, exponentZero)) // Γ ⊢ ¬(base = 0) ∨ exponent = 0
	return iff.EqSym().EqMP(either)
}

// natResidentPositive proves `{h} ⊢ 0 < t` from a hypothesis h that
// states `t ≠ 0` in either orientation; nil where none does.
func natResidentPositive(hyps []Term, t Term) *prop.PropWrapper {
	for _, h := range hyps {
		inner := ext.MatchesNOT(h)
		if inner == nil {
			continue
		}
		l, r, ok := ext.MatchesEQ(inner)
		if !ok {
			continue
		}
		switch {
		case l.AlphaEquals(t) && isZeroNum(r):
			return natPosIffNonzero(t).EqMP(prop.Assume(h))
		case r.AlphaEquals(t) && isZeroNum(l):
			// {¬(0 = t)} ⊢ ¬(t = 0), the equation turned under the negation.
			turned := prop.Assume(eqT(t, natZero)).EqSym().Contraposition(eqT(t, natZero)).DeriveHypFrom(prop.Assume(h))
			return natPosIffNonzero(t).EqMP(turned)
		}
	}
	return nil
}

// natPosIffNonzero is PosIffNonzero at t: `⊢ ¬(t = 0) ⇔ 0 < t`.
func natPosIffNonzero(t Term) *prop.PropWrapper {
	iff := instAll(posIffNonzeroThm(), []Term{t})
	want := eqT(not(eqT(t, natZero)), lt(natZero, t))
	if !iff.Conclusion().AlphaEquals(want) {
		panic(fmt.Sprintf("omega: the nat bundle's PosIffNonzero does not read `%s`: %s",
			ext.PrintTerm(want), ext.PrintTerm(iff.Conclusion())))
	}
	return iff
}

// natProductPositive is `Γ ⊢ 0 < a * b` from pa, `Γ ⊢ 0 < a`, and pb,
// `Γ ⊢ 0 < b`: were the product zero a factor would be (MulEqZero), and
// neither is.
func natProductPositive(a, b Term, pa, pb *prop.PropWrapper) *prop.PropWrapper {
	za, zb := eqT(a, natZero), eqT(b, natZero)
	isZero := eqT(star(a, b), natZero)
	// refuted is `Γ ⊢ z ⇒ ⊥` for a factor's z, from its positivity.
	refuted := func(t, z Term, positive *prop.PropWrapper) *prop.PropWrapper {
		nonzero := natPosIffNonzero(t).EqSym().EqMP(positive) // Γ ⊢ ¬z
		contra := prop.WrapProp(nonzero.MaybeDeriveTrans(prop.Contradict(z)))
		return contra.PromoteHyp(z)
	}
	factor := natMulEqZero(a, b).EqMP(prop.Assume(isZero)) // {a * b = 0} ⊢ a = 0 ∨ b = 0
	contra := prop.ByCases(prop.F, za, zb).
		DeriveHypFrom(factor).
		DeriveHypFrom(refuted(a, za, pa))
	if !za.AlphaEquals(zb) { // a square's two cases are one
		contra = contra.DeriveHypFrom(refuted(b, zb, pb))
	}
	// contra is Γ, a * b = 0 ⊢ ⊥.
	return natPosIffNonzero(star(a, b)).EqMP(contra.NegHyp(isZero))
}
