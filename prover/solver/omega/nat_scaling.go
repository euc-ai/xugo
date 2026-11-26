package omega

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Scaling a comparison by a common factor, and cancelling one, on ℕ.
//
// To the linear core `c * a` and `c * b` are two unknowns, and no
// combination of rows relates them to a and b: that takes a row scaled by
// the term c. ℤ and ℝ scale a goal through their monotone handlers and
// cancel from a hypothesis through their cancellation; this is ℕ's pair.
// Both read a comparison `l ⋈ r` by the factors its two sides share
// (shared_factors.go): with P their product and a, b the products of what
// is left of each side, the comparison is `P * a ⋈ P * b`. A side that is
// itself one of the other's factors leaves 1.
//
//   - A goal `l ≤ r` or `l < r` (natProveScaled) follows from `a ⋈ b`, for
//     `<` with P shown positive. Two products with no factor in common
//     follow from their factors compared pairwise, `a * c ≤ b * d` from
//     `a ≤ b` and `c ≤ d`. A goal that is no comparison of two products
//     follows from the hypotheses' comparisons scaled by the cofactors
//     the sequent spells beside them (natHypScalings).
//   - A hypothesis `l = r` or `l ≤ r` (natCancelFacts) gives `a ⋈ b` where
//     P is shown positive; a hypothesis `l < r` gives `a < b` and `0 < P`
//     outright, a product with a zero factor being below nothing.
//   - A goal `a ⋈ b` follows from `P * a ⋈ P * b` as well where the
//     hypotheses prove that linearly and state it in no one of them
//     (natProveCancelled): two equations with a side in common,
//     `n * n = p * a ∧ n * n = p * b ⊢ a = b`. The factors tried are the
//     ones that put both scaled sides among the products the hypotheses
//     spell.
//
// The scaled and the cancelled comparison are facts for the linear prover,
// which reads a product up to the order and the grouping of its factors,
// so no spelling of the product is asked for.
//
// Positivity is natProvePositive's: the linear prover, a resident `t ≠ 0`,
// a product by its factors, a power by its base. Nothing here re-enters
// the decide chain.

// natNonzero is `Γ ⊢ ¬(t = 0)` from positive, `Γ ⊢ 0 < t`.
func natNonzero(t Term, positive *prop.PropWrapper) *prop.PropWrapper {
	return natPosIffNonzero(t).EqSym().EqMP(positive)
}

// natOrderAtom reads t as `l ≤ r` or `l < r` over ℕ.
func natOrderAtom(t Term) (l, r Term, strict, ok bool) {
	if a, b, m := MatchesLe(t); m {
		return a, b, false, true
	}
	if a, b, m := MatchesLt(t); m {
		return a, b, true, true
	}
	return nil, nil, false, false
}

// natOrder is `a ≤ b`, or `a < b` for strict.
func natOrder(a, b Term, strict bool) Term {
	if strict {
		return lt(a, b)
	}
	return le(a, b)
}

// natProveScaled proves `{hyps} ⊢ goal` for a `≤` or `<` goal that the
// scaling of a comparison of its sides' remaining factors makes linear.
func natProveScaled(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	l, r, strict, ok := natOrderAtom(goal)
	if !ok || posIffNonzeroThm() == nil {
		return nil, false
	}
	facts := natScalingFacts(hyps, l, r, strict)
	if len(facts) == 0 {
		return nil, false
	}
	return enrichAndCut(func(h []Term) (*prop.PropWrapper, bool) {
		return proveLinThenInt(slices.Values(h), goal)
	}, hyps, facts)
}

// natScalingFacts lists the scaled comparisons `l ⋈ r` may follow from
// linearly. Where the sides share a factor, the one comparison of what is
// left, or nothing where that is not shown. Otherwise the hypotheses'
// comparisons scaled by the cofactors in sight, and beside them, for two
// products, the pair that compares them factor by factor, and for sums
// the scaled comparison of each summand of l with each summand of r that
// shares a factor with it.
func natScalingFacts(hyps []Term, l, r Term, strict bool) []*prop.PropWrapper {
	if shared, restL, restR := natDomain.sharedFactors(l, r); len(shared) > 0 {
		w := natScaled(hyps, natDomain.productOf(shared), natDomain.productOf(restL), natDomain.productOf(restR), strict)
		if w == nil {
			return nil
		}
		return []*prop.PropWrapper{w}
	}
	facts := natHypScalings(hyps, l, r)
	if left, right := natSummands(l), natSummands(r); len(left) > 1 || len(right) > 1 {
		return append(facts, natSummandScalings(hyps, left, right)...)
	}
	la, ra, okL := MatchesStar(l)
	lb, rb, okR := MatchesStar(r)
	if strict || !okL || !okR {
		return facts
	}
	// la * ra ≤ x * y from la ≤ x and ra ≤ y: ra * la ≤ ra * x ≤ x * y.
	for _, side := range [][2]Term{{lb, rb}, {rb, lb}} {
		x, y := side[0], side[1]
		first := natScaled(hyps, ra, la, x, false)
		if first == nil {
			continue
		}
		if second := natScaled(hyps, x, ra, y, false); second != nil {
			return append(facts, first, second)
		}
	}
	return facts
}

// natSummands lists the summands of t, the leaves of its tree of sums.
func natSummands(t Term) []Term {
	if a, b, ok := MatchesPlus(t); ok {
		return append(natSummands(a), natSummands(b)...)
	}
	return []Term{t}
}

// natSummandPairs bounds the summand pairs natSummandScalings compares.
const natSummandPairs = 16

// natSummandScalings lists `Γ ⊢ p * a ≤ p * b` for the summands of the two
// sides that share factors p and whose remaining factors compare so: the
// rows a goal between two sums of products is a combination of.
func natSummandScalings(hyps []Term, left, right []Term) []*prop.PropWrapper {
	if len(left)*len(right) > natSummandPairs {
		return nil
	}
	var facts []*prop.PropWrapper
	for _, sl := range left {
		for _, sr := range right {
			shared, restL, restR := natDomain.sharedFactors(sl, sr)
			if len(shared) == 0 || (len(restL) == 0 && len(restR) == 0) {
				continue
			}
			if w := natScaled(hyps, natDomain.productOf(shared), natDomain.productOf(restL), natDomain.productOf(restR), false); w != nil {
				facts = append(facts, w)
			}
		}
	}
	return facts
}

// natMonomialCap bounds the monomials a term is multiplied out to, and
// natHypScalingCap the scaled comparisons natHypScalings lists.
const (
	natMonomialCap   = 8
	natHypScalingCap = 24
)

// natMonomials multiplies t out over its sums: the factors of each
// monomial. nil where there are more than natMonomialCap.
func natMonomials(t Term) [][]Term {
	if a, b, ok := MatchesPlus(t); ok {
		left, right := natMonomials(a), natMonomials(b)
		if left == nil || right == nil || len(left)+len(right) > natMonomialCap {
			return nil
		}
		return append(left, right...)
	}
	if a, b, ok := MatchesStar(t); ok {
		left, right := natMonomials(a), natMonomials(b)
		if left == nil || right == nil || len(left)*len(right) > natMonomialCap {
			return nil
		}
		var out [][]Term
		for _, x := range left {
			for _, y := range right {
				out = append(out, slices.Concat(x, y))
			}
		}
		return out
	}
	return [][]Term{{t}}
}

// natHypScalings lists the hypotheses' comparisons scaled by the cofactors
// the sequent spells beside them: for a hypothesis `a ≤ b` or `a < b` and
// a product of the sequent that holds a's factors, or b's, with a cofactor
// F left over, `Γ ⊢ F * a ≤ F * b` — strictly where the hypothesis is
// strict and F is shown positive. A hypothesis `0 < b` is read `1 ≤ b`.
// These are the rows a goal that is no comparison of two products is a
// combination of: `B ≤ S ∧ c ≤ q + B * r ⊢ c ≤ q + S * r`. l and r are the
// goal's sides, whose products count with the hypotheses'.
func natHypScalings(hyps []Term, l, r Term) []*prop.PropWrapper {
	// The products in sight, as factor lists: each side multiplied out,
	// and each product as it is spelled.
	var products [][]Term
	seen := func(factors []Term) bool {
		return slices.ContainsFunc(products, func(p []Term) bool {
			_, restL, restR := natDomain.sharedFactors(natDomain.productOf(p), natDomain.productOf(factors))
			return len(restL) == 0 && len(restR) == 0
		})
	}
	note := func(factors []Term) {
		if len(factors) > 1 && !seen(factors) {
			products = append(products, factors)
		}
	}
	type comparison struct {
		l, r   Term
		strict bool
		proof  *prop.PropWrapper // Γ ⊢ l ≤ r, or l < r for strict
	}
	var comparisons []comparison
	sides := []Term{l, r}
	for _, h := range hyps {
		rel, a, b, proof, ok := natCancelAtom(h)
		if !ok {
			continue
		}
		sides = append(sides, a, b)
		if _, _, isEq := matchNumEq(rel(a, b)); isEq {
			continue
		}
		_, _, strict := MatchesLt(rel(a, b))
		if strict && isZeroNum(a) { // 0 < b is 1 ≤ b
			weak, ok := proveLinThenInt(slices.Values([]Term{lt(a, b)}), le(Numeral(1), b))
			if !ok {
				continue
			}
			a, strict, proof = Numeral(1), false, prop.WrapProp(proof.MaybeDeriveTrans(weak))
		}
		comparisons = append(comparisons, comparison{l: a, r: b, strict: strict, proof: proof})
	}
	for _, side := range sides {
		for _, m := range natMonomials(side) {
			note(m)
		}
	}
	for _, product := range collectBinderFreeSubterms(sides, isNatSymbolicProduct) {
		note(natDomain.factors(product))
	}
	if len(products) == 0 {
		return nil
	}
	var facts []*prop.PropWrapper
	stated := func(t Term) bool {
		return slices.ContainsFunc(hyps, t.AlphaEquals) ||
			slices.ContainsFunc(facts, func(f *prop.PropWrapper) bool { return f.Conclusion().AlphaEquals(t) })
	}
	for _, c := range comparisons {
		for _, side := range []Term{c.l, c.r} {
			if isNumeralLit(side) {
				continue
			}
			for _, product := range products {
				// product = F * side for the cofactor F.
				_, cofactor, missing := natDomain.sharedFactors(natDomain.productOf(product), side)
				if len(missing) > 0 || len(cofactor) == 0 || !slices.ContainsFunc(cofactor, func(f Term) bool { return !isNumeralLit(f) }) {
					continue
				}
				f := natDomain.productOf(cofactor)
				if fact := natScaleComparison(hyps, f, c.l, c.r, c.strict, c.proof); fact != nil && !stated(fact.Conclusion()) {
					facts = append(facts, fact)
					if len(facts) >= natHypScalingCap {
						return facts
					}
				}
			}
		}
	}
	return facts
}

// natScaleComparison is `Γ ⊢ f * a ⋈ f * b` from compared, `Γ ⊢ a ≤ b` or
// `Γ ⊢ a < b` for strict: strictly where f is shown positive, and
// otherwise by the weaker `≤`.
func natScaleComparison(hyps []Term, f, a, b Term, strict bool, compared *prop.PropWrapper) *prop.PropWrapper {
	if strict {
		if positive := natProvePositive(hyps, f); positive != nil {
			scaled := lt(star(f, a), star(f, b))
			law := implyLeaf(lessThanMulMonoThm(), []Term{f, a, b},
				imply(not(eqT(f, natZero)), imply(lt(a, b), scaled)))
			return mp(mp(law, natNonzero(f, positive)), compared)
		}
		weak, ok := proveLinThenInt(slices.Values([]Term{lt(a, b)}), le(a, b))
		if !ok {
			return nil
		}
		compared = prop.WrapProp(compared.MaybeDeriveTrans(weak)) // Γ ⊢ a ≤ b
	}
	return mp(implyLeaf(lessEqMulMonoThm(), []Term{f, a, b}, imply(le(a, b), le(star(f, a), star(f, b)))), compared)
}

// natScaled proves `Γ ⊢ p * a ⋈ p * b`, Γ ⊆ hyps, from `a ⋈ b` — and for
// `<` from `0 < p`; nil where either is not shown.
func natScaled(hyps []Term, p, a, b Term, strict bool) *prop.PropWrapper {
	rel := natOrder(a, b, strict)
	compared, ok := proveLinThenInt(slices.Values(hyps), rel)
	if !ok {
		compared, ok = natProveScaled(hyps, rel)
	}
	if !ok {
		return nil
	}
	scaled := natOrder(star(p, a), star(p, b), strict)
	if !strict {
		return mp(implyLeaf(lessEqMulMonoThm(), []Term{p, a, b}, imply(rel, scaled)), compared)
	}
	positive := natProvePositive(hyps, p)
	if positive == nil {
		return nil
	}
	nonzero := not(eqT(p, natZero))
	law := implyLeaf(lessThanMulMonoThm(), []Term{p, a, b}, imply(nonzero, imply(rel, scaled)))
	return mp(mp(law, natNonzero(p, positive)), compared)
}

// natCancelLaw is a cancellation law of the bundle at p, a and b:
// `⊢ (p * a ⋈ p * b) ⇔ rhs`.
func natCancelLaw(thm *prop.PropWrapper, scaled, rhs Term, p, a, b Term) *prop.PropWrapper {
	iff := instAll(thm, []Term{p, a, b})
	if want := eqT(scaled, rhs); !iff.Conclusion().AlphaEquals(want) {
		panic(fmt.Sprintf("omega: the nat bundle's cancellation law does not read `%s`: %s",
			ext.PrintTerm(want), ext.PrintTerm(iff.Conclusion())))
	}
	return iff
}

// natCancelAtom reads a hypothesis as `{h} ⊢ rel(l, r)` for an equation
// over ℕ or an order atom, `≥` and `>` read as the swapped `≤` and `<`,
// and a negated `<` or `≤` as the comparison it is the same as.
func natCancelAtom(h Term) (rel func(a, b Term) Term, l, r Term, proof *prop.PropWrapper, ok bool) {
	if inner := ext.MatchesNOT(h); inner != nil {
		if a, b, m := MatchesLt(inner); m { // ¬(a < b) is b ≤ a
			return le, b, a, notLT(a, b).EqMP(prop.Assume(h)), true
		}
		if a, b, m := MatchesLe(inner); m { // ¬(a ≤ b) is b < a
			return lt, b, a, notLE(a, b).EqMP(prop.Assume(h)), true
		}
		return nil, nil, nil, nil, false
	}
	if a, b, m := matchNumEq(h); m {
		return eqT, a, b, prop.Assume(h), true
	}
	if a, b, m := MatchesLe(h); m {
		return le, a, b, prop.Assume(h), true
	}
	if a, b, m := MatchesLt(h); m {
		return lt, a, b, prop.Assume(h), true
	}
	if a, b, m := MatchesGe(h); m {
		return le, b, a, geBridge(a, b).EqMP(prop.Assume(h)), true
	}
	if a, b, m := MatchesGt(h); m {
		return lt, b, a, gtBridge(a, b).EqMP(prop.Assume(h)), true
	}
	return nil, nil, nil, nil, false
}

// natCancelFacts lists, for each hypothesis whose two sides share factors,
// the comparison of what is left of them: `Γ ⊢ a ⋈ b`, Γ ⊆ hyps, and for a
// strict hypothesis `Γ ⊢ 0 < P` beside it. A hypothesis whose shared
// factors are not shown positive gives none, a strict one aside; nor does
// one whose cancelled comparison a hypothesis already states.
func natCancelFacts(hyps []Term) []*prop.PropWrapper {
	if mulEqCancelThm() == nil || lessEqMulCancelThm() == nil || lessThanMulCancelThm() == nil ||
		posIffNonzeroThm() == nil {
		return nil
	}
	resident := func(t Term) bool { return slices.ContainsFunc(hyps, t.AlphaEquals) }
	var facts []*prop.PropWrapper
	for _, h := range hyps {
		rel, l, r, base, ok := natCancelAtom(h)
		if !ok {
			continue
		}
		shared, restL, restR := natDomain.sharedFactors(l, r)
		if len(shared) == 0 {
			continue
		}
		p, a, b := natDomain.productOf(shared), natDomain.productOf(restL), natDomain.productOf(restR)
		cancelled, scaled := rel(a, b), rel(star(p, a), star(p, b))
		if a.AlphaEquals(b) {
			continue
		}
		// The hypothesis in the law's spelling: one linear row, read up to
		// the order and the grouping of the factors.
		spelled, ok := proveLinThenInt(slices.Values([]Term{base.Conclusion()}), scaled)
		if !ok {
			continue
		}
		spelled = prop.WrapProp(base.MaybeDeriveTrans(spelled)) // {h} ⊢ p * a ⋈ p * b
		nonzero := not(eqT(p, natZero))
		if _, _, strict := MatchesLt(cancelled); strict {
			law := natCancelLaw(lessThanMulCancelThm(), scaled, ext.Apply(prop.AND, nonzero, cancelled), p, a, b)
			parts := splitConjuncts(law.EqMP(spelled)) // {h} ⊢ ¬(p = 0), {h} ⊢ a < b
			if !resident(cancelled) {
				facts = append(facts, parts[len(parts)-1])
			}
			if positive := natPosIffNonzero(p).EqMP(parts[0]); !resident(positive.Conclusion()) {
				facts = append(facts, positive)
			}
			continue
		}
		if resident(cancelled) {
			continue
		}
		positive := natProvePositive(hyps, p)
		if positive == nil {
			continue
		}
		thm := lessEqMulCancelThm()
		if _, _, isEq := matchNumEq(cancelled); isEq {
			thm = mulEqCancelThm()
		}
		law := natCancelLaw(thm, scaled, or(eqT(p, natZero), cancelled), p, a, b)
		fact := disjSyllogism(law.EqMP(spelled), natNonzero(p, positive)) // Γ ⊢ a ⋈ b
		if fact == nil {
			panic(fmt.Sprintf("omega: the cancellation of %s from %s did not leave %s",
				ext.PrintTerm(p), ext.PrintTerm(scaled), ext.PrintTerm(cancelled)))
		}
		facts = append(facts, fact)
	}
	return facts
}

// natProveCancelled proves `{hyps} ⊢ goal` for a goal `a = b`, `a ≤ b` or
// `a < b` between two products (or atoms) by cancelling a factor P from
// `P * a ⋈ P * b`, which the hypotheses prove linearly. P is a product of
// factors that, joined to a's and to b's, makes two products the
// hypotheses spell, and is shown positive (for `<` it need not be).
func natProveCancelled(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if mulEqCancelThm() == nil || lessEqMulCancelThm() == nil || lessThanMulCancelThm() == nil ||
		posIffNonzeroThm() == nil {
		return nil, false
	}
	rel, a, b, _, ok := natCancelAtom(goal)
	if !ok || !goal.AlphaEquals(rel(a, b)) {
		return nil, false // `≥` and `>` reach the chain as `≤` and `<`
	}
	if _, _, isSum := MatchesPlus(a); isSum {
		return nil, false
	}
	if _, _, isSum := MatchesPlus(b); isSum {
		return nil, false
	}
	spelled := collectBinderFreeSubterms(hyps, isNatSymbolicProduct)
	inSight := func(factors []Term) bool {
		return slices.ContainsFunc(spelled, func(product Term) bool {
			_, restL, restR := natDomain.sharedFactors(product, natDomain.productOf(factors))
			return len(restL) == 0 && len(restR) == 0
		})
	}
	var tried []Term
	for _, product := range spelled {
		// product = P * a for the factors P that a leaves of it.
		_, p, missing := natDomain.sharedFactors(product, a)
		if len(missing) > 0 || len(p) == 0 || slices.ContainsFunc(p, isNumeralLit) {
			continue
		}
		if !inSight(slices.Concat(p, natDomain.factors(b))) {
			continue
		}
		factor := natDomain.productOf(p)
		if slices.ContainsFunc(tried, factor.AlphaEquals) {
			continue
		}
		tried = append(tried, factor)
		scaled := rel(star(factor, a), star(factor, b))
		proved, ok := proveLinThenInt(slices.Values(hyps), scaled) // Γ ⊢ P * a ⋈ P * b
		if !ok {
			continue
		}
		nonzero := not(eqT(factor, natZero))
		if _, _, strict := MatchesLt(goal); strict {
			law := natCancelLaw(lessThanMulCancelThm(), scaled, ext.Apply(prop.AND, nonzero, goal), factor, a, b)
			parts := splitConjuncts(law.EqMP(proved))
			return parts[len(parts)-1], true
		}
		positive := natProvePositive(hyps, factor)
		if positive == nil {
			continue
		}
		thm := lessEqMulCancelThm()
		if _, _, isEq := matchNumEq(goal); isEq {
			thm = mulEqCancelThm()
		}
		law := natCancelLaw(thm, scaled, or(eqT(factor, natZero), goal), factor, a, b)
		if w := disjSyllogism(law.EqMP(proved), natNonzero(factor, positive)); w != nil {
			return w, true
		}
	}
	return nil, false
}
