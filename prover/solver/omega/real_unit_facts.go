package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The unit facts over ℝ: the shared search (unit_facts.go) with ℝ's
// evidence that a divisor is not zero (real_nonzero.go) and ℝ's
// MulLeftInverse. Each fact is injected as one more hypothesis and the
// whole decide chain runs over the enriched set (enrichAndCut — the shape
// the literal quotients and the positive-factor cancellation use), so the
// sides are re-read on the re-entry: realIsUnitFact keeps the injected
// facts out of them.

// realIsUnitFact recognizes an injected fact, `inv(t)·t = &1` or
// `R · (inv(t)·t) = R`, so that a re-entry does not read cofactors off it.
func realIsUnitFact(h Term) bool {
	l, r, ok := matchRealEq(h)
	if !ok {
		return false
	}
	pair := func(p Term) bool {
		a, b, ok := realDomain.matchStar(p)
		if !ok {
			return false
		}
		t, ok := MatchesRealInv(a)
		return ok && t.AlphaEquals(b)
	}
	if pair(l) {
		return isRealOne(r)
	}
	x, p, ok := realDomain.matchStar(l)
	return ok && pair(p) && x.AlphaEquals(r)
}

// realSequentSides is the carrier terms the sequent compares: both sides of
// every constraint its hypotheses contribute, and of the goal, read in the
// positive form the linear layer reads.
func realSequentSides(hyps []Term, goal Term) []Term {
	var sides []Term
	own := slices.DeleteFunc(slices.Clone(hyps), realIsUnitFact)
	for _, c := range realDomain.hypConstraints(slices.Values(own)) {
		sides = append(sides, c.Lhs, c.Rhs)
	}
	atom := goal
	if inner := ext.MatchesNOT(goal); inner != nil {
		atom = inner
	}
	if mac := realSubneg.moveAcrossCmp(atom); mac != nil {
		atom = prop.Rhs(mac)
	}
	if _, l, r, ok := matchRealRel(atom); ok {
		sides = append(sides, l, r)
	}
	return sides
}

// realUnitFact proves `{…} ⊢ R · (inv(t)·t) = R` — `inv(t)·t = &1` for the
// empty cofactor — from t's being nonzero.
func realUnitFact(t Term, cofactor []Term, neq *prop.PropWrapper) *prop.PropWrapper {
	one := disjSyllogism(realMulLeftInverseDisj(t), neq) // ⊢ &1 = inv t · t
	if one == nil {
		return nil
	}
	unit := one.EqSym() // ⊢ inv t · t = &1
	if len(cofactor) == 0 {
		return unit
	}
	r := realRing.monoProductOf(cofactor)
	scaled := unit.LeftApply(ext.Apply(realStar, r)) // ⊢ R·(inv t · t) = R·&1
	return scaled.EqTrans(realMulRid(r))             // ⊢ R·(inv t · t) = R
}

// realUnitFacts is the unit facts the sequent's monomials ask for that are
// not already resident — the resident check is what ends the re-entry.
func realUnitFacts(hyps []Term, goal Term) []*prop.PropWrapper {
	// The cheap gate: a sequent with no inverse and no symbolic quotient has
	// no pair to cancel.
	mentions := collectBinderFreeSubterms(append(slices.Clone(hyps), goal), func(t Term) bool {
		if _, ok := MatchesRealInv(t); ok {
			return true
		}
		_, ok := realDomain.quotientProduct(t)
		return ok
	})
	if len(mentions) == 0 {
		return nil
	}
	divisors := unitCofactors(realSequentSides(hyps, goal), realSubneg, MatchesRealInv,
		func(t Term) *prop.PropWrapper { return realProveNeqZero(hyps, t) })
	return unitFactsOf(divisors, realUnitFact, func(fact Term) bool {
		return slices.ContainsFunc(hyps, fact.AlphaEquals)
	})
}
