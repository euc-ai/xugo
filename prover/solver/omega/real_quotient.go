package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A quotient by a numeral, wherever it stands in the sequent.
//
// linarith reads `y / &k` as one opaque atom with no relation to `y`. The
// pre-simp clears a literal divisor only when the quotient is a WHOLE side of
// a comparison (realClearLiteralDivSimp: `x/&2 ≤ y` → `x ≤ y·&2`), and the
// field handler clears only in the goal — so `&0 < e ⊢ &0 < e/&2` closed
// while `&0 < e ⊢ x < x + e/&2` and `s − e/&2 < y` did not: the quotient
// beside another summand never met either. Halving ε is the ε-argument's
// reflex, so the sequences and function-limit chapters walked into it.
//
// The fix is not a rewrite. Multiplying an atom through by k would leave
// `&k · (y/&k)` for the ring to cancel, once per atom per quotient, and a
// hypothesis's shape would change under the author. The linear fragment has
// the cheaper reading: the quotient IS a linear unknown, the one tied to y by
//
//	y = (y/&k) · &k
//
// so the handler collects every literal-divisor quotient the hypotheses and
// the goal mention, injects that defining equation for each as one more
// hypothesis, and runs the WHOLE decide chain over the enriched set, cutting
// the equations back (enrichAndCut — the shape the positive-factor
// cancellation uses). Every handler downstream — linarith, the abs case
// split, the ring residual of a cleared equation — then sees the quotient as
// an unknown with a row, which is what makes `x < x + e/&2`, `s − e/&2 < y`
// and `(c + d/&2) − c = d/&2` close from `&0 < e` alone.
//
// The equation's proof is EqDivMulLeft read at x := y/&k:
// `&0 < &k ⇒ (y/&k = y/&k ⇔ y = (y/&k)·&k)`, the left side reflexive and the
// sign a numeral evaluation — no new bundle field. Only a literal divisor: a
// symbolic one needs its sign from the context, which is a proof obligation
// and the field handler's business.

// realLiteralQuotients returns the distinct binder-free `y / &k` subterms of
// terms, k a canonical positive literal. Binder-free (collectBinderFreeSubterms):
// a quotient mentioning a bound variable is not the atom any row of the
// sequent's free part mentions, so its equation would only cost a row.
func realLiteralQuotients(terms []Term) []Term {
	return collectBinderFreeSubterms(terms, func(t Term) bool {
		_, z, ok := MatchesRealDiv(t)
		if !ok {
			return false
		}
		v, shaped, exact := realDomain.asLiteral(z)
		return shaped && exact && !v.isZero()
	})
}

// realQuotientDefiningEq proves `⊢ y = (y/&k) · &k` for q = `y / &k`, k a
// positive literal. nil when the sign evaluation or the lemma declines.
func realQuotientDefiningEq(q Term) *prop.PropWrapper {
	y, z, ok := MatchesRealDiv(q)
	if !ok {
		return nil
	}
	pos, ok := realNormNatLt(realLit(0), z) // ⊢ (&0 < &k) ⇔ ⊤
	if !ok || !prop.Rhs(pos).Equals(prop.T) {
		return nil
	}
	// EqDivMulLeft at (z, other := q, num := y):
	//   &0 < z ⇒ ((q = y/z) ⇔ (y = q·z)), and `y/z` is q itself.
	thm, cleared := realClearLemma(relEq, true, true, q, y, z)
	if cleared == nil {
		return nil
	}
	imp := realImplyLeaf(thm, []Term{z, q, y},
		imply(realLtT(realLit(0), z), eqT(eqT(q, q), cleared)))
	iff := mp(imp, iffTrueElim(pos)) // ⊢ (q = q) ⇔ (y = q·z)
	return iff.EqMP(prop.Refl(q))    // ⊢ y = q·z
}

// A literal quotient that is a FACTOR.
//
// The defining equation ties q = y/&k to y, which makes q a linear unknown
// where it stands alone in a monomial. Where the sequent MULTIPLIES it —
// `&1/&2 · d`, `p · (&3/&2)` — the monomial is q·R, an unknown of its own
// with no row: using the equation on it means multiplying the equation by
// the variable R, which no linear combination does. So the multiplying is
// done here, once per cofactor in sight, as it is for a factor and its
// inverse (real_unit_facts.go): for each monomial q·R of the sequent,
//
//	R · y = R · ((y/&k) · &k)
//
// joins the defining equations, and the product is the unknown tied to R·y
// that the summand was to y. `&2·a ≤ d ⊢ a ≤ &1/&2·d` reads `d = 2·(q·d)`.
// The cofactors are the sequent's own, a hypothesis's and the goal's alike;
// a fact already resident is not injected again, which ends the re-entry.

// realQuotientFactCap bounds the scaled equations one decide call injects.
const realQuotientFactCap = 24

// realIsLiteralQuotient reports whether atom is `y / &k`, k a canonical
// nonzero literal.
func realIsLiteralQuotient(atom Term) bool {
	_, z, ok := MatchesRealDiv(atom)
	if !ok {
		return false
	}
	v, shaped, exact := realDomain.asLiteral(z)
	return shaped && exact && !v.isZero()
}

// realQuotientCofactors is, for each literal quotient that a monomial of the
// sequent multiplies, the cofactors it is multiplied by: the monomial's
// other base atoms, sorted. A quotient standing alone has none.
func realQuotientCofactors(hyps []Term, goal Term) (quotients []Term, cofactors [][][]Term) {
	same := func(a, b []Term) bool {
		return slices.EqualFunc(a, b, func(x, y Term) bool { return x.Compare(y) == 0 })
	}
	for _, side := range realSequentSides(hyps, goal) {
		lf, ok := realDomain.linOf(side)
		if !ok {
			continue
		}
		for _, mono := range lf.monos {
			factors := realRing.sortedFactors(mono.atom)
			if len(factors) < 2 {
				continue
			}
			for i, atom := range factors {
				if i > 0 && factors[i-1].Compare(atom) == 0 || !realIsLiteralQuotient(atom) {
					continue
				}
				rest, _ := removeFactors(factors, []Term{atom})
				at := slices.IndexFunc(quotients, atom.AlphaEquals)
				if at < 0 {
					at = len(quotients)
					quotients = append(quotients, atom)
					cofactors = append(cofactors, nil)
				}
				if !slices.ContainsFunc(cofactors[at], func(c []Term) bool { return same(c, rest) }) {
					cofactors[at] = append(cofactors[at], rest)
				}
			}
		}
	}
	return quotients, cofactors
}

// realQuotientFacts is the equations of the sequent's literal quotients that
// are not already resident: the defining equation of each, and its multiple
// by each cofactor the sequent multiplies the quotient by. The resident
// check is what terminates the re-entry: once the enriched chain re-enters
// realProveDecAtom, every quotient it mentions has its equations in place.
func realQuotientFacts(hyps []Term, goal Term) []*prop.PropWrapper {
	var facts []*prop.PropWrapper
	for _, q := range realLiteralQuotients(append(slices.Clone(hyps), goal)) {
		eq := realQuotientDefiningEq(q)
		if eq == nil || slices.ContainsFunc(hyps, eq.Conclusion().AlphaEquals) {
			continue
		}
		facts = append(facts, eq)
	}
	quotients, cofactors := realQuotientCofactors(hyps, goal)
	scaled := 0
	for i, q := range quotients {
		eq := realQuotientDefiningEq(q)
		if eq == nil {
			continue
		}
		for _, cofactor := range cofactors[i] {
			if scaled >= realQuotientFactCap {
				return facts
			}
			// ⊢ R · y = R · (q · &k)
			fact := eq.LeftApply(ext.Apply(realStar, realRing.monoProductOf(cofactor)))
			if slices.ContainsFunc(hyps, fact.Conclusion().AlphaEquals) {
				continue
			}
			facts = append(facts, fact)
			scaled++
		}
	}
	return facts
}
