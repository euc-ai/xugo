package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A factor and its inverse, wherever they stand in a monomial — the
// search both carriers with an inverse share: ℝ (real_unit_facts.go) and a
// field read by the structure ring (structure_unit_facts.go).
//
// The cancellation a rewrite can do is of one shape: the two operands of a
// single product, `y · inv y`. In `(a / v) · v` the operands are `a / v` and
// `v`; in `(inv u − inv l)·(u·l)` the pairs only exist after the product is
// multiplied out. To a decider over the monomial basis v and inv(v) are two
// unrelated unknowns, so the monomial a·v·inv(v) and a have nothing to do
// with each other — and a resident `inv v · v = 1` does not help, since using
// it on that monomial means multiplying the equation by the VARIABLE a,
// which no linear or integer combination does.
//
// So the multiplying is done once, for the cofactors in sight. For each
// inverse atom inv(t) that a monomial of the sequent holds, with t shown
// nonzero by the carrier's own evidence, and each cofactor R that the
// sequent multiplies the pair by, the fact
//
//	R · (inv(t) · t) = R
//
// joins the facts the decider combines. Read in the monomial basis it is a
// LINEAR row: R·inv(t)·t against R for an atom t, and for t = x − c the row
// R·inv(t)·x − R·inv(t)·c = R, which is what ties a difference quotient
// times its offset back to the increment.
//
// The cofactors are read off the monomials: M = inv(t) · Q holds the pair
// with cofactor R wherever Q = R · m for a monomial m of t. The sequent's
// monomials are read first, and then each cofactor found — the REDUCED side
// of the fact it names, which is one more monomial — is read the same way:
// in x·inv(a)·y·inv(b)·a·b the a-pair's fact reduces the monomial to
// x·y·inv(b)·b, and the b-pair's cancellation of THAT monomial exists
// nowhere in the sequent. A cofactor is its monomial with inv(t) and one
// monomial of t taken out, so each round's monomials are strictly smaller
// and the rounds end. The EXPANDED side of a fact is never read: its
// monomials would offer new cofactors without end when t's monomials differ
// in degree.

// unitFactCap bounds the unit facts one decision adds.
const unitFactCap = 24

// unitDivisor is a divisor t whose inverse a monomial of the sequent holds,
// with the evidence that t is not zero.
type unitDivisor struct {
	t   Term
	neq *prop.PropWrapper
}

// equalWithZeroPut proves `{t = zero} ∪ Γ ⊢ p = q` where zero put for t
// makes p and q equal by prove, whose hypotheses are Γ: the congruence of
// the assumption isZero (`t = zero`) at every occurrence of t, then prove on
// what is left. It is how a factor of what the context shows nonzero is
// shown nonzero, on either carrier.
//
// ok=false where t stands in neither side, where the two sides still
// differ, and where t occurs in zero — t is the zero itself, the divisor of
// `x / &0`: zero put for zero changes nothing, and the rewrite, which goes
// on into what it produced, would not end. A binder of p or q whose bound
// variable is named as a free variable of t is renamed on the way, the
// assumption being carried back out through it.
func equalWithZeroPut(t, zero, isZero, p, q Term, prove func(p, q Term) (*prop.PropWrapper, bool)) (*prop.PropWrapper, bool) {
	if ext.FindTopSubTerm(zero, t.AlphaEquals) != nil {
		return nil, false
	}
	carried := func(pred func(prop.Term) bool) bool { return pred(isZero) }
	put := prop.DeepRewriteWithEnv(carried, func(s Term) *prop.PropWrapper {
		if s.AlphaEquals(t) {
			return prop.Assume(isZero)
		}
		return nil
	})
	wp, wq := put(p), put(q) // {t = zero} ⊢ p = p′, q = q′; nil where t does not occur
	if wp == nil && wq == nil {
		return nil, false
	}
	p2, q2 := p, q
	if wp != nil {
		p2 = prop.Rhs(wp)
	}
	if wq != nil {
		q2 = prop.Rhs(wq)
	}
	eq, ok := prove(p2, q2) // Γ ⊢ p′ = q′
	if !ok {
		return nil, false
	}
	if wp != nil {
		eq = wp.EqTrans(eq)
	}
	if wq != nil {
		eq = eq.EqTrans(wq.EqSym())
	}
	return eq, true
}

// unitPair is one unit fact to prove: the divisor and the cofactor its pair
// stands under, as sorted base atoms.
type unitPair struct {
	d        *unitDivisor
	cofactor []Term
}

// sortedFactors is a monomial's base atoms, Compare-sorted.
func (v *ringVocab) sortedFactors(m Term) []Term {
	factors := slices.Clone(v.decomposeStar(m))
	slices.SortStableFunc(factors, func(a, b Term) int { return a.Compare(b) })
	return factors
}

// removeFactors is target with piece's atoms taken out, one occurrence
// each; ok=false when piece does not divide target. Both sorted.
func removeFactors(target, piece []Term) ([]Term, bool) {
	rest := make([]Term, 0, len(target))
	j := 0
	for _, atom := range target {
		if j < len(piece) && piece[j].Compare(atom) == 0 {
			j++
			continue
		}
		rest = append(rest, atom)
	}
	return rest, j == len(piece)
}

// monomialsOf is the monomials of t's signed form, each as its sorted base
// atoms; a nonzero constant term is the empty monomial.
func (v *subnegVocab) monomialsOf(t Term) [][]Term {
	var out [][]Term
	add := func(lf linForm) {
		if !lf.konst.isZero() {
			out = append(out, nil)
		}
		for _, m := range lf.monos {
			out = append(out, v.ring.sortedFactors(m.atom))
		}
	}
	if p, n, _, ok := v.signedNorm(t); ok {
		add(p)
		add(n)
		return out
	}
	if lf, ok := v.ring.dom.linOf(t); ok {
		add(lf)
	}
	return out
}

// unitCofactors is the pairs the sides ask for: for each divisor whose
// inverse atom (matchInv) stands in a monomial and which neq shows nonzero,
// the cofactors its pairs stand under. The sides' own monomials are read
// first — their pairs come out divisor by divisor, in the order the sides
// first meet each — and then, round by round, the cofactors the round
// before found, until a round finds nothing new or unitFactCap pairs are in
// hand. The sides are read in the positive form the decider reads:
// sub/neg-free.
func unitCofactors(sides []Term, v *subnegVocab, matchInv func(Term) (Term, bool),
	neq func(t Term) *prop.PropWrapper) []unitPair {
	type entry struct {
		*unitDivisor
		index     int
		monos     [][]Term
		cofactors [][]Term
	}
	var divisors []*entry
	find := func(t Term) *entry {
		for _, d := range divisors {
			if d.t.AlphaEquals(t) {
				return d
			}
		}
		d := &entry{unitDivisor: &unitDivisor{t: t, neq: neq(t)}, index: len(divisors)}
		if d.neq != nil {
			d.monos = v.monomialsOf(t)
		}
		divisors = append(divisors, d)
		return d
	}
	same := func(a, b []Term) bool {
		return slices.EqualFunc(a, b, func(x, y Term) bool { return x.Compare(y) == 0 })
	}
	type found struct {
		d        *entry
		cofactor []Term
	}
	// read adds to round the pairs the monomial `factors` holds that no
	// earlier monomial did.
	read := func(factors []Term, round *[]found) {
		for i, atom := range factors {
			if i > 0 && factors[i-1].Compare(atom) == 0 {
				continue
			}
			t, ok := matchInv(atom)
			if !ok {
				continue
			}
			d := find(t)
			if d.neq == nil {
				continue
			}
			rest, _ := removeFactors(factors, []Term{atom})
			for _, m := range d.monos {
				cofactor, ok := removeFactors(rest, m)
				if !ok || slices.ContainsFunc(d.cofactors, func(c []Term) bool { return same(c, cofactor) }) {
					continue
				}
				d.cofactors = append(d.cofactors, cofactor)
				*round = append(*round, found{d: d, cofactor: cofactor})
			}
		}
	}
	var round []found
	for _, side := range sides {
		lf, ok := v.ring.dom.linOf(side)
		if !ok {
			continue
		}
		for _, mono := range lf.monos {
			read(v.ring.sortedFactors(mono.atom), &round)
		}
	}
	var pairs []unitPair
	for len(round) > 0 && len(pairs) < unitFactCap {
		slices.SortStableFunc(round, func(a, b found) int { return a.d.index - b.d.index })
		var next []found
		for _, f := range round {
			pairs = append(pairs, unitPair{d: f.d.unitDivisor, cofactor: f.cofactor})
			read(f.cofactor, &next)
		}
		round = next
	}
	return pairs
}

// unitFactsOf proves the unit fact of each pair through build, up to
// unitFactCap, skipping a fact build declines (nil) and one held already
// reports as in hand.
func unitFactsOf(pairs []unitPair, build func(t Term, cofactor []Term, neq *prop.PropWrapper) *prop.PropWrapper,
	held func(fact Term) bool) []*prop.PropWrapper {
	var facts []*prop.PropWrapper
	for _, p := range pairs {
		if len(facts) >= unitFactCap {
			return facts
		}
		fact := build(p.d.t, p.cofactor, p.d.neq)
		if fact == nil || held(fact.Conclusion()) {
			continue
		}
		facts = append(facts, fact)
	}
	return facts
}
