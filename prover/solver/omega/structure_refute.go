package omega

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The structure ring's refutation: an equation the context denies.
//
// A ring identity and a combination prove an equation and refute none,
// and a context that contradicts itself at a ring's carrier does so by
// an equation that is false: `z * w = one ∧ z = zero` at a field, with
// zero read for z, is `zero * w = one`, which the ring reads
// `zero = one`. ℝ refutes its twin through the order; a field has none,
// and refutes by what it denies.
//
// What a context denies at the carrier: its disequalities `¬(p = q)`,
// and at a field `one ≠ zero` (StructureRingLaws.OneNotZero), which no
// hypothesis need state. An equation `l = r` is refuted where, joined
// to the context's equations, it combines by integers to `p = q` for a
// denied pair (refuteEq) — the search proveNonzero makes for `t = zero`,
// at any equation. A ring that is no field denies nothing by itself: the
// zero ring is a commutative ring.
//
// At a field the elements that are not zero are closed under the
// product and the inverse, so the evidence that a term is not zero
// (proveNonzero) reads a product through its factors, a quotient and an
// inverse through their arguments, and a power through its base
// (unitNonzero). The same law read
// forward: a product the context equates to zero, one factor shown not
// zero, gives the equation of its cofactor to zero
// (zeroProductEquations), which joins the equations a combination reads.
// And an equation whose two sides share a factor shown not zero gives the
// equation of what is left of them (cancelledEquations). All three are
// one cancellation (cancelFrom): the equation times the factor's inverse,
// and the unit facts of that factor.
//
// A field may have a characteristic, so a literal is denied only by a
// resident disequality or by ℝ's evidence at an instance that embeds ℝ
// (embeddedNonzero): `&2 = zero` is refuted over ℂ and not over a field.

// oneNotZero is Γ ⊢ ¬(one = zero) at a field; nil at a ring that is no
// field. The law has no membership guard, so it is read once per ring.
func (b *boundRing) oneNotZero() *prop.PropWrapper {
	sr := b.sr
	sr.oneNotZeroOnce.Do(func() {
		c, laws := sr.comps, sr.laws
		if c.fieldRecord == nil || laws.OneNotZero == nil {
			return
		}
		w := laws.at(laws.OneNotZero, []Term{c.fieldRecord}, sr.fieldFact)
		if want := not(core.Eq(c.one, c.zero)); !w.Conclusion().AlphaEquals(want) {
			panic(fmt.Sprintf("omega: the field's nontriviality law does not read `%s` at the ring's components: %s",
				ext.PrintTerm(want), ext.PrintTerm(w.Conclusion())))
		}
		sr.oneNotZero = w
	})
	return sr.oneNotZero
}

// denials lists what the context denies at the carrier: its
// disequalities, and at a field `one ≠ zero`.
func (b *boundRing) denials(hyps []Term) []structureDisequality {
	out := b.disequalities(hyps)
	if w := b.oneNotZero(); w != nil {
		out = append(out, structureDisequality{p: b.sr.comps.one, q: b.sr.comps.zero, proof: w})
	}
	return out
}

// refuteEq proves Γ ⊢ ¬(l = r), the atoms' memberships checked by the
// caller; nil where the context does not deny the equation.
func (b *boundRing) refuteEq(hyps []Term, l, r Term) *prop.PropWrapper {
	zero := b.sr.comps.zero
	eq := core.Eq(l, r)
	switch {
	case r.AlphaEquals(zero):
		if w := b.proveNonzero(hyps, l); w != nil {
			return w
		}
	case l.AlphaEquals(zero):
		if w := b.proveNonzero(hyps, r); w != nil { // Γ ⊢ ¬(r = zero)
			return refuteBy(eq, prop.Assume(eq).EqSym(), w)
		}
	}
	assumed := append(slices.Clone(hyps), eq)
	for _, d := range b.denials(hyps) {
		if !b.members.proveAtoms(d.p, d.q) {
			continue
		}
		if got, ok := b.proveEqWithoutUnitsSigned(assumed, d.p, d.q); ok { // {hyps, l = r} ⊢ p = q
			return refuteBy(eq, got, d.proof)
		}
	}
	return nil
}

// refuteBy is Γ ⊢ ¬assumed from got, `Γ, assumed ⊢ p = q`, and denied,
// `Γ ⊢ ¬(p = q)`.
func refuteBy(assumed Term, got, denied *prop.PropWrapper) *prop.PropWrapper {
	contra := prop.WrapProp(prop.Contradict(got.Conclusion()).DeriveHypFrom(got))
	contra = prop.WrapProp(denied.MaybeDeriveTrans(contra)) // Γ, assumed ⊢ ⊥
	return contra.NegHyp(assumed)
}

// unitNonzero proves Γ ⊢ ¬(t = zero) at a field for a product whose
// factors are not zero, an inverse or a negation whose argument is not,
// a quotient whose two arguments are not, and a power whose base is not;
// nil at a ring that is no field, for any other t, and where the parts'
// evidence is missing.
func (b *boundRing) unitNonzero(hyps []Term, t Term) *prop.PropWrapper {
	c := b.sr.comps
	if c.fieldRecord == nil || b.oneNotZero() == nil {
		return nil
	}
	isZero := core.Eq(t, c.zero)
	if x, y, ok := b.dom.matchStar(t); ok {
		xNonzero, yNonzero := b.proveNonzero(hyps, x), b.proveNonzero(hyps, y)
		if xNonzero == nil || yNonzero == nil {
			return nil
		}
		yZero, ok := b.cancelFactor(hyps, prop.Assume(isZero), x, y, xNonzero) // Γ, t = zero ⊢ y = zero
		if !ok {
			return nil
		}
		return refuteBy(isZero, yZero, yNonzero)
	}
	if x, ok := b.matchInv(t); ok {
		xNonzero := b.proveNonzero(hyps, x)
		if xNonzero == nil || !b.members.proveAtoms(x) {
			return nil
		}
		// inv(x) = zero gives inv(x)·x = zero·x beside inv(x)·x = one.
		scaled, ok1 := b.equationHyp(prop.Assume(isZero).LeftApply(b.ring.starOp).RightApply(x))
		unit := b.unitFact(x, nil, xNonzero)
		if !ok1 || unit == nil {
			return nil
		}
		unitEq, ok2 := b.equationHyp(unit)
		if !ok2 {
			return nil
		}
		oneZero, ok := b.proveByCombination([]equationHyp{scaled, unitEq}, c.one, c.zero) // Γ, t = zero ⊢ one = zero
		if !ok {
			return nil
		}
		return refuteBy(isZero, oneZero, b.oneNotZero())
	}
	if x, y, ok := b.dom.matchQuotient(t); ok {
		// x / y = x · inv(y), the form its evidence is read in.
		if !b.members.proveAtoms(x, y) {
			return nil
		}
		law := b.ring.quotientUnfold(x, y)            // Γ ⊢ x / y = x · inv(y)
		nonzero := b.unitNonzero(hyps, prop.Rhs(law)) // Γ ⊢ ¬(x · inv(y) = zero)
		if nonzero == nil {
			return nil
		}
		return refuteBy(isZero, law.EqSym().EqTrans(prop.Assume(isZero)), nonzero)
	}
	if x, ok := b.dom.matchNeg(t); ok {
		xNonzero := b.proveNonzero(hyps, x)
		if xNonzero == nil {
			return nil
		}
		xZero, ok := b.proveEqWithoutUnitsSigned([]Term{isZero}, x, c.zero) // −x = zero ⊢ x = zero
		if !ok {
			return nil
		}
		return refuteBy(isZero, xZero, xNonzero)
	}
	if x, n, ok := b.dom.matchPow(t); ok {
		xNonzero := b.proveNonzero(hyps, x)
		if xNonzero == nil {
			return nil
		}
		xZero := b.powerBaseZero(prop.Assume(isZero), x, n) // xⁿ = zero ⊢ x = zero
		if xZero == nil {
			return nil
		}
		return refuteBy(isZero, xZero, xNonzero)
	}
	return nil
}

// powerBaseZero proves Γ ⊢ x = zero from power, Γ ⊢ xⁿ = zero, at a field
// (PowEqZero); nil where the bundle holds no such law or x's membership
// is not held.
func (b *boundRing) powerBaseZero(power *prop.PropWrapper, x, n Term) *prop.PropWrapper {
	sr := b.sr
	c, laws := sr.comps, sr.laws
	if c.fieldRecord == nil || laws.PowEqZero == nil {
		return nil
	}
	memberProof, ok := b.members.prove(x)
	if !ok {
		return nil
	}
	law := laws.at(laws.PowEqZero, []Term{c.fieldRecord}, sr.fieldFact, x, n) // Γ ⊢ x ∈ c ∧ xⁿ = zero ⇒ x = zero
	guard, concl, ok := prop.MatchesIMPLY(law.Conclusion())
	member, vanishes, isConj := prop.MatchesAND(guard)
	if !ok || !isConj || !vanishes.AlphaEquals(power.Conclusion()) || !concl.AlphaEquals(core.Eq(x, c.zero)) {
		panic(fmt.Sprintf("omega: the field's power law does not read `%s ∧ %s ⇒ %s`: %s",
			ext.PrintTerm(b.members.membership(x)), ext.PrintTerm(power.Conclusion()),
			ext.PrintTerm(core.Eq(x, c.zero)), ext.PrintTerm(law.Conclusion())))
	}
	both := prop.WrapProp(power.MaybeDeriveTrans(prop.ConclAND(member, vanishes).DeriveHypFrom(memberProof)))
	return law.DemoteHyp().DeriveHypFrom(both)
}

// cancelFactor proves Γ ⊢ y = zero from product, Γ ⊢ x·y = zero, and
// xNonzero, Γ ⊢ ¬(x = zero).
func (b *boundRing) cancelFactor(hyps []Term, product *prop.PropWrapper, x, y Term, xNonzero *prop.PropWrapper) (*prop.PropWrapper, bool) {
	return b.cancelFrom(hyps, product, x, y, b.sr.comps.zero, xNonzero)
}

// cancelFrom proves Γ ⊢ l = r from eq, an equation Γ ⊢ p = q whose two
// sides are x times l and x times r as polynomials, and xNonzero,
// Γ ⊢ ¬(x = zero): the equation times inv(x), and the unit facts of x at
// the cofactors the monomials of l and r are. A divisor other than x
// that the inverse basis names is shown nonzero by the context's
// resident evidence alone.
func (b *boundRing) cancelFrom(hyps []Term, eq *prop.PropWrapper, x, l, r Term, xNonzero *prop.PropWrapper) (*prop.PropWrapper, bool) {
	invX := ext.Apply(b.sr.comps.inv, x)
	if !b.members.proveAtoms(x, l, r, invX) {
		return nil, false
	}
	scaled, ok := b.equationHyp(eq.LeftApply(b.ring.starLeft(invX))) // Γ ⊢ inv(x)·p = inv(x)·q
	if !ok {
		return nil, false
	}
	nonzero := func(t Term) *prop.PropWrapper {
		if t.AlphaEquals(x) {
			return xNonzero
		}
		return b.residentNonzero(hyps, t)
	}
	pairs := unitCofactors([]Term{scaled.lhs, scaled.rhs}, b.subneg, b.matchInv, nonzero)
	eqs := []equationHyp{scaled}
	for _, fact := range unitFactsOf(pairs, b.unitFact, func(Term) bool { return false }) {
		if eh, ok := b.equationHyp(fact); ok {
			eqs = append(eqs, eh)
		}
	}
	return b.proveByCombination(eqs, l, r)
}

// cancelledEquations lists, at a field, what the context's equations
// leave once a factor their two sides share is cancelled: for a context
// equation whose sides hold a common factor shown not zero, the equation
// of the products of the rest (shared_factors.go), a factor at a time,
// each on its own evidence. An equation with the zero for a side is
// zeroProductEquations'.
func (b *boundRing) cancelledEquations(hyps []Term) []equationHyp {
	c := b.sr.comps
	if c.fieldRecord == nil {
		return nil
	}
	product := func(factors []Term) Term {
		if len(factors) == 0 {
			return c.one
		}
		return b.dom.productOf(factors)
	}
	// cancelOne cancels the first shared factor of eq's sides that the
	// context shows not zero.
	cancelOne := func(eq *prop.PropWrapper) *prop.PropWrapper {
		l, r, _ := ext.MatchesEQ(eq.Conclusion())
		shared, restL, restR := b.dom.sharedFactors(l, r)
		for i, x := range shared {
			others := slices.Concat(shared[:i], shared[i+1:])
			left, right := product(slices.Concat(others, restL)), product(slices.Concat(others, restR))
			if left.AlphaEquals(right) || !b.members.proveAtoms(x, left, right) {
				continue
			}
			xNonzero := b.proveNonzero(hyps, x)
			if xNonzero == nil {
				continue
			}
			if rest, ok := b.cancelFrom(hyps, eq, x, left, right, xNonzero); ok {
				return rest // Γ ⊢ left = right
			}
		}
		return nil
	}
	var out []equationHyp
	for _, e := range b.sr.contextEquations(hyps) {
		if e.l.AlphaEquals(c.zero) || e.r.AlphaEquals(c.zero) || !b.members.proveAtoms(e.l, e.r) {
			continue
		}
		var cancelled *prop.PropWrapper
		for eq := cancelOne(e.proof); eq != nil; eq = cancelOne(eq) {
			cancelled = eq
		}
		if cancelled == nil {
			continue
		}
		if eh, ok := b.equationHyp(cancelled); ok {
			out = append(out, eh)
		}
	}
	return out
}

// zeroProductEquations lists, at a field, the cofactors the context
// equates to zero: for a context equation `x·y = zero` or `zero = x·y`
// with one factor shown not zero, the other's equation to zero; and for a
// context equation `xⁿ = zero`, x's.
func (b *boundRing) zeroProductEquations(hyps []Term) []equationHyp {
	c := b.sr.comps
	if c.fieldRecord == nil {
		return nil
	}
	var out []equationHyp
	for _, e := range b.sr.contextEquations(hyps) {
		product, proof := e.l, e.proof
		switch {
		case e.r.AlphaEquals(c.zero):
		case e.l.AlphaEquals(c.zero):
			product, proof = e.r, e.proof.EqSym()
		default:
			continue
		}
		if base, exponent, ok := b.dom.matchPow(product); ok {
			// A power that is zero has a zero base.
			if baseZero := b.powerBaseZero(proof, base, exponent); baseZero != nil {
				if eh, ok := b.equationHyp(baseZero); ok {
					out = append(out, eh)
				}
			}
			continue
		}
		x, y, ok := b.dom.matchStar(product)
		if !ok || !b.members.proveAtoms(x, y) {
			continue
		}
		var cofactor *prop.PropWrapper
		if xNonzero := b.proveNonzero(hyps, x); xNonzero != nil {
			cofactor, _ = b.cancelFactor(hyps, proof, x, y, xNonzero) // Γ ⊢ y = zero
		} else if yNonzero := b.proveNonzero(hyps, y); yNonzero != nil {
			commute, ok := b.ring.ringProveFull(b.dom.star(y, x), product) // ⊢ y·x = x·y
			if ok {
				cofactor, _ = b.cancelFactor(hyps, commute.EqTrans(proof), y, x, yNonzero) // Γ ⊢ x = zero
			}
		}
		if cofactor == nil {
			continue
		}
		if eh, ok := b.equationHyp(cofactor); ok {
			out = append(out, eh)
		}
	}
	return out
}
