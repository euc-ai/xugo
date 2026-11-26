package omega

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// The unit facts at a field: the shared search (unit_facts.go) read at a
// field fact — ℂ's installed instance or a chapter's field — with the
// field's own left inverse law (StructureRingLaws.MulLeftInverse). The
// facts join the context's equations for one more integer combination
// (proveEq), after the combination of the context's equations alone has
// declined, so a goal that closed without them closes as it did.
//
// The evidence that a divisor t is not zero is the context's: a resident
// `t ≠ zero`, as a hypothesis or a conjunct of one, or — by contradiction
// — a resident disequality `p ≠ q` at the carrier whose two sides the
// assumption t = zero makes equal by a ring identity or an integer
// combination of the context's equations, so `x ≠ c` is evidence for the
// divisor x − c — or makes equal once zero is put for t, so `a·b ≠ zero`
// is evidence for a and for b, what a divisor a·b needs once the inverse
// basis reads inv(a·b) as inv(a)·inv(b). And a term is not zero where its
// parts are not: a product by its factors, an inverse and a quotient by
// their arguments (unitNonzero, structure_refute.go). A field may have a
// characteristic: at an abstract field
// no literal is nonzero without such evidence, `&2 = &0` holding in
// characteristic 2. An instance that names an injective embedding of ℝ
// (StructureInstance.RealEmbedding; ℂ's complex_of_real) has
// characteristic zero, and there t = embed(r) is not zero wherever ℝ's
// own evidence shows r ≠ &0 (realProveNeqZero, the context included):
// injectivity carries it across, embed(&0) being the zero. So ℂ's
// literal complex_of_real(&2) needs no premise, nor complex_of_real(r)
// beside a resident &0 < r.

// matchInv reads t as the field's inverse applied: `F.inv(u)`.
func (b *boundRing) matchInv(t Term) (Term, bool) {
	app, ok := t.AsAppliedTerm()
	if !ok || !app.Fun().AlphaEquals(b.sr.comps.inv) {
		return nil, false
	}
	return app.Arg(), true
}

// mentionsInverse reports whether t holds an inverse or a quotient of the
// field — the cheap gate ahead of the search.
func (b *boundRing) mentionsInverse(t Term) bool {
	hit := false
	walkTerm(t, func(s Term) bool {
		if _, ok := b.matchInv(s); ok {
			hit = true
		} else if matchesQuotient(b.dom, s) {
			hit = true
		}
		return !hit
	})
	return hit
}

// structureDisequality is a resident statement that two elements of the
// carrier differ, `¬(p = q)`, with its proof {h} ⊢ ¬(p = q).
type structureDisequality struct {
	p, q  Term
	proof *prop.PropWrapper
}

// disequalities lists the context's disequalities at the carrier: a
// hypothesis `¬(p = q)`, or a conjunct of one.
func (b *boundRing) disequalities(hyps []Term) []structureDisequality {
	var out []structureDisequality
	read := func(part *prop.PropWrapper) {
		inner := ext.MatchesNOT(part.Conclusion())
		if inner == nil {
			return
		}
		if p, q, ok := ext.MatchesEQ(inner); ok && b.dom.isElem(p) {
			out = append(out, structureDisequality{p: p, q: q, proof: part})
		}
	}
	for _, h := range hyps {
		if _, _, ok := prop.MatchesAND(h); ok {
			for _, part := range splitConjuncts(prop.Assume(h)) {
				read(part)
			}
			continue
		}
		read(prop.Assume(h))
	}
	return out
}

// proveNonzero proves Γ ⊢ ¬(t = zero) from the context's evidence, nil
// when it holds none: the evidence that names t (residentNonzero), and
// at a field the evidence of t's parts (unitNonzero).
func (b *boundRing) proveNonzero(hyps []Term, t Term) *prop.PropWrapper {
	if w := b.residentNonzero(hyps, t); w != nil {
		return w
	}
	return b.unitNonzero(hyps, t)
}

// residentNonzero proves Γ ⊢ ¬(t = zero) from the evidence that names t:
// the disequality itself, an embedded real ℝ shows nonzero, or a
// resident disequality the assumption t = zero contradicts.
func (b *boundRing) residentNonzero(hyps []Term, t Term) *prop.PropWrapper {
	isZero := core.Eq(t, b.sr.comps.zero)
	target := not(isZero)
	for _, h := range hyps {
		if h.AlphaEquals(target) {
			return prop.Assume(h)
		}
	}
	for _, h := range hyps {
		if w := conjunctProof(h, target); w != nil {
			return w
		}
	}
	if w := b.embeddedNonzero(hyps, t); w != nil {
		return w
	}
	assumed := append(slices.Clone(hyps), isZero)
	for _, d := range b.disequalities(hyps) {
		if !b.members.proveAtoms(d.p, d.q) {
			continue
		}
		eq, ok := b.proveEqWithoutUnitsSigned(assumed, d.p, d.q) // {hyps, t = zero} ⊢ p = q
		if !ok {
			eq, ok = b.proveEqUnderZero(hyps, t, isZero, d.p, d.q)
		}
		if !ok {
			continue
		}
		contra := prop.WrapProp(prop.Contradict(core.Eq(d.p, d.q)).DeriveHypFrom(eq))
		contra = prop.WrapProp(d.proof.MaybeDeriveTrans(contra)) // {hyps, t = zero} ⊢ ⊥
		return contra.NegHyp(isZero)
	}
	return nil
}

// proveEqUnderZero proves {hyps, t = zero} ⊢ p = q where zero put for t
// makes p and q equal by a ring identity or the context's equations
// (equalWithZeroPut). ok=false where t stands in neither side, where the
// two sides still differ, and where t occurs in the zero.
func (b *boundRing) proveEqUnderZero(hyps []Term, t, isZero, p, q Term) (*prop.PropWrapper, bool) {
	return equalWithZeroPut(t, b.sr.comps.zero, isZero, p, q, func(p, q Term) (*prop.PropWrapper, bool) {
		return b.proveEqWithoutUnitsSigned(hyps, p, q)
	})
}

// embeddedNonzero proves Γ ⊢ ¬(t = zero) for t = embed(r) at an instance
// with an embedding of ℝ, from ℝ's evidence Γ ⊢ ¬(r = &0); nil when the
// ring has no embedding, the decision's policy withholds ℝ's arithmetic
// (realEvidence), t is not embed-shaped, or ℝ shows nothing.
func (b *boundRing) embeddedNonzero(hyps []Term, t Term) *prop.PropWrapper {
	if !b.realEvidence || b.sr.instance == nil || b.sr.instance.RealEmbedding == nil {
		return nil
	}
	e := b.sr.instance.RealEmbedding
	app, ok := t.AsAppliedTerm()
	if !ok || !app.Fun().AlphaEquals(e.Map) {
		return nil
	}
	r := app.Arg()
	rNonzero := realProveNeqZero(hyps, r) // Γ ⊢ ¬(r = &0)
	if rNonzero == nil {
		return nil
	}
	isZero := core.Eq(t, b.sr.comps.zero)
	injective := e.Injective.ConclForAllInsts(r, realLit(0))                          // ⊢ embed(r) = embed(&0) ⇔ r = &0
	rZero := injective.EqMP(prop.Assume(isZero))                                      // {t = zero} ⊢ r = &0
	contra := prop.WrapProp(prop.Contradict(rZero.Conclusion()).DeriveHypFrom(rZero)) // {t = zero, ¬(r = &0)} ⊢ ⊥
	contra = prop.WrapProp(rNonzero.MaybeDeriveTrans(contra))                         // {Γ, t = zero} ⊢ ⊥
	return contra.NegHyp(isZero)
}

// checkRealEmbedding panics unless e maps ℝ into instance i's carrier,
// injectively by its law, with the carrier's zero its value at &0 — the
// three facts embeddedNonzero reads.
func checkRealEmbedding(i int, e *RealEmbedding, comps structureComponents) {
	if e.Map == nil || e.Injective == nil {
		panic(fmt.Sprintf("omega.SetStructureInstances: instance %d names an embedding of ℝ without its map or its injectivity", i))
	}
	if want := core.MakeFun(dsl.RealType, comps.carrier()); !e.Map.Type().Equals(want) {
		panic(fmt.Sprintf("omega.SetStructureInstances: instance %d's embedding of ℝ %s is not a map real → carrier",
			i, ext.PrintTerm(e.Map)))
	}
	if zero := ext.Apply(e.Map, realLit(0)); !zero.AlphaEquals(comps.zero) {
		panic(fmt.Sprintf("omega.SetStructureInstances: instance %d's embedding of ℝ sends &0 to %s, not the carrier's zero %s",
			i, ext.PrintTerm(zero), ext.PrintTerm(comps.zero)))
	}
	x, y := ext.Var("x", dsl.RealType).Core(), ext.Var("y", dsl.RealType).Core()
	law := e.Injective.ConclForAllInsts(x, y)
	want := core.Eq(core.Eq(ext.Apply(e.Map, x), ext.Apply(e.Map, y)), core.Eq(x, y))
	if law.NumHyps() > 0 || !law.Conclusion().AlphaEquals(want) {
		panic(fmt.Sprintf("omega.SetStructureInstances: instance %d's injectivity law is not `∀x y:real. %s`: %s",
			i, ext.PrintTerm(want), ext.PrintTerm(e.Injective.Conclusion())))
	}
}

// proveEqWithoutUnitsSigned is proveEqWithoutUnits for an equation that
// may carry sub/neg: positivized first, as the move-across leaf does for
// a goal, since the combination reads the positive form.
func (b *boundRing) proveEqWithoutUnitsSigned(hyps []Term, l, r Term) (*prop.PropWrapper, bool) {
	if !b.subneg.hasSubNeg(l) && !b.subneg.hasSubNeg(r) {
		return b.proveEqWithoutUnits(hyps, l, r)
	}
	mv := b.moveAcross(core.Eq(l, r))
	if mv == nil {
		return nil, false
	}
	pl, pr, ok := ext.MatchesEQ(prop.Rhs(mv))
	if !ok {
		return nil, false
	}
	w, ok := b.proveEqWithoutUnits(hyps, pl, pr)
	if !ok {
		return nil, false
	}
	return mv.EqSym().EqMP(w), true
}

// unitFact proves Γ ⊢ R · (inv(t)·t) = R — `inv(t)·t = one` for the
// empty cofactor — from neq, Γ ⊢ ¬(t = zero); nil when a membership
// it needs is not held.
func (b *boundRing) unitFact(t Term, cofactor []Term, neq *prop.PropWrapper) *prop.PropWrapper {
	sr := b.sr
	c, laws := sr.comps, sr.laws
	law := laws.at(laws.MulLeftInverse, []Term{c.fieldRecord}, sr.fieldFact, t) // Γ ⊢ t ∈ c ∧ t ≠ zero ⇒ inv t · t = one
	guard, _, ok := prop.MatchesIMPLY(law.Conclusion())
	if !ok {
		panic(fmt.Sprintf("omega: the field's left inverse law has no guard: %s", ext.PrintTerm(law.Conclusion())))
	}
	member, nonzero, ok := prop.MatchesAND(guard)
	if !ok || !nonzero.AlphaEquals(neq.Conclusion()) {
		panic(fmt.Sprintf("omega: the field's left inverse law is not guarded by `%s ∧ %s`: %s",
			ext.PrintTerm(b.members.membership(t)), ext.PrintTerm(neq.Conclusion()), ext.PrintTerm(guard)))
	}
	memberProof, ok := b.members.prove(t)
	if !ok {
		return nil
	}
	both := prop.WrapProp(neq.MaybeDeriveTrans(prop.ConclAND(member, nonzero).DeriveHypFrom(memberProof)))
	unit := law.DemoteHyp().DeriveHypFrom(both) // Γ ⊢ inv t · t = one
	if len(cofactor) == 0 {
		return unit
	}
	r := b.ring.monoProductOf(cofactor)
	if _, ok := b.members.prove(r); !ok {
		return nil
	}
	scaled := unit.LeftApply(b.ring.starLeft(r))                                                   // Γ ⊢ R·(inv t · t) = R·one
	return scaled.EqTrans(b.at(laws.RightIdentity, []Term{sr.set, c.mul, c.one}, sr.monoidMul, r)) // = R
}

// unitEquations is the unit facts the sequent asks for, as equations the
// combination reads: the sequent is the goal `l = r` and the context's
// equations eqs, both in the positive form the combination reads. Empty
// at a ring that is no field, and when no side holds an inverse.
func (b *boundRing) unitEquations(hyps []Term, eqs []equationHyp, l, r Term) []equationHyp {
	if b.sr.comps.fieldRecord == nil {
		return nil
	}
	sides := []Term{l, r}
	for _, e := range eqs {
		sides = append(sides, e.lhs, e.rhs)
	}
	if !slices.ContainsFunc(sides, b.mentionsInverse) {
		return nil
	}
	divisors := unitCofactors(sides, b.subneg, b.matchInv,
		func(t Term) *prop.PropWrapper { return b.proveNonzero(hyps, t) })
	facts := unitFactsOf(divisors, b.unitFact, func(fact Term) bool {
		return slices.ContainsFunc(hyps, fact.AlphaEquals)
	})
	var out []equationHyp
	for _, f := range facts {
		if eh, ok := b.equationHyp(f); ok {
			out = append(out, eh)
		}
	}
	return out
}
