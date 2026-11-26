// scaled_value.go — the value of a polynomial at a nonzero point, read as a
// value of a polynomial in the inverse point.

package algebraic_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ScaledValueInInverseImage — for a nonzero a and a polynomial p over a subring
// S of degree at most m, a^(−m)·p(a) lies in S[a⁻¹]. Rescaling the variable by
// a⁻¹ (polynomial_evaluation.EvalRescaled at weight one) writes a^(−m)·p(a) as the value
// at a⁻¹·a = 1 of the polynomial with coefficients a^(−(m−j))·p(j), whose
// coefficients lie in the ring S[a⁻¹]; so does its value at one.
var ScaledValueInInverseImage = scaledValueInInverseImageThm{family.Add(registry.ProofEntry{
	Name: "ScaledValueInInverseImage",
	Key:  "prop_adb342f703582f9d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀a:A. ∀m:num. ∀p:(num → A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"a ∈ L.carrier",
			"a ≠ L.zero",
			"polynomial_over(S, p)",
			"polynomial_degree(p) ≤ m",
		},
		Conclusion: "monoid_pow(L.mul, L.one, L.inv(a), m) * polynomial_eval(p, a) ∈ «image»",
		Abbrev: Abbrev{
			{Name: "image", Text: "polynomial_image(field_ring(L), S, L.inv(a))"},
			{Name: "rescaled", Text: "λj:num. " +
				"    COND(j ≤ m, monoid_pow(L.mul, L.one, L.inv(a), m - j) * p(j), L.zero)"},
		},
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		a *Expr[A],
		m *Expr[Nat],
		p *Arrow[Nat, A],
		h Fact,
	) {
		parts := arg.Conjuncts(
			h,
			"S is a subring of L",
			"a lies in L",
			"a is not zero",
			"p is a polynomial over S",
			"of degree at most m")
		subringS, aIn, nonzero, pOver, degree := parts[0], parts[1], parts[2], parts[3], parts[4]
		ring := field.RingOn.Read(L)
		aM := arg.MemberOf[on.L](a, aIn)
		inverse := arg.MemberOf[on.L](
			arg.TermAs[A]("L.inv(a)"),
			arg.Have(
				"a⁻¹ lies in L",
				"L.inv(a) ∈ L.carrier",
				By(aIn, field.InvIn.Read(L))))
		image := arg.TermAs[Set[A]]("«image»")
		rescaled := arg.TermAs[Fun[Nat, A]]("«rescaled»")
		one := arg.TermAs[A]("L.one")
		pOverL := arg.Have(
			"p is a polynomial over L, S lying in L",
			"polynomial_over(L.carrier, p)",
			By(
				pOver,
				comm_ring.SubringSubset.Read(subringS),
				polynomial.PolynomialOverMono.At(arg.TermAs[A]("L.zero"), S, arg.TermAs[Set[A]]("L.carrier"), p)))
		unit := arg.Have(
			"the first power of a⁻¹ times a is one",
			"monoid_pow(L.mul, L.one, L.inv(a), 1) * a = L.one",
			By(
				nonzero,
				inverse,
				field.MulLeftInverseOn.Read(L).At(aM),
				comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(inverse)))
		atOne := arg.Have(
			"rescaling the variable by a⁻¹ at weight one, the rescaled "+
				"polynomial takes at a⁻¹·a = 1 the value a^(−m)·p(a)",
			"polynomial_eval(«rescaled», L.one) = "+
				"monoid_pow(L.mul, L.one, L.inv(a), m) * polynomial_eval(p, a)",
			By(
				pOverL,
				degree,
				polynomial_evaluation.EvalRescaled.Read(ring).At(p, m, arg.TermAs[Nat]("1"), inverse, aM),
				nat_arith.OneMul,
				unit))
		imageFacts := arg.Conjuncts(
			GroupPremises(subringS, PolynomialImageSubring.Read(L).At(S, inverse)),
			"S[a⁻¹] is a subring of L",
			"holding S",
			"and a⁻¹")
		imageRing := arg.Have(
			"S[a⁻¹] is a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), «image»))",
			By(imageFacts[0], comm_ring.SubringRingOn.Read(ring).At(image)))
		pInImage := arg.Have(
			"the coefficients of p lie in S[a⁻¹]",
			"∀j:num. p(j) ∈ «image»",
			By(imageFacts[1], pOver, polynomial.PolynomialOverDef, set_basic.SubsetDef))
		coefficients := arg.Have(
			"so do those of the rescaled polynomial, products "+
				"of a power of a⁻¹ and a coefficient of p, or zero",
			"∀j:num. «rescaled»(j) ∈ «image»",
			By(
				pInImage,
				imageFacts[2],
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(imageRing)),
				comm_ring.MulIn.Read(imageRing),
				comm_ring.ZeroIn.Read(imageRing)))
		past := arg.Have(
			"the rescaled polynomial vanishes past m",
			"vec⟨suc(m)⟩(«rescaled»)",
			ByArith(vec_space.VecDef))
		rescaledOver := arg.Have(
			"so it is a polynomial over S[a⁻¹]",
			"polynomial_over(«image», «rescaled»)",
			By(coefficients, past, polynomial.PolynomialOverDef))
		arg.Show(
			"its value at one lies in the ring S[a⁻¹]",
			By(
				atOne,
				rescaledOver,
				comm_ring.OneIn.Read(imageRing),
				polynomial_evaluation.EvalIn.Read(imageRing).AsFact().At(rescaled, one)))
	}),
})}
