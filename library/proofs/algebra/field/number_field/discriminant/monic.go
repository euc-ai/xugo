package discriminant

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/registry"
)

var GaussMonicFactor = gaussMonicFactorThm{family.Add(registry.ProofEntry{
	Name: "GaussMonicFactor",
	Key:  "prop_65a67f170bea7928",
	Deps: []registry.EntryLike{
		int_lattice.IntegerRationalImagesStructure,
		int_divides.Bezout,
		polynomial.PolynomialMulDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀p q r:(num → A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"polynomial_over(integer_image(field_ring(L)), p)",
			"polynomial_monic(p)",
			"polynomial_over(rational_image(L), q)",
			"polynomial_over(rational_image(L), r)",
			"polynomial_monic(q)",
			"polynomial_monic(r)",
			"p = polynomial_mul(q, r)",
		},
		Conclusion: "polynomial_over(integer_image(field_ring(L)), q) ∧ " +
			"polynomial_over(integer_image(field_ring(L)), r)",
	},
		"Clear integer denominators and separate contents of the two factors. The primitive-product "+
			"lemma from integer Bezout forces the monic rational factors to have integral coefficients."),
})}

var IntegralMinimalPolynomialCoefficients = integralMinimalPolynomialCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "IntegralMinimalPolynomialCoefficients",
	Key:  "prop_d85124170a11b5e5",
	Deps: []registry.EntryLike{
		GaussMonicFactor,
		algebraic_element.MinimalPolynomialSpec,
		integral_closure.RingOfIntegersDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀x:A.",
		Hypotheses: []string{
			"number_field(L)",
			"x ∈ L.carrier",
		},
		Conclusion: "x ∈ ring_of_integers(field_ring(L)) ⇔ " +
			"polynomial_over(integer_image(field_ring(L)), minimal_polynomial(L, rational_image(L), x))",
	},
		"An integral monic relation is divisible by the rational minimal "+
			"polynomial with a monic rational quotient; apply GaussMonicFactor. "+
			"Conversely the minimal polynomial itself is the monic integral relation."),
})}
