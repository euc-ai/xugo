package trace_dual

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/registry"
)

var MonogenicCodifferent = monogenicCodifferentThm{family.Add(registry.ProofEntry{
	Name: "MonogenicCodifferent",
	Key:  "prop_a0a816cd3992fed9",
	Deps: []registry.EntryLike{
		field_trace.TraceDualBasis,
		field_trace.CofactorCoefficientsBasis,
		integral_element.MonicSubringPowerBasis,
		fractional_ideal.FractionalInverseScale,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S:set(A). ∀y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"y ∈ L.carrier",
			"algebraic_over(L, K, y)",
			"field_adjoin(L, K, {y}) = L.carrier",
			"polynomial_separable(«ScalarK», minimal_polynomial(L, K, y))",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"polynomial_over(S, minimal_polynomial(L, K, y))",
		},
		Conclusion: "trace_dual(L, K, polynomial_image(field_ring(L), S, y), S) = " +
			"image(L.mul(L.inv(polynomial_eval(polynomial_derivative(minimal_polynomial(L, K, y)), y))), " +
			"    polynomial_image(field_ring(L), S, y)) ∧ " +
			"fractional_inverse(field_ring(L), " +
			"    polynomial_image(field_ring(L), S, y), " +
			"    trace_dual(L, K, polynomial_image(field_ring(L), S, y), S)) = " +
			"image(L.mul(polynomial_eval(polynomial_derivative(minimal_polynomial(L, K, y)), y)), " +
			"    polynomial_image(field_ring(L), S, y))",
	},
		"The Euler trace-dual power basis consists of the cofactor "+
			"coefficients divided by the derivative. Those coefficients form "+
			"an S-basis of S[y]; invert the resulting nonzero principal ideal."),
})}
