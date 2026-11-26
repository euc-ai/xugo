package different

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/discriminant"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

var MonogenicDifferent = monogenicDifferentThm{family.Add(registry.ProofEntry{
	Name: "MonogenicDifferent",
	Key:  "prop_ba7a0597e09ea57d",
	Reading: "The premise is O_K=Z[y], stronger than " +
		"K=Q(y); arbitrary integer rings need not be monogenic.",
	Deps: []registry.EntryLike{
		DifferentDef,
		discriminant.IntegralMinimalPolynomialCoefficients,
		separable_polynomial.CharZeroIrreducibleSeparable,
		ring_of_integers.RingOfIntegersFractionField,
		trace_dual.MonogenicCodifferent,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀y:A.",
		Hypotheses: []string{
			"number_field(L)",
			"y ∈ L.carrier",
			"ring_of_integers(field_ring(L)) = " +
				"polynomial_image(field_ring(L), integer_image(field_ring(L)), y)",
		},
		Conclusion: "trace_dual(L, " +
			"    rational_image(L), " +
			"    ring_of_integers(field_ring(L)), " +
			"    integer_image(field_ring(L))) = " +
			"image(L.mul(L.inv(polynomial_eval( " +
			"                polynomial_derivative(minimal_polynomial(L, rational_image(L), y)), y))), " +
			"    ring_of_integers(field_ring(L))) ∧ " +
			"number_different(L) = " +
			"image(L.mul(polynomial_eval(polynomial_derivative(minimal_polynomial(L, rational_image(L), y)), " +
			"            y)), " +
			"    ring_of_integers(field_ring(L)))",
	},
		"The monogenic integer-ring assumption and its fraction field make y a primitive "+
			"field generator. The minimal polynomial has integer coefficients and is separable "+
			"in characteristic zero, so the general monogenic codifferent formula applies."),
})}
