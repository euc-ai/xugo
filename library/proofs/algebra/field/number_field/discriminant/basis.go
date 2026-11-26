package discriminant

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var DiscriminantBasisChange = discriminantBasisChangeThm{family.Add(registry.ProofEntry{
	Name: "DiscriminantBasisChange",
	Key:  "prop_788cb2e00568e6ff",
	Deps: []registry.EntryLike{
		DiscriminantDef,
		field_trace.FieldTraceLinear,
		determinant.DeterminantMultiplicative,
		determinant.DeterminantTranspose,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e f:(num → A). ∀U:(num → num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"matrix_over(restrict_ring(field_ring(L), rational_image(L)), n, U)",
			"∀i:num. " +
				"    i < n ⇒ " +
				"    e(i) ∈ L.carrier ∧ f(i) = module_sum(L.add, L.zero, {j:num | j < n}, λj:num. e(j) * U(j, i))",
		},
		Conclusion: "basis_discriminant(L, n, f) = " +
			"monoid_pow(L.mul, " +
			"    L.one, " +
			"    determinant(restrict_ring(field_ring(L), rational_image(L)), n, U), " +
			"    2) * " +
			"basis_discriminant(L, n, e)",
	},
		"Bilinearity gives Gram(f)=Uᵀ Gram(e) U. Apply determinant multiplicativity and "+
			"transpose invariance; this identity does not require either tuple to be a basis."),
})}

var DiscriminantNonzero = discriminantNonzeroThm{family.Add(registry.ProofEntry{
	Name: "DiscriminantNonzero",
	Key:  "prop_6891f15aecf3af05",
	Deps: []registry.EntryLike{
		DiscriminantDef,
		field_trace.CharZeroTraceNondegenerate,
		determinant.DeterminantZeroIffDependent,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"indexed_module_basis(restrict_ring(field_ring(L), rational_image(L)), " +
				"    regular_module(field_ring(L)), " +
				"    n, " +
				"    e)",
		},
		Conclusion: "basis_discriminant(L, n, e) ≠ L.zero",
	},
		"A vector annihilated by the Gram matrix pairs to zero with a "+
			"rational basis and hence with the entire field. Trace nondegeneracy "+
			"forces that vector to vanish, so the Gram determinant is nonzero."),
})}

var IntegralBasisDiscriminantIndependent = integralBasisDiscriminantIndependentThm{family.Add(registry.ProofEntry{
	Name: "IntegralBasisDiscriminantIndependent",
	Key:  "prop_c4338f54bf31422e",
	Deps: []registry.EntryLike{
		IntegerFieldDiscriminantDef,
		DiscriminantBasisChange,
		DiscriminantNonzero,
		ring_of_integers.IntegralTraceInInt,
		lattice_determinant.DeterminantIntegralEntries,
		lattice_determinant.IntegerBasisChangeDetUnit,
		ring_of_integers.RingOfIntegersFreeRankN,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀e:(num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"integral_basis(field_ring(L), n, e)",
		},
		Conclusion: "integer_field_discriminant(L) ≠ 0 ∧ " +
			"basis_discriminant(L, n, e) = integer_map(field_ring(L), integer_field_discriminant(L))",
	},
		"Traces of products of integers give integral Gram entries. Integral basis changes "+
			"have determinant ±1, so their square leaves the nonzero discriminant unchanged."),
})}
