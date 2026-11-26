package different

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/discriminant"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ideal_norm"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/registry"
)

var CodifferentIndexDiscriminant = codifferentIndexDiscriminantThm{family.Add(registry.ProofEntry{
	Name: "CodifferentIndexDiscriminant",
	Key:  "prop_e5a4d6dd6f2c4a4c",
	Deps: []registry.EntryLike{
		CodifferentStructure,
		ring_of_integers.TraceDualFull,
		lattice_determinant.LatticeIndexEqAbsDet,
		discriminant.IntegralBasisDiscriminantIndependent,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "finite(left_cosets(L.add, " +
			"        trace_dual(L, " +
			"            rational_image(L), " +
			"            ring_of_integers(field_ring(L)), " +
			"            integer_image(field_ring(L))), " +
			"        ring_of_integers(field_ring(L)))) ∧ " +
			"card(left_cosets(L.add, " +
			"        trace_dual(L, " +
			"            rational_image(L), " +
			"            ring_of_integers(field_ring(L)), " +
			"            integer_image(field_ring(L))), " +
			"        ring_of_integers(field_ring(L)))) = " +
			"num_of_int(int_abs(integer_field_discriminant(L)))",
	},
		"Compare an integral basis with its trace-dual basis. The inverse coordinate "+
			"matrix is the trace Gram matrix, so the lattice index is its absolute determinant."),
})}

var DifferentNormDiscriminant = differentNormDiscriminantThm{family.Add(registry.ProofEntry{
	Name: "DifferentNormDiscriminant",
	Key:  "prop_f98c488b577cdd06",
	Reading: "This comparison uses quotient cardinality " +
		"directly and does not require fractional norm extension.",
	Deps: []registry.EntryLike{
		CodifferentStructure,
		CodifferentIndexDiscriminant,
		ideal_colength.InvertibleQuotientCardinality,
		ring_of_integers.NonzeroIdealFiniteIndex,
		ideal_norm.IdealNormDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "number_ideal_norm(field_ring(L), number_different(L)) = " +
			"num_of_int(int_abs(integer_field_discriminant(L)))",
	},
		"Twist R/D by the invertible codifferent. Since the product of different and codifferent is R, "+
			"its cardinality is that of the codifferent modulo R, already computed by the discriminant index."),
})}
