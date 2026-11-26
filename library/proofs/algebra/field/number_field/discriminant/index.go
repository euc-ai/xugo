package discriminant

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var DiscriminantIndexSquare = discriminantIndexSquareThm{family.Add(registry.ProofEntry{
	Name: "DiscriminantIndexSquare",
	Key:  "prop_cf069edb7c3d6ad9",
	Deps: []registry.EntryLike{
		DiscriminantBasisChange,
		IntegralBasisDiscriminantIndependent,
		lattice_determinant.LatticeIndexEqAbsDet,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀M:set(A). ∀n:num. ∀e:(num → A).",
		Hypotheses: []string{
			"number_field(L)",
			"full_integer_lattice(L, M)",
			"M ⊆ ring_of_integers(field_ring(L))",
			"indexed_module_basis(restrict_ring(field_ring(L), integer_image(field_ring(L))), " +
				"    restrict_module(regular_module(field_ring(L)), M), " +
				"    n, " +
				"    e)",
		},
		Conclusion: "finite(left_cosets(L.add, ring_of_integers(field_ring(L)), M)) ∧ " +
			"basis_discriminant(L, n, e) = " +
			"integer_map(field_ring(L), " +
			"    int_of_num(card(left_cosets(L.add, ring_of_integers(field_ring(L)), M)) ^ 2) * " +
			"    integer_field_discriminant(L))",
	},
		"Compare the sublattice basis with an integral basis of the integer ring. The "+
			"basis-change determinant squares its absolute value, which is the finite lattice index."),
})}
