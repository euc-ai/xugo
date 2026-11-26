// exterior_power.go — the exterior power of a square matrix in the binary
// basis is multiplicative (Cauchy–Binet), sends the identity to the
// identity and commutes with the transpose.

package exterior_basis

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

// ExteriorPowerProduct — the exterior power of a product is the product of
// the exterior powers.
var ExteriorPowerProduct = exteriorPowerProductThm{family.Add(registry.ProofEntry{
	Name: "ExteriorPowerProduct",
	Key:  "prop_9933e0ad2f788de4",
	Reading: "Both sides vanish off the square of the numbers below 2ʳ and " +
		"between different degrees. The commutative ring is load-bearing, as for the " +
		"multiplicativity of the determinant, the degree-r entry. Of matrix_over " +
		"only the carrier half is read: both sides read P and Q below r only.",
	Deps: []registry.EntryLike{
		MaskBijective,
		SlotSpec,
		determinant.DeterminantColumnMultilinear,
		determinant.ColumnMultilinearHom,
		module.ModuleSumMonoidHomomorphism,
		determinant.DeterminantEqualColumns,
		determinant.DeterminantAlternating,
		determinant.PinnedMapsExtension,
		determinant.PinnedMapsFinite,
		determinant.DeterminantMultiplicative,
		determinant.AlternatingFormPermutationExpansion,
	},
	Build: family.Card(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀r:num. ∀P Q:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, r, P)", "matrix_over(c, r, Q)"},
		Conclusion: "exterior_power(c, r, matrix_product(c, r, P, Q)) = " +
			"matrix_product(c, nat_pow(2, r), exterior_power(c, r, P), exterior_power(c, r, Q))",
	},
		"Cauchy–Binet: the minor of PQ on rows I and columns J, of size k, is the sum over the "+
			"k-element subsets K of {0, …, r − 1} of the minor of P on (I, K) times the minor of Q on (K, "+
			"J). Pad each minor with zeros outside its k × k block, which the determinant does not read, so "+
			"matrix_over holds. A column of the product minor is a sum over the r columns of P on the rows "+
			"I; the determinant is linear in each column (DeterminantColumnMultilinear, "+
			"ColumnMultilinearHom) and carries the finite sums out (ModuleSumMonoidHomomorphism), column by "+
			"column, to one sum over the maps from the k columns into the r indices (PinnedMapsExtension, "+
			"PinnedMapsFinite, at bound r) — MultilinearMapExpansion ranges only over maps of the n columns "+
			"into themselves. The terms whose chosen indices repeat vanish (DeterminantEqualColumns), and "+
			"the rest group by the set K of chosen indices, each the increasing listing of K composed with "+
			"a permutation σ: that minor of P is the minor on (I, K) times the permutation matrix of σ, so "+
			"its determinant is the product of the two (DeterminantMultiplicative), and summing σ against "+
			"Q's entries gives the determinant of Q on (K, J) (AlternatingFormPermutationExpansion at the "+
			"determinant, alternating by DeterminantAlternating). The subsets K are the masks of the "+
			"numbers below 2ʳ of degree k, each once (MaskBijective), listed by their slots (SlotSpec); a "+
			"number of another degree contributes 0 on the right"),
})}

// ExteriorPowerIdentity — the exterior power of the identity is the
// identity.
var ExteriorPowerIdentity = exteriorPowerIdentityThm{family.Add(registry.ProofEntry{
	Name: "ExteriorPowerIdentity",
	Key:  "prop_388b01b46e261330",
	Deps: []registry.EntryLike{
		MaskBijective,
		SlotSpec,
		determinant.DeterminantDef,
		determinant.DeterminantIdentity,
	},
	Build: family.Card(
		"∀c:comm_ring_on(A). ∀r:num. "+
			"    exterior_power(c, r, matrix_identity(c, r)) = matrix_identity(c, nat_pow(2, r))",
		"at a = b < 2ʳ the minor is the identity of the mask's size, the slots being distinct "+
			"digits below r (SlotSpec), of determinant one (determinant.DeterminantIdentity). For "+
			"a ≠ b of one degree the masks differ (MaskBijective) and have the same size, so some "+
			"slot of a is no digit of b (the slots exhaust each mask, SlotSpec and counting), and "+
			"the minor has a zero row, which kills every term of the Leibniz sum "+
			"(determinant.DeterminantDef). Other entries are zero on both sides"),
})}

// ExteriorPowerTranspose — the exterior power of the transpose is the
// transpose of the exterior power.
var ExteriorPowerTranspose = exteriorPowerTransposeThm{family.Add(registry.ProofEntry{
	Name:    "ExteriorPowerTranspose",
	Key:     "prop_22fafed485dfec27",
	Reading: "Of matrix_over only the carrier half is read, the minors reading P below r only.",
	Deps:    []registry.EntryLike{determinant.DeterminantTranspose},
	Build: family.Card(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀r:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, r, P)"},
		Conclusion: "exterior_power(c, r, transpose(P)) = transpose(exterior_power(c, r, P))",
	},
		"the minor of Pᵀ on (a, b) is the transpose of the minor of P on (b, a), "+
			"of the same determinant (determinant.DeterminantTranspose, read on the "+
			"minor's entries below its size), and the guard is symmetric in a and b"),
})}
