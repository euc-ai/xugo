package pfaffian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

var PfaffianInCarrier = pfaffianInCarrierThm{family.Add(registry.ProofEntry{
	Name: "PfaffianInCarrier",
	Key:  "prop_f5623a042a05be5d",
	Deps: []registry.EntryLike{PfaffianDef, symmetric_group.SymmetricGroupFinite},
	Build: family.Card(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "pfaffian(c, n, P) ∈ c.carrier",
	},
		"The matching set is a subset of a finite symmetric group. Every sign and active entry belongs "+
			"to the carrier, which is closed under the two finite folds; in odd dimension the value is zero."),
})}

var PfaffianEmpty = pfaffianEmptyThm{family.Add(registry.ProofEntry{
	Name: "PfaffianEmpty",
	Key:  "prop_71969e03d9c97526",
	Deps: []registry.EntryLike{PfaffianDef, symmetric_group.SymmetricGroupEmpty},
	Build: family.Card("∀c:comm_ring_on(A). ∀P:(num → num → A). pfaffian(c, 0, P) = c.one",
		"The empty symmetric group consists of the identity, whose inversion count "+
			"is zero. Its entry product is empty and hence one; no entry of P is read."),
})}

var PfaffianCongruence = pfaffianCongruenceThm{family.Add(registry.ProofEntry{
	Name: "PfaffianCongruence",
	Key:  "prop_9fe5ae3ab0f1d312",
	Reading: "An arbitrary change of frame contributes det(Q); invariance requires " +
		"det(Q) = 1. No invertibility hypothesis is needed for the polynomial identity.",
	Deps: []registry.EntryLike{
		PfaffianInCarrier,
		matrix.AlternatingMatrixDef,
		determinant.AlternatingFormUniversal,
		determinant.MatrixProductOver,
		determinant.MatrixProductRightIdentity,
	},
	Build: family.Card(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀m:num. ∀P Q:(num → num → A).",
		Hypotheses: []string{"matrix_alternating(c, 2 * m, P)", "matrix_over(c, 2 * m, Q)"},
		Conclusion: "pfaffian(c, " +
			"    2 * m, " +
			"    matrix_product(c, 2 * m, transpose(Q), matrix_product(c, 2 * m, P, Q))) = " +
			"c.mul(determinant(c, 2 * m, Q), pfaffian(c, 2 * m, P))",
	},
		"Expand the matching sum to show Q ↦ pf(QᵀPQ) is an alternating multilinear form in the columns "+
			"of Q: equal-column terms cancel in pairs, and the remaining same-column factors vanish by the "+
			"zero diagonal of the alternating bilinear form. AlternatingFormUniversal identifies it with its "+
			"identity value times det(Q); the cancellations use additive inverses, never division by two."),
})}

var PfaffianDeterminant = pfaffianDeterminantThm{family.Add(registry.ProofEntry{
	Name: "PfaffianDeterminant",
	Key:  "prop_14e9b601e9a827e",
	Deps: []registry.EntryLike{
		PfaffianDef,
		matrix.AlternatingMatrixDef,
		determinant.DeterminantDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀m:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_alternating(c, 2 * m, P)"},
		Conclusion: "determinant(c, 2 * m, P) = c.mul(pfaffian(c, 2 * m, P), pfaffian(c, 2 * m, P))",
	},
		"Expand the determinant and the product of matching sums. Reverse the first odd cycle to "+
			"cancel its pair of Leibniz terms; the remaining even-cycle terms agree with the ordered "+
			"matching-pair expansion, including signs. This finite combinatorial identity works over "+
			"every commutative ring, including characteristic two; the empty expansions both give one."),
})}

var PfaffianUnimodularKernel = pfaffianUnimodularKernelThm{family.Add(registry.ProofEntry{
	Name: "PfaffianUnimodularKernel",
	Key:  "prop_272ce51a782469e9",
	Reading: "The dual vector w with pairing one is essential over rings with zero " +
		"divisors: a merely nonzero kernel vector is insufficient. At m = 0 the " +
		"pairing condition forces zero = one, and the empty Pfaffian then also vanishes.",
	Deps: []registry.EntryLike{PfaffianDef, PfaffianEmpty, matrix.AlternatingMatrixDef},
	Build: family.Card(Statement{
		Binders: "∀c:comm_ring_on(A). ∀m:num. ∀P:(num → num → A). ∀v w:(num → A).",
		Hypotheses: []string{
			"matrix_alternating(c, 2 * m, P)",
			"v ∈ free_module_record(c, {i:num | i < 2 * m}).carrier",
			"w ∈ free_module_record(c, {i:num | i < 2 * m}).carrier",
			"module_sum(c.add, c.zero, {i:num | i < 2 * m}, λi:num. c.mul(w(i), v(i))) = c.one",
			"∀i:num. " +
				"    i < 2 * m ⇒ " +
				"    module_sum(c.add, c.zero, {j:num | j < 2 * m}, λj:num. c.mul(P(i, j), v(j))) = c.zero",
		},
		Conclusion: "pfaffian(c, 2 * m, P) = c.zero",
	},
		"For positive even size, expand the matching sum at a row to form the signed "+
			"Pfaffian cofactor matrix B and establish BP = pf(P)I. Applying it to Pv = 0 gives "+
			"pf(P)v = 0, and pairing with w gives pf(P) = 0. The size-zero case follows from "+
			"PfaffianEmpty and the empty pairing; no conclusion is drawn merely from det(P) = 0."),
})}
