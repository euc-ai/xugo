package determinant

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// AdjugateOver — the cofactor construction stays over the carrier ring.
var AdjugateOver = adjugateOverThm{family.Add(registry.ProofEntry{
	Name: "AdjugateOver",
	Key:  "prop_43f96df2610a9068",
	Deps: []registry.EntryLike{
		AdjugateDef,
		MatrixIdentityOver,
		ReplaceColumnMatrixOver,
		DeterminantInCarrier,
	},
	Build: family.Card(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "matrix_over(c, n, matrix_adjugate(c, n, P))",
	},
		"For active indices, the replacement column is a column of the identity and "+
			"ReplaceColumnMatrixOver puts the replacement matrix over c; DeterminantInCarrier "+
			"supplies its determinant. The defining guards give zero padding, including n = 0."),
})}

// AdjugateIdentity — multiplication on either side gives det(P) times I.
var AdjugateIdentity = adjugateIdentityThm{family.Add(registry.ProofEntry{
	Name: "AdjugateIdentity",
	Key:  "prop_3add676881481641",
	Deps: []registry.EntryLike{
		AdjugateOver,
		MultilinearColumnExpansion,
		DeterminantColumnMultilinear,
		DeterminantEqualColumns,
		DeterminantTranspose,
	},
	Build: family.Card(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "matrix_product(c, n, P, matrix_adjugate(c, n, P)) = " +
			"(λi:num. λj:num. c.mul(determinant(c, n, P), matrix_identity(c, n, i, j))) ∧ " +
			"matrix_product(c, n, matrix_adjugate(c, n, P), P) = " +
			"(λi:num. λj:num. c.mul(determinant(c, n, P), matrix_identity(c, n, i, j)))",
	},
		"Expand in the replacement column: the diagonal entries of adj(P)P are det(P), and "+
			"its off-diagonal entries are determinants with two equal columns. Transpose the "+
			"cofactor formula using DeterminantTranspose to obtain the other product; outside "+
			"the square both sides vanish. No division or nonzero determinant is needed."),
})}

// MatrixInverse — the cofactor formula is a two-sided inverse when det ≠ 0.
var MatrixInverse = matrixInverseThm{family.Add(registry.ProofEntry{
	Name: "MatrixInverse",
	Key:  "prop_137e299fce13504c",
	Deps: []registry.EntryLike{
		MatrixInverseDef,
		AdjugateIdentity,
		AdjugateOver,
		DeterminantInCarrier,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(field_ring(L), n, P)",
			"determinant(field_ring(L), n, P) ≠ L.zero",
		},
		Conclusion: "matrix_over(field_ring(L), n, matrix_inverse(L, n, P)) ∧ " +
			"matrix_product(field_ring(L), n, P, matrix_inverse(L, n, P)) = " +
			"matrix_identity(field_ring(L), n) ∧ " +
			"matrix_product(field_ring(L), n, matrix_inverse(L, n, P), P) = matrix_identity(field_ring(L), n)",
	},
		"DeterminantInCarrier permits the field inverse law. Pull the inverse determinant "+
			"through each finite sum in AdjugateIdentity and cancel the nonzero determinant; "+
			"AdjugateOver and closure under multiplication give the carrier condition."),
})}
