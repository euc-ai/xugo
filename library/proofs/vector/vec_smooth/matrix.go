// Smooth matrix operations are read entry by entry on a fixed finite block.

package vec_smooth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothDeterminant = smoothDeterminantThm{family.Add(registry.ProofEntry{
	Name: "SmoothDeterminant",
	Key:  "prop_bcd548067a1ec33d",
	Deps: []registry.EntryLike{determinant.DeterminantDef, SmoothConst, SmoothAdd, SmoothMul},
	Build: family.Card(Statement{
		Binders: "∀d n:num. ∀U:set(num → real). ∀P:((num → real) → num → num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(d)",
			"∀r s:num. r < n ∧ s < n ⇒ vec_smooth_on⟨d⟩(U, λx:(num → real). P(x, r, s))",
		},
		Conclusion: "vec_smooth_on⟨d⟩(U, λx:(num → real). determinant(real_ring, n, P(x)))",
	},
		"The Leibniz formula is a finite sum of finite products of active entries "+
			"and constant signs. Induction on the finite indexing sets uses SmoothConst, "+
			"SmoothAdd and SmoothMul; at n = 0 the determinant is the constant one."),
})}

var SmoothAdjugate = smoothAdjugateThm{family.Add(registry.ProofEntry{
	Name: "SmoothAdjugate",
	Key:  "prop_5581c109b0a6dcb6",
	Reading: "Only the active entries of P matter. For either output " +
		"index outside the n-square, the adjugate entry is identically zero.",
	Deps: []registry.EntryLike{determinant.AdjugateDef, SmoothDeterminant, SmoothConst},
	Build: family.Card(Statement{
		Binders: "∀d n i j:num. ∀U:set(num → real). ∀P:((num → real) → num → num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(d)",
			"∀r s:num. r < n ∧ s < n ⇒ vec_smooth_on⟨d⟩(U, λx:(num → real). P(x, r, s))",
		},
		Conclusion: "vec_smooth_on⟨d⟩(U, λx:(num → real). matrix_adjugate(real_ring, n, P(x), i, j))",
	},
		"For fixed active output indices, each entry of the replaced-column matrix "+
			"is an entry of P or a constant basis entry; apply SmoothDeterminant. For "+
			"either inactive output index, use SmoothConst at zero."),
})}

var SmoothMatrixInverse = smoothMatrixInverseThm{family.Add(registry.ProofEntry{
	Name: "SmoothMatrixInverse",
	Key:  "prop_8e4515cc797f047c",
	Deps: []registry.EntryLike{
		determinant.MatrixInverseDef,
		real_field.RealFieldRing,
		SmoothDeterminant,
		SmoothAdjugate,
		SmoothReciprocal,
		SmoothMul,
		SmoothConst,
	},
	Build: family.Card(Statement{
		Binders: "∀d n i j:num. ∀U:set(num → real). ∀P:((num → real) → num → num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(d)",
			"∀r s:num. r < n ∧ s < n ⇒ vec_smooth_on⟨d⟩(U, λx:(num → real). P(x, r, s))",
			"∀x:(num → real). x ∈ U ⇒ determinant(real_ring, n, P(x)) ≠ &0",
		},
		Conclusion: "vec_smooth_on⟨d⟩(U, λx:(num → real). matrix_inverse(real_field_ops, n, P(x), i, j))",
	},
		"RealFieldRing identifies the ring in the cofactor formula with real_ring. For "+
			"active output indices multiply the smooth adjugate entry by the smooth "+
			"reciprocal of the nowhere-zero determinant; inactive entries are constant zero."),
})}
