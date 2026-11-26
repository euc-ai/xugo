// definitions.go — the standard n-simplex of ℝⁿ⁺¹, the points with n + 1
// nonnegative coordinates summing to 1, and the affine maps between the
// standard simplices that the faces and the degeneracies of a simplicial
// set are read through.
//
// The coface and the codegeneracy are maps of sequences and read no
// dimension: the i-th coface inserts a zero coordinate at i and shifts the
// rest up, the i-th codegeneracy adds coordinates i and i + 1 and shifts
// the rest down. So the cosimplicial identities hold on every sequence,
// and only where a map lands is a question of dimension.

package euclidean_simplex

import (
	"github.com/euc-ai/xugo/library/registry"
)

// EuclideanSimplexDef — `euclidean_simplex(n)`: the standard n-simplex Δⁿ,
// the (n + 1)-vectors with nonnegative coordinates summing to 1. Δ⁰ is the
// one point e₀, Δ¹ the segment from e₀ to e₁.
var EuclideanSimplexDef = euclideanSimplexDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanSimplexDef",
	Key:   "prop_c594c32c911f7915",
	Const: "euclidean_simplex",
	Type:  "num → set(num → real)",
	Equations: []string{
		"∀n:num. " +
			"    euclidean_simplex(n) = " +
			"    {t:(num → real) | vec⟨n + 1⟩(t) ∧ (∀i:num. i ≤ n ⇒ &0 ≤ t(i)) ∧ Σ_{i<n + 1} t(i) = &1}",
	},
})}

// EuclideanCofaceDef — `euclidean_coface(i)`: a zero coordinate inserted
// at i, the coordinates from i on moved up one place. It carries Δⁿ onto
// the face of Δⁿ⁺¹ opposite the vertex eᵢ.
var EuclideanCofaceDef = euclideanCofaceDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanCofaceDef",
	Key:   "prop_241709352337b9ac",
	Const: "euclidean_coface",
	Type:  "num → (num → real) → num → real",
	Equations: []string{
		"∀i:num. " +
			"    euclidean_coface(i) = λt:(num → real). λj:num. COND(j < i, t(j), COND(j = i, &0, t(j - 1)))",
	},
})}

// EuclideanCodegeneracyDef — `euclidean_codegeneracy(i)`: coordinates i
// and i + 1 added into one, the coordinates past them moved down one
// place. It carries Δⁿ⁺¹ onto Δⁿ, collapsing the edge from eᵢ to eᵢ₊₁.
var EuclideanCodegeneracyDef = euclideanCodegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanCodegeneracyDef",
	Key:   "prop_dfcd9e785f7f01cf",
	Const: "euclidean_codegeneracy",
	Type:  "num → (num → real) → num → real",
	Equations: []string{
		"∀i:num. " +
			"    euclidean_codegeneracy(i) = " +
			"    λt:(num → real). λj:num. COND(j < i, t(j), COND(j = i, t(i) + t(i + 1), t(j + 1)))",
	},
})}
