// Positive orthonormal frames have a smooth metric dual coframe.

package riemannian

import (
	"github.com/euc-ai/xugo/library/registry"
)

var PositiveFrameDef = positiveFrameDefThm{family.Define(registry.DefEntry{
	Name:  "PositiveFrameDef",
	Key:   "prop_b6371da766ff9398",
	Const: "riemannian_positive_frame",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"bool",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{MetricDef},
	Reading: "The columns are orthonormal for g in chart c, and positive relative to " +
		"the ordered coordinate basis of c. Thus they agree with a manifold orientation when " +
		"c is a positive chart; no orientation of the manifold is implicit in this predicate. " +
		"Values outside the coordinate image are zero, with no boundary smoothness requirement.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"    riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E) ⇔ " +
			"    riemannian_metric⟨n⟩(T, 𝒜, g) ∧ " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"    (∀y:(num → real). " +
			"        matrix⟨n, n⟩(E(y)) ∧ (y ∉ «chart image»(c) ⇒ E(y) = «zero real matrix»)) ∧ " +
			"    (∀i j:num. " +
			"        i < n ∧ j < n ⇒ vec_smooth_on⟨n⟩(«chart image»(c), λy:(num → real). E(y, i, j))) ∧ " +
			"    (∀y:(num → real). " +
			"        y ∈ «chart image»(c) ⇒ " +
			"        matrix_product(real_ring, " +
			"            n, " +
			"            transpose(E(y)), " +
			"            matrix_product(real_ring, n, g(c, y), E(y))) = " +
			"        matrix_identity(real_ring, n) ∧ " +
			"        &0 < determinant(real_ring, n, E(y)))",
	},
})}

var coframeDef = coframeDefThm{family.Define(registry.DefEntry{
	Name:  "coframeDef",
	Key:   "prop_fc9d379380bc0046",
	Const: "riemannian_coframe",
	Type: "num → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"(num → num → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Reading: "The coframe is an n by 1 matrix of one-forms. Its coefficient matrix is " +
		"E-transpose times G; for an orthonormal frame this is the inverse of E. The definition does " +
		"not choose a matrix inverse and reads only the first vector column of the form argument.",
	Equations: []string{
		"∀n:num. " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀a b:num. " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    riemannian_coframe⟨n⟩(g, c, E, a, b, y, P) = " +
			"    COND(a < n ∧ b = 0 ∧ y ∈ «chart image»(c), Σ_{i<n} «dual matrix»(y, a, i) * P(i, 0), &0)",
	},
})}
