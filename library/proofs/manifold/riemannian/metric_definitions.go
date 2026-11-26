// Riemannian metrics are normalized compatible families of positive definite coordinate matrices.

package riemannian

import (
	_ "github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var MetricDef = metricDefThm{family.Define(registry.DefEntry{
	Name:  "MetricDef",
	Key:   "prop_dbb2975733faed03",
	Const: "riemannian_metric",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"bool",
	Dimensions: []string{"n"},
	Reading: "Every matrix is padded; incompatible charts and points outside the " +
		"coordinate image carry the zero matrix. Positive definiteness is tested on nonzero " +
		"padded vectors only at points in the image. Compatibility is covariant: the source " +
		"matrix is Jacobian-transpose times the target matrix times Jacobian. Dimension " +
		"zero has the unique empty matrix, and the empty manifold has the zero family.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"    riemannian_metric⟨n⟩(T, 𝒜, g) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀y:(num → real). matrix⟨n, n⟩(g(c, y))) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀y:(num → real). " +
			"        ¬(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ «chart image»(c)) ⇒ " +
			"        g(c, y) = «zero real matrix») ∧ " +
			"    (∀c:prod(set(A), A → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ⇒ " +
			"        (∀i j:num. " +
			"            i < n ∧ j < n ⇒ " +
			"            vec_smooth_on⟨n⟩(«chart image»(c), λy:(num → real). g(c, y, i, j))) ∧ " +
			"        (∀y:(num → real). " +
			"            y ∈ «chart image»(c) ⇒ " +
			"            transpose(g(c, y)) = g(c, y) ∧ " +
			"            (∀v:(num → real). " +
			"                vec⟨n⟩(v) ∧ v ≠ (λi:num. &0) ⇒ &0 < ⟪v, matrix_act⟨n⟩(g(c, y), v)⟫_n))) ∧ " +
			"    (∀c d:prod(set(A), A → num → real). ∀y:(num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ compatible_chart⟨n⟩(T, 𝒜, d) ∧ y ∈ «overlap»(c, d) ⇒ " +
			"        g(c, y) = " +
			"        matrix_product(real_ring, " +
			"            n, " +
			"            transpose(vec_jacobian_matrix⟨n, n⟩(«transition»(c, d), y)), " +
			"            matrix_product(real_ring, " +
			"                n, " +
			"                g(d, «transition»(c, d, y)), " +
			"                vec_jacobian_matrix⟨n, n⟩(«transition»(c, d), y))))",
	},
})}

var PairingDef = pairingDefThm{family.Define(registry.DefEntry{
	Name:  "PairingDef",
	Key:   "prop_ca2149b613df74be",
	Const: "riemannian_pairing",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{MetricDef},
	Reading: "A compatible chart through the base point is chosen only on valid " +
		"tangent inputs for a Riemannian metric. PairingChart removes this choice from every " +
		"calculation. Invalid inputs, including points outside the manifold carrier, give zero.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀x:A. " +
			"∀v w:(prod(set(A), A → num → real) → num → real). " +
			"    riemannian_pairing⟨n⟩(T, 𝒜, g, x, v, w) = " +
			"    COND(riemannian_metric⟨n⟩(T, 𝒜, g) ∧ " +
			"        tangent_vector_on⟨n⟩(T, 𝒜, x, v) ∧ " +
			"        tangent_vector_on⟨n⟩(T, 𝒜, x, w), " +
			"        ⟪v(«source chart»), matrix_act⟨n⟩(g(«source chart», snd(«source chart»)(x)), w(«source chart»))⟫_n, " +
			"        &0)",
	},
})}

var InducedMetricDef = inducedMetricDefThm{family.Define(registry.DefEntry{
	Name:  "InducedMetricDef",
	Key:   "prop_290c1192c7a9eb37",
	Const: "riemannian_induced_metric",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real)",
	Dimensions: []string{"n", "N"},
	Reading: "This is the Euclidean Gram matrix of the coordinate differential, " +
		"normalized on all compatible charts. Immersion supplies positive definiteness; the " +
		"definition of a general Riemannian metric does not require an immersion or an embedding.",
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀i j:num. " +
			"    riemannian_induced_metric⟨n, N⟩(T, 𝒜, f, c, y, i, j) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ «chart image»(c) ∧ i < n ∧ j < n, " +
			"        Σ_{a<N} vec_jacobian_matrix⟨n, N⟩(f ∘ inverse_on(fst(c), snd(c)), y)(a, i) * " +
			"        vec_jacobian_matrix⟨n, N⟩(f ∘ inverse_on(fst(c), snd(c)), y)(a, j), " +
			"        &0)",
	},
})}
