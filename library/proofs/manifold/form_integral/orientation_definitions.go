// An oriented atlas selects positive compatible charts for integration.

package form_integral

import (
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var OrientedManifoldDef = orientedManifoldDefThm{family.Define(registry.DefEntry{
	Name:  "OrientedManifoldDef",
	Key:   "prop_dbb2ab7e5d4247a",
	Const: "oriented_manifold",
	Type:  "num → set(set(A)) → set(prod(set(A), A → num → real)) → bool",
	Dim:   "n",
	Reading: "Orientation is carried by an atlas whose ordered transition determinants are " +
		"positive on open overlaps. The definition includes the underlying Hausdorff, second countable " +
		"smooth manifold. In dimension zero every transition determinant is the empty determinant one.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    oriented_manifold⟨n⟩(T, 𝒜) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    (∀c d:prod(set(A), A → num → real). " +
			"        c ∈ 𝒜 ∧ d ∈ 𝒜 ⇒ " +
			"        (∀y:(num → real). " +
			"            y ∈ «overlap»(c, d) ⇒ &0 < vec_jacobian_determinant⟨n⟩(«transition»(c, d), y)))",
	},
})}

var PositiveChartDef = positiveChartDefThm{family.Define(registry.DefEntry{
	Name:  "PositiveChartDef",
	Key:   "prop_6f847669a1e8d4af",
	Const: "positive_manifold_chart",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"bool",
	Dim: "n",
	Reading: "A positive chart is a smoothly compatible chart with positive " +
		"transition determinant to every original atlas chart wherever they overlap. " +
		"Empty-domain charts satisfy the sign condition vacuously. Forms remain " +
		"indexed by all smoothly compatible charts, including negatively oriented ones.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀c:prod(set(A), A → num → real). " +
			"    positive_manifold_chart⟨n⟩(T, 𝒜, c) ⇔ " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"    (∀d:prod(set(A), A → num → real). " +
			"        d ∈ 𝒜 ⇒ " +
			"        (∀y:(num → real). " +
			"            y ∈ «overlap»(c, d) ⇒ &0 < vec_jacobian_determinant⟨n⟩(«transition»(c, d), y)))",
	},
})}

var OrientedOpenAtlasDef = orientedOpenAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "OrientedOpenAtlasDef",
	Key:   "prop_3a37f2fa892a6a33",
	Const: "oriented_open_atlas",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"set(prod(set(A), A → num → real))",
	Dim:  "n",
	Deps: []registry.EntryLike{PositiveChartDef},
	Reading: "Only positive compatible charts whose domains lie in U enter " +
		"this atlas. The atlas of all compatible charts of U has the same smooth " +
		"structure, but in positive dimension it generally is not an oriented atlas.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A). " +
			"    oriented_open_atlas⟨n⟩(T, 𝒜, U) = " +
			"    {c:prod(set(A), A → num → real) | positive_manifold_chart⟨n⟩(T, 𝒜, c) ∧ fst(c) ⊆ U}",
	},
})}

var reflectedAtlasDef = reflectedAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "reflectedAtlasDef",
	Key:   "prop_f7dd930d1bbbbd99",
	Const: "reflected_manifold_atlas",
	Type:  "set(prod(set(A), A → num → real)) → set(prod(set(A), A → num → real))",
	Reading: "Reflect the first coordinate of every original chart. This " +
		"preserves the smooth structure in every dimension and reverses orientation " +
		"in positive dimension. It acts identically on the zero-dimensional " +
		"Euclidean carrier, so the integral sign-reversal law requires n > 0.",
	Equations: []string{
		"∀𝒜:set(prod(set(A), A → num → real)). reflected_manifold_atlas(𝒜) = image(«reflected chart», 𝒜)",
	},
})}
