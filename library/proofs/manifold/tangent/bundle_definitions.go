// Induced charts concatenate base and fiber coordinates. Their open
// images define the tangent topology on the paired total-space carrier.

package tangent

import "github.com/euc-ai/xugo/library/registry"

// TangentChartDef — the chart over c with coordinates (phi_c(x), v_c).
var TangentChartDef = tangentChartDefThm{family.Define(registry.DefEntry{
	Name:  "TangentChartDef",
	Key:   "prop_6380b681e779adae",
	Const: "tangent_chart",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"    prod(A, prod(set(A), A → num → real) → num → real) → num → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{TangentBundleDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀c:prod(set(A), A → num → real). " +
			"    tangent_chart⟨n⟩(T, 𝒜, c) = " +
			"    ({p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"            p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ fst(p) ∈ fst(c)}, " +
			"        λp:prod(A, prod(set(A), A → num → real) → num → real). «join»(snd(c)(fst(p)), snd(p)(c)))",
	},
})}

// TangentAtlasDef — induced charts from all compatible base charts.
var TangentAtlasDef = tangentAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "TangentAtlasDef",
	Key:   "prop_661eb29d4fc11ec3",
	Const: "tangent_atlas",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"        prod(A, prod(set(A), A → num → real) → num → real) → num → real))",
	Dim:  "n",
	Deps: []registry.EntryLike{TangentChartDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    tangent_atlas⟨n⟩(T, 𝒜) = image(«lift», «compatible atlas»)",
	},
})}

// TangentTopologyDef — sets whose images in every induced chart are open.
var TangentTopologyDef = tangentTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "TangentTopologyDef",
	Key:   "prop_f2cd47ebbfeee091",
	Const: "tangent_topology",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(prod(A, prod(set(A), A → num → real) → num → real)))",
	Dim:  "n",
	Deps: []registry.EntryLike{TangentBundleDef, TangentChartDef},
	Reading: "The carrier-subset guard excludes every pair that is not a tangent vector at " +
		"its own base. Chart images are taken after intersection with that chart's domain. The " +
		"construction is asserted to be a manifold topology only under the base-manifold hypothesis.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    tangent_topology⟨n⟩(T, 𝒜) = " +
			"    {W:set(prod(A, prod(set(A), A → num → real) → num → real)) | " +
			"        W ⊆ tangent_bundle⟨n⟩(T, 𝒜) ∧ " +
			"        (∀c:prod(set(A), A → num → real). " +
			"            compatible_chart⟨n⟩(T, 𝒜, c) ⇒ " +
			"            image(snd(«lift»(c)), W ∩ fst(«lift»(c))) ∈ euclidean_topology(2 * n))}",
	},
})}

// ZeroSectionDef — the base point paired with the zero component family.
var ZeroSectionDef = zeroSectionDefThm{family.Define(registry.DefEntry{
	Name:      "ZeroSectionDef",
	Key:       "prop_8256404a682a4a16",
	Const:     "tangent_zero_section",
	Type:      "A → prod(A, prod(set(A), A → num → real) → num → real)",
	Equations: []string{"∀x:A. tangent_zero_section(x) = (x, «zero tangent»)"},
})}
