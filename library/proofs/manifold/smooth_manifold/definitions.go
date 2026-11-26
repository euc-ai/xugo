// A chart is its open domain and a coordinate map. Atlas compatibility
// is tested on overlap images, where the chosen inverse is determined.

package smooth_manifold

import (
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	_ "github.com/euc-ai/xugo/library/proofs/topology/countability"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartDef — an open domain homeomorphic to an open subset of R^n.
var ChartDef = chartDefThm{family.Define(registry.DefEntry{
	Name:  "ChartDef",
	Key:   "prop_8ab29d3687afb098",
	Const: "manifold_chart",
	Type:  "num → set(set(A)) → prod(set(A), A → num → real) → bool",
	Dim:   "n",
	Reading: "The point type A may contain points outside the space. A " +
		"chart map is constrained only on its domain; inverse_on is used only on " +
		"its coordinate image. Empty chart domains and dimension zero are allowed.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀c:prod(set(A), A → num → real). " +
			"    manifold_chart⟨n⟩(T, c) ⇔ " +
			"    is_topology(T) ∧ " +
			"    fst(c) ∈ T ∧ " +
			"    image(snd(c), fst(c)) ∈ euclidean_topology(n) ∧ " +
			"    homeomorphic_map(subtopology(T, fst(c)), " +
			"        subtopology(euclidean_topology(n), image(snd(c), fst(c))), " +
			"        snd(c))",
	},
})}

// AtlasDef — a covering family of charts with smooth transitions.
var AtlasDef = atlasDefThm{family.Define(registry.DefEntry{
	Name:  "AtlasDef",
	Key:   "prop_a27c0d94b7bfb830",
	Const: "smooth_atlas",
	Type:  "num → set(set(A)) → set(prod(set(A), A → num → real)) → bool",
	Dim:   "n",
	Deps:  []registry.EntryLike{ChartDef},
	Reading: "The topology axiom remains explicit even for an empty atlas. Ordered pairs of " +
		"charts test both directions of each transition. The empty atlas covers only the empty space.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    smooth_atlas⟨n⟩(T, 𝒜) ⇔ " +
			"    is_topology(T) ∧ " +
			"    (∀c:prod(set(A), A → num → real). c ∈ 𝒜 ⇒ manifold_chart⟨n⟩(T, c)) ∧ " +
			"    ⋃image(fst, 𝒜) = ⋃T ∧ " +
			"    (∀c d:prod(set(A), A → num → real). " +
			"        c ∈ 𝒜 ∧ d ∈ 𝒜 ⇒ vec_smooth_map_on⟨n, n⟩(«overlap»(c, d), «transition»(c, d)))",
	},
})}

// CompatibleChartDef — a chart whose transitions with the atlas are
// smooth in both directions.
var CompatibleChartDef = compatibleChartDefThm{family.Define(registry.DefEntry{
	Name:  "CompatibleChartDef",
	Key:   "prop_5a512504f6a0f60b",
	Const: "compatible_chart",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"bool",
	Dim:  "n",
	Deps: []registry.EntryLike{ChartDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀c:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ⇔ " +
			"    manifold_chart⟨n⟩(T, c) ∧ " +
			"    (∀d:prod(set(A), A → num → real). " +
			"        d ∈ 𝒜 ⇒ " +
			"        vec_smooth_map_on⟨n, n⟩(«overlap»(c, d), «transition»(c, d)) ∧ " +
			"        vec_smooth_map_on⟨n, n⟩(«overlap»(d, c), «transition»(d, c)))",
	},
})}

// ManifoldDef — a Hausdorff, second countable space with a smooth atlas.
var ManifoldDef = manifoldDefThm{family.Define(registry.DefEntry{
	Name:  "ManifoldDef",
	Key:   "prop_be1978ecdee10cce",
	Const: "smooth_manifold",
	Type:  "num → set(set(A)) → set(prod(set(A), A → num → real)) → bool",
	Dim:   "n",
	Deps:  []registry.EntryLike{AtlasDef},
	Reading: "Dimension is fixed over the whole carrier, including " +
		"disconnected spaces. The empty space is allowed in every dimension; " +
		"dimension zero uses the singleton carrier of zero-padded zero-vectors.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ⇔ " +
			"    is_topology(T) ∧ hausdorff(T) ∧ second_countable_space(T) ∧ smooth_atlas⟨n⟩(T, 𝒜)",
	},
})}

// SmoothMapDef — a continuous carrier map smooth in every atlas pair.
var SmoothMapDef = smoothMapDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothMapDef",
	Key:   "prop_a4ada29e93c0eb37",
	Const: "smooth_manifold_map",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"bool",
	Deps: []registry.EntryLike{ManifoldDef},
	Reading: "Continuity includes the carrier map and makes each source-chart " +
		"preimage of a target chart open. This is essential even when m=0, where the scalar " +
		"smoothness conditions are vacuous. No value outside the source carrier is prescribed.",
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"    smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    smooth_manifold⟨m⟩(S, ℬ) ∧ " +
			"    continuous_map(T, S, f) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀d:prod(set(B), B → num → real). " +
			"        c ∈ 𝒜 ∧ d ∈ ℬ ⇒ " +
			"        vec_smooth_map_on⟨n, m⟩(«map domain»(c, d, f), «coordinate map»(c, d, f)))",
	},
})}
