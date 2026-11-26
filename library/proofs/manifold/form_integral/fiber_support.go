// Compact fibers control support and zero-dimensional integration is a finite sum of section pullbacks.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

var FiberIntegralSupport = fiberIntegralSupportThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralSupport",
	Key:  "prop_a2e46eb3b9195de0",
	Reading: "The projected support need not be compact, but it is closed because the entire " +
		"fiber is compact. Only inclusion is claimed: different fiber contributions may cancel.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		IntegralZero,
		differential_form.SupportDef,
		differential_form.SupportClosed,
		smooth_manifold.ProductCompatibleChart,
		product_topology.ProjectionClosedMap,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
		},
		Conclusion: "manifold_form_support⟨n⟩(T, 𝒜, manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)) ⊆ " +
			"image(fst, " +
			"    manifold_form_support⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), ω))",
	},
		"Outside the projection of the product support, every vertical slice is zero at "+
			"every fiber point, so the fiber integral is zero. The product support is closed "+
			"and projection along a compact fiber is a closed map. Its image therefore "+
			"contains the closure of the output nonzero locus, which is the stated support."),
})}

var FiberIntegralCompactSupport = fiberIntegralCompactSupportThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralCompactSupport",
	Key:  "prop_8a3e9eb47418013d",
	Deps: []registry.EntryLike{
		FiberIntegralSupport,
		FiberIntegralForm,
		differential_form.SupportClosed,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.SmoothMapDef,
		continuous.ImageCompact,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
			"compact_in(product_topology(T, S), " +
				"    manifold_form_support⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), ω))",
		},
		Conclusion: "compact_in(T, " +
			"    manifold_form_support⟨n⟩(T, 𝒜, manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)))",
	},
		"The continuous product projection sends the compact product support to "+
			"a compact subset of the base. FiberIntegralSupport bounds the closed "+
			"output support by that compact image, so ClosedSubsetCompact applies."),
})}

var FiberIntegralZeroDimension = fiberIntegralZeroDimensionThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralZeroDimension",
	Key:  "prop_d5e855681f818f0c",
	Reading: "There are no vertical columns when the fiber dimension is zero. Every " +
		"point has positive sign under the atlas convention, and the result is the finite " +
		"sum of section pullbacks, not an arbitrarily signed sum. The whole fiber is " +
		"finite, so the scalar-support sum extends by zero to the carrier sum displayed here.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		IntegralZeroDimension,
		OrientedZeroDimension,
		differential_form.FormZeroDegree,
		differential_form.PullbackCoordinate,
		smooth_manifold.ChartDef,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothMapConstant,
		smooth_manifold.SmoothMapIdentity,
		compact.DiscreteCompactIffFinite,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨0⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + 0⟩(product_topology(T, S), smooth_product_atlas⟨n, 0⟩(𝒜, ℬ), k + 0, ω)",
		},
		Conclusion: "finite(⋃S) ∧ " +
			"manifold_fiber_integral⟨n, 0⟩(T, 𝒜, S, ℬ, k, ω) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    Σ_{b∈⋃S} manifold_form_pullback⟨n, n + 0⟩(T, 𝒜, product_topology(T, S), smooth_product_atlas⟨n, 0⟩(𝒜, ℬ), k, λx:A. (x, b), ω, c, y, P)",
	},
		"A compact zero-dimensional manifold is a finite discrete set. At each base chart and "+
			"horizontal frame its vertical slice is a zero-form, and IntegralZeroDimension sums its "+
			"scalar values over this finite carrier. The product-chart pullback formula identifies the "+
			"value at b with pullback along the section x maps to (x,b), including the empty fiber sum."),
})}
