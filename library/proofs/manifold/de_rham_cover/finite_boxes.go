// Finite unions of boxes have finite-dimensional cohomology by the two-open exact sequence.

package de_rham_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/convex_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var EuclideanUnionFiniteCohomology = euclideanUnionFiniteCohomologyThm{family.Add(registry.ProofEntry{
	Name: "EuclideanUnionFiniteCohomology",
	Key:  "prop_f58d474a2d35fab6",
	Reading: "The bottom degree uses the injective start separately. No " +
		"H^(q−1) is read at q=0, and the compatible-chart identification is " +
		"required before applying the hypotheses to the restricted-atlas terms.",
	Deps: []registry.EntryLike{
		MayerVietoris,
		MayerVietorisMaps,
		MayerVietorisExact,
		MayerVietorisStart,
		de_rham.PullbackCompose,
		de_rham.PullbackIdentity,
		vec_smooth.SmoothPartitionOfUnityOpen,
		smooth_manifold.EuclideanManifold,
		smooth_manifold.OpenCompatibleChart,
		module_dimension.DimProduct,
		module_dimension.SubmoduleDim,
		module_dimension.ImageDim,
		module_dimension.DimFiniteOfKernelAndImage,
		module_dimension.IsomorphismDim,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀U V:set(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(n)",
			"∀q:num. finite_dimensional(real_ring, «euclidean cohomology»(U, q))",
			"∀q:num. finite_dimensional(real_ring, «euclidean cohomology»(V, q))",
			"∀q:num. finite_dimensional(real_ring, «euclidean cohomology»(U ∩ V, q))",
		},
		Conclusion: "finite_dimensional(real_ring, «euclidean cohomology»(U ∪ V, k))",
	},
		"Normalize the Euclidean two-open partition on U∪V and apply MayerVietoris. Identify "+
			"each restricted Euclidean atlas with its canonical open atlas through the smooth "+
			"identity maps. In degree zero the first map injects into the finite product. In degree "+
			"q+1 its kernel is an image of the finite H^q(U∩V), and its image is a submodule of the "+
			"finite product; the kernel-and-image dimension criterion gives finiteness."),
})}

var FiniteBoxUnionFiniteCohomology = finiteBoxUnionFiniteCohomologyThm{family.Add(registry.ProofEntry{
	Name: "FiniteBoxUnionFiniteCohomology",
	Key:  "prop_419b8ec6850f88d5",
	Reading: "Empty boxes are permitted, and C empty gives the empty manifold. The " +
		"induction uses cardinality, since different boxes can have the same intersection; " +
		"it does not assume the intersection family has the same size as the remaining family.",
	Deps: []registry.EntryLike{
		de_rham.EmptyCohomology,
		de_rham.ConvexOpenCohomology,
		EuclideanUnionFiniteCohomology,
		euclidean_topology.OpenBoxOpen,
		convex_topology.OpenBoxConvex,
		euclidean_topology.OpenBoxIntersection,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀C:set(set(num → real)).",
		Hypotheses: []string{
			"finite(C)",
			"∀B:set(num → real). B ∈ C ⇒ ∃a b:(num → real). B = euclidean_open_box⟨n⟩(a, b)",
		},
		Conclusion: "finite_dimensional(real_ring, «euclidean cohomology»(⋃C, k))",
	}, "Induct on the number of boxes, with the assertion simultaneous in every cohomological "+
		"degree. Removing one box leaves a smaller union; its intersection with the removed box "+
		"is the union of at most that many pairwise box intersections, again boxes. The convex "+
		"calculation handles the single box and Mayer–Vietoris propagates finiteness to the union."),
})}
