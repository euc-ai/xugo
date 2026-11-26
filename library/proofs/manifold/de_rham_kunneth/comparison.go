// Finite box comparisons descend through smooth retractions to compact manifolds.

package de_rham_kunneth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/convex_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

var FiniteBoxUnionKunneth = finiteBoxUnionKunnethThm{family.Add(registry.ProofEntry{
	Name: "FiniteBoxUnionKunneth",
	Key:  "prop_df564e368078687e",
	Reading: "Empty boxes and an empty family are allowed. Cardinality can " +
		"decrease when different boxes have the same intersection, which is " +
		"why the induction is by cardinality and not by a chosen enumeration.",
	Deps: []registry.EntryLike{
		ConvexOpenKunneth,
		EuclideanUnionKunneth,
		euclidean_topology.OpenBoxOpen,
		convex_topology.OpenBoxConvex,
		euclidean_topology.OpenBoxIntersection,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀C:set(set(num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀E:set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))).",
		Hypotheses: []string{
			"finite(C)",
			"∀B:set(num → real). B ∈ C ⇒ ∃a b:(num → real). B = euclidean_open_box⟨n⟩(a, b)",
			"de_rham_homogeneous_basis⟨m⟩(S, ℬ, E)",
		},
		Conclusion: "«euclidean comparison»(⋃C, k)",
	},
		"Induct strongly on the number of boxes, simultaneously in all degrees. A single box "+
			"is convex; after removing a box, the intersection of that box with the remaining "+
			"union is a union of at most as many box intersections. EuclideanUnionKunneth "+
			"combines the inductive comparisons; the empty union is handled by ConvexOpenKunneth."),
})}

var RetractKunneth = retractKunnethThm{family.Add(registry.ProofEntry{
	Name: "RetractKunneth",
	Key:  "prop_fb4ceb38a4a66cfd",
	Reading: "Only r after i is the identity on the first manifold. A comparison " +
		"map that is a retract of an isomorphism is an isomorphism; neither the " +
		"ambient manifold nor its product must be homotopy equivalent to the retract.",
	Deps: []registry.EntryLike{
		KunnethNaturality,
		KunnethMapHom,
		de_rham_cover.RetractCohomology,
		function_module.IndexedMapHom,
		de_rham.PullbackCompose,
		de_rham.PullbackCongruence,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothProductProjections,
	},
	Build: family.Card(Statement{
		Binders: "∀n m l k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀Q:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))). " +
			"∀i:(A → C). " +
			"∀r:(C → A).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, l⟩(T, 𝒜, Q, 𝒞, i)",
			"smooth_manifold_map⟨l, n⟩(Q, 𝒞, T, 𝒜, r)",
			"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
			"de_rham_homogeneous_basis⟨m⟩(S, ℬ, E)",
			"module_isomorphism(real_ring, " +
				"    de_rham_kunneth_module⟨l⟩(Q, 𝒞, k, E), " +
				"    de_rham_cohomology_module⟨l + m⟩(product_topology(Q, S), " +
				"        smooth_product_atlas⟨l, m⟩(𝒞, ℬ), " +
				"        k), " +
				"    de_rham_kunneth_map⟨l, m⟩(Q, 𝒞, S, ℬ, k, E))",
		},
		Conclusion: "module_isomorphism(real_ring, " +
			"    de_rham_kunneth_module⟨n⟩(T, 𝒜, k, E), " +
			"    de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k), " +
			"    de_rham_kunneth_map⟨n, m⟩(T, 𝒜, S, ℬ, k, E))",
	},
		"Apply the retraction pullbacks componentwise to the coefficient modules and to the product "+
			"manifolds. KunnethNaturality gives a retraction of the comparison maps. Compose the "+
			"ambient inverse with the inclusion and retraction on the two sides; the two naturality "+
			"squares and the splitting identities make it an inverse to the smaller comparison."),
})}

var CompactEuclideanRetractKunneth = compactEuclideanRetractKunnethThm{family.Add(registry.ProofEntry{
	Name: "CompactEuclideanRetractKunneth",
	Key:  "prop_9f7ce17a3f06ac92",
	Reading: "The second factor is any smooth manifold with the supplied finite " +
		"homogeneous basis. The first factor is compact and comes with explicit smooth " +
		"retraction data; existence of that data is a separate geometric statement.",
	Deps: []registry.EntryLike{
		FiniteBoxUnionKunneth,
		RetractKunneth,
		euclidean_topology.CompactOpenBoxCover,
		smooth_manifold.SmoothMapRestrict,
		smooth_manifold.SmoothMapEuclidean,
		continuous.ImageCompact,
		compact.CompactInSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀n m N k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))). " +
			"∀U:set(num → real). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, 𝒜, subtopology(euclidean_topology(N), U), euclidean_atlas(U), i)",
			"smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), euclidean_atlas(U), T, 𝒜, r)",
			"compact_in(T, ⋃T)",
			"U ∈ euclidean_topology(N)",
			"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
			"de_rham_homogeneous_basis⟨m⟩(S, ℬ, E)",
		},
		Conclusion: "module_isomorphism(real_ring, " +
			"    de_rham_kunneth_module⟨n⟩(T, 𝒜, k, E), " +
			"    de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k), " +
			"    de_rham_kunneth_map⟨n, m⟩(T, 𝒜, S, ℬ, k, E))",
	},
		"Cover the compact image i(M) by finitely many Euclidean boxes whose union "+
			"V lies in U. Corestrict i and restrict r to V, using the smooth identity "+
			"between restricted and canonical Euclidean atlases. FiniteBoxUnionKunneth "+
			"gives the comparison on V, and RetractKunneth transfers it to M."),
})}

var CompactEuclideanRetractSelfProductSpan = compactEuclideanRetractSelfProductSpanThm{family.Add(registry.ProofEntry{
	Name: "CompactEuclideanRetractSelfProductSpan",
	Key:  "prop_14a0e2e13cc9747b",
	Reading: "This is the finite-product expansion on the self-product under explicit " +
		"Euclidean retraction hypotheses. ClassRepresentative turns every factor into a " +
		"closed form; real coefficients may be absorbed into either factor by bilinearity.",
	Deps: []registry.EntryLike{
		de_rham_cover.CompactEuclideanRetractFiniteCohomology,
		HomogeneousBasisExists,
		CompactEuclideanRetractKunneth,
		KunnethMapDef,
		de_rham_product.ExternalProductBilinear,
		submodule.SpanSubmodule,
		submodule.SubmoduleModuleSum,
		linear_independence.SpanCombinations,
	},
	Build: family.Card(Statement{
		Binders: "∀n N k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(num → real). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, 𝒜, subtopology(euclidean_topology(N), U), euclidean_atlas(U), i)",
			"smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), euclidean_atlas(U), T, 𝒜, r)",
			"compact_in(T, ⋃T)",
			"U ∈ euclidean_topology(N)",
			"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
		},
		Conclusion: "de_rham_cohomology_module⟨n + n⟩(product_topology(T, T), " +
			"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"    k).carrier = " +
			"module_span(real_ring, " +
			"    de_rham_cohomology_module⟨n + n⟩(product_topology(T, T), " +
			"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"        k), " +
			"    {z:set(prod(set(prod(A, A)), prod(A, A) → num → real) → " +
			"            (num → real) → " +
			"            (num → num → real) → " +
			"            real) | " +
			"        ∃p q:num. " +
			"        ∃s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            p + q = k ∧ " +
			"            s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier ∧ " +
			"            t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, q).carrier ∧ " +
			"            z = de_rham_external_product⟨n, n⟩(T, 𝒜, T, 𝒜, p, q, s, t)})",
	},
		"CompactEuclideanRetractFiniteCohomology and HomogeneousBasisExists supply a finite homogeneous "+
			"basis. Surjectivity of CompactEuclideanRetractKunneth writes each product class as a finite "+
			"sum of external products, hence in the indicated span. Conversely, ExternalProductBilinear "+
			"puts every generator in the target carrier, which is a submodule and contains its span."),
})}
