// The comparison respects the connecting map and glues over Euclidean open covers.

package de_rham_kunneth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ExternalProductConnecting = externalProductConnectingThm{family.Add(registry.ProofEntry{
	Name: "ExternalProductConnecting",
	Key:  "prop_9fcc279ff523d8f8",
	Reading: "Both cover sequences are assumed short exact. The intersection uses the " +
		"atlas restricted from the ambient product, exactly the atlas in the connecting map. " +
		"The fixed second-factor class is on the right, so this formula has no degree sign.",
	Deps: []registry.EntryLike{
		de_rham_cover.ConnectingNaturality,
		ConnectingWedgeClassRight,
		de_rham_product.ExternalProductDef,
		de_rham.PullbackCompose,
		de_rham.PullbackCongruence,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.SmoothMapRestrict,
	},
	Build: family.Card(Statement{
		Binders: "∀n m q p:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀U V:set(A). " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀t:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"«cover exact»",
			"«product cover exact»",
			"s ∈ «open cohomology»(U ∩ V, q).carrier",
			"t ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, p).carrier",
		},
		Conclusion: "de_rham_connecting⟨n + m⟩(product_topology(T, S), " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"    set_cross(U, ⋃S), " +
			"    set_cross(V, ⋃S))(q + p, " +
			"    de_rham_wedge⟨n + m⟩(«product intersection topology», " +
			"        «product intersection atlas», " +
			"        q, " +
			"        p, " +
			"        de_rham_pullback⟨n + m, n⟩(«product intersection topology», " +
			"            «product intersection atlas», " +
			"            subtopology(T, U ∩ V), " +
			"            open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"            q, " +
			"            fst)(s), " +
			"        de_rham_pullback⟨n + m, m⟩(«product intersection topology», " +
			"            «product intersection atlas», " +
			"            S, " +
			"            ℬ, " +
			"            p, " +
			"            snd)(t))) = " +
			"de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, q + 1, p, de_rham_connecting⟨n⟩(T, 𝒜, U, V)(q, s), t)",
	},
		"Apply ConnectingNaturality to the first projection and the base cover. Multiply by the "+
			"global pullback of t along the second projection, using ConnectingWedgeClassRight; "+
			"pullback composition identifies its restriction with the displayed second-factor "+
			"pullback. Associativity of degree addition identifies the target degrees."),
})}

var ConvexOpenKunneth = convexOpenKunnethThm{family.Add(registry.ProofEntry{
	Name: "ConvexOpenKunneth",
	Key:  "prop_62213766b5b417b3",
	Reading: "U and the second manifold may be empty. For a nonempty convex U, H^0 is " +
		"identified with real multiples of the unit; no nonzero unit is asserted on the empty space.",
	Deps: []registry.EntryLike{
		HomogeneousBasisDef,
		KunnethMapHom,
		de_rham.ConvexOpenCohomology,
		de_rham.ConvexProductCohomology,
		de_rham.EmptyCohomology,
		de_rham_product.ExternalProductUnit,
		linear_independence.IndependentUniqueCoefficients,
		linear_independence.SpanCombinations,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀U:set(num → real). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀E:set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"convex(U)",
			"de_rham_homogeneous_basis⟨m⟩(S, ℬ, E)",
		},
		Conclusion: "«euclidean comparison»(U, k)",
	},
		"For nonempty U use its degree-zero unit as a basis and the vanishing in "+
			"positive degrees. The only nonzero coefficient summands are the degree-k basis "+
			"of the second factor; ExternalProductUnit identifies the comparison with their "+
			"basis expansion followed by the projection isomorphism ConvexProductCohomology. "+
			"If U is empty, both source and target modules are zero."),
})}

var EuclideanUnionKunneth = euclideanUnionKunnethThm{family.Add(registry.ProofEntry{
	Name: "EuclideanUnionKunneth",
	Key:  "prop_a9e481475b98219b",
	Reading: "All three local comparisons are required in every degree. The fixed " +
		"finite label set permits shifted exact rows; when a shift first reaches zero, the " +
		"injective start is used instead of a fictitious negative-degree cohomology group.",
	Deps: []registry.EntryLike{
		KunnethMapHom,
		KunnethNaturality,
		ExternalProductConnecting,
		de_rham_cover.MayerVietoris,
		de_rham_cover.EuclideanProductMayerVietoris,
		de_rham_cover.MayerVietorisMaps,
		de_rham_cover.MayerVietorisExact,
		de_rham_cover.MayerVietorisStart,
		function_module.IndexedProductExact,
		function_module.IndexedMapIsomorphism,
		module_homomorphism.FiveLemma,
		smooth_manifold.OpenCompatibleChart,
		vec_smooth.SmoothPartitionOfUnityOpen,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀U V:set(num → real). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀E:set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(n)",
			"de_rham_homogeneous_basis⟨m⟩(S, ℬ, E)",
			"∀j:num. «euclidean comparison»(U, j)",
			"∀j:num. «euclidean comparison»(V, j)",
			"∀j:num. «euclidean comparison»(U ∩ V, j)",
		},
		Conclusion: "«euclidean comparison»(U ∪ V, k)",
	},
		"Take the finite product over E of the degree-shifted base Mayer–Vietoris rows, extending "+
			"every row by zero in negative degrees. IndexedProductExact gives exactness, with the "+
			"product of the two local coefficient modules identified with the coefficient module of the "+
			"paired terms. KunnethNaturality and ExternalProductConnecting give the ladder; identify "+
			"restricted product atlases with canonical product atlases by smooth identity maps. Apply "+
			"FiveLemma in positive degree, and its zero-padded injective start in degree zero."),
})}
