// The cover cohomology is the product of the two cohomologies, making the long exact sequence explicit.

package de_rham_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/registry"
)

var CoverCohomology = coverCohomologyThm{family.Add(registry.ProofEntry{
	Name: "CoverCohomology",
	Key:  "prop_82497c45f3ae46c6",
	Reading: "Elements of the source are sets of pairs of forms. The " +
		"target elements are pairs of sets of forms; the stated isomorphism " +
		"identifies them without treating these different host types as equal.",
	Deps: []registry.EntryLike{
		CoverCochain,
		CoverComplexDef,
		chain_complex.InCohomology,
		chain_complex.CohomologyMapCoset,
		chain_complex.CohomologyMapHom,
		module_homomorphism.ProductModuleOn,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T", "V ∈ T"},
		Conclusion: "module_isomorphism(real_ring, " +
			"    cohomology_module(de_rham_cover_complex⟨n⟩(T, 𝒜, U, V), k), " +
			"    product_module(«open cohomology»(U, k), «open cohomology»(V, k)), " +
			"    (λs:set(prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
			"                prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"        (cohomology_map(«open complex»(U), (λq:num. fst), k, s), " +
			"            cohomology_map(«open complex»(V), (λq:num. snd), k, s))))",
	},
		"The projections are cochain maps and hence induce linear maps on cohomology. "+
			"A pair is a cocycle exactly when both components are, and is a coboundary "+
			"exactly when both are; at degree zero both coboundary spaces are singletons. "+
			"These facts give surjectivity and injectivity on the quotient carriers."),
})}

var ConnectingClass = connectingClassThm{family.Add(registry.ProofEntry{
	Name: "ConnectingClass",
	Key:  "prop_91dd7a30f089d703",
	Reading: "The formula applies to every valid lift, so it also " +
		"proves independence from any weights used to choose the lift.",
	Deps: []registry.EntryLike{
		ConnectingDef,
		de_rham.ClassDef,
		chain_complex.CoconnectingHomCoset,
		chain_complex.CochainCoboundaryTwice,
		chain_complex.ShortExactCochainDegreewise,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀ω η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀z:prod(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real, " +
			"        prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"«cover exact»",
			"ω ∈ «open complex»(U ∩ V).terms(k)",
			"«open complex»(U ∩ V).d(k)(ω) = «open complex»(U ∩ V).zero",
			"z ∈ de_rham_cover_complex⟨n⟩(T, 𝒜, U, V).terms(k)",
			"de_rham_cover_difference⟨n⟩(T, 𝒜, U, V)(z) = ω",
			"η ∈ de_rham_complex⟨n⟩(T, 𝒜).terms(k + 1)",
			"de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)(η) = de_rham_cover_complex⟨n⟩(T, 𝒜, U, V).d(k)(z)",
		},
		Conclusion: "de_rham_complex⟨n⟩(T, 𝒜).d(k + 1)(η) = de_rham_complex⟨n⟩(T, 𝒜).zero ∧ " +
			"de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k, " +
			"    de_rham_class⟨n⟩(subtopology(T, U ∩ V), open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), k, ω)) = " +
			"de_rham_class⟨n⟩(T, 𝒜, k + 1, η)",
	},
		"The derivative of z lies in the kernel of the difference and so glues to η. Its next "+
			"derivative restricts to zero on both opens, hence is zero by injectivity. The generic "+
			"coconnecting coset formula computes the class of η for this particular lift and preimage."),
})}

var MayerVietorisMaps = mayerVietorisMapsThm{family.Add(registry.ProofEntry{
	Name: "MayerVietorisMaps",
	Key:  "prop_495a2f201d8f2987",
	Reading: "All three maps are linear on the stated quotient " +
		"carriers. No equality on arbitrary sets of forms is asserted.",
	Deps: []registry.EntryLike{
		CoverCohomology,
		ConnectingDef,
		de_rham.PullbackHom,
		chain_complex.CohomologyMapHom,
		chain_complex.CoconnectingHom,
		module_homomorphism.HomDiff,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T", "V ∈ T", "U ∪ V = ⋃T", "«cover exact»"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
			"    product_module(«open cohomology»(U, k), «open cohomology»(V, k)), " +
			"    «cohomology restriction»(k)) ∧ " +
			"module_homomorphism(real_ring, " +
			"    product_module(«open cohomology»(U, k), «open cohomology»(V, k)), " +
			"    «open cohomology»(U ∩ V, k), " +
			"    «cohomology difference»(k)) ∧ " +
			"module_homomorphism(real_ring, " +
			"    «open cohomology»(U ∩ V, k), " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k + 1), " +
			"    de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k))",
	},
		"Transport the maps of the short exact sequence through CoverCohomology. "+
			"On representative pairs the maps are exactly the two pullbacks and their "+
			"difference; the generic connecting theorem supplies linearity of δ."),
})}

var MayerVietorisExact = mayerVietorisExactThm{family.Add(registry.ProofEntry{
	Name: "MayerVietorisExact",
	Key:  "prop_1f1c40d0f38b6a31",
	Reading: "The last exactness assertion is at degree k+1, avoiding any truncated " +
		"negative degree. The middle zero is a pair of coboundary cosets, not a set of pairs.",
	Deps: []registry.EntryLike{
		CoverCohomology,
		ConnectingDef,
		chain_complex.CoLongExactMiddle,
		chain_complex.CoLongExactQuotient,
		chain_complex.CoLongExactSub,
		module_homomorphism.ExactAtIsomorphism,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T", "V ∈ T", "U ∪ V = ⋃T", "«cover exact»"},
		Conclusion: "exact_at(«open cohomology»(U ∩ V, k).zero, " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier, " +
			"    product_module(«open cohomology»(U, k), «open cohomology»(V, k)).carrier, " +
			"    «cohomology restriction»(k), " +
			"    «cohomology difference»(k)) ∧ " +
			"exact_at(de_rham_cohomology_module⟨n⟩(T, 𝒜, k + 1).zero, " +
			"    product_module(«open cohomology»(U, k), «open cohomology»(V, k)).carrier, " +
			"    «open cohomology»(U ∩ V, k).carrier, " +
			"    «cohomology difference»(k), " +
			"    de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k)) ∧ " +
			"exact_at(product_module(«open cohomology»(U, k + 1), «open cohomology»(V, k + 1)).zero, " +
			"    «open cohomology»(U ∩ V, k).carrier, " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k + 1).carrier, " +
			"    de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k), " +
			"    «cohomology restriction»(k + 1))",
	},
		"Apply the three generic cohomology exactness theorems to the cover sequence. Identify its "+
			"middle cohomology with the pair of open cohomologies and transport images and kernels across "+
			"this isomorphism; the representative formulas identify the maps and their zero classes."),
})}

var MayerVietorisStart = mayerVietorisStartThm{family.Add(registry.ProofEntry{
	Name: "MayerVietorisStart",
	Key:  "prop_eb9a00e996a4d704",
	Deps: []registry.EntryLike{CoverCohomology, chain_complex.CoLongExactStart},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T", "V ∈ T", "U ∪ V = ⋃T", "«cover exact»"},
		Conclusion: "injective_on(de_rham_cohomology_module⟨n⟩(T, 𝒜, 0).carrier, " +
			"    «cohomology restriction»(0))",
	},
		"Degree-zero coboundaries are zero forms. The generic start of the "+
			"cohomology sequence makes its first map injective; composing with "+
			"the middle-cohomology product isomorphism preserves this property."),
})}
