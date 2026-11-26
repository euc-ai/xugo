// Positive charts orient overlaps, open submanifolds and reflected atlases.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var AtlasMemberPositive = atlasMemberPositiveThm{family.Add(registry.ProofEntry{
	Name: "AtlasMemberPositive",
	Key:  "prop_42681784b78463",
	Deps: []registry.EntryLike{
		OrientedManifoldDef,
		PositiveChartDef,
		smooth_manifold.AtlasMemberCompatible,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "c ∈ 𝒜"},
		Conclusion: "positive_manifold_chart⟨n⟩(T, 𝒜, c)",
	},
		"The original atlas member is smoothly compatible. The ordered positivity "+
			"condition of OrientedManifoldDef supplies its transitions to every original chart."),
})}

var PositiveTransition = positiveTransitionThm{family.Add(registry.ProofEntry{
	Name: "PositiveTransition",
	Key:  "prop_e1e17b9738f97def",
	Reading: "The original atlas cover supplies a third chart near every overlap point. Smooth " +
		"compatibility and the positive-chart predicate alone do not supply this covering hypothesis.",
	Deps: []registry.EntryLike{
		PositiveChartDef,
		OrientedManifoldDef,
		smooth_manifold.CompatibleTransition,
		smooth_manifold.AtlasDef,
		vec_smooth.JacobianDeterminantChain,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c d:prod(set(A), A → num → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, d)",
		},
		Conclusion: "vec_diffeomorphic_map⟨n⟩(«overlap»(c, d), «overlap»(d, c), «transition»(c, d)) ∧ " +
			"(∀y:(num → real). y ∈ «overlap»(c, d) ⇒ &0 < vec_jacobian_determinant⟨n⟩(«transition»(c, d), y))",
	},
		"Smooth compatibility gives the overlap diffeomorphism. At each overlap point choose an "+
			"original chart containing its base point; its two positive transitions express the desired "+
			"transition determinant as a quotient of positive determinants. The coordinate identities hold "+
			"on an open neighbourhood, so locality and the chain rule justify that determinant equation."),
})}

var PositiveChartRestrict = positiveChartRestrictThm{family.Add(registry.ProofEntry{
	Name: "PositiveChartRestrict",
	Key:  "prop_77cab3d3bf02b289",
	Deps: []registry.EntryLike{
		PositiveChartDef,
		smooth_manifold.ChartRestrict,
		smooth_manifold.CompatibleChartDef,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀U:set(A).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"U ∈ T",
			"U ⊆ fst(c)",
		},
		Conclusion: "positive_manifold_chart⟨n⟩(T, 𝒜, (U, snd(c)))",
	},
		"The restricted chart remains compatible, and its transitions agree with the original "+
			"transitions on open restricted overlap images. Local derivative agreement preserves positivity."),
})}

var PositiveAtlas = positiveAtlasThm{family.Add(registry.ProofEntry{
	Name: "PositiveAtlas",
	Key:  "prop_6ac8c51cef2806e2",
	Deps: []registry.EntryLike{
		OrientedManifoldDef,
		PositiveChartDef,
		AtlasMemberPositive,
		PositiveTransition,
		smooth_manifold.CompatibleAtlas,
		smooth_manifold.CompatibleAtlasInvariant,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "oriented_manifold⟨n⟩(T, «positive atlas») ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(T, «positive atlas», c) ⇔ compatible_chart⟨n⟩(T, 𝒜, c)) ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    positive_manifold_chart⟨n⟩(T, «positive atlas», c) ⇔ positive_manifold_chart⟨n⟩(T, 𝒜, c))",
	},
		"Original charts are positive and cover the space. PositiveTransition makes all "+
			"positive charts an oriented atlas, and retaining the original cover keeps exactly "+
			"the same smooth compatibility class. Testing positivity against the original members "+
			"gives one direction of the final equivalence; PositiveTransition gives the other."),
})}

var OrientedAtlasChange = orientedAtlasChangeThm{family.Add(registry.ProofEntry{
	Name: "OrientedAtlasChange",
	Key:  "prop_f8543122b8accd1",
	Reading: "The second atlas must cover the same manifold; an arbitrary " +
		"positive subfamily can lose information outside its domains.",
	Deps: []registry.EntryLike{
		PositiveChartDef,
		OrientedManifoldDef,
		PositiveTransition,
		smooth_manifold.AtlasSubcover,
		smooth_manifold.CompatibleAtlasInvariant,
		vec_smooth.JacobianDeterminantChain,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ℬ:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨n⟩(T, ℬ)",
			"∀c:prod(set(A), A → num → real). c ∈ ℬ ⇒ positive_manifold_chart⟨n⟩(T, 𝒜, c)",
		},
		Conclusion: "(∀c:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ⇔ compatible_chart⟨n⟩(T, ℬ, c)) ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    positive_manifold_chart⟨n⟩(T, 𝒜, c) ⇔ positive_manifold_chart⟨n⟩(T, ℬ, c))",
	},
		"The second atlas is a covering family of positive compatible charts. Local "+
			"transition composition through one of its charts preserves the full smooth "+
			"compatibility class. The same local determinant identities transfer positivity "+
			"in both directions, since both original atlases cover the whole carrier."),
})}

var OrientedOpenSubmanifold = orientedOpenSubmanifoldThm{family.Add(registry.ProofEntry{
	Name: "OrientedOpenSubmanifold",
	Key:  "prop_658c50fbe5e9683c",
	Reading: "The positive submanifold atlas and the atlas of all compatible submanifold " +
		"charts have the same smooth compatibility predicate. This identifies their normalized " +
		"form carriers, supports and coordinate operations without equating the atlas sets.",
	Deps: []registry.EntryLike{
		OrientedOpenAtlasDef,
		PositiveChartRestrict,
		PositiveTransition,
		OrientedAtlasChange,
		smooth_manifold.OpenSubmanifold,
		smooth_manifold.OpenCompatibleChart,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "U ∈ T"},
		Conclusion: "oriented_manifold⟨n⟩(subtopology(T, U), oriented_open_atlas⟨n⟩(T, 𝒜, U)) ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(subtopology(T, U), oriented_open_atlas⟨n⟩(T, 𝒜, U), c) ⇔ " +
			"    compatible_chart⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), c)) ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    positive_manifold_chart⟨n⟩(subtopology(T, U), oriented_open_atlas⟨n⟩(T, 𝒜, U), c) ⇔ " +
			"    positive_manifold_chart⟨n⟩(T, 𝒜, c) ∧ fst(c) ⊆ U)",
	},
		"Restrict positive original charts to U; these cover U and lie in the defined atlas. "+
			"Their positive transitions orient the open submanifold, and their smooth completion is "+
			"the usual open-submanifold atlas. Restriction and local transition composition identify "+
			"positive charts with exactly the ambient positive charts whose domains lie in U."),
})}

var OrientedEuclidean = orientedEuclideanThm{family.Add(registry.ProofEntry{
	Name: "OrientedEuclidean",
	Key:  "prop_e31d0865fed31c2f",
	Deps: []registry.EntryLike{
		OrientedManifoldDef,
		smooth_manifold.EuclideanManifold,
		smooth_manifold.EuclideanAtlasDef,
		vec_smooth.PartialDerivativeLocal,
		determinant.DeterminantIdentity,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀U:set(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "oriented_manifold⟨n⟩(subtopology(euclidean_topology(n), U), euclidean_atlas(U))",
	},
		"The identity chart gives the underlying Euclidean open manifold. Its "+
			"self-transition is locally the identity, whose Jacobian determinant "+
			"is one, including the empty determinant in dimension zero."),
})}

var OrientedZeroDimension = orientedZeroDimensionThm{family.Add(registry.ProofEntry{
	Name: "OrientedZeroDimension",
	Key:  "prop_9e97a0c72894fa69",
	Reading: "This atlas convention gives the canonical positive sign to every " +
		"zero-dimensional point. It does not encode independently signed points.",
	Deps: []registry.EntryLike{
		OrientedManifoldDef,
		PositiveChartDef,
		determinant.DeterminantDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨0⟩(T, 𝒜)"},
		Conclusion: "oriented_manifold⟨0⟩(T, 𝒜) ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    compatible_chart⟨0⟩(T, 𝒜, c) ⇒ positive_manifold_chart⟨0⟩(T, 𝒜, c))",
	},
		"Every zero-dimensional Jacobian has determinant one, so every smooth transition has positive "+
			"determinant. Both orientation predicates therefore reduce to their underlying smooth conditions."),
})}

var ReflectedAtlas = reflectedAtlasThm{family.Add(registry.ProofEntry{
	Name: "ReflectedAtlas",
	Key:  "prop_ff13b1e01333aaa5",
	Reading: "In positive dimension the reflection determinant is minus one; " +
		"in dimension zero it is one. The reflected atlas is oriented in both " +
		"cases, while integral sign reversal is asserted only in positive dimension.",
	Deps: []registry.EntryLike{
		reflectedAtlasDef,
		OrientedManifoldDef,
		PositiveChartDef,
		PositiveTransition,
		smooth_manifold.CompatibleChartDef,
		vec_smooth.LinearSmoothMap,
		vec_smooth.JacobianDeterminantChain,
		determinant.DeterminantDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "oriented_manifold⟨n⟩(T, reflected_manifold_atlas(𝒜)) ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ⇔ compatible_chart⟨n⟩(T, reflected_manifold_atlas(𝒜), c)) ∧ " +
			"(∀c:prod(set(A), A → num → real). " +
			"    positive_manifold_chart⟨n⟩(T, 𝒜, c) ⇒ " +
			"    positive_manifold_chart⟨n⟩(T, reflected_manifold_atlas(𝒜), «reflected chart»(c)))",
	},
		"The coordinate reflection is a smooth linear involution. Conjugating each "+
			"transition by it preserves positive determinant because its two determinant factors "+
			"cancel, and it preserves the underlying smooth compatibility class. Reflecting any "+
			"positive chart gives the corresponding positive chart of the reflected atlas."),
})}
