// Coordinate immersion tests are independent of the atlas and compose locally.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/basis"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ImmersionAtlasCriterion = immersionAtlasCriterionThm{family.Add(registry.ProofEntry{
	Name: "ImmersionAtlasCriterion",
	Key:  "prop_f9d8e129da4bbb70",
	Reading: "It is enough to test original atlas pairs, but only where " +
		"the source point and its image lie in their respective domains. " +
		"Empty source carriers satisfy the derivative condition vacuously.",
	Deps: []registry.EntryLike{
		ImmersionDef,
		AtlasMemberCompatible,
		CompatibleTransition,
		vec_smooth.JacobianChain,
		vec_smooth.DiffeomorphismJacobianNonzero,
		matrix.MatrixActAssoc,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
		},
		Conclusion: "smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"(∀c:prod(set(A), A → num → real). ∀d:prod(set(B), B → num → real). ∀x:A. " +
			"    c ∈ 𝒜 ∧ d ∈ ℬ ∧ x ∈ fst(c) ∧ f(x) ∈ fst(d) ⇒ " +
			"    injective_on({y:num → real | vec⟨n⟩(y)}, " +
			"        matrix_act⟨n⟩(vec_jacobian_matrix⟨n, m⟩(«coordinate map»(c, d, f), snd(c)(x)))))",
	},
		"The forward direction uses AtlasMemberCompatible. For the converse, choose "+
			"original charts through the source point and its image; CompatibleTransition "+
			"and JacobianChain express the desired Jacobian as the tested one composed "+
			"with invertible transition Jacobians, so injectivity is preserved."),
})}

var ImmersionCompose = immersionComposeThm{family.Add(registry.ProofEntry{
	Name: "ImmersionCompose",
	Key:  "prop_b9f7962b49ca09ba",
	Deps: []registry.EntryLike{
		ImmersionDef,
		SmoothMapCompose,
		CompatibleTransition,
		vec_smooth.JacobianChain,
		matrix.MatrixActAssoc,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀f:(A → B). " +
			"∀g:(B → C).",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_immersion⟨m, k⟩(S, ℬ, R, 𝒞, g)",
		},
		Conclusion: "smooth_manifold_immersion⟨n, k⟩(T, 𝒜, R, 𝒞, g ∘ f)",
	},
		"Choose an intermediate compatible chart through f(x) and shrink to the common "+
			"chart preimages. JacobianChain and MatrixActAssoc express the composite "+
			"differential as two injective linear maps; SmoothMapCompose supplies smoothness."),
})}

var ImmersionLocal = immersionLocalThm{family.Add(registry.ProofEntry{
	Name: "ImmersionLocal",
	Key:  "prop_3a35be78e1750de",
	Deps: []registry.EntryLike{
		ImmersionDef,
		SmoothMapLocal,
		OpenCompatibleChart,
		ChartRestrict,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"∀x:A. " +
				"    x ∈ ⋃T ⇒ " +
				"    ∃U:set(A). " +
				"        U ∈ T ∧ " +
				"        x ∈ U ∧ " +
				"        smooth_manifold_immersion⟨n, m⟩(subtopology(T, U), " +
				"            open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
				"            S, " +
				"            ℬ, " +
				"            f)",
		},
		Conclusion: "smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f)",
	},
		"SmoothMapLocal gives the global smooth map. Restrict a compatible source "+
			"chart to its intersection with the supplied immersion neighbourhood; "+
			"OpenCompatibleChart identifies it with a chart of that open submanifold, "+
			"and locality of partial derivatives transfers the injective Jacobian back."),
})}

var ImmersionDimensionBound = immersionDimensionBoundThm{family.Add(registry.ProofEntry{
	Name: "ImmersionDimensionBound",
	Key:  "prop_41055548be9cc79b",
	Reading: "Nonemptiness is essential: an empty n-manifold immerses into an empty " +
		"m-manifold for arbitrary n and m. No target nonemptiness assumption is needed separately.",
	Deps: []registry.EntryLike{
		ImmersionDef,
		basis.StandardBasis,
		basis.IndependentBound,
		matrix.MatrixActLinear,
		vec_smooth.JacobianMatrixDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"⋃T ≠ ∅",
		},
		Conclusion: "n ≤ m",
	},
		"Choose a source point and active chart pair. Its Jacobian sends the n standard basis vectors "+
			"to independent normalized m-vectors, since it acts injectively; IndependentBound gives n≤m."),
})}

var CompactInjectiveImmersion = compactInjectiveImmersionThm{family.Add(registry.ProofEntry{
	Name: "CompactInjectiveImmersion",
	Key:  "prop_602e35492b5f63db",
	Reading: "Compactness is used only to recover the topology of the image. This " +
		"statement does not identify arbitrary injective immersions with embeddings.",
	Deps: []registry.EntryLike{
		EmbeddingDef,
		ImmersionDef,
		ManifoldDef,
		continuous.CompactHausdorffEmbedding,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"compact_in(T, ⋃T)",
			"injective_on(⋃T, f)",
		},
		Conclusion: "smooth_manifold_embedding⟨n, m⟩(T, 𝒜, S, ℬ, f)",
	},
		"The immersion supplies a continuous map and a Hausdorff target. "+
			"CompactHausdorffEmbedding turns its injectivity into a topological "+
			"embedding; EmbeddingDef then combines it with the given immersion."),
})}
