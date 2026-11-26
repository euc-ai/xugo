package spin_geometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/clifford_spin"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/embedding_normal"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/registry"
)

var SpinorBundleExists = spinorBundleExistsThm{family.Add(registry.ProofEntry{
	Name: "SpinorBundleExists",
	Key:  "prop_b394c722c5b1e1b2",
	Deps: []registry.EntryLike{
		clifford_spin.RepresentationProduct,
		clifford_spin.SpinRepresentationUnitary,
	},
	Build: family.Card(Statement{
		Binders: "∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real).",
		Hypotheses: []string{"spin_atlas(m, N, T, 𝒜, f, L, U, F, g)"},
		Conclusion: "∃S:prod(num, A → num → num → complex). ∃W:(num → A → num → num → complex). " +
			"    spinor_realization(m, N, T, 𝒜, f, L, U, F, g, S, W)",
	},
		"Glue the finite-dimensional unitary spin representation using the lifted "+
			"cocycle. A finite subordinate partition of unity embeds the associated Hermitian "+
			"bundle in a finite trivial bundle and produces its smooth orthogonal projection."),
})}

var GradedSpinorBundles = gradedSpinorBundlesThm{family.Add(registry.ProofEntry{
	Name: "GradedSpinorBundles",
	Key:  "prop_49aafd3aa84f26f2",
	Deps: []registry.EntryLike{clifford_spin.SpinRepresentationUnitary},
	Build: family.Card(Statement{
		Binders: "∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex).",
		Hypotheses: []string{"spinor_realization(m, N, T, 𝒜, f, L, U, F, g, S, W)"},
		Conclusion: "(∀e:num. " +
			"    smooth_projection_bundle(2 * m, fst(S), T, 𝒜, snd(spinor_parity(m, T, L, U, S, W, e)))) ∧ " +
			"projection_isomorphic(T, " +
			"    S, " +
			"    projection_sum(spinor_parity(m, T, L, U, S, W, 0), spinor_parity(m, T, L, U, S, W, 1)))",
	},
		"The Spin representation preserves exterior parity, so the local "+
			"orthogonal parity projections agree on overlaps and descend smoothly."),
})}

var SpinConnectionExists = spinConnectionExistsThm{family.Add(registry.ProofEntry{
	Name: "SpinConnectionExists",
	Key:  "prop_5b86ab5aa89f94b5",
	Deps: []registry.EntryLike{clifford_spin.RepresentationProduct},
	Build: family.Card(Statement{
		Binders: "∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex).",
		Hypotheses: []string{"spinor_realization(m, N, T, 𝒜, f, L, U, F, g, S, W)"},
		Conclusion: "∃Γ:(num → " +
			"        num → " +
			"        prod(set(A), A → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        complex). " +
			"    spinor_connection(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ)",
	},
		"Differentiate the lifted transition identity. The differential of the spin representation "+
			"sends a skew matrix omega to minus one quarter sum omega_ab c_a c_b. Consequently the "+
			"displayed local connection forms transform correctly and define a projected global connection."),
})}

var FrameVector = frameVectorThm{family.Add(registry.ProofEntry{
	Name: "FrameVector",
	Key:  "prop_8674488df9efc818",
	Deps: []registry.EntryLike{
		embedding_normal.NormalProjectionSpec,
		embedding_normal.NormalBundleDef,
		embedding_normal.ComplexTangentDef,
		tangent.EuclideanDifferentialLinear,
		tangent.TangentModule,
		module_dimension.AnnihilatorDimension,
		module_dimension.AnnihilatorSubspace,
		module_dimension.SubmoduleDimEq,
		smooth_manifold.EmbeddingDef,
		smooth_manifold.ImmersionDef,
	},
	Build: family.Card(Statement{
		Binders: "∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀i j:num. " +
			"∀x:A.",
		Hypotheses: []string{"spin_atlas(m, N, T, 𝒜, f, L, U, F, g)", "i < L", "j < 2 * m", "x ∈ U(i)"},
		Conclusion: "tangent_vector_on⟨2 * m⟩(T, " +
			"    𝒜, " +
			"    x, " +
			"    spin_frame_vector(2 * m, N, T, 𝒜, f, F(i), x, j)) ∧ " +
			"manifold_euclidean_differential⟨2 * m, N⟩(T, " +
			"    𝒜, " +
			"    f, " +
			"    x, " +
			"    spin_frame_vector(2 * m, N, T, 𝒜, f, F(i), x, j)) = " +
			"(λa:num. F(i, x, a, j))",
	},
		"The ε in FrameVectorDef needs only some tangent vector with differential w, the j-th "+
			"column of F(i, x); injectivity is not used. The frame laws give FᵀF = I and FFᵀ = I − "+
			"R(x) for the normal projection R, so Rw = 0, and NormalProjectionSpec makes R "+
			"symmetric with image the annihilator of the differential's image V; hence w lies in "+
			"the double annihilator of V. V is a subspace (tangent.EuclideanDifferentialLinear), so "+
			"its double annihilator is V by dimension count (AnnihilatorDimension, SubmoduleDimEq)."),
})}
