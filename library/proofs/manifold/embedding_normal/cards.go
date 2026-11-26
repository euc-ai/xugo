package embedding_normal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

// NormalProjectionSpec — at a carrier point the selected normal projection is a padded
// symmetric idempotent whose image is the normal space.
var NormalProjectionSpec = normalProjectionSpecThm{family.Add(registry.ProofEntry{
	Name: "NormalProjectionSpec",
	Key:  "prop_9aff90b8346051a0",
	Reading: "Only x ∈ ⋃T is assumed. The normal space is the annihilator of a set of " +
		"vectors, a subspace of ℝ^N whatever f is; at a point with no tangent vectors it is " +
		"all of ℝ^N and the projection is the identity. Off the carrier the definition is zero.",
	Deps: []registry.EntryLike{
		NormalProjectionDef,
		module_dimension.AnnihilatorSubspace,
		linear_independence.BasisExists,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀x:A.",
		Hypotheses: []string{"x ∈ ⋃T"},
		Conclusion: "(∀i j:num. N ≤ i ∨ N ≤ j ⇒ «normal projection»(i, j) = &0) ∧ " +
			"(∀i j:num. «normal projection»(i, j) = «normal projection»(j, i)) ∧ " +
			"(∀i j:num. " +
			"    i < N ∧ j < N ⇒ " +
			"    real_sum({k:num | k < N}, λk:num. «normal projection»(i, k) * «normal projection»(k, j)) = " +
			"    «normal projection»(i, j)) ∧ " +
			"image(λu:(num → real). λi:num. " +
			"        COND(i < N, real_sum({j:num | j < N}, λj:num. «normal projection»(i, j) * u(j)), &0), " +
			"    {u:(num → real) | vec⟨N⟩(&0, u)}) = " +
			"«normal space»",
		Abbrev: Abbrev{
			{Name: "normal projection", Text: "embedding_normal_projection(n, N, T, 𝒜, f, x)"},
			{Name: "normal space", Text: "{u:(num → real) | " +
				"    vec⟨N⟩(&0, u) ∧ " +
				"    (∀v:(prod(set(A), A → num → real) → num → real). " +
				"        tangent_vector_on⟨n⟩(T, 𝒜, x, v) ⇒ " +
				"        real_sum({i:num | i < N}, " +
				"            λi:num. u(i) * manifold_euclidean_differential⟨n, N⟩(T, 𝒜, f, x, v, i)) = " +
				"        &0)}"},
		},
	},
		"The normal space is the annihilator, under the standard pairing on the free module over "+
			"{i<N}, of the differential's values, so a subspace "+
			"(module_dimension.AnnihilatorSubspace). An orthonormal basis e₁…e_k of it gives R = Σ "+
			"e_l e_lᵀ, which satisfies the clauses and so witnesses the ε in NormalProjectionDef. "+
			"The filler promotes the step the corpus lacks: a subspace of ℝ^N has an orthonormal "+
			"basis (Gram–Schmidt on linear_independence.BasisExists), hence an orthogonal projection."),
})}

// NormalProjectionChart — in a compatible chart at x the normal projection of an immersion
// is I − J(JᵀJ)⁻¹Jᵀ, with J the Jacobian of f in that chart.
var NormalProjectionChart = normalProjectionChartThm{family.Add(registry.ProofEntry{
	Name: "NormalProjectionChart",
	Key:  "prop_7324382c1fad0515",
	Deps: []registry.EntryLike{
		NormalProjectionSpec,
		tangent.EuclideanDifferentialCoordinate,
		tangent.TangentFromChart,
		smooth_manifold.ImmersionDef,
		determinant.DeterminantZeroIffDependent,
		determinant.MatrixInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀i j:num.",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
			"i < N",
			"j < N",
		},
		Conclusion: "embedding_normal_projection(n, N, T, 𝒜, f, x, i, j) = " +
			"COND(i = j, &1, &0) - " +
			"real_sum({a:num | a < n}, " +
			"    λa:num. " +
			"        real_sum({b:num | b < n}, " +
			"            λb:num. «J»(i, a) * matrix_inverse(real_field_ops, n, «Gram», a, b) * «J»(j, b)))",
		Abbrev: Abbrev{
			{Name: "J", Text: "vec_jacobian_matrix⟨n, N⟩(f ∘ inverse_on(fst(c), snd(c)), snd(c)(x))"},
			{Name: "Gram", Text: "λa:num. λb:num. real_sum({k:num | k < N}, λk:num. «J»(k, a) * «J»(k, b))"},
		},
	},
		"In c the differential's values are the vectors J·u for padded u ∈ ℝⁿ "+
			"(tangent.EuclideanDifferentialCoordinate, with tangent.TangentFromChart reaching every "+
			"u), so NormalProjectionSpec's image is the orthogonal complement of the column space of "+
			"J. Injectivity of J (smooth_manifold.ImmersionDef) makes JᵀJ invertible "+
			"(determinant.DeterminantZeroIffDependent, MatrixInverse), and I − J(JᵀJ)⁻¹Jᵀ is a "+
			"symmetric idempotent with that image; two symmetric idempotents with one image are equal."),
	Reading: "The immersion is what makes JᵀJ invertible: its injectivity at the " +
		"codomain's identity chart is injectivity of exactly this J. At n = 0 every sum " +
		"is empty and the projection is the identity, the normal space being all of ℝ^N.",
})}
