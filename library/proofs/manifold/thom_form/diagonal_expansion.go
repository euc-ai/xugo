package thom_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalExpansionReproducing = diagonalExpansionReproducingThm{family.Add(registry.ProofEntry{
	Name: "DiagonalExpansionReproducing",
	Key:  "prop_fabb98e5374a563a",
	Deps: []registry.EntryLike{DiagonalReproducing},
	Reading: "The supplied expansion is homogeneous in total degree n, and every " +
		"representative is closed. No linear independence of its summands is needed.",
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀η:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
				"∀r p:num. " +
				"∀d e:(num → num). " +
				"∀a b:(num → (prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
				"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"manifold_diagonal_form⟨n⟩(T, 𝒜, η)",
				"∀j:num. " +
					"    j < r ⇒ " +
					"    d(j) + e(j) = n ∧ " +
					"    a(j) ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), d(j)) ∧ " +
					"    b(j) ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), e(j))",
				"de_rham_class⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), n, η) = " +
					"module_sum(de_rham_cohomology_module⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        n).add, " +
					"    de_rham_cohomology_module⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        n).zero, " +
					"    {j:num | j < r}, " +
					"    (λj:num. " +
					"        de_rham_external_product⟨n, n⟩(T, " +
					"            𝒜, " +
					"            T, " +
					"            𝒜, " +
					"            d(j), " +
					"            e(j), " +
					"            de_rham_class⟨n⟩(T, 𝒜, d(j), a(j)), " +
					"            de_rham_class⟨n⟩(T, 𝒜, e(j), b(j)))))",
				"α ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), p)",
			},
			Conclusion: "de_rham_class⟨n⟩(T, 𝒜, p, α) = " +
				"module_sum(de_rham_cohomology_module⟨n⟩(T, 𝒜, p).add, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, p).zero, " +
				"    {j:num | j < r ∧ d(j) = p}, " +
				"    (λj:num. " +
				"        de_rham_cohomology_module⟨n⟩(T, 𝒜, p).smul((-&1)^p * " +
				"            manifold_form_integral⟨n⟩(T, 𝒜, manifold_form_wedge⟨n⟩(T, 𝒜, p, e(j), α, b(j))), " +
				"            de_rham_class⟨n⟩(T, 𝒜, p, a(j)))))",
		},
		"Insert the finite external-product expansion into DiagonalReproducing. Fiber "+
			"integration keeps precisely the summands whose first degree is p; commuting the "+
			"degree-p second-factor form past that first-factor form contributes (−1)^(p²)=(−1)^p."),
})}

var DiagonalDegreeTrace = diagonalDegreeTraceThm{family.Add(registry.ProofEntry{
	Name: "DiagonalDegreeTrace",
	Key:  "prop_adbc1c2e287dc53d",
	Deps: []registry.EntryLike{
		DiagonalExpansionReproducing,
		de_rham_cover.CompactManifoldFiniteCohomology,
		module_dimension.TraceFromBasis,
		module_dimension.BasisCoordinateDelta,
		module_dimension.TraceAdd,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀η:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
				"∀r p:num. " +
				"∀d e:(num → num). " +
				"∀a b:(num → (prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)).",
			Hypotheses: []string{
				"manifold_diagonal_form⟨n⟩(T, 𝒜, η)",
				"∀j:num. " +
					"    j < r ⇒ " +
					"    d(j) + e(j) = n ∧ " +
					"    a(j) ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), d(j)) ∧ " +
					"    b(j) ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), e(j))",
				"de_rham_class⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), n, η) = " +
					"module_sum(de_rham_cohomology_module⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        n).add, " +
					"    de_rham_cohomology_module⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        n).zero, " +
					"    {j:num | j < r}, " +
					"    (λj:num. " +
					"        de_rham_external_product⟨n, n⟩(T, " +
					"            𝒜, " +
					"            T, " +
					"            𝒜, " +
					"            d(j), " +
					"            e(j), " +
					"            de_rham_class⟨n⟩(T, 𝒜, d(j), a(j)), " +
					"            de_rham_class⟨n⟩(T, 𝒜, e(j), b(j)))))",
			},
			Conclusion: "&de_rham_betti⟨n⟩(T, 𝒜, p) = " +
				"(-&1)^p * " +
				"real_sum({j:num | j < r ∧ d(j) = p}, " +
				"    λj:num. manifold_form_integral⟨n⟩(T, 𝒜, manifold_form_wedge⟨n⟩(T, 𝒜, p, e(j), a(j), b(j))))",
		},
		"Take the trace of the finite-rank reproduction identity on H^p. "+
			"TraceFromBasis gives the identity trace as dimension, BasisCoordinateDelta "+
			"gives trace(x↦φ(x)a)=φ(a), and TraceAdd sums the rank-one terms."),
})}
