// Equivalent positive atlases give the same metric predicate and Euler form.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var EulerAtlasInvariant = eulerAtlasInvariantThm{family.Add(registry.ProofEntry{
	Name: "EulerAtlasInvariant",
	Key:  "prop_f13fc65c3bfd86f8",
	Deps: []registry.EntryLike{
		MetricAtlasInvariant,
		EulerFormDef,
		eulerRepresentativeDef,
		EulerRepresentativeExistsUnique,
		PositiveFrameDef,
		form_integral.OrientedAtlasChange,
		differential_form.FormOnDef,
	},
	Reading: "The second atlas is itself an oriented atlas on the same topology and " +
		"consists of positive charts for the first. A mere positive subfamily without " +
		"the covering manifold condition would not determine the same global form.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀ℬ:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"riemannian_metric⟨n⟩(T, 𝒜, g)",
			"oriented_manifold⟨n⟩(T, ℬ)",
			"∀c:prod(set(A), A → num → real). c ∈ ℬ ⇒ positive_manifold_chart⟨n⟩(T, 𝒜, c)",
		},
		Conclusion: "riemannian_metric⟨n⟩(T, ℬ, g) ∧ " +
			"riemannian_euler_form⟨n⟩(T, 𝒜, g) = riemannian_euler_form⟨n⟩(T, ℬ, g)",
	},
		"OrientedAtlasChange identifies both compatible and positive chart "+
			"predicates. MetricAtlasInvariant transfers the metric, and these identical "+
			"predicates also identify positive frames and Euler representatives as "+
			"literal normalized families, so the chosen Euler forms coincide."),
})}
