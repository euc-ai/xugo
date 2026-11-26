package cech_cohomology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var FiniteRepeatedCoverVanishing = finiteRepeatedCoverVanishingThm{family.Add(registry.ProofEntry{
	Name: "FiniteRepeatedCoverVanishing",
	Key:  "prop_a034bd8fc2c2f27a",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀F:(set(num) → module_ops(A, C)). " +
				"∀r:(set(num) → set(num) → C → C). " +
				"∀q:(num → num). " +
				"∀m n:num.",
			Hypotheses: []string{
				"intersection_module_datum(R, F, r)",
				"∀i:num. q(q(i)) = q(i)",
				"image(q, 𝕌) ⊆ 0 .. m",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ F(σ) = F(image(q, σ))",
				"∀σ τ:set(num). " +
					"    σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
					"    r(σ, τ) = r(image(q, σ), image(q, τ))",
				"m < n",
			},
			Conclusion: "cohomology(intersection_cech_complex(R, F, r), n) = " +
				"{coboundaries(intersection_cech_complex(R, F, r), n)}",
		},
		"The refinement q and inclusion of its finite image induce mutually inverse "+
			"cohomology maps, using the alternating prism homotopy. The normalized "+
			"increasing-tuple complex on at most m+1 vertices is zero above degree m."),
	Deps: []registry.EntryLike{IntersectionCechCochain},
	Reading: "This is reduction of repeated copies of one finite " +
		"cover; it does not assert invariance for arbitrary refinements.",
})}
