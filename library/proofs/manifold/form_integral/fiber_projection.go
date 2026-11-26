// Horizontal-before-vertical order fixes both projection formulas and product-form integration.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var FiberIntegralProjectionFormula = fiberIntegralProjectionFormulaThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralProjectionFormula",
	Key:  "prop_a9f9ae2fc53aeaac",
	Reading: "The projected base form is on the left. Horizontal-before-vertical order gives " +
		"exactly this formula with no factorial or sign, including zero and excessive degrees.",
	Deps: []registry.EntryLike{
		FiberIntegralForm,
		FiberIntegralDef,
		fiberSliceDef,
		IntegralAdd,
		IntegralScale,
		smooth_manifold.SmoothProductProjections,
		differential_form.PullbackCoordinate,
		differential_form.WedgeDef,
		vec_form.WedgeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀p q:num. " +
			"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), q + m, ω)",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    p + q, " +
			"    manifold_form_wedge⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        p, " +
			"        q + m, " +
			"        manifold_form_pullback⟨n + m, n⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            T, " +
			"            𝒜, " +
			"            p, " +
			"            fst, " +
			"            α), " +
			"        ω)) = " +
			"manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, q, ω))",
	},
		"On a product chart the pullback of α vanishes if any of its inputs is "+
			"vertical. In the shuffle expansion, only choices of p horizontal columns "+
			"for α survive; all vertical columns stay in the other factor. Integrate the "+
			"finite horizontal shuffle sum using linearity to recover the base wedge."),
})}

var FiberIntegralRightProjection = fiberIntegralRightProjectionThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralRightProjection",
	Key:  "prop_29cefd7f885995fd",
	Reading: "Moving a base p-form past integration contributes the fiber-degree sign. " +
		"This is distinct from the sign-free exterior-derivative and left-projection formulas.",
	Deps: []registry.EntryLike{
		FiberIntegralProjectionFormula,
		FiberIntegralScale,
		FiberIntegralForm,
		differential_form.WedgeGradedCommutative,
		differential_form.PullbackForm,
		smooth_manifold.SmoothProductProjections,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀p q:num. " +
			"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), q + m, ω)",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    q + p, " +
			"    manifold_form_wedge⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        q + m, " +
			"        p, " +
			"        ω, " +
			"        manifold_form_pullback⟨n + m, n⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            T, " +
			"            𝒜, " +
			"            p, " +
			"            fst, " +
			"            α))) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    (-&1) ^ (m * p) * " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, q, p, manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, q, ω), α)(c, " +
			"        y, " +
			"        P)",
	},
		"Move the pulled-back p-form to the left in the product, apply the left projection formula, and "+
			"move it back on the base. The two graded signs multiply to (-1)^(p*(q+m)+p*q) = (-1)^(m*p)."),
})}

var FiberIntegralProduct = fiberIntegralProductThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralProduct",
	Key:  "prop_37235c7c803ce0c1",
	Reading: "No orientation of the base or of the product is required. The sign is positive " +
		"because the factor order, coordinate blocks and wedge factors all put the base before the fiber.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		IntegralScale,
		smooth_manifold.SmoothProductProjections,
		differential_form.PullbackCoordinate,
		differential_form.WedgeDef,
		vec_form.WedgeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀β:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, α)",
			"manifold_form_on⟨m⟩(S, ℬ, m, β)",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    manifold_form_wedge⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k, " +
			"        m, " +
			"        manifold_form_pullback⟨n + m, n⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            T, " +
			"            𝒜, " +
			"            k, " +
			"            fst, " +
			"            α), " +
			"        manifold_form_pullback⟨n + m, m⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            S, " +
			"            ℬ, " +
			"            m, " +
			"            snd, " +
			"            β))) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_form_integral⟨m⟩(S, ℬ, β) * α(c, y, P)",
	},
		"For a split frame, the pullback of α reads only the k horizontal columns and "+
			"the pullback of β reads only the m vertical columns. Exactly the identity "+
			"block shuffle survives, so the slice is α(c,y,P) times β. Integrate that "+
			"scalar multiple on the compact fiber and retain the base normalization."),
})}
