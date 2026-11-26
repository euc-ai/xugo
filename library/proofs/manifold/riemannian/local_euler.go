// The normalized curvature Pfaffian is a closed local form and agrees on positive overlaps.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var LocalEulerForm = localEulerFormThm{family.Add(registry.ProofEntry{
	Name: "LocalEulerForm",
	Key:  "prop_2fe0637fdc55606d",
	Deps: []registry.EntryLike{
		localEulerDef,
		ConnectionSkew,
		vec_form.CurvatureSkew,
		vec_form.FormModule,
		vec_form.PfaffianForm,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)"},
		Conclusion: "vec_form_on⟨n⟩(«chart image»(c), n, riemannian_local_euler_form⟨n⟩(g, c, E))",
	},
		"The connection curvature is a skew matrix of two-forms. Constant "+
			"multiplication by 1/(2π) preserves each two-form carrier and "+
			"padding, so its order-n Pfaffian is a normalized smooth n-form."),
})}

var LocalEulerScale = localEulerScaleThm{family.Add(registry.ProofEntry{
	Name: "LocalEulerScale",
	Key:  "prop_3157fde1d4ec4625",
	Deps: []registry.EntryLike{
		localEulerDef,
		ConnectionSkew,
		vec_form.CurvatureForm,
		vec_form.PfaffianScale,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀m:num.",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)", "n = 2 * m"},
		Conclusion: "riemannian_local_euler_form⟨n⟩(g, c, E) = " +
			"(λy:(num → real). λP:(num → num → real). " +
			"    (&1 / (&2 * π)) ^ m * " +
			"    vec_form_pfaffian⟨n⟩(«chart image»(c), " +
			"        n, " +
			"        vec_form_curvature⟨n⟩(«chart image»(c), n, riemannian_connection⟨n⟩(g, c, E)), " +
			"        y, " +
			"        P))",
	},
		"Apply the homogeneous Pfaffian scaling law in order 2m to the constant factor "+
			"1/(2π). At m=0 the factor is one and the empty matching remains the normalized unit."),
})}

var LocalEulerFrameIndependent = localEulerFrameIndependentThm{family.Add(registry.ProofEntry{
	Name: "LocalEulerFrameIndependent",
	Key:  "prop_b2920571bd6d3671",
	Deps: []registry.EntryLike{
		localEulerDef,
		LocalEulerScale,
		CurvaturePfaffianFrameChange,
		vec_form.PfaffianOdd,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, F)",
		},
		Conclusion: "riemannian_local_euler_form⟨n⟩(g, c, E) = riemannian_local_euler_form⟨n⟩(g, c, F)",
	},
		"For even order the common scalar factor from LocalEulerScale "+
			"multiplies equal curvature Pfaffians. For odd order both scaled "+
			"Pfaffians are zero, so the equality holds in every dimension."),
})}

var LocalEulerOverlap = localEulerOverlapThm{family.Add(registry.ProofEntry{
	Name: "LocalEulerOverlap",
	Key:  "prop_cb527fc4f69e0239",
	Deps: []registry.EntryLike{
		localEulerDef,
		CurvatureChartChange,
		ChartFrameChangeOrthogonal,
		ChartFrameChangeDeterminant,
		ConnectionSkew,
		form_integral.PositiveTransition,
		vec_form.CurvatureSkew,
		vec_form.PfaffianPullback,
		vec_form.PfaffianOrientedFrame,
		vec_form.PfaffianOdd,
		vec_form.PullbackLinear,
	},
	Reading: "Both charts must be positive for this unsigned equality. A " +
		"general compatible overlap may have determinant minus one, whose Pfaffian " +
		"sign cannot be discarded. Normalization is to the actual overlap image.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, d, F)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, d)",
		},
		Conclusion: "normalize_on(«overlap»(c, d), " +
			"    (λP:(num → num → real). &0), " +
			"    riemannian_local_euler_form⟨n⟩(g, c, E)) = " +
			"vec_form_pullback⟨n, n⟩(«overlap»(c, d), " +
			"    n, " +
			"    «transition»(c, d), " +
			"    riemannian_local_euler_form⟨n⟩(g, d, F))",
	},
		"Positive coordinate transition makes the overlap gauge determinant one. "+
			"CurvatureChartChange, constant scaling, and Pfaffian congruence identify the pulled-back "+
			"target Euler form with the restricted source Euler form; odd order is zero on both sides."),
})}
