// radial.go — polar coordinates in the plane, and the integral over ℝ²ⁿ⁺²
// of a function of the squared norm, which is a one-variable integral
// against sⁿ with the constant πⁿ⁺¹/n!. The even dimension is what lets the
// induction split off one plane at a time. The Gaussian integral is the
// square root of the plane's.

package vec_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/registry"
)

// PolarCoordinates — the integral over the plane in polar coordinates.
var PolarCoordinates = polarCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "PolarCoordinates",
	Key:  "prop_304ef0ddba0027a7",
	Reading: "R bounds the support's radius; for R ≤ 0 the function vanishes on the " +
		"whole plane and both sides are 0, the inner integrals of 0 for r between R and 0.",
	Deps: []registry.EntryLike{
		ChangeOfVariables,
		Fubini,
		CcRapid,
		integral_convergence.DominatedConvergence,
		lebesgue_measure.LebesgueMeasureOn,
		lebesgue_integral.MeasurableFunctionIffRealMeasurable,
		lebesgue_integral.LebesgueIntegrableIff,
		lebesgue_integral.LebesgueIntegralEq,
		lebesgue_riemann.LebesgueIntegralInterval,
		lebesgue_measure.OuterMeasureSingleton,
	},
	Build: family.Card(Statement{
		Binders: "∀g:((num → real) → real). ∀R:real.",
		Hypotheses: []string{
			"continuous_map(euclidean_topology(2), real_topology, g)",
			"∀y:(num → real). vec⟨2⟩(y) ∧ R ≤ ‖y‖_2 ⇒ g(y) = &0",
		},
		Conclusion: "vec_integral⟨2⟩(g) = " +
			"real_integral(λr:real. r * real_integral(λθ:real. g(«polar»(r, θ)), -π, π), &0, R)",
	},
		"(r, θ) ↦ «polar»(r, θ) is a diffeomorphism of ⟬0, ∞⟭ × ⟬−π, π⟭ onto the plane less the "+
			"closed half-line {(x, 0) : x ≤ 0}, with Jacobian determinant r (ChangeOfVariables); g·χₖ, "+
			"with χₖ continuous, 0 near that half-line and increasing to 1 off it, has compact support in "+
			"the image, and both sides pass to the limit (integral_convergence.DominatedConvergence at "+
			"the Lebesgue measure, read through lebesgue_integral.MeasurableFunctionIffRealMeasurable, "+
			"LebesgueIntegrableIff and LebesgueIntegralEq, the support being bounded). The limit is g off "+
			"the half-line, so the outer integrands converge except on the one slice that holds it, and a "+
			"change of a function at one point does not change its Lebesgue integral (a singleton is "+
			"null, lebesgue_measure.OuterMeasureSingleton); Fubini puts θ inside"),
})}

// EvenRadialIntegral — the integral over ℝ²ⁿ⁺² of a function of the
// squared norm.
var EvenRadialIntegral = evenRadialIntegralThm{family.Add(registry.ProofEntry{
	Name: "EvenRadialIntegral",
	Key:  "prop_28717b6ff180b43a",
	Reading: "Only ψ on the nonnegative reals is read, ⟪y, y⟫ being nonnegative. For R " +
		"≤ 0, ψ vanishes there and both sides are 0. At n = 0 the constant is π: the plane.",
	Deps: []registry.EntryLike{
		PolarCoordinates,
		IntegralSplit,
		Fubini,
		CcRapid,
		real_integral.IntegralSubstitution,
		real_integral.IntegrationByParts,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀ψ:(real → real). ∀R:real.",
		Hypotheses: []string{
			"real_continuous_on({s:real | &0 ≤ s}, ψ)",
			"∀s:real. R ≤ s ⇒ ψ(s) = &0",
		},
		Conclusion: "vec_integral⟨2 * n + 2⟩(λy:(num → real). ψ(⟪y, y⟫_(2 * n + 2))) = " +
			"π ^ (n + 1) / &factorial(n) * real_integral(λs:real. ψ(s) * s ^ n, &0, R)",
	},
		"replace ψ by s ↦ ψ(|s|), continuous on all of ℝ and equal to ψ wherever either side reads it, "+
			"so that the substitutions and the integration by parts below may read it at negative arguments. "+
			"Induction on n. At n = 0: in polar coordinates the θ-integral is 2π·ψ(r²) (PolarCoordinates), "+
			"and s = r² turns ∫₀^√R 2πr·ψ(r²) dr into π∫₀^R ψ(s) ds (real_integral.IntegralSubstitution). At "+
			"n + 1: split ℝ²ⁿ⁺⁴ as ℝ²ⁿ⁺² × ℝ² (IntegralSplit, Fubini); at fixed y the plane integral of "+
			"ψ(⟪y, y⟫ + ⟪z, z⟫) is π·Φ(⟪y, y⟫) with Φ(u) = ∫_u^R ψ, the case n = 0 at s ↦ ψ(⟪y, y⟫ + s); the "+
			"induction hypothesis at Φ gives πⁿ⁺²/n!·∫₀^R Φ(s)·sⁿ ds, and integration by parts, Φ' = −ψ and "+
			"Φ(R) = 0, makes it ∫₀^R ψ(s)·sⁿ⁺¹/(n + 1) ds (real_integral.IntegrationByParts)"),
})}

// GaussianIntegral — the integral of exp(−⟪x, x⟫) over ℝⁿ is the n-th
// power of √π.
var GaussianIntegral = gaussianIntegralThm{family.Add(registry.ProofEntry{
	Name:    "GaussianIntegral",
	Key:     "prop_8982b265adef3d30",
	Reading: "At n = 0 the integral is the integrand's value at the zero vector, exp(0) = 1 = √π⁰.",
	Deps: []registry.EntryLike{
		IntegralProduct,
		lebesgue_riemann.GaussianIntegral,
		real_exp_log.ExpAdd,
	},
	Build: family.Card(
		"∀n:num. "+
			"    vec_integral⟨n⟩( "+
			"        λx:(num → real). real_exp(-real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2)))) = "+
			"    real_pow(real_sqrt(pi), n)",
		"the integrand is the product over i < n of exp(−x(i)²) (real_exp_log.ExpAdd), "+
			"and IntegralProduct makes the integral the n-th power of the integral of "+
			"exp(−t²) over the line, which is √π (lebesgue_riemann.GaussianIntegral)"),
})}
