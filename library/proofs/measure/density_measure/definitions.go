// definitions.go — the measure a density gives: a set has for mass the
// integral of the density over it.

package density_measure

import (
	"github.com/euc-ai/xugo/library/registry"
)

// DensityMeasureDef — `density_measure(Ω, S, μ, ρ)`: a set E has mass
// ∫ ρ·1_E dμ, the integral against μ of the density ρ cut to 0 off E.
var DensityMeasureDef = densityMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "DensityMeasureDef",
	Key:   "prop_6dd0b45be8b9185",
	Const: "density_measure",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → extended_nonneg_real) → " +
		"set(A) → " +
		"extended_nonneg_real",
	Reading: "The formula is a number for every set E and every ρ; that it is a measure " +
		"on S is the chapter's theorem for a measurable ρ. The density takes values in ⟦0, ∞⟧, " +
		"so a real density enters through extended_of_real, which reads a negative value as 0.",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀ρ:(A → extended_nonneg_real). " +
			"∀E:set(A). " +
			"    density_measure(Ω, S, μ, ρ, E) = " +
			"    nonneg_integral(Ω, S, μ, λx:A. COND(x ∈ E, ρ(x), extended_of_real(&0)))",
	},
})}
