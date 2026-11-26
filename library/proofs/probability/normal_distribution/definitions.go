// definitions.go — the normal density and the measure it gives the line.

package normal_distribution

import (
	"github.com/euc-ai/xugo/library/registry"
)

// NormalDensityDef — `normal_density(m, v, x)` is the density at x of the
// normal distribution of mean m and variance v,
// exp(−(x − m)²/(2v)) / √(2πv).
var NormalDensityDef = normalDensityDefThm{family.Define(registry.DefEntry{
	Name:  "NormalDensityDef",
	Key:   "prop_7bf8ecd0283b90cc",
	Const: "normal_density",
	Type:  "real → real → real → real",
	Reading: "The second argument is the variance, not the standard deviation. The " +
		"formula is a number for every v: at v = 0 it is 0, real division by zero being 0, " +
		"and for v < 0 it is negative, the square root of a negative real being negative.",
	Equations: []string{
		"∀m v x:real. " +
			"    normal_density(m, v, x) = real_exp(-(real_pow(x - m, 2) / (&2 * v))) / real_sqrt(&2 * pi * v)",
	},
})}

// NormalDistributionDef — `normal_distribution(m, v)` is the measure on
// the line with density `normal_density(m, v)` against the Lebesgue
// measure.
var NormalDistributionDef = normalDistributionDefThm{family.Define(registry.DefEntry{
	Name:  "NormalDistributionDef",
	Key:   "prop_a7fd6b7852879c9a",
	Const: "normal_distribution",
	Type:  "real → real → set(real) → extended_nonneg_real",
	Reading: "For v ≤ 0 the density is nowhere positive and the distribution is " +
		"the zero measure, not the point mass at m: a statement about it asks 0 < v.",
	Equations: []string{
		"∀m v:real. ∀E:set(real). " +
			"    normal_distribution(m, v, E) = " +
			"    density_measure(𝕌, " +
			"        {s:set(real) | lebesgue_measurable(s)}, " +
			"        lebesgue_outer_measure, " +
			"        λx:real. extended_of_real(normal_density(m, v, x)), " +
			"        E)",
	},
	Deps: []registry.EntryLike{NormalDensityDef},
})}
