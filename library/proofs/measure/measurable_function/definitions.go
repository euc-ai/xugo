package measurable_function

import (
	"github.com/euc-ai/xugo/library/registry"
)

var RealMeasurableDef = realMeasurableDefThm{family.Define(registry.DefEntry{
	Name:  "RealMeasurableDef",
	Key:   "prop_241c56b2912920b6",
	Const: "real_measurable",
	Type:  "set(A) → set(set(A)) → (A → real) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). " +
			"    real_measurable(Ω, S, f) ⇔ measurable_map(Ω, S, 𝕌, borel_sets(real_topology), f)",
	},
})}

var ExtendedBorelDef = extendedBorelDefThm{family.Define(registry.DefEntry{
	Name: "ExtendedBorelDef",
	Reading: "The strict rays also determine the measurable singleton " +
		"{0} by complement and {infinity} by a countable intersection. " +
		"Clamping negative thresholds does not lose either endpoint.",
	Key:   "prop_7f8c4b2199930755",
	Const: "extended_borel",
	Type:  "set(set(extended_nonneg_real))",
	Equations: []string{
		"extended_borel = " +
			"generated_sigma(𝕌, " +
			"    {E:set(extended_nonneg_real) | " +
			"        ∃r:real. E = {x:extended_nonneg_real | extended_of_real(r) < x}})",
	},
})}

var ExtendedMeasurableDef = extendedMeasurableDefThm{family.Define(registry.DefEntry{
	Name:  "ExtendedMeasurableDef",
	Key:   "prop_40151cee473dc6a",
	Const: "extended_measurable",
	Type:  "set(A) → set(set(A)) → (A → extended_nonneg_real) → bool",
	Deps:  []registry.EntryLike{ExtendedBorelDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → extended_nonneg_real). " +
			"    extended_measurable(Ω, S, f) ⇔ measurable_map(Ω, S, 𝕌, extended_borel, f)",
	},
})}
