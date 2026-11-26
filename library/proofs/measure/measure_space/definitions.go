package measure_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

var MeasureOn = measureOnThm{family.DefineStructure(registry.DefEntry{
	Name:  "MeasureOn",
	Key:   "prop_9a2ed8d3cd4c3c43",
	Const: "measure_on",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → bool",
	Reading: "The measure is constrained only on the sigma " +
		"algebra. Empty carriers and zero measures are permitted.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    measure_on(Ω, S, μ) ⇔ " +
			"    sigma_algebra_on(Ω, S) ∧ " +
			"    μ(∅) = &0 ∧ " +
			"    (∀a:(num → set(A)). " +
			"        (∀n:num. a(n) ∈ S) ∧ (∀i j:num. i ≠ j ⇒ a(i) ∩ a(j) = ∅) ⇒ " +
			"        μ(⋃image(a, 𝕌)) = extended_series(λn:num. μ(a(n))))",
	},
})}

var FiniteMeasureDef = finiteMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteMeasureDef",
	Key:   "prop_b891c742134ccf0",
	Const: "finite_measure_on",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → bool",
	Deps:  []registry.EntryLike{MeasureOn},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    finite_measure_on(Ω, S, μ) ⇔ measure_on(Ω, S, μ) ∧ μ(Ω) ≠ extended_infinity",
	},
})}

var NullSetDef = nullSetDefThm{family.Define(registry.DefEntry{
	Name:  "NullSetDef",
	Key:   "prop_658aae71d1f749a7",
	Const: "measure_null",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → set(A) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀E:set(A). " +
			"    measure_null(Ω, S, μ, E) ⇔ E ⊆ Ω ∧ ∃N:set(A). N ∈ S ∧ μ(N) = &0 ∧ E ⊆ N",
	},
})}

var AlmostEverywhereDef = almostEverywhereDefThm{family.Define(registry.DefEntry{
	Name:  "AlmostEverywhereDef",
	Key:   "prop_9c85def43a931590",
	Const: "measure_ae",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → bool) → bool",
	Deps:  []registry.EntryLike{NullSetDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀P:(A → bool). " +
			"    measure_ae(Ω, S, μ, P) ⇔ measure_null(Ω, S, μ, {x:A | x ∈ Ω ∧ ¬P(x)})",
	},
})}

var AEEqualDef = aEEqualDefThm{family.Define(registry.DefEntry{
	Name:  "AEEqualDef",
	Key:   "prop_f61748be4f8c2915",
	Const: "measure_ae_eq",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → B) → (A → B) → bool",
	Deps:  []registry.EntryLike{AlmostEverywhereDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → B). " +
			"    measure_ae_eq(Ω, S, μ, f, g) ⇔ measure_ae(Ω, S, μ, λx:A. f(x) = g(x))",
	},
})}

var RestrictMeasureDef = restrictMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "RestrictMeasureDef",
	Key:   "prop_77e1df533feb248f",
	Const: "restricted_measure",
	Type:  "(set(A) → extended_nonneg_real) → set(A) → set(A) → extended_nonneg_real",
	Equations: []string{
		"∀μ:(set(A) → extended_nonneg_real). ∀E U:set(A). restricted_measure(μ, E, U) = μ(U ∩ E)",
	},
})}

var PushforwardMeasureDef = pushforwardMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "PushforwardMeasureDef",
	Key:   "prop_e1ba74a8791e0152",
	Const: "pushforward_measure",
	Type:  "set(A) → (set(A) → extended_nonneg_real) → (A → B) → set(B) → extended_nonneg_real",
	Equations: []string{
		"∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → B). ∀E:set(B). " +
			"    pushforward_measure(Ω, μ, f, E) = μ(preimage_on(Ω, f, E))",
	},
})}

var DiscreteMeasureDef = discreteMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "DiscreteMeasureDef",
	Key:   "prop_b99c9c7e96a67f7e",
	Const: "discrete_measure",
	Type:  "set(A) → (A → extended_nonneg_real) → set(A) → extended_nonneg_real",
	Reading: "Mass is the supremum of finite subsums. This " +
		"definition works for arbitrary index sets and infinite weights.",
	Equations: []string{
		"∀Ω:set(A). ∀w:(A → extended_nonneg_real). ∀E:set(A). " +
			"    discrete_measure(Ω, w, E) = " +
			"    extended_sup({r:extended_nonneg_real | ∃F:set(A). finite(F) ∧ F ⊆ Ω ∩ E ∧ r = Σ_{x∈F} w(x)})",
	},
})}

// SigmaFiniteDef — a measure is σ-finite when its carrier is a countable
// union of measurable sets of finite measure.
var SigmaFiniteDef = sigmaFiniteDefThm{family.Define(registry.DefEntry{
	Name:  "SigmaFiniteDef",
	Key:   "prop_5e8a3cff736b23a6",
	Const: "sigma_finite_on",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → bool",
	Deps:  []registry.EntryLike{MeasureOn},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    sigma_finite_on(Ω, S, μ) ⇔ " +
			"    measure_on(Ω, S, μ) ∧ " +
			"    (∃a:(num → set(A)). (∀n:num. a(n) ∈ S ∧ μ(a(n)) ≠ extended_infinity) ∧ ⋃image(a, 𝕌) = Ω)",
	},
})}

// DiracMeasureDef — `dirac_measure(a)` gives mass one to every set that
// holds a and none to the others: the law of a constant.
var DiracMeasureDef = diracMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "DiracMeasureDef",
	Key:   "prop_58a7fa3f24a95b22",
	Const: "dirac_measure",
	Type:  "A → set(A) → extended_nonneg_real",
	Equations: []string{
		"∀a:A. ∀E:set(A). dirac_measure(a, E) = COND(a ∈ E, extended_of_real(&1), extended_of_real(&0))",
	},
})}
