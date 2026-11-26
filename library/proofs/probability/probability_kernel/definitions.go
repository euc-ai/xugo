// definitions.go — probability kernels between explicit measurable
// spaces, and the three ways a kernel acts: mixed against a measure on
// its source, joined with that measure into a measure on pairs, and
// composed with a second kernel.

package probability_kernel

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ProbabilityKernelOn — `probability_kernel_on(Ω, S, V, T, K)`: K gives
// each point of Ω a probability on (V, T), and the mass of each
// measurable set is a measurable function of the point. Off Ω the
// kernel carries no condition.
var ProbabilityKernelOn = probabilityKernelOnThm{family.Define(registry.DefEntry{
	Name:  "ProbabilityKernelOn",
	Key:   "prop_3995b016632c870b",
	Const: "probability_kernel_on",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"set(B) → " +
		"set(set(B)) → " +
		"(A → set(B) → extended_nonneg_real) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀V:set(B). ∀T:set(set(B)). ∀K:(A → set(B) → extended_nonneg_real). " +
			"    probability_kernel_on(Ω, S, V, T, K) ⇔ " +
			"    sigma_algebra_on(Ω, S) ∧ " +
			"    (∀x:A. x ∈ Ω ⇒ probability_on(V, T, K(x))) ∧ " +
			"    (∀t:set(B). t ∈ T ⇒ extended_measurable(Ω, S, λx:A. K(x, t)))",
	},
})}

// KernelMixtureDef — `kernel_mixture(Ω, S, μ, K)` is the measure μK on
// the target: a set has the μ-average of its kernel masses.
var KernelMixtureDef = kernelMixtureDefThm{family.Define(registry.DefEntry{
	Name:  "KernelMixtureDef",
	Key:   "prop_83f96ab070d0e95f",
	Const: "kernel_mixture",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → set(B) → extended_nonneg_real) → " +
		"set(B) → " +
		"extended_nonneg_real",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀t:set(B). " +
			"    kernel_mixture(Ω, S, μ, K, t) = nonneg_integral(Ω, S, μ, λx:A. K(x, t))",
	},
})}

// KernelJointDef — `kernel_joint(Ω, S, μ, K)` is the measure μ ⊗ K on
// pairs: a set of pairs has the μ-average of the kernel mass of its
// section. For a constant kernel it is `product_measure`.
var KernelJointDef = kernelJointDefThm{family.Define(registry.DefEntry{
	Name:  "KernelJointDef",
	Key:   "prop_3db3844c0b00d9db",
	Const: "kernel_joint",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → set(B) → extended_nonneg_real) → " +
		"set(prod(A, B)) → " +
		"extended_nonneg_real",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀E:set(prod(A, B)). " +
			"    kernel_joint(Ω, S, μ, K, E) = nonneg_integral(Ω, S, μ, λx:A. K(x, {y:B | (x, y) ∈ E}))",
	},
})}

// KernelComposeDef — `kernel_compose(V, T, K, L)` is the kernel K
// followed by L: at x, a set has the K(x)-average of its L-masses.
var KernelComposeDef = kernelComposeDefThm{family.Define(registry.DefEntry{
	Name:  "KernelComposeDef",
	Key:   "prop_a6b387ea4e03c5d2",
	Const: "kernel_compose",
	Type: "set(B) → " +
		"set(set(B)) → " +
		"(A → set(B) → extended_nonneg_real) → " +
		"(B → set(C) → extended_nonneg_real) → " +
		"A → " +
		"set(C) → " +
		"extended_nonneg_real",
	Equations: []string{
		"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"∀L:(B → set(C) → extended_nonneg_real). " +
			"∀x:A. " +
			"∀u:set(C). " +
			"    kernel_compose(V, T, K, L, x, u) = nonneg_integral(V, T, K(x), λy:B. L(y, u))",
	},
})}
