// definitions.go — a kernel that disintegrates a probability on pairs
// along its first coordinate: a version of the conditional distribution
// of the second coordinate given the first.

package conditional_distribution

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IsDisintegrationDef — `is_disintegration(W, U, V, T, π, K)`: π is a
// probability on the product σ-algebra of W × V, K a probability kernel
// from (W, U) to (V, T), and on every measurable rectangle b × a, π is
// the integral of K(·, a) over b against the first marginal of π. For
// random variables Z and Y the law of (Z, Y) is π, and K is a version of
// the conditional distribution of Y given Z.
var IsDisintegrationDef = isDisintegrationDefThm{family.Define(registry.DefEntry{
	Name:  "IsDisintegrationDef",
	Key:   "prop_2194aef1844409c7",
	Const: "is_disintegration",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"set(B) → " +
		"set(set(B)) → " +
		"(set(prod(A, B)) → extended_nonneg_real) → " +
		"(A → set(B) → extended_nonneg_real) → " +
		"bool",
	Equations: []string{
		"∀W:set(A). " +
			"∀U:set(set(A)). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀π:(set(prod(A, B)) → extended_nonneg_real). " +
			"∀K:(A → set(B) → extended_nonneg_real). " +
			"    is_disintegration(W, U, V, T, π, K) ⇔ " +
			"    probability_on(set_cross(W, V), product_sigma(W, U, V, T), π) ∧ " +
			"    probability_kernel_on(W, U, V, T, K) ∧ " +
			"    (∀b:set(A). ∀a:set(B). " +
			"        b ∈ U ∧ a ∈ T ⇒ " +
			"        π(set_cross(b, a)) = " +
			"        nonneg_integral(W, " +
			"            U, " +
			"            restricted_measure(pushforward_measure(set_cross(W, V), π, fst), b), " +
			"            λw:A. K(w, a)))",
	},
})}
