// definitions.go — the chapter's definitional layer: what it means for
// a sequence of functions to converge uniformly on a set.
//
// A sequence of functions is curried, f : ℕ → ℝ → ℝ, its n-th member
// f(n) and that member's value at x written f(n)(x). It converges to g
// at each point of s when every point has its own index; it converges
// UNIFORMLY on s when one index serves every point at once. The
// definition is that ε-N sentence and nothing more: as the sequences
// chapter mints no `lim`, no limit function is minted here, and the
// relation names the limit it is about.

package real_uniform_convergence

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealConvergesUniformlyOnDef — `real_converges_uniformly_on(s, f, g)`:
// every positive distance is met, at every point of s at once, by all
// the members of f past some index.
var RealConvergesUniformlyOnDef = realConvergesUniformlyOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealConvergesUniformlyOnDef",
	Key:   "prop_d3f54b3f3bf1294d",
	Const: "real_converges_uniformly_on",
	Type:  "set(real) → (num → real → real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:(num → real → real). ∀g:(real → real). " +
			"    real_converges_uniformly_on(s, f, g) ⇔ " +
			"    ∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. ∀x:real. N ≤ n ∧ x ∈ s ⇒ |f(n)(x) - g(x)| < ε",
	},
})}
