// definitions.go — the chapter's definitional layer: the two binary
// extrema, the two set extrema, and the two predicates that say a set
// HAS one.
//
// The binary pair is a case split on the order and carries no content
// beyond it. The set pair is a CHOICE: `real_sup(s)` is some number that
// bounds s above and is below every other such bound — which says
// nothing at all when s has no least upper bound, and everything when
// it does. That is why the chapter's theorems about `real_sup` are all
// stated under a hypothesis, and why `real_has_sup` exists: it is the
// bound-for-bound characterization that a completeness argument can
// establish without first knowing the supremum.

package real_sup_inf

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealMaxDef — the larger of two.
var RealMaxDef = realMaxDefThm{family.Define(registry.DefEntry{
	Name:      "RealMaxDef",
	Key:       "prop_269f306c6b2ced91",
	Const:     "real_max",
	Type:      "real → real → real",
	Overload:  "max",
	Equations: []string{"∀x y:real. real_max(x, y) = COND(x ≤ y, y, x)"},
})}

// RealMinDef — the smaller of two.
var RealMinDef = realMinDefThm{family.Define(registry.DefEntry{
	Name:      "RealMinDef",
	Key:       "prop_e5225ad8c72b336d",
	Const:     "real_min",
	Type:      "real → real → real",
	Overload:  "min",
	Equations: []string{"∀x y:real. real_min(x, y) = COND(x ≤ y, x, y)"},
})}

// RealSupDef — the least upper bound, chosen: some bound of s below every
// bound of s.
var RealSupDef = realSupDefThm{family.Define(registry.DefEntry{
	Name:     "RealSupDef",
	Key:      "prop_8f43fc41d2739ca8",
	Const:    "real_sup",
	Type:     "set(real) → real",
	Overload: "sup",
	Equations: []string{
		"∀s:set(real). " +
			"    real_sup(s) = εa:real. (∀x:real. x ∈ s ⇒ x ≤ a) ∧ ∀b:real. (∀x:real. x ∈ s ⇒ x ≤ b) ⇒ a ≤ b",
	},
})}

// RealInfDef — the greatest lower bound, chosen the same way.
var RealInfDef = realInfDefThm{family.Define(registry.DefEntry{
	Name:     "RealInfDef",
	Key:      "prop_610366290aabf33d",
	Const:    "real_inf",
	Type:     "set(real) → real",
	Overload: "inf",
	Equations: []string{
		"∀s:set(real). " +
			"    real_inf(s) = εa:real. (∀x:real. x ∈ s ⇒ a ≤ x) ∧ ∀b:real. (∀x:real. x ∈ s ⇒ b ≤ x) ⇒ b ≤ a",
	},
})}

// RealHasSupDef — b IS the supremum of s: the numbers above everything in
// s are exactly the numbers above b. Says the same thing as "least
// upper bound" without naming one.
var RealHasSupDef = realHasSupDefThm{family.Define(registry.DefEntry{
	Name:  "RealHasSupDef",
	Key:   "prop_53a2cf0a9c58edd",
	Const: "real_has_sup",
	Type:  "set(real) → real → bool",
	Equations: []string{
		"∀s:set(real). ∀b:real. real_has_sup(s, b) ⇔ ∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇔ b ≤ c",
	},
})}

// RealHasInfDef — and b IS the infimum, the same characterization below.
var RealHasInfDef = realHasInfDefThm{family.Define(registry.DefEntry{
	Name:  "RealHasInfDef",
	Key:   "prop_9b481d902f201a50",
	Const: "real_has_inf",
	Type:  "set(real) → real → bool",
	Equations: []string{
		"∀s:set(real). ∀b:real. real_has_inf(s, b) ⇔ ∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇔ c ≤ b",
	},
})}
