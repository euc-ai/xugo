// override.go — one map overriding another on a set. `override_on(K, f,
// g)` takes f's values on K and g's elsewhere: a configuration of a
// model with an intervened group, a mechanism family with some
// mechanisms replaced, and the restriction of a map to K with the
// other coordinates pinned to defaults are all this one operation.
// `normalize_on` is the case where g is constant. `agree_on(K, v)` is
// the set of maps that take v's values on K, so two maps override a
// third on K to the same map exactly when one agrees with the other on
// K.

package functions

import (
	"github.com/euc-ai/xugo/library/registry"
)

// OverrideOnDef — `override_on(K, f, g)` is f on K and g off K.
var OverrideOnDef = overrideOnDefThm{family.Define(registry.DefEntry{
	Name:  "OverrideOnDef",
	Key:   "prop_ab2c44f6f5f9141b",
	Const: "override_on",
	Type:  "set(A) → (A → B) → (A → B) → A → B",
	Equations: []string{
		"∀K:set(A). ∀f g:(A → B). override_on(K, f, g) = λx:A. COND(x ∈ K, f(x), g(x))",
	},
})}

// AgreeOnDef — `agree_on(K, v)` is the set of maps that agree with v
// at every point of K; off K they are free.
var AgreeOnDef = agreeOnDefThm{family.Define(registry.DefEntry{
	Name:           "AgreeOnDef",
	Key:            "prop_7a47e6189f13a126",
	Const:          "agree_on",
	Type:           "set(A) → (A → B) → set(A → B)",
	MembershipRead: true,
	Equations: []string{
		"∀K:set(A). ∀v:(A → B). agree_on(K, v) = {w:A → B | ∀x:A. x ∈ K ⇒ w(x) = v(x)}",
	},
})}
