// definitions.go — the chapter's definitional layer: continuity of a
// real function at a point, on a set, and uniformly on a set; and a
// real function increasing or decreasing on a set, weakly or strictly.

package real_continuous

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealContinuousAtDef — `real_continuous_at(f, c)`: every positive
// distance around f(c) is met by the values of f on some ball around
// c. The point c is not excluded, as it is from a limit: the value at c
// is what the nearby values are compared with.
var RealContinuousAtDef = realContinuousAtDefThm{family.Define(registry.DefEntry{
	Name:  "RealContinuousAtDef",
	Key:   "prop_ff765ff1d0ca306d",
	Const: "real_continuous_at",
	Type:  "(real → real) → real → bool",
	Equations: []string{
		"∀f:(real → real). ∀c:real. " +
			"    real_continuous_at(f, c) ⇔ " +
			"    ∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀x:real. |x - c| < δ ⇒ |f(x) - f(c)| < ε",
	},
	// The mints of `<`, real_abs, `-` and the embedding `&`.
})}

// RealContinuousOnDef — `real_continuous_on(s, f)`: at every point c of
// s, every positive distance around f(c) is met by the values of f on
// the points of s within some ball around c. Only points of s are
// compared, so what f does off s does not matter: the relative
// continuity an interval's endpoint needs.
var RealContinuousOnDef = realContinuousOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealContinuousOnDef",
	Key:   "prop_c692ea37ff008539",
	Const: "real_continuous_on",
	Type:  "set(real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:(real → real). " +
			"    real_continuous_on(s, f) ⇔ " +
			"    ∀c:real. " +
			"        c ∈ s ⇒ " +
			"        ∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀x:real. x ∈ s ∧ |x - c| < δ ⇒ |f(x) - f(c)| < ε",
	},
	// The mints of membership, `<`, real_abs, `-` and `&`.
})}

// RealUniformlyContinuousOnDef — `real_uniformly_continuous_on(s, f)`:
// every positive distance ε is met by one radius δ serving every pair
// of points of s at once — any two points of s within δ of each other
// have values within ε of each other. Continuity on s lets the radius
// depend on the centre as well; here it depends on ε alone.
var RealUniformlyContinuousOnDef = realUniformlyContinuousOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealUniformlyContinuousOnDef",
	Key:   "prop_fc60b58c620e0c17",
	Const: "real_uniformly_continuous_on",
	Type:  "set(real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:(real → real). " +
			"    real_uniformly_continuous_on(s, f) ⇔ " +
			"    ∀ε:real. " +
			"        &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀x y:real. x ∈ s ∧ y ∈ s ∧ |x - y| < δ ⇒ |f(x) - f(y)| < ε",
	},
})}

// RealIncreasingOnDef — `real_increasing_on(s, f)`: f never goes down
// between two points of s, the larger point having the value at least as
// large. Increasing is meant weakly here, as "non-decreasing" says it;
// the strict order is `real_strictly_increasing_on`.
var RealIncreasingOnDef = realIncreasingOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealIncreasingOnDef",
	Key:   "prop_2735e9cf7ff7abd",
	Const: "real_increasing_on",
	Type:  "set(real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:(real → real). " +
			"    real_increasing_on(s, f) ⇔ ∀x y:real. x ∈ s ∧ y ∈ s ∧ x ≤ y ⇒ f(x) ≤ f(y)",
	},
	// The mints of membership and `≤`.
})}

// RealStrictlyIncreasingOnDef — `real_strictly_increasing_on(s, f)`: of
// two points of s, the larger has the strictly larger value.
var RealStrictlyIncreasingOnDef = realStrictlyIncreasingOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealStrictlyIncreasingOnDef",
	Key:   "prop_dd84c55684a2d934",
	Const: "real_strictly_increasing_on",
	Type:  "set(real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:(real → real). " +
			"    real_strictly_increasing_on(s, f) ⇔ ∀x y:real. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f(x) < f(y)",
	},
	// The mints of membership and `<`.
})}

// RealDecreasingOnDef — `real_decreasing_on(s, f)`: f never goes up
// between two points of s, the larger point having the value at most as
// large. Decreasing is meant weakly, as "non-increasing" says it.
var RealDecreasingOnDef = realDecreasingOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealDecreasingOnDef",
	Key:   "prop_9a47d79970c2d46b",
	Const: "real_decreasing_on",
	Type:  "set(real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:(real → real). " +
			"    real_decreasing_on(s, f) ⇔ ∀x y:real. x ∈ s ∧ y ∈ s ∧ x ≤ y ⇒ f(y) ≤ f(x)",
	},
	// The mints of membership and `≤`.
})}

// RealStrictlyDecreasingOnDef — `real_strictly_decreasing_on(s, f)`: of
// two points of s, the larger has the strictly smaller value.
var RealStrictlyDecreasingOnDef = realStrictlyDecreasingOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealStrictlyDecreasingOnDef",
	Key:   "prop_7d2f192c0337536e",
	Const: "real_strictly_decreasing_on",
	Type:  "set(real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:(real → real). " +
			"    real_strictly_decreasing_on(s, f) ⇔ ∀x y:real. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f(y) < f(x)",
	},
	// The mints of membership and `<`.
})}
