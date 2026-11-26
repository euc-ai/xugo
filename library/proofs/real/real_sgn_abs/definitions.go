// definitions.go — the chapter's definitional layer: magnitude, sign,
// and the distance between two reals, the magnitude of their
// difference.
//
// Both are defined by cases on the order, which is what makes the
// chapter's proofs case analyses: the magnitude is the number itself
// when it is not negative and its negation otherwise, and the sign is
// one of three constants chosen the same way. Neither definition is
// stated with a hypothesis, so every law about them holds everywhere
// and the case split is the argument.

package real_sgn_abs

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealAbsDef — the magnitude: the number, or its negation.
var RealAbsDef = realAbsDefThm{family.Define(registry.DefEntry{
	Name:      "RealAbsDef",
	Key:       "prop_437ec88444bba036",
	Const:     "real_abs",
	Type:      "real → real",
	Notation:  "|x|",
	Overload:  "abs",
	Equations: []string{"∀x:real. real_abs(x) = COND(&0 ≤ x, x, -x)"},
})}

// RealSgnDef — the sign: one, minus one, or zero.
var RealSgnDef = realSgnDefThm{family.Define(registry.DefEntry{
	Name:      "RealSgnDef",
	Key:       "prop_1ff909d2b92221d0",
	Const:     "real_sgn",
	Type:      "real → real",
	Overload:  "sgn",
	Equations: []string{"∀x:real. real_sgn(x) = COND(&0 < x, &1, COND(x < &0, -&1, &0))"},
})}

// RealDistDef — the distance between two reals: the magnitude of their
// difference, written `dist(x, y)`, the word the natural numbers' and
// ℝⁿ's distances share.
var RealDistDef = realDistDefThm{family.Define(registry.DefEntry{
	Name:      "RealDistDef",
	Key:       "prop_11ec0378c66e9f27",
	Const:     "real_dist",
	Type:      "real → real → real",
	Overload:  "dist",
	Equations: []string{"∀x y:real. real_dist(x, y) = |x - y|"},
	Deps:      []registry.EntryLike{RealAbsDef},
})}
