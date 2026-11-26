// definitions.go — the chapter's definitional layer: the cosine, the
// sine and π.
//
// The cosine and the sine are sums of series, chosen through the
// relation `real_sums` because the series chapter mints no value for a
// sum: cos x is Σ (−1)ⁿ·x²ⁿ/(2n)! and sin x is Σ (−1)ⁿ·x²ⁿ⁺¹/(2n+1)!, the
// even and the odd terms of the exponential series with alternating
// signs. Both series converge for every x (CosSums, SinSums), so each
// constant IS its sum.
//
// π is a choice too, and a property of a choice `εx. P x` follows from
// `∃x. P x`: the constant is unfolded on its own goal before any
// resident fact mentions it, because a goal-side Unfold also rewrites
// every resident fact that does (the manual's `Unfold`, "The goal and
// every hypothesis"); the ε-δ definitions (the derivative, the limit)
// are opened by `Simp(Fwd(<Def>))`, which rewrites the goal alone.

package real_trigonometry

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealCosDef — `real_cos(x)`: the sum of the series Σ (−1)ⁿ·x²ⁿ/(2n)!.
var RealCosDef = realCosDefThm{family.Define(registry.DefEntry{
	Name:     "RealCosDef",
	Key:      "prop_7d2de8fa3276194b",
	Const:    "real_cos",
	Overload: "cos",
	Type:     "real → real",
	Equations: []string{
		"∀x:real. " +
			"    real_cos(x) = " +
			"    εs:real. real_sums(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n), s)",
	},
	// The mints of the series relation, the power, the quotient, the
	// factorial, ℕ's product, ℝ's product and negation, and the embedding.
})}

// RealSinDef — `real_sin(x)`: the sum of the series Σ (−1)ⁿ·x²ⁿ⁺¹/(2n+1)!.
var RealSinDef = realSinDefThm{family.Define(registry.DefEntry{
	Name:     "RealSinDef",
	Key:      "prop_ad07853a571b3b3e",
	Const:    "real_sin",
	Overload: "sin",
	Type:     "real → real",
	Equations: []string{
		"∀x:real. " +
			"    real_sin(x) = " +
			"    εs:real. " +
			"        real_sums(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1), s)",
	},
	// RealCosDef's mints and ℕ's sum.
})}

// PiDef — `pi`: twice the zero of the cosine between 0 and 2.
var PiDef = piDefThm{family.Define(registry.DefEntry{
	Name:      "PiDef",
	Key:       "prop_fc52f78f04da6d68",
	Const:     "pi",
	Type:      "real",
	Overload:  "π",
	Equations: []string{"pi = &2 * (εx:real. &0 ≤ x ∧ x ≤ &2 ∧ cos(x) = &0)"},
	// The cosine, and the mints of ℝ's product, order and embedding.
	Deps: []registry.EntryLike{RealCosDef},
})}
