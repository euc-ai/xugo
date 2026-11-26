// definitions.go — the chapter's definitional layer: the greatest
// common divisor and coprimality, defined in ℕ.
//
// Both constants go through the define door (family.Define): each
// equation is read in the chapter's own vocabulary, the kernel mints
// the constant, and the entry is the characterizing statement a proof
// cites to unfold it. Constant identity is process-global:
// `ctx.Const("nat_gcd", …)` in any package hands back the minted meta
// with the definition attached.

package nat_gcd

import (
	"github.com/euc-ai/xugo/library/registry"
)

// GcdDef — a common divisor that every common divisor divides. Two
// things about that specification are choices, and both are
// deliberate.
//
// The arguments are CURRIED. A gcd that takes a pair puts fst and snd
// into the statement of everything that unfolds it;
// nothing here needs a pair, so nothing here meets a projection.
//
// Maximality is stated by DIVISIBILITY, not by ≤. That is the stronger
// property, it is the one the chapter's theorems actually use — and it
// is TOTAL: at (0, 0) every natural is a common divisor, so an
// ≤-maximal one does not exist and the ε would have nothing to choose
// from, while a ∣-maximal one is 0.
var GcdDef = gcdDefThm{family.Define(registry.DefEntry{
	Name:  "GcdDef",
	Key:   "prop_beeaff4e23e2a41f",
	Const: "nat_gcd",
	Type:  "num → num → num",
	Equations: []string{
		"∀a b:num. nat_gcd(a, b) = εd:num. (d ∣ a ∧ d ∣ b) ∧ ∀e:num. (e ∣ a ∧ e ∣ b) ⇒ e ∣ d",
	},
})}

// CoprimeDef — the definition a reader expects, and NOT a Bézout
// combination equal to 1, which asks for coefficients in ℤ. nat_gcd.go's
// Coprime reads it in ℕ's own terms: 1 is the only common divisor.
var CoprimeDef = coprimeDefThm{family.Define(registry.DefEntry{
	Name:      "CoprimeDef",
	Key:       "prop_8f9f0bc40615301",
	Const:     "nat_coprime",
	Type:      "num → num → bool",
	Equations: []string{"∀a b:num. nat_coprime(a, b) ⇔ nat_gcd(a, b) = 1"},
	Deps:      []registry.EntryLike{GcdDef},
})}
