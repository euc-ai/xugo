// definitions.go — the chapter's definitional layer: divisibility and
// coprimality over ℤ.
//
// Divisibility is stated as it is over ℕ — some multiple lands on the
// target — and over ℤ that is already the whole notion, with no sign
// condition anywhere: a divisor divides the negation of everything it
// divides. Coprimality is NOT "no common factor but a unit": it is
// Bézout's identity taken as the definition, which is the form every
// argument here actually uses, and the form that survives to ℤ from
// the ℕ-side theory without a gcd having to exist first.

package int_divides

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IntDividesDef — m divides n when some multiple of m is n.
var IntDividesDef = intDividesDefThm{family.Define(registry.DefEntry{
	Name:      "IntDividesDef",
	Key:       "prop_3dbc1618ce90f769",
	Const:     "int_divides",
	Type:      "int → int → bool",
	Equations: []string{"∀m n:int. int_divides(m, n) ⇔ ∃x:int. n = m * x"},
})}

// IntCoprimeDef — a pair is coprime when one is a combination of the
// two: Bézout as the definition. Written through fst and snd; a
// definition matching a pair pattern mints the identical constant.
var IntCoprimeDef = intCoprimeDefThm{family.Define(registry.DefEntry{
	Name:      "IntCoprimeDef",
	Key:       "prop_7cbb0e05f86eca16",
	Const:     "int_coprime",
	Type:      "prod(int, int) → bool",
	Equations: []string{"∀p:prod(int, int). int_coprime(p) ⇔ ∃x y:int. fst(p) * x + snd(p) * y = 1"},
})}
