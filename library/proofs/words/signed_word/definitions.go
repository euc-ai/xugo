// definitions.go — the chapter's definitional layer: the term-level
// signed reading's two constants, each through the define door.
//
// A word of width n is its unsigned value — an ordinary `num` — and
// the signed reading is the two's-complement one: a value in the low
// half of the range is itself, a value in the high half is itself less
// the whole range. Each equation is read in the chapter's own
// vocabulary and the kernel mints the constant with its defining
// theorem; proof bodies open the definitions with `Unfold(name)` (or
// take `ctx.ConstDefNormalized`'s theorem as a premise where the close
// consumes it whole — the same certificate through two doors).
//
// `int_of_word` is CONGRUENCE-PRESERVING — an unreduced input is read
// through its residue, the same deliberate strengthening the carrier
// chapter's arithmetic operations carry: the reading's range bound and
// congruences then hold for ALL inputs and land free of range guards
// (a width guard may still carry content — the sign law keeps one),
// and the val-face twins recover the type-level shapes under their range
// guards. `word_of_int` needs no outer reduction: `int_rem` is
// Euclidean, so the remainder it takes is already the reduced value.

package signed_word

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IntOfWordDef — the two's-complement reading of a word of width n.
var IntOfWordDef = intOfWordDefThm{family.Define(registry.DefEntry{
	Name:  "IntOfWordDef",
	Key:   "prop_99fc288467c28248",
	Const: "int_of_word",
	Type:  "num → num → int",
	Equations: []string{
		"∀n x:num. " +
			"    int_of_word(n, x) = " +
			"    COND(rem(x, nat_pow(2, n)) < nat_pow(2, n - 1), " +
			"        int_of_num(rem(x, nat_pow(2, n))), " +
			"        rem(x, nat_pow(2, n)) - int_pow(2, n))",
	},
})}

// WordOfIntDef — the word of width n an integer reads as: its
// Euclidean remainder modulo the range.
var WordOfIntDef = wordOfIntDefThm{family.Define(registry.DefEntry{
	Name:      "WordOfIntDef",
	Key:       "prop_2d82ab03efe049de",
	Const:     "word_of_int",
	Type:      "num → int → num",
	Equations: []string{"∀n:num. ∀x:int. word_of_int(n, x) = num_of_int(rem(x, int_pow(2, n)))"},
})}
