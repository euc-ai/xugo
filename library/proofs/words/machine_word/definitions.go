// definitions.go — the chapter's definitional layer: the term-level
// machine word's constants, each through the define door.
//
// A machine word of width n here IS its unsigned value — an ordinary
// `num`, with the width an ordinary num variable — and each operation
// normalizes by reduction mod 2^n, the val-face reading of the
// type-level chapters' arithmetic. Each equation is read in the
// chapter's own vocabulary and the kernel mints the constant with its
// defining theorem; the entry is the characterizing statement a proof
// cites to unfold it, and `ctx.ConstDefNormalized` reads the same
// definition off the meta. The referenced arithmetic (`+ nat_mod nat_pow`)
// is the manager's own — a definition is written over the same
// constants every other ℕ proof reads — and every entry that reads
// another's constant declares it in Deps, the initialization-order
// edge Go honours.
//
// The vocabulary grows one member at a time, never in advance: only
// what a landed member states is minted and declared.

package machine_word

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The value of a bit
// ---------------------------------------------------------------------------

// BitValueDef — a set bit counts one, a clear bit none. A bit is a
// `bool` in this domain, not a one-element word, and `bit_value` is
// what lets one enter arithmetic: every bit's contribution to a number
// is its value times the place. It comes first because the window
// combinators below are built over it.
var BitValueDef = bitValueDefThm{family.Define(registry.DefEntry{
	Name:      "BitValueDef",
	Key:       "prop_892923edaed20432",
	Const:     "bit_value",
	Type:      "bool → num",
	Equations: []string{"∀b:bool. bit_value(b) = COND(b, 1, 0)"},
})}

// ---------------------------------------------------------------------------
// The arithmetic, and the bits face
// ---------------------------------------------------------------------------
//
// Each arithmetic operation is CONGRUENCE-PRESERVING in each argument —
// an unreduced input is read through its residue, so the ring laws hold
// for ALL inputs and land hypothesis-free (the strong forms). That is
// a deliberate strengthening of the type-level operations, which never
// see an unreduced value; the val-face twins recover the type-level
// shapes under their range guards.
//
// The claim is about these operations and not about the chapter: word_bit
// reads its argument RAW (it is a digit of the value, not of a
// residue), and the bitwise operations further down drop their guards
// for a different reason again — they window at x + y, which already
// holds both operands whole. word_not keeps a width because
// complementing IS a window fact. The chapter narrative's "two ways a
// guard disappears" is where those are told apart.
//
// (+ and * respect congruence already, so word_add/word_mul need no
// inner reduction; monus and nat_div do not, so word_neg,
// word_unsigned_div and word_unsigned_mod reduce their operands first.
// word_sub is subtraction AS addition of the negation — the mod-2^n
// ring's own reading, and the compositional unfold every sub law
// wants.)

// WordAddDef — addition mod 2^n.
var WordAddDef = wordAddDefThm{family.Define(registry.DefEntry{
	Name:      "WordAddDef",
	Key:       "prop_8930fd07aaef44bd",
	Const:     "word_add",
	Type:      "num → num → num → num",
	Equations: []string{"∀n x y:num. word_add(n, x, y) = rem(x + y, nat_pow(2, n))"},
})}

// WordMulDef — multiplication mod 2^n.
var WordMulDef = wordMulDefThm{family.Define(registry.DefEntry{
	Name:      "WordMulDef",
	Key:       "prop_c0ca50a0373549e0",
	Const:     "word_mul",
	Type:      "num → num → num → num",
	Equations: []string{"∀n x y:num. word_mul(n, x, y) = rem(x * y, nat_pow(2, n))"},
})}

// WordNegDef — negation mod 2^n: the range less the reduced value,
// reduced again so that 0 stays 0.
var WordNegDef = wordNegDefThm{family.Define(registry.DefEntry{
	Name:  "WordNegDef",
	Key:   "prop_56ee4fd4cfb8b9fc",
	Const: "word_neg",
	Type:  "num → num → num",
	Equations: []string{
		"∀n x:num. word_neg(n, x) = rem(nat_pow(2, n) - rem(x, nat_pow(2, n)), nat_pow(2, n))",
	},
})}

// WordSubDef — subtraction as addition of the negation.
var WordSubDef = wordSubDefThm{family.Define(registry.DefEntry{
	Name:      "WordSubDef",
	Key:       "prop_d29189b0773c3943",
	Const:     "word_sub",
	Type:      "num → num → num → num",
	Equations: []string{"∀n x y:num. word_sub(n, x, y) = word_add(n, x, word_neg(n, y))"},
	Deps:      []registry.EntryLike{WordAddDef, WordNegDef},
})}

// WordUnsignedDivDef — the quotient of the reduced operands.
var WordUnsignedDivDef = wordUnsignedDivDefThm{family.Define(registry.DefEntry{
	Name:  "WordUnsignedDivDef",
	Key:   "prop_1e23e5e09229c904",
	Const: "word_unsigned_div",
	Type:  "num → num → num → num",
	Equations: []string{
		"∀n x y:num. word_unsigned_div(n, x, y) = div(rem(x, nat_pow(2, n)), rem(y, nat_pow(2, n)))",
	},
})}

// WordUnsignedModDef — the remainder of the reduced operands.
var WordUnsignedModDef = wordUnsignedModDefThm{family.Define(registry.DefEntry{
	Name:  "WordUnsignedModDef",
	Key:   "prop_8ee6e4856ce9bc0e",
	Const: "word_unsigned_mod",
	Type:  "num → num → num → num",
	Equations: []string{
		"∀n x y:num. word_unsigned_mod(n, x, y) = rem(rem(x, nat_pow(2, n)), rem(y, nat_pow(2, n)))",
	},
})}

// WordBitDef — the bits face, WIDTH-FREE: position i of the value x is
// a fact about x alone, the parity of x shifted down i places; the
// width enters a statement only through range guards.
var WordBitDef = wordBitDefThm{family.Define(registry.DefEntry{
	Name:      "WordBitDef",
	Key:       "prop_eafc86ea716ee597",
	Const:     "word_bit",
	Type:      "num → num → bool",
	Equations: []string{"∀i x:num. word_bit(i, x) ⇔ nat_odd(div(x, nat_pow(2, i)))"},
})}

// ---------------------------------------------------------------------------
// The window combinators
// ---------------------------------------------------------------------------
//
// The window combinators lift a boolean operation pointwise over the
// low-k bits — place i contributes weight 2^i exactly when the
// operation holds at the operands' i-th bits. Each is a recursive
// definition on the window with the operation and the operands as
// curried parameters; the door discharges the existence through ℕ's
// recursion principle, and the entry states the two clauses at the
// constant — what every window member cites.

// WordBitwiseUnaryDef — one operand's bit under the operation, place
// by place.
var WordBitwiseUnaryDef = wordBitwiseUnaryDefThm{family.Define(registry.DefEntry{
	Name:  "WordBitwiseUnaryDef",
	Key:   "prop_c185e7b82e093697",
	Const: "word_bitwise_unary",
	Type:  "num → (bool → bool) → num → num",
	Equations: []string{
		"∀op:(bool → bool). ∀x:num. word_bitwise_unary(0, op, x) = 0",
		"∀k:num. ∀op:(bool → bool). ∀x:num. " +
			"    word_bitwise_unary(suc(k), op, x) = " +
			"    word_bitwise_unary(k, op, x) + nat_pow(2, k) * bit_value(op(word_bit(k, x)))",
	},
	Deps: []registry.EntryLike{BitValueDef, WordBitDef},
})}

// WordBitwiseBinaryDef — two operands' bits under the operation, place
// by place.
var WordBitwiseBinaryDef = wordBitwiseBinaryDefThm{family.Define(registry.DefEntry{
	Name:  "WordBitwiseBinaryDef",
	Key:   "prop_9ea01e00e4912253",
	Const: "word_bitwise_binary",
	Type:  "num → (bool → bool → bool) → num → num → num",
	Equations: []string{
		"∀op:(bool → bool → bool). ∀x y:num. word_bitwise_binary(0, op, x, y) = 0",
		"∀k:num. ∀op:(bool → bool → bool). ∀x y:num. " +
			"    word_bitwise_binary(suc(k), op, x, y) = " +
			"    word_bitwise_binary(k, op, x, y) + " +
			"    nat_pow(2, k) * bit_value(op(word_bit(k, x), word_bit(k, y)))",
	},
	Deps: []registry.EntryLike{BitValueDef, WordBitDef},
})}

// WordOfBitsDef — the position-set face's builder: the number whose
// bits below n are exactly the positions a set holds. The same window
// as the combinators with the predicate coming from a SET rather than
// from another word's bits — place k contributes 2^k exactly when k
// belongs. The width is real and not droppable: the set may hold
// positions at or above n, and the window is precisely what cuts them
// off. (`bits_of_word` needs no counterpart, being the plain
// set-builder `{i | word_bit(i, x)}` over the bits face.)
//
// Membership is spelled `k ∈ s` and not the raw application `s(k)`:
// Normalize does not unfold set_member, so the two are different terms
// with distinct keys, and every twin on this face reaches its set
// through ∈. The definitional layer speaks the same language, which is
// what keeps the clauses usable against a twin without an unfold
// standing in between.
var WordOfBitsDef = wordOfBitsDefThm{family.Define(registry.DefEntry{
	Name:  "WordOfBitsDef",
	Key:   "prop_e50fc491d873d02e",
	Const: "word_of_bits",
	Type:  "num → set(num) → num",
	Equations: []string{
		"∀s:set(num). word_of_bits(0, s) = 0",
		"∀k:num. ∀s:set(num). " +
			"    word_of_bits(suc(k), s) = word_of_bits(k, s) + nat_pow(2, k) * bit_value(k ∈ s)",
	},
	Deps: []registry.EntryLike{BitValueDef},
})}

// ---------------------------------------------------------------------------
// The bitwise operators, as instances of the combinators
// ---------------------------------------------------------------------------
//
// Every operator is one instantiation of a combinator. word_and/word_or/word_xor
// are WIDTH-FREE — a set bit of either operand sits below it (n < 2^n),
// so the window x + y covers every bit either operand has; the window
// never leaks into their laws. word_not alone takes the width:
// complement is a fact about a WINDOW — the bits it sets are exactly
// the clear bits below n — and that window parameter is the
// combinator's own.

// WordAndDef — conjunction of bits, width-free.
var WordAndDef = wordAndDefThm{family.Define(registry.DefEntry{
	Name:  "WordAndDef",
	Key:   "prop_aabe5e6a86feb1aa",
	Const: "word_and",
	Type:  "num → num → num",
	Equations: []string{
		"∀x y:num. word_and(x, y) = word_bitwise_binary(x + y, (λa:bool.λb:bool. a ∧ b), x, y)",
	},
	Deps: []registry.EntryLike{WordBitwiseBinaryDef},
})}

// WordOrDef — disjunction of bits, width-free.
var WordOrDef = wordOrDefThm{family.Define(registry.DefEntry{
	Name:  "WordOrDef",
	Key:   "prop_d3e4091572f005ce",
	Const: "word_or",
	Type:  "num → num → num",
	Equations: []string{
		"∀x y:num. word_or(x, y) = word_bitwise_binary(x + y, (λa:bool.λb:bool. a ∨ b), x, y)",
	},
	Deps: []registry.EntryLike{WordBitwiseBinaryDef},
})}

// WordXorDef — difference of bits, width-free. (The operation is
// spelled (a ∨ b) ∧ ¬(a ∧ b): the ⇔-negation spelling prints as the ⊕
// the parser does not read back.)
var WordXorDef = wordXorDefThm{family.Define(registry.DefEntry{
	Name:  "WordXorDef",
	Key:   "prop_dfb8df36a41ebbdc",
	Const: "word_xor",
	Type:  "num → num → num",
	Equations: []string{
		"∀x y:num. " +
			"    word_xor(x, y) = word_bitwise_binary(x + y, (λa:bool.λb:bool. (a ∨ b) ∧ ¬(a ∧ b)), x, y)",
	},
	Deps: []registry.EntryLike{WordBitwiseBinaryDef},
})}

// WordNotDef — complement WITHIN the width.
var WordNotDef = wordNotDefThm{family.Define(registry.DefEntry{
	Name:      "WordNotDef",
	Key:       "prop_d411901c43657911",
	Const:     "word_not",
	Type:      "num → num → num",
	Equations: []string{"∀n x:num. word_not(n, x) = word_bitwise_unary(n, (λa:bool. ¬a), x)"},
	Deps:      []registry.EntryLike{WordBitwiseUnaryDef},
})}
