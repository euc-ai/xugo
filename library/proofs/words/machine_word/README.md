# machine_word — machine words with the width as a number

The words domain's DEFINITIONAL SUBSTRATE: the minted constants
(below) and the value face's own theory — the val/word round trips,
congruences and quantifier transports, and the ring laws of width-n
arithmetic. The other faces are sibling families built on this one:
`words/word_bits` (reading positions and windows), `words/bitwise_algebra` (the
pointwise boolean algebra), `words/bit_arith` (the algebra against
arithmetic), `words/bit_set` (places as a set), `words/signed_word` (the
two's-complement reading).

A word of width `n` here is its unsigned VALUE — an ordinary `num` — and
the width an ordinary num variable: the val-face of the sibling chapters'
`word(N)`, with reduction mod `2^n` where the type-level encoding leans on
the type. That convention is the chapter's one idea: the width is a TERM,
so a statement may quantify over it (`∀n` replaces one theorem per width),
compute with it (`m + n` where the type level moves through `finite_sum`),
and state the laws with far fewer guards than the type carries implicitly.

## The definitional layer (definitions.go)

Every constant is defined through the define door (`family.Define`), one
entry per constant, by demand: only what a landed member states is
defined and declared. They fall into three groups, and the groups behave
differently enough that the difference organises the whole chapter.

**The arithmetic operations** are CONGRUENCE-PRESERVING in each argument —
an unreduced input is read through its residue — which is what lets their
laws land hypothesis-free:

    word_add          : num → num → num → num    word_add(n, x, y)          = nat_mod(x + y, 2^n)
    word_mul          : num → num → num → num    word_mul(n, x, y)          = nat_mod(x * y, 2^n)
    word_neg          : num → num → num          word_neg(n, x)             = nat_mod(2^n - nat_mod(x, 2^n), 2^n)
    word_sub          : num → num → num → num    word_sub(n, x, y)          = word_add(n, x, word_neg(n, y))
    word_unsigned_div : num → num → num → num    word_unsigned_div(n, x, y) = nat_div(nat_mod(x, 2^n), nat_mod(y, 2^n))
    word_unsigned_mod : num → num → num → num    word_unsigned_mod(n, x, y) = nat_mod(nat_mod(x, 2^n), nat_mod(y, 2^n))

**The bits face** reads its argument RAW, and is width-free: position `i`
of the value `x` is a fact about `x` alone, and a width enters a statement
about it only through a range guard. Its inverse builds a word from a SET
of positions, and does take the width, because building truncates — a set
may hold places the window does not reach, and the cut is the content:

    word_bit     : num → num → bool         word_bit(i, x) = nat_odd(nat_div(x, 2^i))
    word_of_bits : num → set(num) → num     word_of_bits(0, s) = 0
                                            word_of_bits(suc(n), s) =
                                              word_of_bits(n, s) + 2^n·bit_value(n ∈ s)

**The bitwise operations** are the window combinators and their four
instantiations. `word_bitwise_unary`/`word_bitwise_binary` lift a boolean operation pointwise
over the low `k` bits — place `i` contributes `2^i` exactly when the
operation holds at the operands' `i`-th bits — and each operator is one
instantiation:

    word_bitwise_unary  : num → (bool → bool) → num → num
    word_bitwise_binary : num → (bool → bool → bool) → num → num → num
    word_and, word_or, word_xor : num → num → num        word_not : num → num → num

`word_and`/`word_or`/`word_xor` are WIDTH-FREE — each windows at `x + y`, which holds
both operands whole, since a value sits under its own power and powers
grow with the exponent. `word_not` alone takes the width, because complementing
IS a fact about a window: the bits it sets are the ones `x` leaves clear
BELOW `n`, so naming a different `n` names a different word.

## The two ways a guard disappears

A member states the STRONG form — the fewest guards the mathematics
allows. Which guards a member may drop depends on which mechanism it
is standing on, and the chapter has two:

- **Congruence**, for the arithmetic operations: an unreduced input is
  read through its residue, so a range guard is never needed and the ring
  laws are hypothesis-free at every width.
- **The window**, for the binary bitwise operations: they window at `x + y`,
  which already covers every bit either operand has, so their laws hold at
  every pair with no width mentioned at all.

Everywhere else a surviving guard means a position is genuinely being
measured against the width — a round trip back to a REDUCED value, a
val-face reading, or a `word_not` whose window is the statement's subject.

## The files

- **values.go** — the value face: a word read as a number
  mod `2^n`. The val/word translation cluster and the ring laws
  (add · mul · neg · sub · udiv · umod, with their congruences).
- **definitions.go** — the constants above as definition entries,
  the arithmetic, the bits face, the window combinators (recursions on
  the window with the operation and the operands as parameters, whose
  entries state the clauses every window member cites) and the four
  bitwise operators (`word_and` · `word_or` · `word_xor` · `word_not`).
- **vocab.go** — the vocabulary (the `VocabSpec` rows), which is the
  substrate: each of the four bit-face families embeds it whole
  (`Embed(machine_word.Bundle)`). (`words/signed_word` declares
  its own instead, because it needs a superset: its two minted
  readings and the ℤ heads its statements land in, alongside the word
  constants.)

The other faces are their own families, each with its own README: the
bit face (a word read one bit at a time — projections, bit
extensionality, the window laws) in `words/word_bits`; the pointwise
boolean algebra in `words/bitwise_algebra`; the bitwise operators read as
ARITHMETIC in `words/bit_arith`; the position-set face, and with it the
only borrowing from finite-summation arithmetic, in `words/bit_set`;
and the two's-complement reading in `words/signed_word`.

The mathematics of the arithmetic laws here lives one level down, in
`nat_div_mod`'s raw-nat_mod algebra (mint-once); a member is that layer
read through the definitions at modulus `2^n`. That is the whole shape
of this chapter — no induction and no borrowing of its own; the window
inductions went with the faces that need them.
