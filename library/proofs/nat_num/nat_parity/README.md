# nat_parity — even and odd

Parity is the only nontrivial thing a natural number can be modulo
something, and this chapter is what ℕ's arithmetic looks like when you
forget everything else about a number and keep just that.

`nat_even` and `nat_odd` are two primitive recursions over `num`, each flipping
at every successor and disagreeing at zero. That single fact — they flip
together and start apart — is what makes them complementary, and once
complementarity is available the rest of the chapter is a homomorphism:
the map `n ↦ nat_even(n)` from ℕ onto the two-element algebra carries `+` to
`⇔` and `*` to `∨`, and the chapter's laws are exactly the statements
that it does.

## The movement

**The definitions**. `nat_even` and `nat_odd` are defined by the same
primitive recursion every ℕ operation is defined by, read at result
type `bool` rather than `num`. That is the only unusual thing about
them, and it costs nothing: the principle is polymorphic in the result
type.

**Complementarity**. `nat_odd n ⇔ ¬nat_even n` is the chapter's hinge, and its
converse reading `nat_even n ⇔ ¬nat_odd n`, "at most one" and "at least one" all
follow from it propositionally. Stating four separate members is not a
mathematical necessity — but they are
the four ways a reader wants to use the fact, so all four are members.

**The homomorphism**. `nat_even(m + n) ⇔ (nat_even m ⇔ nat_even n)`,
`nat_even(m · n) ⇔ nat_even m ∨ nat_even n`, and the exponent law
`nat_even(mⁿ) ⇔ nat_even m ∧ n ≠ 0`, whose side condition is the whole content:
`m⁰ = 1` is odd no matter what `m` is. Each is one induction on the
operand its defining recursion moves, and each leans on the one above
it, so the file reads downward.

**The shapes**. Parity is a predicate, and these turn it
back into arithmetic: `nat_even n ⇔ ∃m. n = 2m` and `nat_odd n ⇔ ∃m. n =
suc(2m)`. One lemma supplies the forward reading of both — every number
is `2m` or `suc(2m)`, according to its parity — and complementarity is
what reaches its second branch for the nat_odd one. The two converses are
separate members (`nat_even(2m)` and `nat_odd(suc(2m))`), because they say
nothing about `n` and everything about the shapes. Under a bound the shapes
split the numbers up to `2k`: each is `2i` with `i ≤ k` or `2i + 1` with
`i < k`. That member closes its bounds by arithmetic, whose parity layer
reads `EvenIffModTwoZero` (below), so it is registered after that member.

**The residue**. `nat_even n ⇔ nat_mod(n, 2) = 0`, its odd twin, and two facts
about what division leaves behind: reducing modulo an even number does
not disturb parity at all, and reducing modulo `2ᵏ` preserves oddness
exactly when `k ≠ 0` — the same degenerate exponent the `nat_pow` law has to
exclude, since `nat_mod(n, 1)` is `0` for every `n`.

## The members

The members, in construction order, plus one that is deliberately not
exported. Statements are written here in the README's notation; the
checked texts live beside their proofs.

| member | statement |
|---|---|
| `NatEven` | `nat_even(0) ∧ (∀n. nat_even(suc n) ⇔ ¬nat_even n)` |
| `NatOdd` | `¬nat_odd(0) ∧ (∀n. nat_odd(suc n) ⇔ ¬nat_odd n)` |
| `OddIffNotEven` | `∀n. nat_odd n ⇔ ¬nat_even n` |
| `EvenIffNotOdd` | `∀n. nat_even n ⇔ ¬nat_odd n` |
| `NotEvenAndOdd` | `∀n. ¬(nat_even n ∧ nat_odd n)` |
| `EvenOrOdd` | `∀n. nat_even n ∨ nat_odd n` |
| `EvenAdd` | `∀m n. nat_even(m + n) ⇔ (nat_even m ⇔ nat_even n)` |
| `EvenMul` | `∀m n. nat_even(m · n) ⇔ nat_even m ∨ nat_even n` |
| `EvenPow` | `∀m n. nat_even(mⁿ) ⇔ nat_even m ∧ n ≠ 0` |
| `EvenDouble` | `∀n. nat_even(2n)` |
| `OddSucDouble` | `∀n. nat_odd(suc(2n))` |
| `EvenIffDouble` | `∀n. nat_even n ⇔ ∃m. n = 2m` |
| `OddIffSucDouble` | `∀n. nat_odd n ⇔ ∃m. n = suc(2m)` |
| `EvenIffModTwoZero` | `∀n. nat_even n ⇔ nat_mod(n, 2) = 0` |
| `OddIffModTwoOne` | `∀n. nat_odd n ⇔ nat_mod(n, 2) = 1` |
| `DoubleOrSucDoubleBelow` | `∀k j. j ≤ 2k ⇒ (∃i. i ≤ k ∧ j = 2i) ∨ (∃i. i < k ∧ j = 2i + 1)` |
| `OddModEven` | `∀m n. nat_even n ⇒ (nat_odd(nat_mod(m, n)) ⇔ nat_odd m)` |
| `OddModPowTwo` | `∀n k. nat_odd(nat_mod(n, 2ᵏ)) ⇔ nat_odd n ∧ k ≠ 0` |
| `SquareModFour` | `∀a. (nat_even a ⇒ nat_mod(a · a, 4) = 0) ∧ (nat_odd a ⇒ nat_mod(a · a, 4) = 1)` |
| `OddSquareModEight` | `∀m. nat_odd m ⇒ ∃a. m · m = 8a + 1` |
| `UpperHalfCountEven` | `∀h. nat_even(h − nat_div(h, 2)) ⇔ nat_mod(2h + 1, 8) = 1 ∨ nat_mod(2h + 1, 8) = 7` |
| `OddSquareEighthEven` | `∀n. nat_odd n ⇒ (nat_even(nat_div(n · n − 1, 8)) ⇔ nat_mod(n, 8) = 1 ∨ nat_mod(n, 8) = 7)` |
| `TwoNotDividesOdd` | `∀n. nat_odd n ⇒ ¬(2 ∣ n)` |

One further theorem is proved and deliberately not exported:
`doubleOrSucDouble`, which supplies the forward
reading of both shape characterisations. Its only consumers are the two
members above it, so it stays chapter implementation rather than public
surface.

## What is not here

The chapter is one-sided on `+`, `*` and `nat_pow`: each law is stated
for `nat_even`, and its `nat_odd` mirror is that law read through
`OddIffNotEven`, which no member states. Subtraction is absent on both
sides, so it is not a mirror artifact but simply a law the chapter does
not have.

## Related chapters

The parity part of `int_num/int_div_rem` is the ℤ analogue and is deliberately
NOT this chapter transported: over ℤ there is no `nat_even` predicate, and
the corresponding statements classify `int_rem(n, &2)` into `&0` or `&1`
using discreteness. The two chapters share a subject and no vocabulary
— though since this chapter's doubling laws forced `2 = suc(1)` into
`nat_arith`, they now share one cited fact.
