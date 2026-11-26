# real_zpow — ℝ's integer powers

`real_zpow(x, n)` is x to an integer exponent n, defined by cases over the
exponent's sign: at a nonnegative exponent it is `real_pow` at the natural
that exponent names, at a negative one the inverse of that. So the constant
carries no content of its own: every ℤ-indexed law is a ℕ-indexed law of
`real_pow` read through the sign split. The chapter stands on `real/real_pow`
for those laws and on ℤ for its exponents; `real_pow` itself needs no ℤ.

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `real_zpow(x, n)` | `COND(0 ≤ n, real_pow(x, num_of_int(n)), real_inv(real_pow(x, num_of_int(-n))))` |

Nothing in the definition asks the base to be nonzero, so every law that
needs that says so itself.

## The movements (real_zpow.go)

1. **The bridges and the evaluations.** `ZpowOfNum` is the reading's
   nonnegative half and the only place the definition is unfolded and its
   guard argued about — an exponent in the image of ℕ is never negative, so
   the other branch is discarded unexamined. `ZpowZero`, `ZpowOne` and
   `ZpowTwo` are that bridge composed with the natural-power evaluations,
   and have no argument of their own. `OneZpow` is the exception the bridge
   does not reach, because it pins the BASE and leaves the exponent an
   arbitrary integer; the sign split is not avoided there but made
   irrelevant, both branches of `&1` evaluating to `&1`.

   `ZpowNeg` is the reading's other half and the only law in the chapter
   whose exponent has a sign nobody knows. Negating an exponent exchanges
   the definition's two branches, and each branch absorbs the exchange
   through an involution of its own — inverting twice on the value side,
   negating twice on the exponent side — so the law says nothing about
   powers at all. The exponent `&0` is peeled off first, being the only
   integer nonnegative on both sides of the negation; that is also what
   leaves the sign analysis with two live cases instead of four, since two
   guards that can no longer agree make both like-signed combinations
   impossible. `ZpowClauses` then names the two bridges as a single
   conjunction, for the readers who want the pair under one name.
2. **The base's laws.** What follows the bridges is `real_pow`'s algebra
   restated at a ℤ exponent — `MulZpowDistrib`, `InvZpow`, `DivZpow`. None
   has an argument of its own, and their sign split is much cheaper than
   `ZpowNeg`'s for a structural reason: those laws vary the BASE and leave
   the exponent alone, so every `real_zpow` in such a statement guards on
   the one condition, and the analysis collapses to two branches that prove
   the same ℕ-indexed law twice — once plainly, once under an inverse.
   Neither branch consults the guard it was handed; choosing the natural was
   the guard's whole job. `DivZpow` carries no split at all, its quotient
   opening into the other two before any guard is reached.
3. **The zero base.** `ZeroZpow` belongs to neither group. Like `OneZpow`
   it pins the base; unlike it, `&0`'s two branches do not agree, and the
   statement asks a second question of the exponent besides — whether it
   vanishes. Two different questions about one exponent make the split the
   full 2×2, so four cases there is the honest shape rather than a failure
   to simplify: one is impossible, two compute, and the last says that a
   negative exponent cannot rescue a zero base, the inverse of zero being
   zero by convention.
4. **The exponent's law.** `ZpowAdd` and `ZpowSub` close the chapter, and
   they are the only members that relate two exponents to one another
   rather than pinning one or sharing one. That is exactly where the sign
   split stops paying: three exponents `m`, `n` and `m + n` carry three
   independent guards, and there is no arrangement of cases over them that
   is cheap. The way through is to stop asking about signs. Every integer
   is a difference of two naturals, and presented that way a ℤ-indexed
   power is a QUOTIENT of two ℕ-indexed ones — so adding exponents adds the
   numerators and the denominators separately, which is the ℕ-indexed law
   twice with the two denominators gathered under one inverse. The signs
   are absorbed once, into the presentation, rather than met four times
   over; the case analysis that does survive is not about sign at all but
   about ℕ's order, deciding which of the two naturals is larger and so
   which side of zero their difference falls on.

   What the negative exponents genuinely need is that a power meets its own
   inverse at `&1`, and that is a four-step computation rather than an
   induction: inversion passes through a power, two powers at one exponent
   are the power of the product, what is left under the exponent is the
   base against its own inverse, and every power of `&1` is `&1`. Note where
   the nonvanishing hypothesis is spent — on the BASE, before any power is
   formed, because the multiplicative-inverse laws are stated as
   disjunctions. So the chapter never needs to know that a power is
   nonzero, which is a fact it does not have. `ZpowSub` is then the
   addition law read at a negated exponent, and carries nothing of its own.

Public member map:

| member | statement |
|---|---|
| `RealZpowDef` | x zpow n = COND(0 ≤ n, x^num_of_int(n), (x^num_of_int(−n))⁻¹) — the definition |
| `ZpowOfNum` | x zpow &n = xⁿ — the bridge |
| `ZpowZero` | x zpow &0 = &1 |
| `ZpowOne` | x zpow &1 = x |
| `ZpowTwo` | x zpow &2 = x · x |
| `OneZpow` | &1 zpow n = &1 — the base pinned, the exponent free |
| `ZpowNeg` | x zpow (−n) = (x zpow n)⁻¹ |
| `ZpowClauses` | the two bridges as one conjunction — stated for readers, never cited |
| `MulZpowDistrib` | (x·y) zpow n = (x zpow n)·(y zpow n) |
| `InvZpow` | (x⁻¹) zpow n = (x zpow n)⁻¹ — stated power-first like its ℕ sibling |
| `DivZpow` | (x/y) zpow n = (x zpow n)/(y zpow n) |
| `ZeroZpow` | &0 zpow n = COND(n = &0, &1, &0) |
| `ZpowAdd` | x ≠ &0 ⇒ x zpow (m + n) = (x zpow m)·(x zpow n) |
| `ZpowSub` | x ≠ &0 ⇒ x zpow (m − n) = (x zpow m)/(x zpow n) |

Every statement is written zpow-first, as `real_pow` writes its own
subject first: the left-hand side is the ℤ-indexed power and the
right-hand side is what it turns out to be.

## Naming

The names follow `real_pow`'s rule for fixed slots: a special BASE puts
the noun first, a special EXPONENT puts `Zpow` first (`OneZpow` for
1 zpow n against `ZpowOne` for x zpow &1).
