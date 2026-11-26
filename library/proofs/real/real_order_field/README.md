# real_order_field — where ℝ's order meets its inverse

`real_order_ring` develops everything `≤` and `<` say about themselves
and about `+`, `−` and `·`. `real_field` develops the multiplicative
inverse and division with the order set aside. Neither cites the other,
and neither can state the facts this chapter is about — because those
facts are exactly the ones whose statements name **both** an order
relation and `real_inv` or `real_div`.

That question — *does the statement name `real_inv` or `real_div`?* — is
the single criterion that assigns a statement to a chapter across all four of
ℝ's theory packages. It separates `real_ring` from `real_field`, and it
separates the two order chapters the same way, which is why they are
`real_order_ring` and `real_order_field` rather than one `real_order`
plus a pile of special cases.

## The chapter's arc

**The sign of an inverse.** An inverse cannot change sign, and the whole
proof is one cancellation: to see `&0 < inv x`, multiply both sides by
the positive `x` and observe that the claim becomes `&0 < &1`. That
single member carries the tier; the non-strict version follows by
splitting `≤` into `<` or `=` and noting that `real_inv` sends `&0` to
`&0` **and sends nothing else there**, so a vanishing side stays a
vanishing side in both directions.

**The sign of a quotient.** A quotient is a product with an inverse in
it, so positivity of `x / y` is positivity of `x` times positivity of
`inv y` — the one place in the chapter where `real_div` is unfolded
rather than read off a `real_field` law.

**Clearing a positive denominator.** The chapter's largest movement: six
laws that move a division across a relation and turn it into a
multiplication. They are the multiplicative analogue of
`real_order_ring`'s `LessEqSubAddLeft` family, which does the same for
subtraction and addition, and they are named the same way — for the side
the resulting PRODUCT lands on.

Three of the six are one move: ground the right-cancellation law for the
member's relation at the quotient, then clear the denominator with
`field.DivRightMulOn` read at `real_field.Field`. The relation picks the law —
`real_order_ring.LessEqMulRightEq` for `≤`, `real_ring.MulRightCancel`
for `=` — so the `≤` strand and the `=` strand are independent of each
other, and what the positivity hypothesis is spent on differs between
them. Each member's own comment says which.

The other three read off those: one `=` law from the other, and the two
strict laws from the `≤` pair — crossed, which is the chapter's one
trap, because `<` is a negated `≤` and the negations reverse the
comparison. Each member states its own version of that.

**Antitonicity and density.** Inversion reverses the order on the
positives, strictly and again with both comparisons weakened — the weak
reading follows from the strict one by splitting each `≤` into a `<` or
an `=` and matching the halves. And because a positive can always be
halved, no positive real is least: that is what makes ℝ dense above
`&0`, and it is the fact analysis reaches for whenever an ε has to be
shrunk.

**Below every small multiple.** A real at most C·ε for every positive ε
up to some η > 0 is at most 0 (`NonposOfSmallMultiples`), the closing of
an ε-argument: at $\varepsilon = \frac{x}{2C}$, or at η, a positive x would be at most half
of itself. It is the chapter's one member closed by the arithmetic
decider.

## Why `ExistsSmallerPos` lives here

Its statement — `&0 < d ⇒ ∃e. &0 < e ∧ e < d` — names no division at
all, so the criterion above appears to send it to `real_order_ring`. It
does not, and the reason is that the criterion is about what the
statement *needs*, not only about what it spells: the witness is `d`
halved, and in an ordered ring with no inverses the statement is simply
false. ℤ is the counterexample, with `d = 1`. `NonposOfSmallMultiples`
lives here for the same reason: it names no division, but in ℤ, with
x = C = η = 1, the premise holds and the conclusion fails.

## The idea the chapter repeats

One observation recurs in five members and is worth stating once here:
**a single positivity hypothesis does two jobs.** `&0 < z` is what
licenses an order move — rescaling a comparison, cancelling a factor —
and it is also what discharges the `z ≠ &0` side condition that every
inverse and quotient law carries. The chapter never needs a separate
non-vanishing assumption, and that is why its statements read with one
hypothesis where a field textbook would write two.

## Names

In the cross-multiplication members (`LessEqDivMulLeft`,
`LessEqDivMulRight`, `LessThanDivMulLeft`, `LessThanDivMulRight`,
`EqDivMulLeft`) the `Left`/`Right` suffix names where the resulting
PRODUCT lands — the convention `real_order_ring` already uses for the
same shape one operation down.

Members in lowerCamel are internal to the chapter: they are the ⇒-form
readings of an ⇔ member (`invPosOfPos` of `InvPos`, `invNonnegOfNonneg`
of `InvNonneg`), verified like any other entry, but not part of what
later chapters cite.

## Mechanics

Typed deps, the shared `real_order_field.cnf.pb`, and replay under
`TestReplayAll/real/real_order_field/` work exactly as in every
family — see `library/registry` and `library/chapter_constitution.md`.
Its statement alphabet comes from the ℝ domain table at
`real/internal/realvocab`.

The one chapter-specific mechanic is that **both `<` and `/` are
normally left folded**, which distinguishes this chapter from
`real_order_ring` next door, where unfolding `<` is half the method.
Here the order facts are cited as they are stated, and a division is
read off `real_field`'s laws rather than expanded into `x · inv y`. The
unfold appears only where no law consumes the folded form: the strict
cross-multiplication pair, each unfolding to its crossed `≤` sibling,
and `DivPos`, where the quotient has to become a product because no law
states the SIGN of one. Each of the three says so at its site.
