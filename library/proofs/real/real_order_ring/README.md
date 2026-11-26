# real_order_ring — ℝ as an ordered ring

The construction hands down its order as axioms and stops: `≤` is
antisymmetric and transitive, any two reals are comparable, adding a
constant preserves it, a product of non-negatives is non-negative, and
it agrees with ℕ's order across the embedding. This chapter is
everything else — the order's own properties, and what it does to `+`,
`−` and `·`.

Its sibling `real_order_field` carries the order laws that mention
`real_inv` or `real_div`, and `real_archimedean` carries the chain
that additionally needs Dedekind completeness. Nothing here reaches
either.

## The one idea the chapter runs on

**`<` is not a second relation.** It is defined:

```
x < y   ≝   ¬(y ≤ x)
```

So a statement about `<` becomes a statement about `≤` by unfolding one
constant, and that unfold is where the chapter's arguments become
visible. Read this way, trichotomy — "any two reals are equal or one is
smaller" — is just antisymmetry:

```
x = y ∨ x < y ∨ y < x        unfolds to        x = y ∨ ¬(y ≤ x) ∨ ¬(x ≤ y)
```

which says that two reals comparing both ways are equal, and nothing
more. Totality plays no part.

The unfold also cancels double negations as it goes: `¬(x < x)` arrives
as `x ≤ x`, so irreflexivity of `<` is literally reflexivity of `≤`.

## Members

Names are ours. The **same chapter stands at ℕ** as
`nat_num/nat_order`, and members take their ℕ counterpart's name where
one exists, so the two can be read side by side. Lower-case names are
internal lemmas rather than chapter API; which names demote is taken
from `nat_order`'s own list where a counterpart exists. Where none
does — the negation, subtraction, embedding and cancellation members
have no ℕ twin — a name is demoted when it is the second face of a
mirror pair, which is what `ofNumGreaterThan` and `LessThanMulRightEq`
are. Demotion is undone by a consumer: `LessThanSelfAddRight` and
`LessThanAddOne` are capitalized against their ℕ list and their mirror
siblings because `real_order_field` and `real_archimedean` cite them,
and an entry cited across a family boundary is chapter API.

Three names are exported against those rules —
`LessEqLessThanTrans`, `LessThanLessEqTrans` and `ZeroLessEqOne`.
Export tracks USE, not role: ℤ inherits all three across the embedding
(`int_num/int_real_lift`), and a chapter another chapter builds on
publishes what it is built on.

| member | |
|---|---|
| `LessEqRefl` | `x ≤ x` |
| `NotLessThan` | the definition of `<` |
| `NotLessEq` | the definition read from the ≤ side |
| `RealGtDef` | the definition of `>` |
| `RealGeDef` | the definition of `≥` |
| `LessThanIrrefl` | |
| `LessEqSplit` | `≤` as `<` or `=` |
| `LessThanSplit` | `<` as `≤` and `≠` |
| `LessThanTrichotomy` | |
| `LessThanAsym` | |
| `lessThanLessEqAsym` | mixed |
| `lessEqOrLessThan` | mixed |
| `LessEqOfLessThan` | |
| `LessEqOfEq` | |
| `NotEqualOfLessThan` | |
| `NonzeroOfPositive` | |
| `LessEqLessThanTrans` | mixed |
| `LessThanLessEqTrans` | mixed |
| `LessThanTrans` | |
| `LessEqAddLeft` | translation invariance |
| `LessEqAddRight` | |
| `LessThanAddLeft` | |
| `LessThanAddRight` | |
| `LessThanAddLeftImp` | |
| `LessEqAdd2` | comparisons add |
| `AddNonneg` | a sum of non-negatives is non-negative |
| `LessThanAdd2` | |
| `LessEqLessThanAdd2` | |
| `lessThanLessEqAdd2` | |
| `LessEqSelfAddRight` | `x` against `x + y` |
| `LessEqSelfAddLeft` | |
| `LessThanSelfAddRight` | |
| `lessEqLeftNeg` | a negation crosses the comparison |
| `lessEqRightNeg` | |
| `lessThanLeftNeg` | |
| `lessThanRightNeg` | |
| `LessEqNeg2` | negating both sides reverses |
| `LessEqSubAddLeft` | a difference becomes a sum |
| `LessEqSubAddRight` | |
| `LessThanSubAddLeft` | |
| `LessThanSubAddRight` | |
| `SubNonneg` | the sign of a difference |
| `SubPos` | |
| `NegNonnegativeIffNonpositive` | the sign of a negation |
| `NegNonpositiveIffNonnegative` | |
| `NegPositiveIffNegative` | |
| `NegNegativeIffPositive` | |
| `LessThanNeg2` | negating both sides, strict |
| `LessEqNegTotal` | one of `x`, `-x` is non-negative |
| `LessThanNegTotal` | |
| `lessEqSelfNeg` | `x` against `-x` |
| `OfNumLessThan` | the embedding carries `<` |
| `ofNumGreaterThan` | and carries it backwards |
| `NumNonneg` | `&0 ≤ &n` |
| `ZeroLessEqOne` | |
| `ZeroLessThanOne` | `&0 < &1` |
| `LessThanAddOne` | stepping up by one makes a bound strict |
| `LessEqMulLeft` | scaling a comparison |
| `LessEqMulRight` | |
| `MulPos` | a product of positives is positive |
| `LessThanMulLeft` | |
| `LessThanMulRight` | |
| `SquareNonneg` | `&0 ≤ x·x` |
| `SquarePos` | |
| `SumSquaresEqZero` | `x·x + y·y = &0 ⇔ x = &0 ∧ y = &0` |
| `LessThanCancelMulLeft` | cancelling a positive factor |
| `LessThanCancelMulRight` | |
| `LessEqCancelMulLeft` | |
| `LessEqCancelMulRight` | |
| `LessEqMul2` | comparisons multiply |
| `LessThanMul2` | |
| `LessEqMulRightEq` | scaling by a positive factor is reversible |
| `LessThanMulRightEq` | |
| `CommonRadius` | finitely many radii have a common one |

`LessEqRefl` is the chapter's floor: reflexivity is the degenerate case
of totality, and it is what every later equal-case branch cites.
`NotLessThan` and its twin `NotLessEq` state the definition above as members (the second is it verbatim, read from the ≤ side). A member
whose own statement carries `<` normally unfolds rather than citing it —
but two of the cancellation members cite it instead, because unfolding
moves the goal while a dep INSTALLED afterwards keeps its own `<`. When
the two relations have to be crossed on the dep's side, this member is
how.

Four of the order-bridge members cite nothing at all. `NotLessThan`,
`NotLessEq`, `lessEqOrLessThan` and `lessThanLessEqAsym` are what the definition
alone gives: unfolded they are the defining equation, an instance of
excluded middle, and a formula conjoined with its own negation.

The two `Self` names mark the members comparing a real with a sum it is
itself a summand of, and they are distinct theorems from the
translation laws sitting next to them in the table: `LessEqSelfAddRight`
says a summand's sign decides whether the sum beats the other summand,
`LessEqAddRight` says adding the same thing to both sides changes
nothing.

## What addition does to the order

One statement carries the tier. `LessEqAddLeft` — `x + y ≤ x + z ⇔
y ≤ z` — gets its ⇐ from the axiom outright, and its ⇒ from the same
axiom used backwards: translate by `-x` and watch each side collapse.
That collapse, `-x + (x + y) = y`, is where associativity, the left
inverse and the left identity are spent, and it is the only internal
lemma in the tier.

Everything else reads it back. Commutativity turns it into
`LessEqAddRight`, once; the `<` unfold turns each of those into its
strict twin without spending commutativity a second time. Adding two
comparisons moves one summand at a time through the mixed sum `x + y`,
so `LessEqAdd2` and its three mixed siblings are two translations and a
transitivity. And `x ≤ x + y` is translation invariance too, once `x`
is read as `x + &0` — which is the chapter's FIRST reach into
`real_ring`, for the right identity.

## Negation and subtraction

The same statement carries this too, and that is the surprise. Moving a
negation across a comparison is translation invariance at a chosen
instance: `-x ≤ y` becomes `&0 ≤ x + y` by translating both sides by
`x`, because that is what sends `-x` to zero. Every one of the negation
laws is that move plus the one ring equation naming the inverse pair it
creates, and `LessEqNeg2` — negating both sides reverses the
comparison — is two such translations meeting at `&0 ≤ -y + x`.

Subtraction never gets unfolded. `x - y` stays an opaque term, and the
chapter meets it through `LessEqSubAddLeft` and its mirror, which say
that moving the subtracted term to the other side of the comparison
changes nothing. The only fact about `−` they use is `(x - y) + y = x`.
Then `SubNonneg` is the left law read at `&0` — the sign of a
difference IS the comparison of its two terms.

The strict twins cost nothing, and one fact explains all of them.
`x < y` is `¬(y ≤ x)`, so unfolding a strict comparison SWAPS ITS TWO
OPERANDS — the ⇔'s own sides stay put, and the two negations cancel
across it. A term therefore changes which side of its comparison it
sits on. That is why each strict subtraction law is its non-strict
MIRROR rather than its own twin, cited bare and nothing else: the
difference has moved across the comparison, so a law about a
left-hand difference proves the strict right-hand one.

## What the order says about a sign

Comparing a real with `&0` is the special case where the negation laws
become statements about sign, and the four of them are one law seen
from four sides: `&0 ≤ -x ⇔ x ≤ &0` and its mirror, then both of those
made strict. `LessEqNegTotal` is the order's totality read through
them — of `x` and `-x`, at least one is non-negative.

`lessEqSelfNeg` is the chapter's first theorem with two directions to
argue, and it is worth reading for the shape rather than the content.
Comparing `x` with `-x` directly leads to `x + y ≤ &0` at `y = x`, and
finishing from there would need a doubling law this chapter does not
state. Going through `&0` instead — `x ≤ &0` gives `&0 ≤ -x`, and
transitivity closes — needs only the sign laws already proved. Each
direction is one chain, and both are written as such.

## The order across the ℕ embedding

The construction gives one embedding fact — `&m ≤ &n ⇔ m ≤ n` — and
these six are what follows from it. Three of them are translations
rather than arguments: the comparison moves down to ℕ, ℕ answers it,
and the answer comes back.

That makes the tier the one place where the chapter's characteristic
unfold meets a domain that does not share it. At ℝ, `<` is DEFINED as
the negation of the flipped `≤`, so it unfolds; at ℕ, `≤` and `<` each
have their own defining clauses and the same duality is a theorem. So
`OfNumLessThan` unfolds on the ℝ side, rewrites the embedding off the
one comparison that carries it, and lands on ℕ's `NotLessEq` — the
duality proved, where ℝ had it by definition. Note which one: the
goal's surface has `<` on both sides, but after the unfold what is
wanted is the duality that negates the NON-strict order.

`ofNumGreaterThan` is the same move run twice at once. Neither `>` is a
relation of its own — ℝ and ℕ each define theirs as their own strict
order with the arguments swapped — so unfolding both leaves the same
swap on both sides of the equivalence, and a swap common to both sides
is undone by renaming the binders. What is left is `OfNumLessThan`.

The two facts about the unit are where the chapter borrows something it
cannot prove. `&0 ≤ &1` is just `NumNonneg` at `1`. But `&0 < &1` is
not an order fact about a ring at all — in ℕ it says `1` is positive,
which ℕ holds as the same fact as `1 ≤ 1`, and that is structural. That is why
`LessThanAddOne` — a bound stepped up by one becomes strict — sits in
this tier rather than with the additive laws it looks like it belongs
to: all of its strength is in the positivity of the unit, and the
additive laws only carry it.

## What the order says about multiplication

One idea again, and it is the additive tier's: **a comparison is the
sign of a difference.** `x·y ≤ x·z` is `&0 ≤ x·z - x·y`, and
distribution turns that into `&0 ≤ x·(z - y)` — a product of two
non-negatives, which is precisely the construction's one multiplicative
order axiom. So `LessEqMulLeft` is: restate the hypothesis as a sign,
scale it, distribute, read the sign back. `LessThanMulLeft` is the same
four steps with every ≤ strict, and it reads as a copy of its sibling
because it is one.

The right-hand laws are the left-hand ones seen through commutativity,
and the sign laws are the axiom applied to whichever of `x` and `-x`
is non-negative — `SquareNonneg` is that case split, with the ring
identifying `(-x)·(-x)` with `x·x` in the negative case. `MulPos` and
`SquarePos` are both the same disassembly: positive means non-negative
AND non-zero, so each is proved by handing the two halves to two
different laws — the order axiom for the first, the zero-product law
for the second — and reassembling. `SumSquaresEqZero` puts the two to
work together: neither square is negative, so a zero sum leaves both
zero, and a square vanishes only at zero.

## Cancelling a positive factor, without dividing by it

The converse direction is the chapter's last group and its sharpest
result, because of what it does NOT use. From `x·y < x·z` and `&0 < x`,
conclude `y < z`. The obvious argument multiplies through by `1/x`.
**An ordered ring has no inverses, and it does not need them here.**
`y < z` IS `¬(z ≤ y)`, so the statement is already a
denial: suppose `z ≤ y`; then scaling by the non-negative `x` gives
`x·z ≤ x·y`, which is exactly what `x·y < x·z` denies. Totality supplies
the `&0 ≤ x` that scaling wants, from the `¬(x ≤ &0)` the hypothesis
became. Two facts, no inverse.

So cancellation is the contraposition of monotonicity, and the chapter
closes without ever importing `real_order_field`. The two right-hand
cancellation laws are the left-hand ones read through commutativity, as
everywhere else here, and `LessEqMulRightEq` puts the two directions
together: scaling by a positive factor is not merely monotone but
reversible, hence an equivalence.

The pairwise laws are the additive `Add2` family's argument at a
product: `w·y ≤ x·z` moves one factor at a time through the mixed
product `x·y`, and transitivity joins the halves — appearing twice,
once to join them and once to get the `&0 ≤ x` that the second half's
scaling needs and the statement does not give.

## A common radius for finitely many

When each index i below k has a radius δ > 0 within which some
condition R(i, y) holds, one radius serves every i below k at once:
`(∀i. i < k ⇒ ∃δ. &0 < δ ∧ ∀y. d(y) < δ ⇒ R(i, y)) ⇒ ∃δ. &0 < δ ∧ ∀y.
d(y) < δ ⇒ ∀i. i < k ⇒ R(i, y)`. By induction on k: the smaller of a
common radius for the first k and the radius for k itself serves the
first k + 1, the strict order passing below the smaller one.

## What is elsewhere

The order laws that mention `real_inv` or `real_div` are
`real_order_field`'s, and the Archimedean chain is
`real_archimedean`'s.

## Mechanics

- **Statements** are text, in the chapter's alphabet: `≤`, `<` and `>`
  as notation, the ring operations, and the embedded literals `&0` and
  `&1`. The types come from the ℝ domain alphabet,
  `real/internal/realvocab`; `vocab.go` says which names this chapter
  uses. One of them is not ℝ's: ℕ's `>`, declared inline because the
  ℕ-embedding tier's statements mention it and ℕ has no domain
  alphabet to borrow from.
- **The unfold** is `Unfold(NotLessEq)`, the definition of `<`, plus
  `Unfold(RealGtDef)` and `Unfold(nat_order.GtDef)` where the embedding
  states a backwards comparison. It
  rewrites under binders and implications, so the goal stays ∀-closed
  and a member that unfolds and then cites BARE takes no closure
  parameters. Taking parameters
  is about BUILDING terms, not about the unfold: the members that
  ground a cite at `-x` or `y - z` name their binders for that reason.
- **Cites** are typed entry vars — `axioms.*`, this chapter's own entries,
  and eight laws from `real_ring`. Three serve the additive and
  subtraction tiers: the right identity `AddRightId` (to read `x` as
  `x + &0`), the right inverse `AddRightInv`, and `SubAddRight`
  (`(x - y) + y = x`), which is how the chapter handles `−` without
  ever unfolding it. Five arrive with multiplication:
  `SubLeftDistrib` (distribution over a difference, which is what
  turns a scaled comparison back into a comparison of products),
  `MulEqZero`, and the sign trio `MulLeftNeg` / `MulRightNeg` /
  `NegNeg`. The chapter's only reach outside
  `real/` is the ℕ-embedding tier's, and it goes to one family:
  `nat_order.*`, for ℕ's half of each equivalence.
- **The CNF blob** and its recording recipes are described in
  `family.go`.
