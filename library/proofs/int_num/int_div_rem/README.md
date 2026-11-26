# int_div_rem — the division algorithm on ℤ

Integer division and remainder. Unlike ℤ's ring and order structure —
inherited from ℝ along the embedding, see `int_real_lift` — division is
native to ℤ, and what it rests on is discreteness: between a remainder
and the divisor there is room for nothing, which is false over ℚ and is
the whole reason `int_div` and `int_rem` are well defined.

## How the chapter is built

`int_div` and `int_rem` arrive by CHOICE. Every dividend and divisor admit a
quotient and a remainder; the two constants name one such assignment,
and the theorem that introduces them is the one that turns a per-point
existence statement into a specification the constants satisfy
everywhere. **That specification is minted exactly once**, and
everything else in the chapter is read off it:

- **`divModExists`** — every pair admits a quotient and remainder: at a
  nonzero divisor by Archimedean descent and well-ordering, at a zero
  divisor by convention. The chapter's floor.
- **`divRemSpec`** — the same statement, with `int_div` and `int_rem` in it
  instead of existential witnesses. The constants are introduced here.

Immediately above those sit the statements that are each ONE instance
of the specification, and one line of proof:

| member | says |
|---|---|
| `DivisionAlgorithm` | at a nonzero divisor: the quotient/remainder equation, and `0 ≤ rem < \|n\|` |
| `DivisionIdentity` | the equation ALONE, at every pair — the zero divisor included |
| `RemNonneg` | at a nonzero divisor, the remainder is nonnegative |
| `DivByZero`, `RemByZero` | the zero-divisor convention: no quotient taken out, the whole dividend left over |

That bound is then sharpened, and then made exact. Both halves of
`0 ≤ rem < |n|` are stated under a guard the algorithm needs but the
facts themselves do not, and saying when each half really holds costs
three more statements:

| member | says |
|---|---|
| `RemBelowDivisor` | where the divisor is positive it is its own size, so the remainder falls short of the divisor itself |
| `RemNonnegIff` | the lower bound holds unless the divisor is `0` and the dividend negative |
| `RemBelowDivisorIff` | the upper bound holds exactly at a positive divisor, or at `0` with a negative dividend |

The two `…Iff` members are not symmetric, and the asymmetry is the
zero divisor's. There the whole dividend is what is left over, so both
bounds become statements about the dividend's sign — the lower one
asking `0 ≤ m`, the upper one `m < 0`. Away from zero they part
company: the lower bound holds at EVERY nonzero divisor, so
`RemNonnegIff`'s condition is about the zero divisor alone, while the
upper bound needs the divisor positive — below zero a remainder, never
being negative, cannot lie strictly under it. That is why
`RemBelowDivisorIff`'s disjunction names the positive case explicitly
where `RemNonnegIff`'s says nothing about it.

Two more sit just off that list rather than on it, and they are a
matched pair — one per side of the quotient/remainder split. Neither is
a statement a reader looks up; both are how the chapter's later laws
reach what is below them, which is why both are unexported.

| tool | says | reaches |
|---|---|---|
| `divExact` | at a nonzero divisor, `m = q·n` forces `int_div(m,n) = q` | the uniqueness |
| `remDiv` | `int_rem(m,n) = m − int_div(m,n)·n` | the identity |

`divExact` is the uniqueness with the remainder fixed at `0`: its three
conditions then collapse, the lower bound saying nothing and the upper
one reducing to "the divisor is not zero", so all a caller supplies is a
factorisation. `remDiv` is the identity solved the other way, and it
carries no guard at all — which is what lets a member that already knows
its quotient read off its remainder with no case analysis.

Below the specification's totality is the reason `DivisionIdentity`
needs no guard where `DivisionAlgorithm` does: the bound is the part
that fails at a zero divisor, and the equation is not.

The algorithm's first consequence is about a set of integers rather
than a pair, and it is the chapter's one statement in group vocabulary:

| member | says |
|---|---|
| `IntegerSubgroupPrincipal` | every additive subgroup of the integers is the multiples of one nonnegative integer, and of only one |

The generator is the subgroup's least positive member, or `0` when it
has none. Dividing a member by it leaves a remainder that is again in
the subgroup and below the generator, so the remainder is `0`. Two
generators of the same multiples divide each other, so they are equal.

Then uniqueness, which is what makes the two constants COMPUTABLE:

| member | says |
|---|---|
| `DivModUnique` | any pair meeting the three conditions IS `(div, rem)` |
| `DivUnique`, `RemUnique` | its two halves, for arguments that want only one |

Uniqueness is the chapter's other real argument, and the only one that
does algebra: two decompositions of the same dividend are compared by
difference, so their quotients differ by a multiple of the divisor while
their remainders — both drawn from the same half-open interval — differ
by less than its size. The only such multiple is zero. That last step is
where discreteness enters, and it is the single lemma the file rests on.

## Where the chapter starts paying

From here on the chapter mostly says the same thing several ways. Four
times over — the remainder's two bounds below, the small-dividend pair,
the four faces of the adjunction, and the two multiplicative packings —
a single fact is stated in every form a caller might want it in, and one
member of each group carries the argument for the rest. The packings are
the clearest case, because there the carrier is EXPORTED alongside the
group: `DivMulAdd` and `RemMulAdd` are the laws, and the four-conjunct
packs are `…Clauses` members that rearrange and cite them.

Three later things do not fit that description, and it is worth saying
where the pattern stops. The negation laws add content rather than
restating it — a correction term, and a constant the chapter did not
previously need — and their left-hand pair shares a single argument
between its two members. The two-step division pair adds the chapter's second real argument,
and is the only place a THIRD place value enters. Its internal
`divRemByProductPair` proves the mixed-radix quotient and remainder
together with `DivModUnique`; `DivByProduct` and `RemByProduct` read
the corresponding halves. And parity is not a
computation at all: it exhibits no candidate pair and classifies instead
of computing. From the adjunction onward the chapter also increasingly
consumes its own exported laws instead of the specification it started
from — by the last strand it is citing them almost exclusively.

Uniqueness is not the end of the chapter but the point of it. Above it
the statements stop being read off the specification and start being
COMPUTED: to know a quotient, exhibit a candidate pair and check the
three conditions against it. These proofs are short but they are no
longer one-liners — a candidate has to be produced, and the condition
that fails at a zero divisor has to be disposed of first.

| member | says |
|---|---|
| `ZeroDiv`, `ZeroRem` | nothing comes out of nothing, and nothing is left over |
| `DivByOne`, `RemByOne` | the unit divisor takes the whole dividend and leaves nothing |
| `DivSelf` | an integer goes into itself once — and into `&0` not at all |
| `DivMul`, `RemMul` | a product divided by either factor gives back the other, exactly |
| `DivEqZero`, `RemEqSelf` | nothing comes out, and all of it stays, exactly when the dividend was already too small |
| `DivOfSmall`, `RemOfSmall` | the same, on the hypothesis a caller usually holds: the dividend below the DIVISOR rather than below its size |
| `RemRem` | taking a remainder twice is taking it once |

Most of these come in twos, and the pairing is about work rather than
symmetry: only the QUOTIENT half needs a candidate argument, and the
remainder half is then short. `ZeroRem` and `RemByOne` are one line
each through `remDiv` — `int_rem(0,n) = 0 − int_div(0,n)·n = 0`, no case
analysis; `RemMul` reaches `remDiv` too, but inside a case analysis of
its own, and has the longest body here.

`RemOfSmall` does not use `remDiv` at all, and the reason is worth
seeing: its QUOTIENT member exhibits no candidate either, so there is
no arithmetic left for `remDiv` to do. `DivEqZero` and `RemEqSelf` are
stated against the SAME condition, which makes a vanishing quotient and
a self-remainder one fact, and `RemOfSmall` simply crosses between
them.

Three members are not, and they mark the section's other shapes.
`DivSelf` has no partner because `int_rem(n,n) = &0` is not stated
separately here — `n` is already the product `&1 · n`, so `RemMul`
covers it — and what it shows instead is the zero divisor being split
off first, the remainder bound being the one condition a zero divisor
cannot meet. `RemEqSelf` has a partner but is not a computation off it:
its two directions are genuinely different arguments, and only the
easier one goes through `DivEqZero`. And `RemMulAdd` breaks the pairing
a third way: it is a remainder law with no candidate-free route off its
quotient partner, because `remDiv` would import `DivMulAdd`'s guard into
a statement that has none. Both halves therefore run the same candidate
argument, one through `DivUnique` and one through `RemUnique` — the only
place in the chapter where that happens.

## Division as an adjunction

Fix a positive divisor `a`. Everything above treats `int_div(b, a)` as a
value to be computed; there is a second way to see it, as the LARGEST
`c` whose multiple `a · c` still fits under `b`:

```
a · c ≤ b   ⇔   c ≤ int_div(b, a)
```

That single equivalence has four faces, because each side can be
negated — turning `u ≤ v` into `v < u` and swapping which end `int_div`
is bounded at — and because ℤ is discrete, so a strict bound and a
weak one differ by the one correction `c ↦ c + 1`.

| member | at `0 < a` |
|---|---|
| `LessEqDivIff` | `c ≤ int_div(b, a) ⇔ a · c ≤ b` |
| `DivLessIff` | `int_div(b, a) < c ⇔ b < a · c` |
| `DivLessEqIff` | `int_div(b, a) ≤ c ⇔ b < a · (c + 1)` |
| `LessDivIff` | `c < int_div(b, a) ⇔ a · (c + 1) ≤ b` |

`LessEqDivIff` states the display itself, but `DivLessIff` is where the
work is: the display is its double negation, and the other two are one
discrete shift away. Two independent moves generate the four — which
side of `int_div(b, a)` is bounded, and whether the bound is strict —
and the order section's header sets out both them and the window argument.

Discreteness enters four times in this chapter, and every time it is
load-bearing rather than convenient. Here, where `DivLessIff`'s `⇒`
direction needs a WHOLE further step of `a` to be available; in
`DivNoLarger` below, where a divisor above `0` must be at least `1`; in
`RemByProduct`, where the middle digit's being short of `|p|` has to
become a whole step short before `n` can scale it; and twice over in
`RemTwoCases`, which is the only place the chapter reads it in BOTH
directions against one quantity. Over ℚ the second fails outright —
`|int_div(m,n)| ≤ |m|` is false there, not merely unproved.

One more statement is about `int_div` and order, and it is not part of
that picture at all:

| member | says |
|---|---|
| `DivNonneg` | a nonnegative dividend and divisor leave a nonnegative quotient |

It never reaches for the division algorithm. Its subject is signs, and
signs are what the embedding is for: `&` maps ℕ onto exactly the
nonnegative integers and carries ℕ's division across, so a division of
nonnegatives is a division of naturals in disguise, and among naturals
there is nothing left to prove.

## Under a change of sign

The negation strand is the only one that adds mathematics rather
than restating it, and it needs a constant nothing earlier did:
`int_sgn`.

Negating the DIVISOR costs nothing. A decomposition `m = q·n + r` read
against `−n` is `m = (−q)·(−n) + r` — the two sign changes cancel
inside the product, the remainder is untouched, and `−n` has the same
size as `n`, so the remainder still lies where uniqueness demands.

Negating the DIVIDEND cannot be that clean. `−m = (−q)·n − r`, and
`−r` is not a legal remainder unless it is `0`. So the quotient absorbs
one further step of the divisor and the remainder reflects to
`|n| − r` — and WHICH WAY the quotient steps is the sign of the
divisor, since the step is by `n` while the bound is stated in `|n|`.

| member | says |
|---|---|
| `DivRightNeg`, `RemRightNeg` | negating the divisor flips the quotient and leaves the remainder alone |
| `DivLeftNeg`, `RemLeftNeg` | negating the dividend corrects both, unless the division was already exact |
| `DivBothNeg`, `RemBothNeg` | negating both, which is negating each in turn |
| `DivNoLarger` | a quotient is never larger than its dividend, in absolute value |

The composites take the CHEAP side first, which is why they are short:
after the divisor's sign is off, what remains is exactly what the
left-hand pair already solved. `RemBothNeg` has nothing left to prove
at all; `DivBothNeg` still has one sign to distribute over a
conditional, and deciding an equality of two conditionals under one
condition is a case analysis — which is why it carries the strand's
only refutation.

`DivNoLarger` sits with the adjunction rather than here, in
The order section: a bound on the SIZE of a quotient is a pair of bounds on
the quotient, which is what the adjunction converts. It reaches the
negation laws only to reduce a negative divisor to a positive one.

## Dividing in two steps

Everything so far divides once. Fix a nonnegative `n` and a `p`, and
there are two ways to take `m` apart by `n · p`: in one go, or by
dividing by `n` and then dividing the quotient by `p`. The chapter's
last argument says they agree.

The two-step reading writes `m` in mixed radix, with places
`…, n·p, n, 1` and three digits — `int_rem(m, n)` at the units, `int_rem(int_div(m,
n), p)` at the `n` place, and `int_div(int_div(m, n), p)` carrying everything
above. What `n · p` leaves over is then everything below its own place:

| member | says |
|---|---|
| `RemByProduct` | `int_rem(m, n·p) = n · int_rem(int_div(m,n), p) + int_rem(m,n)` — the two lower digits |
| `DivByProduct` | `int_div(m, n·p) = int_div(int_div(m,n), p)` — the top digit: dividing by the product IS dividing twice |
| `RemDivExchange` | `int_rem(int_div(m,n), p) = int_div(int_rem(m, n·p), n)` — the middle digit read back out |

`RemByProduct` is the chapter's second real argument, after
`divModExists`. It exhibits the pair and hands it to the uniqueness, and
the three conditions that come back are of three different kinds: an
equation that is a regrouping rather than a deduction, a lower bound
that is a sum of nonnegatives, and one genuine estimate. The estimate is
where a nonnegative divisor is finally needed — twice over, to let `n`
scale an inequality without reversing it, and to identify `n` with its
own size.

`DivByProduct` says the same decomposition from the quotient's side, and
it is short BECAUSE `RemByProduct` came first: handing the uniqueness
the remainder `int_rem(m, n·p)` itself, both bounds are the algorithm's own,
and the one equation left is the mixed-radix regrouping.

`RemDivExchange` is that divided by `n`, and it is short because the low
digit contributes no further multiple of `n`. It closes on `DivMulAdd`,
which is the multiplicative section's exported law: the packing promoted
earlier is exactly the fact this corollary needs.

## When the division comes out even

The divisibility section is where the chapter meets `∣`. Its content is that
three ways of saying a division is exact are one statement: `n` divides
`m`, the remainder `int_rem(m, n)` vanishes, and `m` is exactly `n` times
its own quotient.

| member | says |
|---|---|
| `DividesIffRemZero` | `int_rem(m, n) = &0 ⇔ n ∣ m` |
| `DividesIffQuotientExact` | `n · int_div(m, n) = m ⇔ n ∣ m`, in both factor orders |
| `DividesQuotient` | dividing by a divisor loses nothing: `e ∣ int_div(n, d) ⇔ d · e ∣ n` |
| `QuotientDivides` | and the same read the other way |

The first is the bridge and each of its directions uses a different half
of the algorithm: a vanishing remainder makes the specification's
equation exhibit the quotient as the cofactor `∣` asks for, while the
converse is a computation — a multiple of `n` leaves nothing over `n`.
It carries no guard, because at the zero divisor the convention answers
too: `int_rem(m, &0) = m`, so a vanishing remainder there says `m = &0`,
which is exactly what `&0` divides.

The quotient pair is where `int_div` being TOTAL shows through. Going up,
the cofactor carries over untouched; coming down, a shared factor has to
be cancelled, and at `d = &0` there is nothing to cancel — so that
branch is settled by the convention instead.

## The least common multiple

`int_lcm` is the reason this strand is here rather than with `∣`: its
DEFINITION names a division.

    lcm(m, n) = COND(m · n = &0, &0, int_div(|m · n|, gcd(m, n)))

**And the guard is redundant.** Where it fires, `m · n` is `&0`, so the
dividend `|m · n|` is `&0` too, and dividing `&0` by anything gives `&0`
back — the very value the guard supplies. The two branches agree, the
COND goes, and

    lcm(m, n) = int_div(|m · n|, gcd(m, n))

holds outright. Saying that once is most of what the lcm section is; each
member is then one sentence about that quotient.

| member | says |
|---|---|
| `LcmNonneg` | `&0 ≤ lcm(m, n)` — a size over a gcd, both nonnegative |
| `GcdTimesLcm` | `gcd(m, n) · lcm(m, n) = \|m · n\|` |
| `DividesLcmIff` | what divides the lcm: `d ∣ lcm(m, n) ⇔ d · gcd(m, n) ∣ m · n` |
| `LcmDividesIffBoth` | what the lcm divides: `lcm(m, n) ∣ d ⇔ m ∣ d ∧ n ∣ d` |
| `LcmIsLeastCommonMultiple` | it is a common multiple, and it divides every common multiple |

The last is the name in full, and it follows from the two `…Iff`
members: the third conjunct is `LcmDividesIffBoth` read right to left,
and the first two are `DividesLcmIff` at `d := m` and `d := n`.

The one fact the strand needs from outside is that the gcd divides
`|m · n|` — from `int_divides`, which supplies the gcd's specification,
that a divisor of a factor divides the product, and that a divisibility
does not see a sign.

The sizes are not decoration. `m · n` itself is recovered only up to
sign, because the lcm is nonnegative and the product need not be.

## Evens and odds

Pinning the divisor at `&2` turns the remainder BOUND into a remainder
LIST — the algorithm puts `int_rem(n, &2)` in `⟦&0, &2⟭`, and over ℤ that
interval holds exactly two integers.

| member | says |
|---|---|
| `RemTwoCases` | `int_rem(n, &2)` is `&0` or `&1` |
| `RemTwoIff` | and each is exactly the failure of the other |

A literal is opaque to the order laws — nothing in ℤ's ordered-ring
theory knows how far `&2` stands from `&0` — so the argument spends the
numeral once, on `&2 = &1 + &1`, and is ordered-ring algebra over `&1`
thereafter. That is why theorems about the number two rest on a single ℕ
fact.

`RemTwoCases` is also the chapter's one member that computes nothing: it
exhibits no candidate pair and cites neither the uniqueness nor
`remDiv`. It classifies what the remainder interval can hold, which is a
different kind of statement from everything above it.

Then the file crosses to `∣` and stays there. `TwoDividesIffRemZero` is
the bridge — even means remainder `&0`, odd means remainder `&1` — and
after it nothing looks at the interval again:

| member | says |
|---|---|
| `TwoDividesIffRemZero` | `int_rem(n, &2) = &0 ⇔ &2 ∣ n`, and `= &1 ⇔ ¬(&2 ∣ n)` |
| `TwoDividesProduct` | a product is even exactly when a factor is |
| `TwoDividesDifference` | two integers have the same parity exactly when their difference is even |
| `TwoDividesPower` | a power is even exactly when its base is and its exponent is not `&0` |

Two shapes carry all three, and neither is about `&2` in particular:
exhibit a cofactor and the number is even, or write one number as
`q · &2 + r` and read another's remainder off it. The first is
`int_divides.DividesOwnMultiple`'s job, the second `RemMulAdd`'s, and
`oddDecomposition` — `¬(&2 ∣ m) ⇒ m = int_div(m, &2) · &2 + &1` — is what
turns "not even" into something the first shape can use.

## Boundary

Divisibility as a relation is `int_divides` — `a ∣ b` and everything
provable about it in RING vocabulary, before division exists: the sign
and size laws, the two closure laws, the gcd. Everything that JOINS `∣`
to the algorithm is this chapter's, and the layering is what forces
that: this chapter reads `int_divides` for divisibility and the gcd
specification, so a theorem naming `int_div` or `int_rem` belongs here.
That is the divisibility and lcm sections below, plus parity's `∣` half.
The congruence
relation and `int_cong` are `int_congruence`'s — and so is `int_rem`'s
respect for `+`, `·` and powers, which is the congruence story told
without the notation. The transport facts that carry ℕ's
`nat_div`/`nat_mod` across the embedding are this chapter's own:
they exhibit ℕ's pair to THIS chapter's uniqueness law, so they sit
above the chapter core, citing `int_embed` for the embedding alone —
the direction that keeps the package graph matching the theorem
layering.

Everything else that STATES something about `int_div` or `int_rem` is this
chapter's — the order, negation, multiplicative, nesting and mod-2
laws — and the test is the statement, not the name.
