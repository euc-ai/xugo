# num_segment — the interval of naturals between two bounds

`m .. n` is the set of naturals between two bounds. It is defined as a
comprehension,

```
m .. n = {x | m ≤ x ∧ x ≤ n}
```

and that single line decides how the whole chapter reads. Unfolding it
once gives `Membership`,

```
x ∈ m .. n ⇔ m ≤ x ∧ x ≤ n
```

and after that nothing here unfolds anything. A claim about an interval
becomes a claim about `≤` on its bounds — which the order chapter
already proves — so the members are short and the work is in choosing
which arithmetic fact each one reduces to.

## What the chapter is for

Intervals are how the corpus makes finiteness and counting concrete.
`finite(s)` is an existence statement about a closure; `has_size(1..n, n)`
is a set you can point at.

Downstream they are index sets. A sum over a range is a fold over a
finite set, and the ranges an indexed statement writes are this
chapter's two: the interval `m .. n`, which `iterate/real/real_sum`'s
interval calculus and the polynomial chapter are written over, and the
numbers below a bound, `{x | x < n}` — the range `Σ_{i<n}` binds, the
active range of an n-vector in the `vector/` chapters, the places of a
word of width n. What those consumers cite is the finiteness of the
range and its recursion clauses, which peel one index off a fold;
membership they cite nothing for, since the definition declares that
the closers read `i ∈ m .. n` as the pair of inequalities their own
statements are written with (`MembershipRead`), and `Membership` states
that reading for a rewrite or an instance. Two members are cited for what
they say about finite sets at large: a map of the numbers below k into
themselves that never repeats a value misses none of them
(`BelowStrictInjectiveOnto`), and a set of anything at all is finite
exactly when some interval indexes it injectively (`FiniteIndex`).

## The four movements

**Membership.** The unfolding law, and its corollaries at a zero lower
bound: `MembershipFromZero`, and a map normalized on `0 .. n` read at a
coordinate straight from its bound — its own value up to `n`
(`NormalizeOnSegmentIn`) and the default past it (`NormalizeOnSegmentOut`).
Every member about `..` reads through it — see the unfolding law's own
note for where that scope stops.

**The interval's shape.** When `m .. n` is empty (exactly when `n < m`),
when it is a singleton, and how it recurses at either end — peel `suc n`
off the top, or `m` off the bottom. Then how the set relations read on
two intervals: `⊆` in terms of the bounds, `∩` as `nat_max .. nat_min`, and the
disjointness criterion that falls out of it. Then how two adjacent
intervals combine into one.

The one-sided sets `{x | x ≤ n}` and `{x | x < n}` are set-builders,
not intervals — the theorems that IDENTIFY them with `0 .. n` and
`0 .. (n-1)` are the bridge, and the recursion clauses on that side are
stated over the builder, mentioning `..` nowhere. One inclusion places a
set inside the strict side: the numbers below a bound no larger.

| Member | Statement |
|---|---|
| `BelowStrictMono` | The numbers below k lie below every m at least k. |

**Finiteness.** `finite(m .. n)`, because an interval is built by
`insert` from below. The induction runs on the intervals that start at
0, which are exactly the ones the successor clause grows with no side
condition to discharge; every other interval is a subset of one of
those, and a subset of a finite set is finite. So there is no case
analysis of the empty intervals at all. The one-sided sets then read
off the identifications above, and the movement closes by turning the
reasoning around: a set of numbers is finite exactly when some interval
holds it, proved by carrying a bound along each insertion.

**Counting.** `card(m .. n) = (n + 1) - m`, and the `has_size` forms.
The heart of it is a single induction over the list_length of the interval
(`card(m .. (m + d)) = d + 1`), which is why the chapter's counting
member is stated that way rather than in terms of the bounds: an
interval only ever grows in one direction, so fixing the lower bound
makes the lower bound a spectator and leaves no empty interval anywhere
in the argument. The familiar two-bound form is then a corollary whose
content is entirely the crossed case, where there is nothing to count
and truncated subtraction sends the width to 0 with it.

The `has_size` forms cost almost nothing on top, because `has_size` is
by definition "finite, and of this count" — so each of them is this
movement's count and the previous movement's finiteness, read together.
That is why the whole movement reaches only two rules from outside the
chapter: how a count reacts when a single point is laid on a finite set,
and the fact that two finite sets of equal count admit a mutually
inverse pair.

Halving is counted here as well: of 1, …, n, the numbers whose double
exceeds n are the upper half.

| Member | Statement |
|---|---|
| `UpperHalfCount` | Of 1, …, n, those whose double exceeds n number n − ⌊n/2⌋ |

The second of those buys the member the counting is FOR: a set of
anything at all is finite exactly when some interval indexes it
injectively. Finiteness was characterised once already, in the previous
movement, by a bound; here it is characterised by an enumeration, and the
count is what says how long the enumeration has to be.

The pigeonhole principle read the other way round belongs here too, at
the one-sided set a counting argument over a family runs on: a map of the
numbers below k into themselves that never repeats a value misses none of
them (`BelowStrictInjectiveOnto`). It is the general fact that a self-map
of a finite set is onto exactly when it is one-to-one, read at
`{x | x < k}`. A map of the numbers below n into themselves that climbs at every step
fixes each of them (`IncreasingSelfMapIsIdentity`): the climb from 0
puts f(i) at least i, the climb down from n − 1 at most i.

## Finiteness before counting

An interval is finite because of how it is built, and nothing about
that argument needs a cardinality. So the chapter proves finiteness
first, by induction, and puts counting on top of it. The practical gain
is that the first three movements reach no cardinality theorem at all.

## Names

Members are named for what they say, and the package prefix already
reads `num_segment.`, so no member repeats `Numseg` —
`num_segment.Membership`, not `num_segment.InNumseg`.

| Member | Statement |
|---|---|
| `FiniteRangeRepeats` | A map of the numbers up to N into at most N values repeats a value |
