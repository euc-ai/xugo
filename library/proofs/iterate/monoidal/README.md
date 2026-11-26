# monoidal — the fold mechanism

What does it take to fold an operation over a set? The chapter's
answer is four constants deep. An operation folds when it is
associative, commutative, and has a two-sided identity — `monoidal_op op`
— and that identity is `neutral_elem op`, the element folding starts from.
A function `f` on an index set matters only where it differs from the
neutral: `op_support op f s` carves that subset out, and finiteness of
the SUPPORT, not of the index set, is what makes a fold well-defined —
which is how an infinite index set can still carry a meaningful fold.
On top of these sits `iterated_op op s f`: the operation applied across
the support when that is finite, the neutral otherwise.

Everything is doubly polymorphic — the carrier the operation acts on
and the index type are both free — and no carrier domain is named
anywhere in the chapter (the index side admits one concrete reading:
ℕ, through the ranges below a bound and the intervals `m .. n`). The
payoff of that austerity is
downstream:
Σ and Π over ℝ, ℕ and ℤ are each one instantiation of this chapter's
laws at one `monoidal_op` fact, and the sibling chapters that read them
(`iterate/real/real_sum` first) inherit the whole index-side calculus —
recursion clauses, unions, images, reindexing — without re-proving a
line of it.

The chapter unfolds from the definitions upward: what `monoidal_op`
demands; the support's own algebra (it commutes with the
constructors); the recursion clauses of the fold at `∅` and `insert`;
then the fold's algebra — splitting over unions, transport along
images and bijections, iterated folds over product sets.

## The language layer

`monoidal_op` is the chapter's subject as a STRUCTURE — a predicate of
one component, the operation — named by `family.StructureOf`, and every
law below is stated over it through the structure door: the member
writes the body, the door prefixes `∀op. monoidal_op(op) ⇒`, and the
proof names `op` before the hypothesis since the chapter grounds its
cites at the operation. The carrier is `B` in every member but one —
`Homomorphic`, which crosses to a SECOND carrier at `C` — and the
doubly-indexed members take their second index at `C` too.

| member | statement |
|---|---|
| `MonoidalAC` | `monoidal_op op` licenses the five rearrangement laws — left-commute, associativity, commutativity, and the neutral from either side |
| `InSupport` | `x ∈ op_support op f s ⇔ f x ≠ neutral_elem op ∧ x ∈ s` |
| `SupportSubset` | `op_support op f s ⊆ s` |
| `SupportIdempotent` | `op_support op f (op_support op f s) = op_support op f s` |
| `SupportClauses` | the support commutes with `∅`, insert, delete, ∪, ∩, ∖ and image |
| `SupportFinite` | `finite s ⇒ finite (op_support op f s)` |
| `SupportDelta` | a delta function's support is `op_support op f {a}` when `a ∈ s`, else `∅` |
| `SupportDeltaFinite` | a delta function's support is finite outright |

## The recursion layer

What `iterated_op` is, and the clauses everything downstream computes with.

| member | statement |
|---|---|
| `ExpandCases` | the definition as an equation: the fold over the support when that is finite, the neutral otherwise |
| `OnSupport` | `iterated_op op s f = iterated_op op (op_support op f s) f` — the fold never sees the points it can ignore |
| `ClausesGen` | the `∅` and `insert` clauses, guarded by finiteness of the SUPPORT |
| `Clauses` | the same clauses at the plain `finite s` guard everything downstream carries |
| `OneTurn` | the insert clause with its guard decided: a NEW point comes back out of the fold |
| `BelowClauses` | the clauses along the half-open range `{i \| i < n}` — nothing below 0, and raising the bound to `suc k` admits exactly `k`: the range is empty at 0 where an interval is not |

## The inheritance layer

A fold inherits a property of the values it combines. `ClosedNonempty`
is not `Closed` at a different hypothesis package — it asks a strictly
stronger pointwise premise, which is what buys the neutral hypothesis it
drops.

| member | statement |
|---|---|
| `Closed` | a property holding at the neutral and surviving `op` is inherited by the fold — no finiteness needed |
| `ClosedNonempty` | the same with no hypothesis at the neutral, paid for by a finite nonempty index set AND a premise holding at every point |

## The evaluation layer

What a fold is worth once you know its support.

| member | statement |
|---|---|
| `Sing` | `iterated_op op {x} f = f x` |
| `EqNeutral` | a summand neutral everywhere on `s` folds to `neutral_elem op` |
| `Delta` | a summand silent off `a` folds to `f a` when `a ∈ s`, else `neutral_elem op` |
| `Superset` | enlarging `s` by points the summand is silent at does not move the fold |
| `Univ` | the same, with the enlargement taken all the way to `𝕌` |
| `BelowTruncate` | the same on the half-open ranges: for `t ≤ m`, a fold over `{i \| i < m}` whose summands from `t` on are neutral is the fold over `{i \| i < t}` — the form a coefficient sequence extended by zero, or cut off at an index, asks for |
| `Delete` | `op (f a) (iterated_op op (s ∖ {a}) f) = iterated_op op s f` for `a ∈ s`, `s` finite |
| `Related` | a relation `op` respects and holding pointwise is inherited by the fold |
| `Congruence` | summands agreeing on `s` have the same fold — the case everything downstream uses |
| `Homomorphic` | a map to a SECOND monoidal carrier that fixes the neutral and carries the operation to the operation carries the fold itself: `h(iterated_op(op, s, F)) = iterated_op(op₂, s, λi. h(F(i)))`. `Related` read at two operations — and the shorter member, because its two hypotheses speak of `h` alone and never of the index set, so they stay resident where `Related`'s and `Closed`'s must travel inside the induction property. The fold's recursion has exactly two clauses and each spends one hypothesis, which is why those two are the ones a homomorphism is asked for |

## The algebra layer

A fold is a HOMOMORPHISM, read on both of its arguments — on the index
set (`Union`, `Diff`, `Split`, `UnionIntersection`), where each law
lands at `op (fold) (fold)`, and on the summand (`Pointwise`, and
`Swap`, which iterates that reading rather than applying it and so
equates two double folds instead). The fold's other face — that it
INHERITS a property of the values it combines — is the inheritance layer's
subject.

| member | statement |
|---|---|
| `Union` | disjoint index sets fold separately: `iterated_op op (s ∪ t) f = op (iterated_op op s f) (iterated_op op t f)` |
| `Diff` | the same splitting at a subset, which cuts the set it sits in |
| `Split` | a summand deciding between two others folds as the two folds, over the halves the test cuts |
| `UnionIntersection` | two sets that overlap, inclusion–exclusion at two sets: `op (fold s) (fold t) = op (fold (s ∪ t)) (fold (s ∩ t))` |
| `Pointwise` | a summand combined pointwise folds to the combination of the folds |
| `Swap` | a double fold does not care which of its two index sets is taken first |

## The transport layer

Carrying a fold from one index set to another. Every member answers the
same question — given a map between two index sets, when does a fold over
one equal a fold over the other? — and they differ in how the map's
faithfulness is presented. `ImageOffSupport` restricts to the support,
where its collision hypothesis makes the map injective, and then uses
`Image`. `Regroup` extends `Fibres` from the image to any containing
index set using `Superset`: every added fibre is empty.

| member | statement |
|---|---|
| `Image` | `f` injective on `s`: folding `g` over `image(f, s)` is folding `g ∘ f` over `s` |
| `ImageOffSupport` | the same with collisions allowed wherever the summand is the neutral |
| `Bijection` | a permutation of `s` does not move the fold |
| `Injection` | on a finite `s`, an injective self-map does not either — injective and surjective coincide there |
| `ReindexGeneral` | a correspondence between `s` and `t` carrying `f` to `g` equates their folds |
| `Reindex` | the same with the inverse written down, which is the form consumers have |
| `Restrict` | narrowing to the points a test accepts = silencing the summand off them |
| `Fibres` | grouping along a map's fibres and folding each group over the image = folding the whole |
| `Regroup` | the same grouping over any set containing the image; empty fibres contribute the neutral element |

## The indexed layer

The chapter's two readings of a structured index set — an interval of
numbers, and a dependent product. The interval laws are the recursion
along `m .. n` and the laws an indexed series computes with, each
proved once for every fold, so that a carrier (Σ over ℕ or ℝ, a
product, …) reads each in one line at its own operation. `Fubini`
regroups the finite set of dependent pairs by its first projection;
transport along the pairing map identifies each fibre with its
original index set.

| member | statement |
|---|---|
| `IntervalClauses` | the recursion clauses along `m .. n`, recursing on the upper bound: the clause pair every Σ over an interval computes with |
| `IntervalPoint` | a fold over `n .. n` is the summand's value at n |
| `PeelLeft` | when m ≤ n, the fold over `m .. n` is f(m) combined with the fold over `m + 1 .. n` |
| `PeelRight` | when 0 < n and m ≤ n, the fold over `m .. n` is the fold over `m .. n - 1` combined with f(n) |
| `Shift` | folding `λi. f(i + p)` over `m .. n` is folding f over `m + p .. n + p` |
| `IntervalCongruence` | summands agreeing between the bounds have the same fold |
| `IntervalEvenOdd` | the fold over `0 .. 2n + 1` is the fold of the even-indexed values `f(2k)` over `0 .. n` combined with the fold of the odd-indexed values `f(2k + 1)` over `0 .. n` — by induction, each step putting one even and one odd point on top |
| `Fubini` | a doubly-indexed family folds the same inward-first (each point's fibre, then across the base) or over all index pairs at once |
