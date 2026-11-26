# nat_sum — Σ over ℕ

`nat_sum` is the fold of natural addition over a finite index set:
`nat_sum(s, f) = iterated_op (+) s f`. The chapter is the fold mechanism of
`iterate/monoidal` read through ℕ's additive algebra, and it says of
`nat_sum` only what its consumers need:

- **The bridge** — natural addition folds: it commutes, associates,
  and zero is its neutral element (`monoidal_op(+)`, `neutral_elem(+) = 0`).
  Once these two facts are in hand every law of the mechanism
  instantiates at `+`; together they make `(+, 0)` a commutative monoid
  (`CommMonoidNatAdd`), the form the module and polynomial sums read.
- **The mechanism's laws at ℕ** — congruence (summands agreeing on the
  index set give the same sum), the sum over a disjoint union of finite
  sets (and its reading where the union is given as an equation),
  restriction (summing over the indices satisfying a predicate is
  summing a summand silenced off it), reindexing along a map one-to-one
  on the index set, two sums over one finite index set adding termwise,
  a factor common to every term coming out (multiplying by it keeps 0
  and addition, so it passes through the fold), enlarging the index set
  past points where the summand vanishes (`Superset`), exchanging two
  sums over finite index sets (`Swap`), and the recursion
  clauses: the
  empty sum is 0, and inserting a point into a finite index set either
  changes nothing, because the point was already there, or contributes
  its own value. The recursion below a bound (`BelowClauses`) reads
  `monoidal.BelowClauses` at natural addition as well.
- **The ℕ-proper readings** — a digit sum $\sum_{i \in s} B^i \cdot b(i)$ split
  at any place `n` into the digits below and the digits from `n` on,
  the latter carrying the factor `B^n`, and a finite sum vanishing
  exactly when every term does (`EqZero`).
- **The interval calculus** — the fold mechanism's interval laws read
  at `+`, one line each: the recursion on the upper
  bound, a sum over one point, peeling the lowest or the highest term
  off, shifting every index by p, and two summands agreeing between the
  bounds giving one sum.
- **Common divisors and multiples** — a number dividing every term of a
  finite sum divides the sum: divisibility holds of 0 and survives
  addition, so it survives the fold. Beside it, a law with no
  sum in it: the positive members of a finite set of naturals have a
  positive common multiple (`FinitePositiveCommonMultiple`), each member
  adjoined by multiplying the multiple already obtained.
- **Counting** — the members of the table below. Summing 1 counts a
  finite set (`SumOfOnes`); a finite set related uniquely into T, with
  w(y) of its points over each y, has $\sum_{y \in T} w(y)$ points
  (`CardByFibres`); a term of a finite sum is at most the sum
  (`TermLeSum`), and two equal sums, one termwise below the other, agree
  term by term (`SumLeEqTermwise`); with no sum in its statement, a set
  over a finite T whose fibres have at most n points each is finite, with
  at most card(T)·n points (`CardFibresBound`).
  The union of a finite family of pairwise disjoint finite sets is
  counted by the sets it falls into (`CardOfDisjointFamily`). The
  counting laws also treat a constant sum (`SumConst`),
  the count of a predicate as the sum of its indicator
  (`CountByIndicator`), and a relation counted by rows or by columns
  (`DoubleCounting`). Beside it is the parity that counting an incidence
  both ways gives, doors and rooms (`DoorsAndRoomsParity`): faces and
  simplices under an incidence, each boundary face in one simplex and
  every other face in two, each full simplex holding one door and every
  other none or two, have an odd number of full simplices when the
  boundary doors are odd in number. Kuhn's lemma (`cartesian/kuhn_labelling`) reads
  it at the Kuhn simplices. `OddSumIffOddCount` supplies the parity
  comparison for these two counts.

The sieve (`InclusionExclusion`) counts points and the index subsets
whose intersections contain them. For a covered point, toggling one covering
index pairs its even and odd choices. An uncovered point contributes
only through the empty subset.

`TermLeSum` separates one term with `monoidal.Delete` and uses the
natural bound `m ≤ m + n`. `CardByFibres` chooses the map specified by
the relation, identifies its fibre sums with w, and applies
`monoidal.Regroup` over T.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.

| Member | Statement |
|---|---|
| `SumOfOnes` | Summing 1 over a finite set counts it |
| `CardByFibres` | A finite set related uniquely into T, with w(y) elements related to each y in T, has $\sum_{y \in T} w(y)$ elements |
| `CardOfDisjointFamily` | The union of a finite family of pairwise disjoint finite sets has as many points as the sets have between them |
| `TermLeSum` | A term of a finite sum of naturals is at most the sum |
| `SumLeEqTermwise` | Two equal sums over a finite set, one at most the other term by term, agree at every term |
| `CardFibresBound` | A set over a finite set with bounded fibres is finite, with at most the product of points |
| `SumConst` | A constant summed over a finite set is the set's size times the constant |
| `CountByIndicator` | The points of a finite set satisfying P are counted by summing P's indicator |
| `DoubleCounting` | A relation between two finite sets is counted by its rows or by its columns |
| `OddSumIffOddCount` | A finite sum of naturals is odd exactly when an odd number of its terms are odd |
| `EvenOddSubsetCounts` | A nonempty finite set has equally many even and odd subsets |
| `InclusionExclusion` | Over a finite universe, the even intersection counts sum to the number of uncovered points plus the odd intersection counts |
| `DoorsAndRoomsParity` | Faces and simplices under an incidence, one simplex per boundary face and two per other face, one door in a full simplex and none or two in any other: an odd number of boundary doors ⇒ an odd number of full simplices |
