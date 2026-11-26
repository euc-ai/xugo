# twist_quotient_bound — point counts of the fixed fields of subgroups, before and after base change

The invariant chart of a subgroup H of a good open is a model of the fixed field K of H: finite over k[t] with the denominator inverted, with K as its field of fractions, and it agrees with a plane model of K off the zeros of one polynomial, so the two count the same points up to the fibres removed. Its points in the field of Q elements are the evaluations twisted over H, counted by scheme/twisted_count, each bounded above by scheme/fixed_twist_models; averaging over H and over the whole group gives K, over a square field, Q + 1 + O(√Q) rational points (`QuotientTwoSidedCoarseBound`). Base change to a larger field of constants carries that bound to every admissible degree (`CoarseBoundAfterAdmissibleBaseChange`), which scheme/weil_curve reads.

## The invariant chart

| Member | Statement |
|---|---|
| `InvariantChartRing` | The invariant chart of H is C ∩ K, a subring of K holding k, t and k[t] with the denominator inverted |
| `InvariantChartFractions` | The fixed field K of H is the fraction field of its invariant chart |
| `InvariantChartFinite` | The invariant chart is finite over k[t] with the denominator inverted |
| `InvariantPointsOverBase` | The invariant chart has at most \|G\| points in a finite subfield over each value of t |
| `PlaneChartMeetsInvariantChart` | A plane model of K and the invariant chart agree off the zeros of one nonzero polynomial over k |
| `InvariantChartCountAgrees` | The rational count of a model of K and the points of the invariant chart differ by a bound independent of the field |

## The two-sided bound

| Member | Statement |
|---|---|
| `GoodBaseCountLower` | All but deg a points of the field of card(k)^m elements are good base points |
| `InvariantChartPointsNearPower` | Over a square field the invariant chart has Q + O(√Q) points in the field of Q elements |
| `QuotientTwoSidedCoarseBound` | Over a square field the fixed field of H has Q + 1 + O(√Q) rational points |

## After base change

| Member | Statement |
|---|---|
| `ExactGaloisClosure` | A separating parameter, a finite Galois closure and its exact constants, with a geometric group of positive order |
| `ExtendedConstantsData` | Extending the constants to q^R keeps regularity and Galois data, and K·c is the fixed field of a subgroup |
| `SeparatingModelCoarseBound` | A plane model over a separating parameter carries the two-sided bound |
| `CoarseBoundAtExtendedConstants` | For a fixed even R divisible by r, the bound at R·m along admissible m |
| `AdmissibleExponent` | 1 + h·n is positive, at least n, and one more than a multiple of h |
| `CoarseBoundAfterAdmissibleBaseChange` | r the exact-constant degree of a finite Galois closure and h₀ twice its geometric group order bound the count at R(1 + h₀ n) for every positive R divisible by 2r |
