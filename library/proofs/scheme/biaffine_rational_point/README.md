# biaffine_rational_point — the rational points of a biaffine datum: a point by its ideal in each chart, the chart it lies on, and its colengths

A rational point of a biaffine datum (scheme/lattice_pair) over a subfield
k is held by its ideal in each chart — the chart itself where the point
lies off it, the ideal of a k-rational point of the chart where it lies
on it (`rational_ideal`). On chart 0 the rational points are the
k-algebra maps A₀ → k; a point lies on both charts exactly when t does
not vanish at it, and then the ideal it generates in R is maximal and
meets each chart in the chart ideal. Its ideal pair is a lattice pair
inside the structure pair, and modulo the point's ideal a chart has
dimension one over k on a chart the point lies on and zero off it, the
overlap one exactly on both: a point on the overlap is counted on both
charts and once on the overlap, 1 + 1 − 1. The chart a point lies on, and
its ideal there, are read off whether its first component is all of A₀.

## Members

### The definitions

| Member | Statement |
|---|---|
| `BiaffineRationalPointDef` | `biaffine_rational_point(R, k, A₀, A₁, P)`: a k-rational point given by its ideal in each chart, the chart or the ideal of a k-rational point of it (`rational_ideal`) |
| `PointChartDef` | `point_chart(A₀, A₁, P)`: the chart P lies on, A₁ where P's first ideal is all of A₀ and A₀ otherwise |
| `PointIdealDef` | `point_ideal(A₀, P)`: P's ideal in that chart |

### Rational points

| Member | Statement |
|---|---|
| `RationalPointMaximal` | each chart ideal of a rational point is the chart or a maximal ideal of it |
| `RationalPointHomomorphism` | the rational points on chart 0 are the k-algebra maps φ : A₀ → k, the point being (ker φ, A₁ ∩ the ideal ker φ generates in R) |
| `RationalPointOverlap` | a point lies on both charts exactly when t ∉ fst(P); then the ideal it generates in R is maximal and meets each chart in the chart ideal |
| `RationalPointChartIdeals` | each chart set of a rational point is an ideal of its chart |
| `PointIdealLattice` | the ideal pair of a rational point is a lattice pair in R inside (A₀, A₁) |
| `RationalPointColengths` | over k, a chart modulo the point's ideal has dimension one on a chart the point lies on and zero off it; R modulo the generated ideal has dimension one exactly on both charts |
| `RationalPointSwap` | a rational point read with the charts swapped is a rational point |
| `RationalChartSeparate` | a rational point other than P does not lie inside P on chart 0 when P is proper there |
| `RationalPointsSeparate` | a rational point Q other than P lies inside P on no chart where P is proper |

### The chart of a point

| Member | Statement |
|---|---|
| `PointOffChartZero` | a point whose first ideal is all of A₀ lies on chart A₁, with ideal snd(P) there |
| `PointOnChartZero` | a point whose first ideal is not all of A₀ lies on chart A₀, with ideal fst(P) there |
| `RationalPointChart` | inside a field whose charts are subrings holding k, a rational point's chart is a subring holding k, where the point's ideal is the ideal of a k-rational point |
