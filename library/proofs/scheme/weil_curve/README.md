# weil_curve — the full Weil statements for smooth finite-field curves

The same integer zeta numerator is used throughout the trace formula, the reciprocal-coefficient and reciprocal-root modulus statements. Coarse bounds after every admissible constant extension combine with finite-spectrum growth to give the Riemann hypothesis and all extension point bounds. The conjectures themselves are one predicate, `weil_conjectures(q, g, N, P)`, on a point-count function N and a numerator P, stated once; the theorems say where it holds — for a smooth curve presented by two charts, for a projective curve cut out by equations (whose projective points the presentation counts) inside a closed field holding a point transcendental over its constants, and for a smooth projective equation curve over any finite field. A finite field k sits inside an algebraically closed field M (its algebraic closure, for one), and M may hold no transcendental point. So the curve is carried along the embedding of M into the algebraic closure of M(x) (algebra/field/rational_function_field, scheme/projective_transfer), where the presentation's transcendental point exists. The carrying keeps q, the genus and every count, so the predicate holds for every smooth projective equation curve over every finite field, with no hypothesis but the closed field holding k and the curve's own. Throughout, M is the ambient closed field, K the function field inside it, k the finite field of constants, t the parameter, A₀ and A₁ the two charts and A₀₁ their overlap.

## Definitions

| Member | Meaning |
|---|---|
| `WeilConjecturesDef` | `weil_conjectures(q, g, N, P)`: P is the Weil numerator for the point counts N of a curve of genus g over q elements — integer coefficients, constant term one, degree 2g, top coefficient q^g, $(1 - T)(1 - qT) \cdot \exp\left(\sum N(m) \frac{T^m}{m}\right) = P$, reciprocal coefficients, 2g reciprocal roots of modulus √q with power sums q^m + 1 − N(m), and $\lvert N(m) - (q^m + 1) \rvert \le 2g \cdot \sqrt{q^m}$ for every m > 0 |

## Members

| Member | Statement |
|---|---|
| `PowerSumIsPointDefect` | For reciprocal roots of a smooth finite curve and m > 0, the modulus of the m-th power sum is the distance of the point count N(m) from q^m + 1 |
| `RootOfConstantsPositive` | For a smooth curve over a finite field of q elements, √q is positive |
| `CurveReciprocalRootsUpperModulus` | Every reciprocal root of a smooth curve over a finite field has modulus at most √q |
| `RiemannHypothesisGeneralCurves` | For a smooth curve of genus g over a finite field of q elements, the 2g reciprocal roots of the zeta numerator have modulus √q and its zeros have modulus 1/√q |
| `HasseWeilAllExtensions` | For every m > 0, the number of points over the extension of degree m lies within $2g \cdot \sqrt{q^m}$ of q^m + 1 |
| `WeilConjecturesOfAgreeingCounts` | weil_conjectures(q, g, N, P) reads the counts N at positive m only: if N₁(m) = N(m) for every m > 0, then weil_conjectures(q, g, N₁, P) holds with the same q, g and P |
| `FullWeilConjecturesCurves` | For a smooth curve of genus g over a field k of q elements, its point counts N(m) over the extensions of degree m, its genus and its zeta numerator P satisfy weil_conjectures(q, g, N, P), and its effective-divisor series is the formal exponential of N(m)/m |
| `FullWeilProjectiveEquationCurves` | A smooth projective curve cut out by equations over a finite field k, inside a closed field holding a point transcendental over k, has a presentation by two charts of the curve's genus whose counts are the numbers of the curve's projective points over every finite extension of k, and the curve's genus and projective counts satisfy weil_conjectures with the presentation's zeta numerator |
| `HasseWeilClosedPoints` | For a smooth curve over a finite field of q elements, the closed points of degree dividing m weighted by their degrees number q^m + 1 up to $2g \cdot \sqrt{q^m}$, for every m > 0: HasseWeilAllExtensions with the extension count read as the curve's own closed points |
| `WeilConjecturesOverFiniteFields` | For every algebraically closed field M and every finite subfield k of it, every smooth projective equation curve over k satisfies weil_conjectures at its own genus and its numbers of projective points over the fields of q^m elements, q = \|k\|, for some numerator P |
