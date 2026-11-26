# real_polynomial_geometry — finite-dimensional polynomial continuity, compactness and real extremum sources

Real polynomial geometry supplies the analytic source theorems for transfer. Compactness is proved in every finite dimension; polynomial extrema are obtained on compact nonempty sets. The sources take all polynomial coefficients universally, so each can be transported as a sentence.

The chapter works at ℝ: a statement spells `vec⟨n⟩(u)` and `dist⟨n⟩(u, v)` with the real ring's components implicit, and a numeral `&k` is a real one.

## Reading the real field

| Member | Statement |
|---|---|
| `RealRingTuple` | A tuple of reals of length n is an n-vector. |
| `RealCarrierCube` | The carrier cube of ℝ is the unit cube. |

## Continuity

| Member | Statement |
|---|---|
| `PolynomialContinuous` | Multivariate real polynomial functions are continuous in every finite dimension. |
| `PolynomialNearby` | A polynomial below n is ε-δ continuous at every point of ℝⁿ. |
| `PolynomialMapContinuous` | A normalized multivariate real polynomial map is continuous. |

## Compactness and extrema

| Member | Statement |
|---|---|
| `BoxAppendImage` | The box in ℝⁿ⁺¹ is the image of the box in ℝⁿ times ⟦−M, M⟧ under appending a coordinate. |
| `BoxCompact` | Every closed real coordinate box is compact. |
| `ClosedConstraintsCompact` | A bounded set cut out by closed polynomial constraints is compact over the reals. |
| `CompactPolynomialMinimum` | A real polynomial attains its minimum on a nonempty compact set. |

## The real sources

| Member | Statement |
|---|---|
| `LexicographicSource` | The real field satisfies every degree-bounded lexicographic minimum statement. |
| `BrouwerSource` | The real cube has the polynomial fixed-point property in every dimension and degree. |
| `CubePositiveSource` | Over the reals a polynomial of bounded degree positive on the carrier cube has a positive lower bound there, in every dimension. |
| `IntervalMinimumSource` | Over the reals a polynomial in one variable with at most n coefficients attains its minimum on every nonempty closed interval, for every n. |
