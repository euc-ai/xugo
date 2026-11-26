# polynomial_optimization — polynomial extrema, lexicographic minimizers and the cube's positive bound over real closed fields

A nonempty bounded set defined by finitely many polynomial weak inequalities and equations has a point minimizing f and then q among the f-minimizers. The source is `real_polynomial_geometry.LexicographicSource`, stated on the property `lexicographic_minimum_property` of `semialgebraic_properties`: at a common degree bound it quantifies the coefficient blocks and the bound, and elementarity carries it from the reals to every real closed field. Two more properties are carried over the same way, each from its own real source: a polynomial in one variable, quantified as the tuple of its coefficients, attains its minimum on a nonempty closed interval (`IntervalMinimumSource`), whence both extrema; and a polynomial positive on the carrier cube has a positive lower bound there (`CubePositiveSource`). No topology on the target field is assumed.

The theorems stand apart from their properties. `real_polynomial_geometry` proves its sources on the properties `semialgebraic_properties` defines, and this chapter, like `polynomial_brouwer`, reads a source to carry it over, so the property chapter sits below the real one and the theorems above both.

| Member | Statement |
|---|---|
| `LexicographicMinimum` | Nonempty bounded closed polynomial constraints admit a primary and secondary minimizer. |
| `ClosedIntervalMinimum` | A univariate polynomial attains its minimum on a nonempty closed interval of any real closed field. |
| `ClosedIntervalExtrema` | A univariate polynomial attains its minimum and maximum on a nonempty closed interval of any real closed field. |
| `CubePositiveLowerBound` | Over a real closed field a polynomial positive on the carrier cube has a positive lower bound there. |
