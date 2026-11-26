# semialgebraic_properties — polynomial properties of ordered fields at a degree bound

Each property speaks of the polynomials of bounded degree over an ordered field: of degree at most d in a fixed number of variables, or in one variable with at most n coefficients. The sets the properties speak of — a constraint set, the carrier cube 0 ≤ x(i) ≤ 1, the box −M ≤ x(i) ≤ M of a bound M — are cut out by polynomial equations and weak inequalities, which is what makes the properties semialgebraic, and once the degree is bounded each is a first-order statement: it quantifies the coefficients. Each is true over ℝ, where real analysis proves it (`real_polynomial_geometry` states it at the reals), and is carried to every real closed field by elementarity. The constraint set, its box bound and the lexicographic minimizer are the notions the lexicographic minimum is stated with, the carrier cube is the set the Brouwer and cube properties speak of, and the interval minimum speaks of a closed interval of the field itself.

| Member | Statement |
|---|---|
| `ConstraintSetDef` | The normalized tuples satisfying the closed polynomial constraints. |
| `BoundedSetDef` | A positive carrier element bounds every active coordinate of the set. |
| `LexMinimizerDef` | Minimize f first, then minimize q among all primary minimizers; uniqueness is not asserted. |
| `LexPropertyDef` | The degree-bounded lexicographic minimum statement universal in all coefficient data. |
| `CarrierCubeDef` | The carrier cube: the n-tuples of carrier points with every coordinate between 0 and 1. |
| `BrouwerPropertyDef` | Every degree-bounded polynomial self-map of the cube has a fixed point. |
| `CubePositiveBoundPropertyDef` | The degree-bounded statement that a polynomial positive on the carrier cube has a positive lower bound there. |
| `IntervalMinimumPropertyDef` | The statement that a polynomial in one variable with at most n coefficients attains its minimum on every nonempty closed interval. |
