# galois_good_fibres — a Galois cover of the line has a good open

A regular function field L over a finite field k, Galois over k(t), has a good open (scheme/galois_good_open): the chart of a primitive element. The argument runs from a primitive element z integral over k[t] to the chart C = k[t][z][1/a(t)], the points of C over each good base point, the group acting on them as a torsor, and the subgroups' quotients read off the same fibres, which together are the clauses of `galois_good_open` that `ChartGoodOpen` proves. `good_fibres.go` holds that argument at its full length, and is kept as one file for that reason.

## Good fibres

| Member | Statement |
|---|---|
| `GaloisPrimitiveElement` | L has a generator over k(t) whose minimal polynomial over k[t] is monic, separable and of degree card(G) |
| `SeparableChartDenominator` | A finite part of k(t)(z) lies in k[t][z] with one a(t) inverted, where F′ is a unit at every root of F |
| `ChartFacts` | The rings k[t], k[t][z] and C = k[t][z][1/a(t)] of a chart, and what each holds |
| `GaloisChartRing` | The chart is a commutative ring in L with fraction field L, finite over k[t] with a(t) inverted |
| `GaloisChartStable` | A chart holding every conjugate of z is kept by the group |
| `ChartPointDetermined` | A point of the chart is determined by its values at t and z |
| `PointExtendsAtRoot` | In a closed field a point of S extends to S[z] along a monic relation of least degree |
| `ChartFibreNonempty` | The chart has a point over each algebraic x with a(x) ≠ 0 |
| `PointSeparatesRoots` | A point of C is injective on roots where the derivative is a unit of C |
| `PointsOnOneOrbit` | Points agreeing at t and on the coefficients of the orbit polynomial differ by H |
| `InvariantChartGenerates` | The invariants of the chart hold k and t, and generate C with z |
| `OrbitPolynomial` | The orbit polynomial of z has its coefficients in the invariants |
| `OrbitPolynomialLeast` | A nonzero relation of z over the invariants has degree at least the size of the orbit |
| `ChartFibreTorsor` | G acts freely and transitively on a fibre of card(G) points |
| `InvariantFibreImage` | The fibre of C restricts onto the fibre of the invariants |
| `InvariantAgreement` | Two points agree on the invariants of H exactly when they differ by H |
| `ChartFibres` | The fibre clause of a good open, for the chart |
| `ChartGoodOpen` | The chart of a primitive element is a good open |
| `GaloisGoodFibresAreTorsors` | L, Galois over k(t), has a good open: the chart of an integral primitive element |
