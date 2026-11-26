# rational_point_bound — upper bounds on the rational points of a curve, an integral plane model and a plane equation over square fields

The bounds follow Bombieri's derivative-free method. The pole spaces at a regular rational point (regular_point) have the dimensions Euler Riemann–Roch gives, even on an integral model with singularities elsewhere. Distinct pole orders below the Frobenius scale give the Frobenius tensor a trivial kernel; an ordinary linear kernel followed by coefficient Frobenius provides a nonzero function vanishing at the other regular points. Counting its zeros bounds the regular points. The descent to plane equations fixes a Bezout certificate over k[t]: over each finite constant field its good locus consists of regular points, the bad fibres add a constant, and a solution of the equation is a point of the chart. A curve is stated over its own function field L; the plane bounds, which compare constant extensions inside one field M, read Bombieri's bound at a subfield K of M through smooth_curve's `InAmbient`.

## Members

| Member | Statement |
|---|---|
| `frobeniusTensorDef` | `frobenius_tensor`: ring_ops(A) → set(A) → set(A) → num → (prod(A, A) → A) → A |
| `frobeniusSwapDef` | `frobenius_swap`: ring_ops(A) → set(A) → set(A) → num → (prod(A, A) → A) → A |
| `FrobeniusCoefficient` | At a pair of E×F a coefficient with values in a field k of s² elements lies in k, and so does its s-th power, whose s-th power is the coefficient again |
| `FrobeniusTensorRows` | The sum over E×F of d(p)·fst(p)·snd(p)^s is Σ_x x·σ(g(x)), where g(x) = Σ_y σ(d(x, y))·y and σ is the s-th power |
| `FrobeniusTensorInjectivity` | The Frobenius tensor has trivial kernel: a coefficient function with values in k and tensor zero vanishes on E×F, when the pole orders on E are distinct and a < s |
| `FrobeniusTwistSum` | Over values in a field k of s² elements, the s-th power of Σ c·(u·v^s) is Σ c^s·(u^s·v) |
| `FrobeniusEntryPoles` | Bounds on the order of the poles of a pair of basis members, of their s-th powers and of the two twisted products |
| `FrobeniusEntryKernel` | With more pairs than the dimension bound, the products x^s y satisfy a nonzero relation with constant coefficients |
| `FrobeniusSwapEvaluation` | The tensor lies in the (a + s·b)-th pole space, and at a regular Q ≠ P the s-th power of its value is the value of the swap |
| `FrobeniusSwapKernel` | Rank-nullity gives a nonzero relation among the products x^s y with constant coefficients; coefficient Frobenius carries it to a coefficient function whose tensor is a nonzero section with poles of order at most a + s·b at P, vanishing at every other regular point |
| `TensorDimensionExcess` | Once s exceeds g² + 3g + 1, spaces of dimensions at least s - g and s + g + 1 have a tensor product larger than s(s - 1) + (s + 2g) + 1 |
| `BombieriUpperRegularPoints` | A curve of genus g over a field of s² elements with g² + 3g + 1 < s has at most s² + (2g + 1)s regular rational points |
| `PlaneModelHasCertificate` | An integral plane model has a Bezout certificate UF + VF′ = a(t) over k[t], with a nonzero over k |
| `PlaneModelChartBound` | Given a certificate, over a finite l with s² elements and s > g² + 3g + 1 the first chart has at most s² + (2g + 1)s + d(e + 1) points in l |
| `IntegralPlaneModelSquareFieldUpperBound` | An integral plane model has at most card(l) + B·s points in every finite constant extension l with s² elements above a fixed threshold |
| `PlaneEquationSquareFieldUpperBound` | An absolutely irreducible plane equation has at most card(l) + B·s solutions in every large finite field l of s² elements over k |
