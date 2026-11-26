# quadratic_twist — quadratic twisting of coefficients

A twist is only a pair of coefficients. All coordinate comparisons occur
in k²; no twisted function field is a public object. PointCountAffine, in
closed_point, is the sole bridge from an arbitrary model to coordinates,
and TwistTrace reads the two traces through it.

## Definitions

| Member | Meaning |
|---|---|
| `twistCoefficientsDef` | `twist_coefficients` |

## Theorems

| Member | Statement |
|---|---|
| `TwistSolutionBijection` | for e ≠ 0, (X,Y)↦(eX,e²Y) maps the solutions of the curve with the twisted coefficients one to one onto the solutions of y²=e f(x), where f(x)=x³+ax+b |
| `AffineSolutionsPairing` | for a nonsquare e and each x∈k, the equations y²=f(x) and y²=e f(x) have two solutions in total |
| `TwistCountSum` | The original and twisted affine solution counts sum to 2q. — card |
| `TwistTrace` | The two coefficient traces q−A and q−A_twist have opposite signs. — card |
