# real_closed_instance — the real numbers as a real closed carrier field

The source real field enters the transfer theory through its ordered-field instance, which `real_ordered_instance` proves below continuity together with the reading of the weak order as ≤. This chapter adds the bridge from coefficient polynomials to real polynomial functions (`PolynomialFunctionBridge`). Polynomial continuity and the real intermediate-value theorem establish real closedness. This instance is a consumer of the abstract foundation, not a premise of its elimination theorem.

| Member | Statement |
|---|---|
| `PolynomialFunctionBridge` | A coefficient polynomial evaluates to a real polynomial function. |
| `PolynomialIntermediateValue` | A real polynomial negative at one point and positive at a later one has a root strictly between them. |
| `RealClosed` | The reals with their strict order are a real closed field. |
