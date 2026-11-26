# field_trace — finite-set traces, separable trace pairing and the inverse Gram basis

The trace of a linear map is the sum of its diagonal coordinates in a finite set basis, supplied by algebra/module/module_dimension. No enumeration or matrix is chosen. For a finite extension L/K, field_trace is the trace of multiplication on L.

For a simple separable extension L=K(y), work over L in the ordinary polynomial quotient L[T]/(μ). The cofactor $q = \frac{\mu}{T-y}$ gives $e = \frac{q(T)}{\mu'(y)}$, an idempotent with one-dimensional image and trace one. Comparing quotient power coordinates with the field power basis gives the trace identity, nondegeneracy and Euler's dual basis. The quotient uses algebra/ring/quotient_ring; it imports no cotangent chapter.

## Members

### Definitions

| Member | Statement |
|---|---|
| `FieldTraceDef` | The field trace is the trace of multiplication over the base field. |
| `traceQuotientModuleDef` | The polynomial quotient by a principal ideal, as a module under constant classes. |
| `traceCofactorDef` | The polynomial cofactor of T−y in the minimal polynomial. |
| `traceIdempotentDef` | The cofactor class scaled by the inverse derivative value. |

### Trace

| Member | Statement |
|---|---|
| `FieldTraceFromBasis` | A finite basis of the extension computes the field trace. |
| `FieldTraceLinear` | The field trace of a finite extension is a base-field linear functional. |
| `TracePairingBilinear` | The trace pairing (x, y) ↦ Tr(x * y) is a symmetric base-field bilinear pairing |
| `FieldTraceOfScalar` | A base scalar has trace equal to the extension degree times that scalar. |
| `CharZeroTraceNondegenerate` | A finite characteristic-zero extension has positive degree and a nondegenerate trace pairing |
| `FieldTraceInSubring` | A common integral and field basis puts the trace back in the coefficient subring. — card |

### Quotient

| Member | Statement |
|---|---|
| `PolynomialQuotientPowerBasis` | Short monomial classes form a basis of a positive-degree monic polynomial quotient. — card |

### Nondegenerate

| Member | Statement |
|---|---|
| `LinearFactorQuotient` | The minimal polynomial factors by T−y with its monic cofactor. — card |
| `CofactorAtRoot` | The cofactor at y is the derivative of the minimal polynomial at y. — card |
| `CofactorAtRootUnit` | Separability makes the derivative value a nonzero field element. — card |
| `CofactorCoefficients` | The cofactor coefficients satisfy the descending monic recurrence. — card |
| `IdempotentAnnihilatesLinear` | Multiplication by the variable on the idempotent agrees with multiplication by y. — card |
| `IdempotentIsIdempotent` | The scaled cofactor class is an idempotent. — card |
| `IdempotentImageIsLine` | The idempotent is nonzero and its multiplication image is a line. — card |
| `IdempotentTraceOne` | Multiplication by the trace idempotent has trace one. — card |
| `QuotientPowerTraceAgrees` | Variable powers in the polynomial quotient and generator powers in the field have the same trace. — card |
| `TraceIdentityPower` | The cofactor-weighted trace identity holds on every power of the primitive element. — card |
| `TraceIdentity` | The cofactor-weighted trace identity reconstructs every field element. — card |
| `TraceNondegenerate` | Vanishing trace pairings against the power basis force a field element to vanish. — card |
| `TraceDualBasis` | The scaled cofactor coefficients are trace-dual to the power basis. — card |
| `TraceDualityIso` | Trace pairing identifies the extension with its base-field linear dual. — card |
| `CofactorCoefficientsBasis` | Cofactor coefficients form a subring basis of the monogenic algebra. — card |
