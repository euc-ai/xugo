# real_closed_field — real closed fields defined by polynomial intermediate values

A real closed field is a structure over an ordered carrier field: `real_closed_field(F, lt)` projects to `ordered_field_on(F, lt)`, and its one axiom is the intermediate-value property for univariate polynomials. The chapter's theorems over a real closed field are laws of the structure. By the axiom a polynomial takes every value strictly between its values at two points somewhere strictly between them, so a polynomial injective on the carrier is strictly monotone there: the ordered-field law `ordered_field.IntermediateValueInjectiveMonotone`, read at the field. Rolle and the polynomial mean-value theorem are algebraic consequences, and so is the order: every positive element is a square, so a ring homomorphism out of a real closed field into an ordered field preserves and reflects it. The signs of a polynomial at infinity hold over any ordered field; they are proved in ordered_field_polynomial. This chapter does not use real topology, extrema, real closures or quantifier elimination.

| Member | Statement |
|---|---|
| `RealClosedField` | An ordered field in which every polynomial crossing from negative to positive has a root between the endpoints. |
| `OrderedFieldOn` | A real closed field is an ordered field. |
| `IntermediateValue` | A polynomial negative at one point and positive at a later one has a root between them. |
| `DownwardIntermediateValue` | A polynomial positive at one point and negative at a later one has a root between them. |
| `OppositeSignsRoot` | A polynomial with nonzero values of different signs at two points has a root between them. |
| `RootFreeIntervalSign` | A polynomial without roots on a closed interval has equal endpoint signs. |
| `InjectivePolynomialMonotone` | A polynomial in one variable injective on the carrier is strictly increasing or strictly decreasing there. |
| `EuclideanField` | A real closed field is a Euclidean field. |
| `PositiveSquareRoot` | Every positive element has a positive square root. |
| `HomomorphismOrderEmbedding` | A ring homomorphism from a real closed field to an ordered field is an order embedding. |
| `OddDegreeRoot` | Every polynomial of odd degree over a real closed field has a root in it: `odd_degree_roots(F)`. |
| `ConsecutiveRootsRolle` | Between consecutive roots of a polynomial lies a root of its derivative. |
| `RolleBetweenRoots` | Between two roots of a polynomial lies a root of its derivative. |
| `PolynomialRolle` | Equal polynomial endpoint values give an interior derivative root. |
| `PolynomialMeanValue` | A polynomial secant slope is an interior derivative value. |
| `DerivativeSignMonotone` | A polynomial changes by the sign its derivative keeps between two points. |
