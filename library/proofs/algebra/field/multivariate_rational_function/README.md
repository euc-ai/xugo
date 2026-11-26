# multivariate_rational_function — rational functions, generic points and sums-of-squares denominators

The rational function field is the existing fraction-field record of the multivariate polynomial algebra. Its points are fraction classes; polynomial coefficients embed as constant fractions and variables give the generic tuple. Formal reality follows by evaluating common denominators at a nonvanishing base point.

| Member | Statement |
|---|---|
| `RationalFunctionFieldDef` | The fraction field record of the polynomial algebra in n variables. |
| `PolynomialFractionDef` | A polynomial as its fraction with denominator one. |
| `rationalConstantDef` | A base coefficient as a constant rational function. |
| `genericPointDef` | The variable fractions below n, zero above n. |
| `RationalSOSDef` | A nonzero common denominator turns f into a finite sum of polynomial squares. |
| `RationalField` | The multivariate fraction-field record is a field with an injective coefficient embedding. — card |
| `NonzeroPolynomialValue` | A nonzero multivariate polynomial over an ordered field is nonzero at some finite tuple. — card |
| `RationalFormallyReal` | The rational function field over an ordered field is formally real. — card |
| `GenericPointEvaluation` | Evaluation at the generic variable fractions equals polynomial inclusion. — card |
| `ClearDenominators` | Rational sums of squares are exactly polynomial square identities after a nonzero common denominator. — card |
