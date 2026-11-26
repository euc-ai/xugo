# ordered_field_polynomial — polynomials over an ordered field

A polynomial over an ordered field is read here through the order alone. Past some positive bound a monic polynomial is at least one, so a nonzero polynomial has the sign of its leading coefficient far to the right and that sign times (−1)^deg far to the left; and a pseudo-remainder taken with an even power of the divisor's leading coefficient keeps the dividend's sign at every root of the divisor's image in an ordered field. These facts need the order and not the intermediate-value axiom, so the chapter sits below real closed fields: real_closed_field reads the signs at infinity for its odd-degree roots, the Cohen–Hörmander step of the sign tables (parametric_sign_table.DerivativeRemainderStep) reads the signs at both ends, and the family that step reduces to over the parameter ring (uniform_sign_table.DerivativeRemainderFamily) reads the pseudo-remainders.

| Member | Statement |
|---|---|
| `MonicEventuallyAtLeastOne` | A monic polynomial over an ordered field is at least one past some positive bound. |
| `SignAtPositiveInfinity` | Past some positive bound a nonzero polynomial has the sign of its leading coefficient. |
| `SignsAtInfinity` | The leading coefficient and degree determine both eventual signs. |
| `SignsAtBothEnds` | Far to the right a nonzero polynomial has its leading sign, far to the left that sign times (−1)^deg. |
| `PseudoRemainderSigns` | A pseudo-remainder taken with an even power of the divisor's leading coefficient has the dividend's sign at every root of the divisor, in every ordered field the leading coefficient survives in. |
