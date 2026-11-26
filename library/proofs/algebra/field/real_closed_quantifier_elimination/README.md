# real_closed_quantifier_elimination — quantifier elimination over real closed fields without new free variables

One-variable elimination is obtained from uniform realizable-sign control, `uniform_sign_table.RealizableSignControl`: `OneVariableElimination`, and through it `QuantifierElimination`, stand on that theorem. The theorem for all formulas lifts it through first_order.QuantifierEliminationFromOne. Its existentially chosen output precedes every field on the fixed host type; different host types are handled by real_closed_field_transfer.

| Member | Statement |
|---|---|
| `SignVectorValue` | A quantifier-free formula is evaluated through the sign vector of its atom list. |
| `SignConditionFormula` | Every set of sign vectors of a parameter-polynomial list is cut out by a quantifier-free formula. |
| `OneVariableElimination` | Eliminate one existential without leaving its name or adding free names. |
| `QuantifierElimination` | Every ordered-ring formula has a uniform support-preserving quantifier-free equivalent over real closed fields. |
