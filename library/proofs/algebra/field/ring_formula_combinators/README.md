# ring_formula_combinators — polynomial equations and the true formula over fields

Derived ring formulas use only vanishing atoms: an equation is the atom of a difference, and the true formula is the atom of the zero polynomial. Each is well formed on the variables of its polynomials, and in a field the equation holds exactly when its two sides take one value, the true formula everywhere.

| Member | Statement |
|---|---|
| `ringTrueFormulaDef` | The true formula is the atom of the zero polynomial. |
| `ringEqualityFormulaDef` | Equality of two polynomial expressions is one difference atom. |
| `RingTrueFormulaSupport` | The true formula is a well-formed atom with no free variables. |
| `RingTrueFormulaHolds` | The true formula holds in every field at every environment. |
| `RingEqualityFormulaSupport` | The equation between two integer polynomials is a well-formed atom whose variables are among theirs. |
| `RingEqualityFormulaEval` | Over a field, the equation of two integer polynomials holds exactly when they take one value. |
