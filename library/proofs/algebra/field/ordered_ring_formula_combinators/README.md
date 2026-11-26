# ordered_ring_formula_combinators — polynomial comparison formulas

Derived comparison formulas use only strict-negativity atoms: the weak inequality p ≤ q denies the atom of q − p, the equality is the two weak inequalities, and the true formula, which seeds first_order's finite conjunctions, denies that the zero polynomial is negative. Each is well formed on the variables of its polynomials. In an ordered field the atom of p − q holds exactly when the value of p lies below that of q, the weak inequality and the equality read the weak order and the equality of the two values, and the true formula holds everywhere.

| Member | Statement |
|---|---|
| `trueFormulaDef` | The true formula denies that the zero polynomial is negative; it seeds the finite conjunctions. |
| `LeFormulaDef` | The weak inequality p ≤ q is the negation of q < p. |
| `eqFormulaDef` | Equality is the conjunction of the two weak inequalities. |
| `OrderedTrueFormulaSupport` | The ordered true formula is a well-formed sentence. |
| `OrderedTrueFormulaHolds` | The ordered true formula holds in an ordered field at every environment. |
| `WeakInequalityFormulaSupport` | A weak inequality between integer polynomials is well formed and reads only their variables. |
| `OrderedEqualityFormulaSupport` | An ordered equation between integer polynomials is well formed and reads only their variables. |
| `StrictComparisonBridge` | The atom of a difference p − q expresses the strict order of the values of p and q. |
| `ComparisonBridge` | Derived comparison formulas express carrier weak order and equality. |
