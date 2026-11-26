# algebraically_closed_quantifier_elimination — uniform quantifier elimination for algebraically closed fields

The one-variable algebra decides one system at a time: equations and one inequation in the eliminated variable, with coefficients that are polynomials in the parameters. It inducts on the formal degrees, branches on whether a leading coefficient specializes to zero, and reduces two equations by pseudo-division. A root of one equation avoiding the inequation is characterized by nondivisibility of a bounded power (`algebraic_closure.RootAvoidance`, beside the one-variable Nullstellensatz there), and so, under a homomorphism keeping the equation's leading coefficient, by the image of a pseudo-remainder (`algebraic_closure.PseudoRemainderDecision`). The zero patterns a list of polynomials takes along the variable are then decided too (`ParameterizedZeroPatterns`); a quantifier-free formula in the parameters cuts out the patterns that admit a solution (`ZeroConditionFormula`), which eliminates one existential (`OneVariableElimination`), and `first_order.QuantifierEliminationFromOne` lifts that elimination to every formula (`QuantifierElimination`). The result is uniform across characteristics on the fixed host type.

The parameter polynomials are the polynomial algebra on `U`, `polynomial_algebra(int_ring, U)`. `polynomial_formula`'s table says that `f` is a univariate polynomial over them, `«overParameters»(f)`, and names such a polynomial `p` specialized at `ρ` in a ring, read here at a field's ring, `«specialized»(field_ring(F), ρ, p)`, and its value at `x`, `«value»(F, ρ, p, x)`. The chapter's own table names whether that value is nonzero somewhere, `«nonzeroSomewhere»(p)`, and whether the first `n` equations `g(j)` and the inequation `h` have a common solution, `«system»(n, g, h)`; and the models a decision ranges over, the algebraically closed fields with `U` assigned, `«models»`, and those where a parameter polynomial `c` specializes to zero or does not, `«vanishes»(c)` and `«survives»(c)`. The zero pattern of a list `E` decides a property `Φ` of the models `M`, `zero_pattern_decides(E, M, Φ)`, when it determines `Φ` at every model of `M`, and `Φ` is decided by zero patterns, `decided_by_zero_patterns(U, M, Φ)`, when some list of parameter polynomials decides it; the polynomials over a field are read from `polynomial_division` as `«fieldPolynomials»`. The parameter ring and its specialization at an environment are `polynomial_formula`'s; pseudo-division and its remainder's divisibility are `polynomial_division`'s, the remainder's roots `polynomial_roots`', and the specialization of a truncation `polynomial_formula`'s.

## Zero patterns: deciding a parametric system

| Member | Statement |
|---|---|
| `zeroPatternDef` | The zero pattern of a list of polynomials at a field and an environment: the truth values of their atoms, ⊤ where the polynomial vanishes and ⊥ where it does not. |
| `zeroPatternDecidesDef` | The zero pattern of a list decides a property on a class of models when some set of patterns has the property hold exactly where the list's zero pattern lies in the set. |
| `decidedByZeroPatternsDef` | A property is decided by zero patterns on a class of models when the zero pattern of some list of parameter polynomials decides it there. |
| `ModelSpecialization` | An algebraically closed field with the variables U assigned is a field, into which specialization is a ring homomorphism from the parameter polynomials that keeps zero. |
| `NoEquationDecision` | With no equation, whether h is nonzero somewhere is decided by the zero pattern of finitely many parameter polynomials. |
| `ZeroPatternAgreement` | Two zero patterns of one list are equal exactly when every member vanishes at both or at neither. |
| `DecisionByCases` | A property decided by zero patterns where a parameter polynomial specializes to zero, and where it does not, is decided by zero patterns. |
| `DecisionByEquivalence` | A property that agrees, on a class of models inside one where another property is decided by zero patterns, with that property is decided there. |
| `SingleEquationDecision` | Whether one equation and one inequation have a common solution is decided by the zero pattern of finitely many parameter polynomials. |
| `PairReduction` | A system of k + 2 equations is decided once every system of k + 1 equations is. |
| `ParameterizedSystemDecision` | Whether equations and one inequation in v have a common solution is decided by the zero pattern of finitely many parameter polynomials. |
| `DecisionByLargerList` | On any class of models, a property the zero pattern of a list decides is decided by the zero pattern of any list holding its members. |
| `ParameterizedZeroPatterns` | The zero patterns a list of polynomials takes along v are uniformly determined by the zero pattern of finitely many parameter polynomials. |

## Formulas: eliminating the quantifiers

| Member | Statement |
|---|---|
| `ZeroPatternValue` | A quantifier-free formula takes the value the zero pattern of its atoms gives it. |
| `ZeroConditionFormula` | Every set of zero patterns of a list of valid polynomials is cut out by a valid quantifier-free formula in their variables. |
| `OneVariableElimination` | Eliminate one existential over algebraically closed fields without adding free variables. |
| `QuantifierElimination` | Every ring formula has a uniform support-preserving quantifier-free equivalent over algebraically closed fields. |
