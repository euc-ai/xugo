# polynomial_formula — integer polynomial atoms: their support, their values in carrier rings, and their reading in one variable over the parameter polynomials

The atoms are the finitely supported functions of the polynomial algebra over int_ring, with natural-number variable names. Their data contains no element of the model. Evaluation uses the canonical integer map and polynomial_algebra_evaluation; the same atoms support equality and strict-negativity interpretations in different theories.

A polynomial's negation and the difference of two are written coefficientwise, `λm. -p(m)` and `λm. p(m) - q(m)`. The difference is how the polynomial algebra writes its subtraction; the negation departs on purpose from the algebra's `fun_neg(int_neg, p)`, and PolynomialNegation and EvaluationNegation each read the two spellings equal off `fun_neg`'s definition (`function_module.FunNegDef`) before reading the algebra's laws.

| Member | Statement |
|---|---|
| `IntegerPolynomialDef` | Valid atomic polynomials have finite coefficient and monomial support. |
| `PolynomialVarsDef` | The variables appearing in a nonzero coefficient monomial. |
| `IntegerPolynomialEvalDef` | Evaluate integer coefficients through their canonical ring map. |
| `IntegerPolynomialRingDef` | The polynomial algebra over the integers on all natural-number variable names. |
| `FormulaValidDef` | A polynomial formula has valid polynomial atoms. |
| `FormulaVarsDef` | Free variables of a polynomial formula. |
| `FormulaClosedDef` | A sentence is well formed and has empty free-variable support. |
| `PolynomialListOverDef` | A finite polynomial list whose variable names lie in U. |
| `AtomList` | The atoms of a valid quantifier-free formula are listed by valid polynomials in its free variables. |
| `PolynomialVarsFinite` | A valid polynomial has finitely many variable names. |
| `FormulaVarsFinite` | A well-formed polynomial formula has finite free support. |
| `PolynomialOnOwnVariables` | A valid polynomial is a polynomial on its own variable names. |
| `PolynomialSupportFinite` | A valid polynomial is nonzero at finitely many monomials, each a monomial of its own variables. |
| `PolynomialOnVariables` | The polynomials on U are exactly the integer polynomials whose variables lie in U. |
| `PolynomialVariableSupport` | A variable is an integer polynomial in that variable alone. |
| `EvaluationInCarrier` | Evaluation at carrier-valued active variables lies in the carrier. |
| `EvaluationCongruence` | Evaluation depends only on the variables of nonzero monomials. |
| `EvaluationNatural` | Evaluation commutes with a ring homomorphism applied to the values. |
| `IntegerPolynomialEvalHom` | Evaluating integer polynomials at an environment carrier-valued on U is a ring homomorphism from the integer polynomials in the variables of U. |
| `VariableValue` | A variable evaluates to the environment's value at it. |
| `ZeroPolynomialValid` | The zero polynomial is a valid polynomial with no variable. |
| `ZeroPolynomialValue` | The zero polynomial evaluates to the zero of a ring. |
| `OnePolynomialSupport` | The one polynomial is an integer polynomial without variables. |
| `OnePolynomialValue` | The one polynomial evaluates to the one of a commutative ring. |
| `PolynomialNegation` | Negating the coefficients of a valid polynomial keeps it valid in the same variables. |
| `EvaluationNegation` | A polynomial with negated coefficients evaluates to the negated value. |
| `PolynomialDifference` | The difference of two valid polynomials is valid, its variables among theirs. |
| `EvaluationDifference` | The difference of two valid polynomials evaluates to the difference of their values. |
| `VariableFreeEvaluation` | A polynomial in which no variable occurs evaluates to the image of its constant coefficient. |

## Formulas read through a predicate

An atom read through a predicate P off the value of its polynomial in a ring R, `P(integer_polynomial_eval(R, ρ, p))`, gives the formulas over the carrier of R read through P; the chapter's table names these atoms `«predicateAtoms»(R, P)`, read at the type R is a ring on, so that `«predicateAtoms»(S, Q)` names those of a second ring S on another type. The ring formulas are those read through vanishing in a field's ring, and the ordered ones those read through negativity; their congruence, embedding, invariance and sentence transfer are the statements here at those predicates.

| Member | Statement |
|---|---|
| `PolynomialAtomLocal` | An atom reading a predicate off the value of its polynomial depends only on the polynomial's variables. |
| `PolynomialAtomEmbedding` | A ring homomorphism carrying one predicate to another embeds the atoms reading them off a polynomial's value. |
| `EnvironmentCongruence` | A formula read through a predicate takes one value at environments agreeing on its free variables. |
| `QuantifierFreeEmbedding` | A ring homomorphism carrying one predicate to another preserves and reflects the quantifier-free formulas read through them. |
| `OntoInvariant` | A ring homomorphism onto the target carrier carrying one predicate to another preserves every formula read through them. |
| `QuantifierFreeSentenceTransfer` | Two commutative rings whose predicates agree on the image of every integer agree on every closed quantifier-free formula read through them. |

## Polynomials in one variable over the others

The eliminations look at a polynomial as a polynomial in the eliminated variable v whose coefficients are polynomials in the remaining names. A monomial splits into a power of v and its lowering, the monomial with v's exponent zeroed, so evaluating p with v sent to x is evaluating its coefficients, each read at the other variables, as a univariate polynomial at x. The coefficients are polynomials on the other variables of p, finitely many of them nonzero.

| Member | Statement |
|---|---|
| `integerPolynomialCoefficientDef` | The coefficient of v^k in p, an integer polynomial in the other variables. |
| `MonomialLowered` | Zeroing the exponent of v in a monomial of S leaves a monomial of the other variables of S. |
| `MonomialAtUpdate` | A monomial evaluated with v sent to x is x to its exponent of v times its lowering, evaluated at ρ. |
| `CoefficientAtLowered` | The coefficient of v^m(v) at m with v's exponent zeroed is p's coefficient at m. |
| `CoefficientSupport` | The k-th coefficient in v is nonzero exactly at the lowerings of p's monomials of exponent k at v. |
| `CoefficientEvaluation` | Evaluating p with v at x is evaluating its specialized coefficients, as a univariate polynomial, at x. |
| `SpecializeOneVariable` | Fixing all but one variable gives a univariate carrier polynomial. |
| `CoefficientsOverParameters` | An integer polynomial is a univariate polynomial in v over the polynomials on its other variables. |

## The parameter ring

The integer polynomial ring operates as the polynomial algebra over the integers. The parameter polynomials are the polynomial algebra on U, `polynomial_algebra(int_ring, U)`, which holds exactly the integer polynomials whose variables lie in U (`PolynomialOnVariables`). They form a subring, and the integer polynomial ring restricted to them, `restrict_ring(integer_polynomial_ring, polynomial_algebra(int_ring, U))`, is `«parameterRing»(U)` in the chapter's table. A univariate polynomial g over them, `polynomial_over(integer_polynomial_ring.zero, polynomial_algebra(int_ring, U), g)`, is `«overParameters»(g)` in the chapter's table. Specializing them at an environment of a commutative ring R is a ring homomorphism (`IntegerPolynomialEvalHom`), which carries a univariate polynomial g over the parameters to one over R, its coefficients specialized: `«specialized»(R, ρ, g)` in the chapter's table. At a field F it is read at F's ring, `«specialized»(field_ring(F), ρ, g)`, whose value at a point x of F is `«value»(F, ρ, g, x)`; at the coefficient family of an integer polynomial p in v it is p's coefficients in v specialized, `«specialized»(R, ρ, integer_polynomial_coefficient(v, p))`. Specialization keeps the degree of g where its leading coefficient survives; where it vanishes, g specializes as its truncation below the degree. Specialization commutes with the formal derivative.

| Member | Statement |
|---|---|
| `IntegerPolynomialRingOperations` | The integer polynomial ring adds coefficientwise, has the zero function as zero, and multiplies with the one and product of the polynomial algebra over the integers. |
| `ParameterRing` | The ring of integer polynomials restricted to the polynomials on U is the polynomial algebra on U. |
| `ParameterRingCommutative` | The parameter ring is a commutative ring. |
| `ParameterPolynomialsSubring` | The polynomials on U form a subring of the integer polynomials. |
| `SpecializedPolynomial` | A polynomial over the parameters specializes, coefficient by coefficient, to a polynomial over the ring. |
| `SpecializedDerivative` | Specializing the parameters commutes with the formal derivative. |
| `SpecializedDegree` | Where its leading coefficient specializes to a nonzero element, a polynomial over the parameters keeps its degree. |
| `SpecializedTruncation` | Where its leading coefficient specializes to zero, a polynomial over the parameters specializes as its truncation below its degree. |
