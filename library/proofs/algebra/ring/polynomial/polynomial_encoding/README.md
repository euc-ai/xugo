# polynomial_encoding — finite coefficient slots and polynomial formulas in arbitrary dimension and degree, and polynomials determined by their values

Finite tuples are zero-padded and have carrier-valued active coordinates. Total-degree-bounded monomials have a fixed distinct listing depending only on dimension and degree, and a monomial's slot is its position in that listing. Coefficient slots and coordinate slots are natural-number blocks of an environment: a coefficient block decodes to a polynomial and a coordinate block to a tuple. A polynomial's value at a tuple is its evaluation along the identity coefficient map, and a polynomial in one variable is a polynomial in the variable 0, read at a tuple's first coordinate. Dimensions and degree bounds are natural-number parameters of the statements, never types.

| Member | Statement |
|---|---|
| `RingTupleDef` | A finite tuple is carrier-valued below n and padded by the ring zero above it. |
| `BoundedMonomialsDef` | Monomials in n variables of total degree at most d. |
| `monomialListingDef` | Choose a distinct finite listing of the bounded monomials. |
| `monomialSlotDef` | The index below its length at which the fixed listing holds a monomial, specified only on the bounded monomials. |
| `coefficientCountDef` | The number of coefficient slots for a degree-bounded polynomial. |
| `PolynomialBoundDef` | A polynomial in n variables supported in total degree at most d. |
| `PolynomialValueDef` | Polynomial evaluation along the identity coefficient map. |
| `UnivariatePolynomialValue` | A polynomial in one variable is a polynomial in the variable 0 taking its values at first coordinates. |
| `polynomialCodeDef` | An integer polynomial whose coefficient slots and coordinate slots are variables. |
| `univariateCodeDef` | An integer polynomial in one coordinate slot whose coefficient slots are a block of variables. |
| `decodePolynomialDef` | Substitute a coefficient block to obtain a polynomial over the target ring. |
| `DecodePolynomialsDef` | Decode consecutive coefficient blocks from a slot on, the j-th polynomial from the j-th block. |
| `DecodeTupleDef` | Read a coordinate block as a zero-padded tuple. |
| `EncodePolynomialDef` | Write a polynomial's coefficients into a block of an environment, slot by slot. |
| `BoundedMonomialsFinite` | There are finitely many monomials in bounded dimension and degree. |
| `MonomialSlots` | The fixed monomial listing gives distinct bounded coefficient slots. |
| `BoundedMonomialsAreMonomials` | A bounded monomial is a monomial of the variables below n. |

## Decoding

A decoded tuple reads the environment on its block and is zero past it; a decoded polynomial reads the environment at the slot of each bounded monomial and is zero at every other monomial. What either decodes to depends on the environment on its block alone, and a ring homomorphism applied to the environment is applied to what its blocks decode to.

| Member | Statement |
|---|---|
| `DecodeTupleMonomialValue` | A bounded monomial at a decoded coordinate tuple is the product of the environment's coordinate values raised to its exponents. |
| `DecodeTupleRingTuple` | A coordinate block of a carrier-valued environment decodes to a ring tuple. |
| `DecodeTupleApart` | Substituting a block apart from a coordinate block leaves the tuple decoded there unchanged. |
| `DecodeUpdatedTuple` | Decoding a coordinate block after substituting a ring tuple there gives the tuple back. |
| `DecodeCongruence` | The polynomial decoded from a coefficient block depends only on the environment on that block. |
| `DecodeTupleCongruence` | The tuple decoded from a coordinate block depends only on the environment on that block. |
| `DecodePolynomialsCongruence` | The polynomials decoded from consecutive blocks depend only on the environment on those blocks. |
| `DecodePolynomialBound` | The polynomial decoded from a carrier-valued block has degree at most d. |
| `DecodeImage` | Decoding commutes with a ring homomorphism applied to the environment. |
| `DecodeTupleImage` | Decoding a coordinate block commutes with a ring homomorphism applied to the environment. |

## Encoding

Encoding writes a polynomial's coefficients into a block, slot by slot, and decoding that block gives the polynomial back. A family of k polynomials is written into k consecutive blocks from c, each member over the environment the earlier ones left; the environment is unchanged outside the blocks, and each member is decoded from its own block.

| Member | Statement |
|---|---|
| `DecodeEncode` | Decoding the block a polynomial supported in the bounded monomials was encoded in gives the polynomial back. |
| `EncodeInCarrier` | Encoding a polynomial over the carrier keeps a carrier value of the environment a carrier value. |
| `encodePolynomialsDef` | Write the coefficients of the first k members of a family into k consecutive blocks from c, each over the environment the earlier members left. |
| `EncodePolynomialsOutside` | Encoding a family leaves the environment as it was outside its blocks. |
| `EncodePolynomialsInCarrier` | Encoding a family of polynomials over the carrier keeps a carrier value of the environment a carrier value. |
| `DecodeEncodePolynomials` | The members of a family encoded from c are decoded from their blocks. |

## Codes

The polynomial code of dimension n and degree d is an integer polynomial in the variables of a coefficient block and a coordinate block: the sum over the bounded monomials of the coefficient variable at the monomial's slot times the monomial in the coordinate variables. Evaluating it at an environment substitutes the coefficients, then the coordinates. A code's variables lie below the end of its two blocks. The univariate code is the same in one variable, its coefficient block read as a tuple: a polynomial in one variable with at most n coefficients is a ring tuple of length n, and the code evaluates to its polynomial_eval at the coordinate slot's value.

| Member | Statement |
|---|---|
| `CodeTermsInSlots` | The coordinate and coefficient variables of a polynomial code, the powers, products and terms built from them are polynomials in its slots. |
| `PolynomialCodeSupport` | Polynomial codes use only their coefficient and coordinate blocks. |
| `CodeSupportBelow` | A polynomial code's variables lie below any k its two blocks end by. |
| `TwoStageEvaluation` | Substituting coefficients then coordinates equals evaluating the integer code. |
| `UnivariateCodeSupport` | A univariate code is an integer polynomial in its coefficient block and its coordinate slot. |
| `UnivariateCodeBelow` | A univariate code's variables lie below any k its block and slot lie below. |
| `UnivariateCodeEvaluation` | Evaluating a univariate code is the polynomial in one variable decoded from its block, evaluated at its slot's value. |

## Representation

Every degree-bounded polynomial over the ring is what some carrier-valued environment decodes to, and finitely many of them are decoded from one environment, block by block. A finite family of polynomials in n variables has a common degree bound, so the block representation holds for any finite family.

| Member | Statement |
|---|---|
| `CoefficientBlockRepresentation` | Finitely many degree-bounded polynomials are encoded by one environment, block by block. |
| `CoefficientRepresentation` | Every degree-bounded polynomial over the ring is decoded from a carrier-valued environment at any block start. |
| `CommonDegreeBound` | A finite family of polynomials has a common total-degree bound. |
| `PolynomialBoundMono` | A degree bound is a bound at every larger degree. |
| `PolynomialBoundMul` | The product of polynomials of degree at most d and at most e has degree at most d + e. |
| `TupleOfPolynomial` | A polynomial in one variable over the carrier is a ring tuple of some length. |

## Polynomial maps

The polynomial map of n coordinate polynomials sends an n-tuple to the tuple of their values, zero past n. Its injectivity and surjectivity are read on the ring tuples, and it depends only on its first n coordinate polynomials. Two ring tuples of one length are equal when their first n coordinates are, a finite ring has finitely many of them, and over a commutative ring the tuples of length n + 1 are the vectors of the free module on {i | i ≤ n}. A map with coordinates in the first n variables sends ring tuples to ring tuples, and one with coefficients in a subring sends the subring's tuples to tuples of the subring.

| Member | Statement |
|---|---|
| `PolynomialMapDef` | The polynomial map has n active coordinates and zero padding. |
| `PolynomialMapInjectiveDef` | Injectivity is tested on the normalized finite-tuple carrier. |
| `PolynomialMapSurjectiveDef` | Every normalized finite tuple is the image of one in the carrier. |
| `PolynomialMapCongruence` | A polynomial map, its injectivity and its surjectivity depend only on its first n coordinate polynomials. |
| `RingTupleEqual` | Two ring tuples of one length are equal exactly when their first n coordinates agree. |
| `RingTuplesFinite` | A ring with finitely many elements has finitely many n-tuples. |
| `TuplesAsVectors` | Over a commutative ring, the tuples of length n + 1 are the vectors of the free module on {i \| i ≤ n}. |
| `PolynomialMapRingTuple` | A polynomial map with coordinates in the first n variables sends ring tuples to ring tuples. |
| `PolynomialMapSubring` | A polynomial map whose coefficients lie in a subring sends the subring's n-tuples to n-tuples of the subring. |

## Quantifier blocks

A block of names quantified one after another reads, under any evaluator, as one quantifier over what the block decodes to: a ring tuple, a degree-bounded polynomial, or a family of them. "Bridge" in their names marks that one job, reading a block of names as a quantifier for the elementarity step's bridge proof; the engine names these members by string. Each takes the body hypothesis of [first_order](../../../../datatypes/first_order/README.md)'s quantifier bridges on the whole block, s its first name, τ reading the decoded value from s on. The polynomial and family bridges read their block back by `first_order.UpdateRangeCopy`, the tuple bridges by `DecodeUpdatedTuple`.

| Member | Statement |
|---|---|
| `AllRangeTupleBridge` | A universal block of n names reads as a universal quantifier over the ring tuples of length n, under any evaluator. |
| `ExistsRangeTupleBridge` | An existential block of n names reads as an existential quantifier over the ring tuples of length n, under any evaluator. |
| `AllRangePolynomialBridge` | A universal coefficient block reads as a universal quantifier over the degree-bounded polynomials, under any evaluator. |
| `ExistsRangePolynomialBridge` | An existential coefficient block reads as an existential quantifier over the degree-bounded polynomials, under any evaluator. |
| `AllRangeFamilyBridge` | A universal run of k coefficient blocks reads as a universal quantifier over the families of k degree-bounded polynomials, under any evaluator. |
| `ExistsRangeFamilyBridge` | An existential run of k coefficient blocks reads as an existential quantifier over the families of k degree-bounded polynomials, under any evaluator. |

## Polynomials determined by their values

Over an infinite integral domain a polynomial in finitely many variables vanishing at every point is zero. Fixing the last variable at a value of the ring gives a polynomial in the others. A polynomial whose every substitution of a constant for one variable vanishes, read as a polynomial in that variable over the polynomials, has every constant as a root, infinitely many, so it is zero. Induction on the number of variables concludes.

| Member | Statement |
|---|---|
| `SubstituteLastVariable` | Fixing the last of N + 1 variables at a value t of the ring gives a polynomial in the first N variables, whose value at an N-tuple x is the value of p at x with t put last. |
| `ZeroAfterEverySubstitution` | Over an infinite domain, a polynomial that becomes zero whenever one variable is fixed at any value of the domain is zero. |
| `PolynomialVanishingIsZero` | Over an infinite integral domain, a polynomial in N variables that vanishes at every ring tuple of length N is the zero polynomial. |
| `PolynomialDeterminedByValues` | Over an infinite integral domain, two polynomials in N variables taking the same value at every ring tuple of length N are equal. |
