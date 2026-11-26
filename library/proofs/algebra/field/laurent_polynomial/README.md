# laurent_polynomial — the Laurent polynomials k[t, 1/t] of an element of a field, and their coefficients when the element is transcendental

Inside a field L, a subfield k and a nonzero element t give the polynomials
k[t] and k[1/t] in L and the Laurent ring k[t, 1/t], the ring away from t
over k[t]: a subring of L holding k, t and inv(t). The powers of t at
integer exponents, tⁱ being `laurent_monomial(t, i)`, lie in it and
multiply by adding exponents; tⁿ lies in k[t] for n ≥ 0 and in k[1/t] for
n ≤ 0.

Every member of k[t, 1/t] is a finite sum Σ aᵢ · tⁱ over the integers
with coefficients in k; transcendence of t over k makes the coefficients
unique. `laurent_polynomial_coefficient` chooses an expansion, and any
finite expansion is the chosen one (`LaurentCoeffWellDefined`), so a
coefficient is linear and shifts with multiplication by a power of t, and
the polynomials in an element s with sᵐ = t^e(m) are the Laurent
polynomials whose coefficients lie along e. The projective line
(scheme/projective_line) reads its charts by these coefficients.

## Members

### The definitions

| Member | Statement |
|---|---|
| `LaurentMonomialDef` | `laurent_monomial(t, n)`: tⁿ at an integer n, (t⁻¹)⁻ⁿ for n < 0 |
| `LaurentPolynomialCoefficientDef` | `laurent_polynomial_coefficient(k, t, f, i)`: the coefficient of tⁱ in a chosen finite expansion of f over k |

### The monomials

| Member | Statement |
|---|---|
| `LaurentMonomialOfNum` | at a natural n, tⁿ is the n-th power of t and t⁻ⁿ the n-th power of inv(t) |
| `LaurentMonomialProduct` | t⁰ = one, t¹ = t, t⁻¹ = inv(t), and tᵐ · tⁿ = tᵐ⁺ⁿ, nonzero members of L |
| `LaurentMonomialInverse` | tⁿ · t⁻ⁿ = one, for t ≠ zero |

### The Laurent ring k[t, 1/t]

| Member | Statement |
|---|---|
| `LaurentRingSubring` | for t ≠ zero, the Laurent ring k[t, 1/t] is a subring of L holding k, t and inv(t) |
| `LaurentScalarSubring` | for t ≠ zero, k is a subring of k[t, 1/t] under its operations |
| `LaurentMonomialInRing` | every power tⁿ, n an integer, lies in the Laurent ring k[t, 1/t], for t ≠ zero |
| `LaurentMonomialInPolynomials` | tⁿ lies in k[t] for n ≥ 0 and in k[1/t] for n ≤ 0 |

### Finite sums Σ c(j) · tʲ

| Member | Statement |
|---|---|
| `LaurentTermsInField` | for t ≠ zero and coefficients in k, every term c(j) · tʲ lies in L |
| `LaurentSumOverSuperset` | for t ≠ zero and coefficients in k, Σ c(j) · tʲ over a finite S holding the support of c is the sum over the support |
| `LaurentSumAdd` | for t ≠ zero and finitely supported coefficients a, b in k, the expansion with coefficients a + b is the sum of the two expansions |
| `LaurentSumScale` | for t ≠ zero, finitely supported coefficients a in k and c in k, the expansion with coefficients c · a is c times that of a |
| `LaurentSumInPolynomials` | for t ≠ zero, a finite expansion over k lies in k[t] when no exponent is negative, and in tⁿ · k[1/t] when none lies above n |
| `LaurentExpansionShift` | an expansion of f multiplied by tᵐ term by term, j ↦ a(j − m), is an expansion of tᵐ · f |
| `LaurentSumAsPolynomial` | a Laurent sum supported along e : ℕ → ℤ with t^e(m) = sᵐ is the polynomial (a ∘ e)(s) |

### The coefficients

| Member | Statement |
|---|---|
| `LaurentChosenExpansion` | once f has a finite expansion over k, the chosen coefficients have finite support, lie in k and expand f |
| `LaurentShiftToPolynomial` | tᴺ times a finite expansion Σ a(j) tʲ over k with no exponent below −N is the value at t of the polynomial n ↦ a(n − N) over k |
| `LaurentCoeffWellDefined` | for t transcendental, a finite expansion of f over k is the chosen one |
| `LaurentExpansion` | a member of k[t, 1/t] is the finite sum of its coefficients, which lie in k, times the powers of t |
| `LaurentCoeffWellDefinedOver` | for t transcendental, a finite sum Σ c(j) · tʲ with coefficients in k, over any finite S holding the support of c, has the coefficients c |
| `LaurentExpansionOver` | a member of k[t, 1/t] is the sum of its coefficients times the powers of t over any finite S holding their support |
| `LaurentCoeffShift` | the coefficient of tⁱ in tᵐ · f is the coefficient of tⁱ⁻ᵐ in f |
| `LaurentCoeffLinear` | each coefficient is a k-linear map from k[t, 1/t] to k |
| `LaurentMonomialCoefficient` | for t transcendental, the coefficient of tⁱ in tʲ is one if i = j and zero otherwise |

### The polynomials in s among the Laurent polynomials

| Member | Statement |
|---|---|
| `PolynomialImageCoefficients` | for sᵐ = t^e(m) along an e with a left inverse, k[s] is the Laurent polynomials with coefficients only along e |
