# signed_ideal_power — the integer powers of an invertible fractional ideal

An invertible fractional ideal N of a subring S of a field L has integer
powers Nⁿ, `signed_ideal_power(L, S, N, n)`: the natural powers for
n ≥ 0, S at 0, and the powers of (S : N) for n < 0. They are the integer
powers of a unit of the monoid of fractional ideals, so the exponents
add and N⁻ʲ is the inverse of Nʲ. When N is a proper ideal inside S they
decrease strictly, Nⁱ ⊆ Nʲ exactly when j ≤ i, and an exponent v with
f · S = N^v(f) for every nonzero f is a valuation, the principal ideals
multiplying as their generators do.

Every statement is read under the bundle `∀L:field_on(A)`, with S a
subring of L, `subring(field_ring(L), S)`.

## Members

### The definitions

| Member | Statement |
|---|---|
| `SignedIdealPowerDef` | `signed_ideal_power(L, S, I, n)`: the n-th power of I under the product for n ≥ 0, S at 0, and the (−n)-th power of (S : I) for n < 0 |

### Signed powers

| Member | Statement |
|---|---|
| `SignedPowerLaws` | for x and y inverse in a commutative monoid, the integer powers, yⁿ for n ≥ 0 and x⁻ⁿ for n < 0, lie in the monoid, are the unit at 0 and x at −1, and add their exponents |
| `SignedIdealPowerLaws` | the integer powers of an invertible N are the ring at 0, N at 1 and the natural powers at natural exponents, are fractional ideals, and add their exponents |
| `SignedPowerInverse` | N⁻ʲ is the inverse of Nʲ |
| `SignedPowerOfRing` | every integer power of the ring itself is the ring |
| `SignedPowerHoldsPrincipal` | Nⁿ holds a member f of L exactly when it holds the principal ideal f · S |
| `SignedPowerAntitone` | for a proper invertible ideal N inside the ring, Nⁱ ⊆ Nʲ exactly when j ≤ i |
| `SignedPowerInjective` | the integer powers of a proper invertible ideal inside the ring are distinct: Nᵐ = Nⁿ gives m = n |
| `SignedPowerValuation` | for a proper invertible ideal N inside the ring, an exponent v with f · S = N^v(f) for every nonzero f of L is a valuation |
