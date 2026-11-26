# subring_localization — fractional ideals extended along subrings and to the localization at a prime, and the order at a rational point

Extending fractional ideals along subrings S ⊆ T of a field L,
X ↦ T · X, takes products to products and an invertible ideal to an
invertible ideal whose inverse is the extended inverse, so it takes each
signed power to the same power of the extension. The localization S_m
of S at a prime m, `subring_localization(L, S, m)`, the fractions a/b of
S with b off m, is a subring of L holding S and the inverse of each such
b. The extension of a fractional ideal M to S_m is the set of members of
L that some such b brings into M, so m generates a proper ideal of it.
A member of S off a maximal ideal p is a unit modulo each power of p,
and when p is invertible the powers of the maximal ideal of S_p meet S
in the powers of p. At the ideal p of a k-rational point of S that is
invertible, with L the field of fractions of S and every S/aS
finite-dimensional, S_p is a valuation ring: every nonzero f generates
exactly one integer power of its maximal ideal, and the exponent is a
valuation of L.

Every statement is read under the bundle `∀L:field_on(A)`, with S a
subring of L, `subring(field_ring(L), S)`.

## Members

### The definitions

| Member | Statement |
|---|---|
| `SubringLocalizationDef` | `subring_localization(L, S, p)`: the fractions a/b of S with b off p, the localization of S at a prime p |

### Powers of a maximal ideal

| Member | Statement |
|---|---|
| `UnitModuloMaximalPowers` | a member of S off a maximal ideal p is a unit modulo every power pⁿ |
| `ClearedOffMaximalIntegral` | a member of the field that pʲ, p maximal, and some b of S off p each multiply into S lies in S |

### Extension along subrings

| Member | Statement |
|---|---|
| `ExtensionOfProduct` | for S ⊆ T with T a subring and X, Y ⊆ L, T · (X ·_S Y) = (T · X) ·_T (T · Y) |
| `ExtensionOfInvertible` | for subrings S ⊆ T and X invertible over S, T · X is invertible over T with inverse T · (S : X) |
| `ExtensionOfSignedPowers` | for subrings S ⊆ T, extension takes each signed power of an invertible ideal of S to the same power of its extension |

### Localization at a prime

| Member | Statement |
|---|---|
| `LocalRingSubring` | the localization S_m at a prime m is a subring of L holding S and the inverse of every member of S off m |
| `LocalExtensionCleared` | the extension of a fractional ideal M of S to S_p, p a prime, is the set of y in L with b · y ∈ M for some b ∈ S off p |
| `LocalIdealProper` | a prime m of S generates a proper ideal of S_m: one ∉ ideal_span(S_m, m) |
| `LocalExtensionLaws` | extension to S_m takes S to S_m, is multiplicative on invertible ideals and keeps their inverses, takes m to the maximal ideal, a proper ideal inside S_m, and takes an ideal holding a member off m to S_m |
| `LocalHoldsSignedPowers` | S_m holds every signed power of an invertible ideal inside S but not inside m |
| `LocalPowerContraction` | for p maximal and invertible, the n-th power of the maximal ideal of S_p meets S in pⁿ |
| `OrderAtChartPoint` | at the invertible ideal p of a k-rational point of S, L the field of fractions and every S/aS finite-dimensional, each nonzero f generates exactly one integer power of the maximal ideal of S_p, the powers decrease strictly, and an exponent so chosen is a valuation |
