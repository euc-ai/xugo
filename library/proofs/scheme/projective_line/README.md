# projective_line — the projective line inside a field, and its lattice pairs O(n)

The projective line over a subfield k is held inside a field L by an
element t transcendental over k: chart 0 is k[t], chart 1 is k[1/t], and
they are glued along k[t, 1/t], every one of them a subset of L — a
biaffine datum in the sense of `scheme/lattice_pair`. L need not be
k(t). The line's lattice pairs live in any field containing t, so a
curve's lattice pair is read on the line inside the curve's own function
field, and the curve's duality stands on the line's.

The checked API takes L as a `field_ops` record satisfying `field_on(L)`.
Its underlying set is `L.carrier`; polynomial images take `field_ring(L)`,
and the rings of the charts and overlap restrict that ring record to their
respective sets. The pair operations take L explicitly.

Its charts are read by the coefficients of the Laurent polynomials in t
(algebra/field/laurent_polynomial): k[t] is the Laurent polynomials with
no negative powers, tⁿ · k[1/t] those with no power above n.

The pair O(n) is (k[t], tⁿ · k[1/t]). Its H⁰ is the polynomials of
degree at most n and its H¹ has the classes of tⁱ, n < i < 0, as a
basis, so h⁰ = max(n + 1, 0), h¹ = max(−n − 1, 0) and χ(O(n)) = n + 1;
O(0) is the structure pair, whose global sections are k, and the line
has genus zero.

The free pairs on the line are scheme/projective_line_free_pair, and its
duality with O(−2) by the coefficient of t⁻¹ is
scheme/projective_line_duality.

## Members

### The definitions

| Member | Statement |
|---|---|
| `ProjectiveLinePairDef` | `projective_line_pair(F, k, t, n)`: O(n) = (k[t], tⁿ · k[1/t]) |

### The datum

| Member | Statement |
|---|---|
| `ProjectiveLineBiaffine` | k[t] and k[1/t] glued along k[t, 1/t] form a biaffine datum, for t ≠ zero |
| `LaurentThroughInverse` | k[t, 1/t] read through inv(t): k[1/t] with inv(t) inverted in L is k[t, 1/t], for t ≠ zero |
| `LineDatum` | for t ≠ zero, the line is a biaffine datum in L: k ⊆ k[t], k[1/t] ⊆ k[t, 1/t] ⊆ L, all three rings, t ∈ k[t], inv(t) ∈ k[1/t], and L a module over k, k[t], k[1/t] and k[t, 1/t] |

### The pairs O(n)

| Member | Statement |
|---|---|
| `LinePairZero` | O(0) = (k[t], k[1/t]) |
| `LineChartCoefficients` | k[t] is the Laurent polynomials with no negative powers, k[1/t] those with no positive powers |
| `LinePairCoefficients` | k[t] is the Laurent polynomials with no negative powers, tⁿ · k[1/t] those with no power above n |
| `LineChartSumCoefficients` | a member of k[t] + tⁿ · k[1/t] has no coefficient strictly between n and 0 |
| `LinePairChartPowers` | for a lattice pair M on the line and i ≤ j, tⁱ · v ∈ fst(M) gives tʲ · v ∈ fst(M), and tʲ · v ∈ snd(M) gives tⁱ · v ∈ snd(M) |
| `LinePairInvertible` | every O(n) is an invertible lattice pair |
| `LinePairIsLattice` | every O(n) is a lattice pair on the line, for t ≠ zero |
| `LinePairAmbient` | the ambient of O(n) is the overlap k[t, 1/t] |
| `LineGlobalSections` | for t transcendental, k[t] ∩ k[1/t] = k |
| `LineNegativeSectionsVanish` | H⁰(O(−n)) = 0 for n > 0: a polynomial in t that is $t^{-n}$ times a polynomial in 1/t is zero |
| `LineIntersectionBasis` | t⁰, …, tⁿ form a basis of H⁰(O(n)) = k[t] ∩ tⁿ · k[1/t] |
| `LineQuotientBasis` | the classes of tⁱ, n < i < 0, form a basis of H¹(O(n)) |
| `LineH0Dim` | H⁰(O(n)) is finite of dimension max(n + 1, 0) |
| `LineH1Dim` | H¹(O(n)) is finite of dimension max(−n − 1, 0) |
| `LineH1Module` | for every lattice pair M on the line, the ambient and chart 0 + chart 1 are k-subspaces, the sum inside the ambient, and H¹(M) is a vector space over k |
| `LineEuler` | O(n) is finite with χ(O(n)) = n + 1 |
