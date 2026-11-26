# projective_line_duality — duality on the projective line: H¹ of a lattice pair dual to its maps into O(−2), by the coefficient of t⁻¹

On the projective line inside a field (scheme/projective_line), duality
is coefficient extraction. A map φ of lattice pairs from M into O(−2)
reads, on a class of H¹(M), the coefficient of t⁻¹ in φ at a
member of the class — well defined because t⁻¹ lies in neither chart of
O(−2). Conversely a k-linear functional u on H¹(M) gives the map
$x \mapsto \sum u([t^{-m-1} \cdot x]) \cdot t^m$, a finite sum over all integers m, linear
over k[t, 1/t] with no basis chosen. The two constructions are inverse
to each other for every lattice pair on the line, so Hom(M, O(−2)) is the
k-dual of H¹(M), of the same dimension when H¹(M) is finite. No lattice
pair is first split into a sum of O(n)'s: the duality does not need the
splitting, and it is not stated here.

`LineCanonicalCheck` is the chapter's sanity check, read off
scheme/projective_line's dimension counts.

## Members

### The definitions

| Member | Statement |
|---|---|
| `ProjectiveLineDualityMapDef` | `projective_line_duality_map(L, k, t, V, M, φ, X)`: the coefficient of t⁻¹ in φ at a member of the class X, zero off the classes |
| `projectiveLineDualityInverseDef` | `projective_line_duality_inverse(L, k, t, V, M, u, x)`: $\sum u([t^{-m-1} \cdot x]) \cdot t^m$ on the ambient of M, zero off it |

### Duality

| Member | Statement |
|---|---|
| `DualityMapKillsLattice` | a map into O(−2) has no coefficient at t⁻¹ on fst(M) + snd(M) |
| `LinePairMapAmbient` | a map of lattice pairs from M into O(n) carries the ambient of M into the overlap k[t, 1/t] |
| `DualityFunctional` | the functional of a map φ into O(−2) lies in the k-dual of H¹(M) and reads the coefficient of t⁻¹ in φ(x) at the class of x |
| `DualityMapLinear` | φ ↦ the functional of φ is a k-linear map from Hom(M, O(−2)) into the k-dual of H¹(M) |
| `DualityKillsChartSum` | a k-linear functional on H¹(M) kills the class of every member of fst(M) + snd(M) |
| `DualityInverseFinite` | for a functional u and x in the ambient, u kills all but finitely many classes $[t^{-m-1} \cdot x]$ |
| `LaurentMonomialSmulInAmbient` | for a lattice pair M on the line and x in its ambient, tʲ · x lies in the ambient, for every integer j |
| `DualityFunctionalOnAmbient` | a functional u on H¹(M), read on the ambient through the classes y ↦ u([y]), is k-linear into k |
| `DualityInverseExpansion` | on the ambient, the map of u at x is the finite expansion $\sum u([t^{-m-1} \cdot x]) \cdot t^m$ with coefficients in k |
| `DualityInverseShift` | the map of u at tʲ · x is tʲ times its value at x |
| `DualityInverseLinear` | the map of a functional is k-linear on the ambient and zero off it |
| `DualityInverseLaurentLinear` | the map of a functional is linear over k[t, 1/t] on the ambient and zero off it |
| `DualityInverseCharts` | the map of a functional carries fst(M) into k[t] and snd(M) into t⁻² · k[1/t] |
| `DualityInversePairMap` | the map of a functional on H¹(M) is a map of lattice pairs from M into O(−2) |
| `DualityRoundTripOne` | the functional of the map of u is u |
| `DualityRoundTripTwo` | the map of the functional of φ is φ |
| `LineSerreDuality` | for every lattice pair M on the line, Hom(M, O(−2)) is isomorphic to the k-dual of H¹(M) by the coefficient of t⁻¹, of dimension h¹(M) when H¹(M) is finite |
| `LineCanonicalCheck` | h⁰(O) = h¹(O(−2)) = 1 and h¹(O) = h⁰(O(−2)) = 0 |
