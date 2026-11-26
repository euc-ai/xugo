# real_closure — ordered algebraic extensions and real closures

The real closure extends the prescribed order and is algebraic over the embedded base field. Its construction uses maximal ordered subfields in a fixed algebraically closed host. Positive square-root and odd-degree root extensions are stated separately from maximality, so closure construction is independent of quantifier elimination. Both extend the order through `WeightedSquaresOrderExtension`, the Artin–Schreier criterion relative to the base field, which rests on the positive cones of [`field_ordering`](../field_ordering/README.md).

`RootsCharacterization` — a field with an order is real closed exactly when
it is Euclidean (`ordered_field.EuclideanField`) and every odd-degree
polynomial over it has a root (`polynomial_evaluation.OddDegreeRootsDef`) — is assembled from
these members:

- `RootsCharacterization` ← `QuadraticIrreduciblesRealClosed` and
  `RootsIrreducibleDegreeBound`: IVT gives the two root conditions; conversely
  the root conditions bound every irreducible polynomial by degree two, and
  positive square roots with that bound give IVT.
- `RootsIrreducibleDegreeBound` ← `FiniteGaloisImaginaryAdjoin`: in an
  algebraic closure the order and both root conditions pass to the image of
  the field, and the field of the adjoined roots of an irreducible polynomial
  and of a square root i of minus one is K(i), of degree at most two.
- `FiniteGaloisImaginaryAdjoin` ← `ImaginaryAdjoinSquareClosed`,
  `OddDegreeExtensionTrivial`,
  `algebraic_element.SquareClosedNoQuadraticExtension`,
  `field_automorphism.ArtinFixedField` ([N : F] = |H| for the field F a
  subgroup H fixes) and `AutomorphismsTowerSubgroup`: Artin's argument
  through a Sylow 2-subgroup of the Galois group.
- `ImaginaryAdjoinSquareClosed` ← `SquareRootCoordinates`: a square root of
  a + ib from its two real coordinates.
- `QuadraticIrreduciblesRealClosed` rests on sign arguments and the
  positive square roots of a Euclidean field, by induction on the degree.

| Member | Statement |
|---|---|
| `OrderedSubfieldExtensionDef` | An ordered subfield of an ambient field extending the given order on K. |
| `WeightedSquaresOrderExtension` | An order on K extends to a subfield L ⊇ K when −1 is no sum of squares of L weighted by positive elements of K. — card |
| `SquareRootOrderExtension` | A positive element acquires a square root in an order-extending subfield. — card |
| `OddDegreeOrderExtension` | An odd-degree polynomial acquires a root in an order-extending subfield. — card |
| `SquareRootCoordinates` | In a Euclidean field every pair a, b has coordinates u, v with u² − v² = a and 2uv = b. |
| `ImaginaryAdjoinSquareClosed` | If K is a Euclidean subfield and i² = −1, K(i) is square-closed. |
| `OddDegreeExtensionTrivial` | If every odd-degree polynomial over K has a K-root, every finite odd-degree extension E/K is K. |
| `FiniteGaloisImaginaryAdjoin` | A finite Galois extension N of a Euclidean subfield K over which odd-degree polynomials have roots, containing an i with i² = −1, is K(i). |
| `RootsIrreducibleDegreeBound` | In a Euclidean field over which odd-degree polynomials have roots, every irreducible polynomial has degree at most two. |
| `QuadraticIrreduciblesRealClosed` | A Euclidean field whose irreducible polynomials have degree at most two is real closed. |
| `RootsCharacterization` | A field with an order is real closed exactly when it is Euclidean and its odd-degree polynomials have roots. |
| `MaximalOrderedSubfield` | A maximal ordered subfield of an algebraically closed field is real closed. — card |
| `RealClosureExists` | Every ordered field embeds order-preservingly in an algebraic real closure. — card |
| `NoProperOrderedAlgebraicExtension` | A real closed field has no proper ordered algebraic extension. — card |
