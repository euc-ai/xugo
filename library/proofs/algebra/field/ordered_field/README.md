# ordered_field — ordered fields on explicit carriers and their order-preserving embeddings

An ordered field is a field record together with a strict order on its carrier. The order and all algebraic laws are read only on that carrier; total functions outside it remain unrestricted. Integer coefficients use characteristic_zero.integer_map. Transport carries the field record and the order together, and a ring isomorphism onto a given field carries the order alone, and a Euclidean order as Euclidean. A Euclidean field is an ordered field whose positive elements are squares, each with a positive square root.

| Member | Statement |
|---|---|
| `OrderedFieldOn` | A field with a strict linear order compatible with addition and positive multiplication. |
| `EuclideanField` | An ordered field in which every positive element is a square. |
| `OrderedLeDef` | The weak order associated to a strict order. |
| `OrderedEmbeddingDef` | An embedding preserves ring operations and preserves and reflects strict order. |
| `TransportOrderDef` | Order on an image is read through the chosen preimage in the source carrier. |
| `OrderedSignDef` | The three-valued sign of a field element. |
| `FieldOn` | An ordered field is a field. |
| `Irreflexive` | No point of the carrier lies below itself. |
| `Transitive` | The order is transitive on the carrier. |
| `Trichotomy` | Two points of the carrier are comparable. |
| `AddPreservesOrder` | Adding a point of the carrier preserves the order. |
| `MulPositive` | A product of positive points is positive. |
| `OnePositive` | One is strictly positive. |
| `AddOrderIff` | Translation preserves and reflects strict order. |
| `WeakOrderTranslation` | Adding a carrier value keeps and reflects the weak order of an ordered field. |
| `OrderMixedTransitive` | A weak step and a strict step, in either order, make a strict step. |
| `LessThanSelfAddLeft` | Adding x to y moves y up exactly when x is positive. |
| `AddPositive` | A sum of positive points is positive. |
| `TwoPositive` | Two is positive. |
| `TwoNonzero` | Two is not zero. |
| `SubPositive` | y − x is positive exactly when x lies below y. |
| `SubNegative` | x − y is negative exactly when x lies below y. |
| `NegationReversesSign` | Negation reverses the order against zero. |
| `SquareNonnegative` | Every carrier square is nonnegative. |
| `SquarePositive` | The square of a nonzero point is positive. |
| `SumSquaresZero` | Two points whose squares sum to zero are both zero. |
| `IncreasingMapReflectsOrder` | A map into an ordered field that carries a relation into the strict order reflects it, on a set where the relation compares any two points. |
| `IntermediateValueInjectiveMonotone` | A map injective on a set, taking strictly between two of its points every value strictly between theirs, is strictly increasing or strictly decreasing there. |
| `NegativeIffImageNegative` | A ring homomorphism that preserves and reflects the order carries negativity both ways. |
| `PositiveMulOrderIff` | Multiplication by a positive element preserves and reflects strict order. |
| `PositiveInverse` | The inverse of a positive element is positive. |
| `MultipleOfOnePositive` | Every positive natural multiple of one is positive. |
| `IntegerOrderEmbedding` | The canonical integer map preserves and reflects strict order. |
| `CharacteristicZero` | An ordered field has characteristic zero. |
| `DenseOrder` | Between any two ordered carrier points lies another. |
| `NoEndpoints` | No point of the carrier is least or greatest. |
| `SignValues` | The sign of a point is −1, 0 or 1 exactly as the point is negative, zero or positive. |
| `SignMul` | The sign of a product is the product of the signs. |
| `SignNegOne` | The sign of −1 is −1. |
| `SignNeg` | The sign of a negation is the negated sign. |
| `SignPow` | The sign of a power is the power of the sign. |
| `FiniteGreatest` | A finite nonempty subset of the carrier has a greatest point. |
| `IncreasingCutsDef` | Increasing cuts are carrier points r(0) < r(1) < … < r(k − 1), each below every later one: the cut points of a sign table, where its open cells meet. |
| `IncreasingEnumeration` | A finite subset of the carrier is listed by a strictly increasing sequence. |
| `ConsecutiveIncreasing` | A finite sequence of carrier points increasing from each index to the next increases throughout: its points are increasing cuts. |
| `TransportOrderedField` | A map one-to-one on the carrier is an ordered-field embedding into the transported copy. |
| `TransportOrderIsomorphism` | An order is carried along a ring isomorphism onto any field. |
| `EuclideanOrderedField` | A Euclidean field is an ordered field. |
| `PositiveIsSquare` | Every positive element of a Euclidean field is a square. |
| `PositiveSquareRoot` | Every positive element of a Euclidean field has a positive square root. |
| `TransportEuclideanIsomorphism` | A Euclidean order is carried along a ring isomorphism onto any field. |
