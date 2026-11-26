# indexed_functions — functions on an indexed family of carriers with prescribed values outside the index set

An indexed function has a value in each active carrier and a prescribed value at every inactive coordinate. This normalization makes equality of functions agree with equality on their active coordinates; it also allows empty index sets and varying coordinate zeroes.

Four laws read the definition back: an active coordinate lies in its factor; two indexed functions that agree on the active indices are equal; the set depends on the factors only at the active indices; and, when the prescribed values are admissible, a function is an indexed function exactly when it departs from them only at active indices, within the factors.

`finite_coordinate_dependence(J, C, f)` says that one finite subset of the active indices determines the value of `f` throughout the carrier `C`. The finite support is fixed for the whole carrier, rather than chosen separately at each input. This is a property of total functions restricted to a carrier; it requires neither topology nor algebra. The continuity card that uses it is in [polish_space](../../topology/polish_space/README.md).

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `IndexedFunctionsDef` | definition | Functions are normalized outside the active index carrier. |
| `FiniteCoordinateDependenceDef` | definition | One finite subset of the active indices determines the function on its specified carrier. |
| `IndexedFunctionsCoordinate` | theorem | `f ∈ indexed_functions(J, z, X) ∧ i ∈ J ⇒ f(i) ∈ X(i)` |
| `IndexedFunctionsExtensional` | theorem | `f ∈ indexed_functions(J, z, X) ∧ g ∈ indexed_functions(J, z, X) ∧ (∀i. i ∈ J ⇒ f(i) = g(i)) ⇒ f = g` |
| `IndexedFunctionsCongruence` | theorem | `(∀i. i ∈ J ⇒ X(i) = Y(i)) ⇒ indexed_functions(J, z, X) = indexed_functions(J, z, Y)` |
| `IndexedFunctionsChangedCoordinates` | theorem | `(∀i. i ∈ J ⇒ z(i) ∈ X(i)) ⇒ (f ∈ indexed_functions(J, z, X) ⇔ ∀i. f(i) ≠ z(i) ⇒ i ∈ J ∧ f(i) ∈ X(i))` |
| `OverrideIndexedFunctions` | card | `(∀i. i ∈ J ⇒ v(i) ∈ X(i)) ⇒ override_on(J, v, z) ∈ indexed_functions(J, z, X)`: a restriction is an indexed function |
| `IndexedFunctionsFinite` | card | `finite(J) ∧ (∀i. i ∈ J ⇒ finite(X(i))) ⇒ finite(indexed_functions(J, z, X))` |
