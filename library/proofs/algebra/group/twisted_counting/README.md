# twisted_counting — twisted fixed points of free finite group actions

A map commuting with a subgroup of a free finite group action carries that subgroup's orbits to its orbits. Counting the points the map keeps in their orbit, once by the subgroup element that moves them as the map does and once by their orbit, gives the exact fixed-orbit formula; the subgroup need not be normal.

## Members

| Member | Statement |
|---|---|
| `FreeFiniteActionDef` | `free_finite_action`: group_ops(A) → set(B) → (A → B → B) → bool |
| `FreeActionTwistedFixedPoints` | Counted over a subgroup H, the points phi moves as an element of H does number card(H) for every H-orbit phi preserves |
| `SubgroupSumInverse` | A sum over a subgroup does not see inversion |
| `FreeActionTwistedCountByInvariant` | Where r tells the H-orbits of X apart and phi keeps X, the fixed-orbit formula counts card(H) for each value of r that phi leaves unchanged |
