# linear_pairing — nondegenerate pairings and dual bases

Finite-dimensional nondegenerate bilinear pairings identify a vector space with its dual. The chosen dual basis has the orientation stated by the pairing; symmetric trace pairings specialize the coordinate formulas.

## Members

| Member | Statement |
|---|---|
| `BilinearPairingDef` | `bilinear_pairing`: ring_ops(A) → module_ops(A, B) → (B → B → A) → bool |
| `PairingNondegenerateDef` | `pairing_nondegenerate`: ring_ops(A) → module_ops(A, B) → (B → B → A) → bool |
| `NondegeneratePairingDualityIso` | Over a field, a bilinear left-nondegenerate pairing on a finite-dimensional module M makes x ↦ b(x, −), zero off M, an isomorphism of M onto its dual |
| `NondegeneratePairingDualBasis` | Over a field, a bilinear left-nondegenerate pairing and a finite basis E of M give a unique d with b(d(e), f) = δ(e, f) on E; `image(d, E)` is a basis and every x ∈ M.carrier is `Σ_{e∈E} b(x, e) • d(e)` |
