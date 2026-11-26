# exterior_basis — the binary subset basis of a finite exterior algebra, its wedge-plus-contraction matrix and the exterior power of a matrix

The basis vector numbered a of the exterior algebra on r generators is the wedge of the generators at the binary digits of a below r. `exterior_mask` is that set of digits and `exterior_slot` its k-th element in increasing order; a vector of the exterior algebra is a function on the numbers below 2^r. `koszul_ambient_matrix(r, v)` is the matrix of wedge with v plus contraction with v in this basis, with the sign of the generators passed over. It is Hermitian and squares to the norm of v times the identity. `exterior_power(R, r, P)` is the matrix of the exterior power of an r × r matrix P over a ring, each entry the minor of P on the slots of the row's and the column's masks.

The digits behave as a set should: adding 2ⁱ to a number without the digit i inserts i, subtracting it removes i, only 0 has no digit below r, and the masks of the numbers below 2ʳ are the subsets of {0, …, r − 1}, each once. Inserting i adds one to the count of digits below j exactly when i < j, which is the sign rule: wedges with distinct generators anticommute. The k-th slot is the digit with k digits below it. Over a commutative ring the exterior power is multiplicative, the Cauchy–Binet formula, and it sends the identity to the identity and the transpose to the transpose.

Exterior powers of projection bundles and the Koszul Thom class, the Clifford product and the spin representation, and the exterior factor of the Hermite sequence model and its orthogonal frame changes are written in this basis in their own chapters.

## Members

| Member | Statement or role |
|---|---|
| `MaskDef` | Definition of `exterior_mask` |
| `SlotDef` | Definition of `exterior_slot` |
| `CliffordMatrixDef` | Definition of `koszul_ambient_matrix` |
| `PowerDef` | Definition of `exterior_power` |

## The digits (masks.go)

| Member | Statement |
|---|---|
| `MaskWordBits` | The mask of a below r is the set of a's binary places below r |
| `MaskInsert` | i < r and i ∉ mask(r, a) ⇒ mask(r, a + 2ⁱ) = insert(i, mask(r, a)), and a + 2ⁱ < 2ʳ when a < 2ʳ — card |
| `MaskDelete` | i ∈ mask(r, a) ⇒ 2ⁱ ≤ a and mask(r, a − 2ⁱ) = delete(mask(r, a), i) — card |
| `MaskEmpty` | a < 2ʳ ⇒ (mask(r, a) = ∅ ⇔ a = 0) — card |
| `MaskBijective` | the masks of the numbers below 2ʳ are the subsets of {0, …, r − 1}, each once — card |
| `SignToggle` | i < r and i ∉ mask(r, a) ⇒ the count of digits below j of a + 2ⁱ is that of a plus [i < j] — card |
| `SlotSpec` | k < card(mask(r, a)) ⇒ slot(r, a, k) is a digit with exactly k digits below it — card |

## The exterior power of a matrix (exterior_power.go)

| Member | Statement |
|---|---|
| `ExteriorPowerProduct` | over a commutative ring, Λ(PQ) = Λ(P)Λ(Q), the Cauchy–Binet formula — card |
| `ExteriorPowerIdentity` | Λ(I_r) is the identity below 2ʳ — card |
| `ExteriorPowerTranspose` | Λ(Pᵀ) = Λ(P)ᵀ — card |
