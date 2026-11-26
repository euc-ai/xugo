# projective_line_free_pair — the free pairs on the projective line, sums of the O(N(e)) · e, and their cohomology

On the projective line inside a field (scheme/projective_line), a free
pair is the sum of the O(N(e)) · e along field elements e independent
over k[t], and its cohomology is the sum of theirs. Adding an element e to E splits off e · O(N(e)) as a direct summand, and
multiplying by e ≠ zero leaves h⁰ and h¹ of O(n) unchanged, so h⁰ and h¹
of a free pair along a finite E are the sums of those of the O(N(e)).

## Members

### The definitions

| Member | Statement |
|---|---|
| `ProjectiveLineFreePairDef` | `projective_line_free_pair(L, k, t, E, N)`: the k[t]-span of E and the k[1/t]-span of the t^N(e) · e |

### The free pairs

| Member | Statement |
|---|---|
| `FreeLinePairIsLattice` | a free pair is a lattice pair on the line |
| `FreeLinePairSplit` | for e ∉ E with insert(e, E) independent over k[t], each chart of the free pair on insert(e, E) is that of e · O(N(e)) plus that along E, the two ambients meeting only in zero |
| `ScaledLineH0Dim` | for e ≠ zero, H⁰(e · O(n)) is finite over k of dimension max(n + 1, 0) |
| `FreeLinePairH0Dim` | along a finite E independent over k[t], h⁰ of the free pair is Σ max(N(e) + 1, 0) |
| `ScaledLinePairH1Dim` | H¹(e · O(n)) is finite of dimension max(−n − 1, 0) for e ≠ zero |
| `FreeLinePairH1Dim` | along a finite E independent over k[t], h¹ of the free pair is Σ max(−N(e) − 1, 0) |
