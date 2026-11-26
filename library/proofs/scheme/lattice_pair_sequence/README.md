# lattice_pair_sequence — the six-term sequence of a sub-pair of lattice pairs, and the Euler characteristic it counts

A sub-pair M' ⊆ M of lattice pairs (scheme/lattice_pair) whose chart
quotients are finite over k gives the snake lemma's six-term sequence
0 → H⁰(M') → H⁰(M) → ker c̄ → H¹(M') → H¹(M) → 0, where c̄ is the Čech
difference on the chart quotients, onto the quotient of the ambients.
Its classes are cosets, and the maps are read on them: the inclusion,
v ↦ (v + M'₀, v + M'₁), the connecting map δ, which takes two cosets to
their difference, and X ↦ X + (M₀ + M₁). Counting dimensions along it is
the three-term formula χ(M) − χ(M') = dim M₀/M'₀ + dim M₁/M'₁ − dim of
the ambients' quotient.

## Members

### The definitions

| Member | Statement |
|---|---|
| `latticePairConnectingDef` | `lattice_pair_connecting(V, z)`: δ, the differences of fst(z) and snd(z); on cosets (m₀ − m₁) + (M'₀ + M'₁) |
| `latticePairQuotientDifferenceDef` | `lattice_pair_quotient_difference(R, V, M', z)`: c̄, δ(z) modulo ambient(M') |
| `LatticePairQuotientKernelDef` | `lattice_pair_quotient_kernel(R, V, M, M')`: ker c̄ inside the product of the chart quotients |

### A sub-pair: the six-term sequence

| Member | Statement |
|---|---|
| `QuotientPairCosets` | a point of Q₀ × Q₁ is a pair of cosets (x + M'₀, y + M'₁) with x ∈ M₀ and y ∈ M₁ |
| `ConnectingOfCosets` | δ of the cosets x + N₀ and y + N₁ of two subgroups of V is the coset (x − y) + (N₀ + N₁) |
| `QuotientDifferenceCoset` | c̄(x + M₀, y + M₁) = (x − y) + ambient(M) |
| `ConnectingLinear` | over any subring S of both charts, Q₀ and Q₁ are S-modules and δ is an S-linear map of Q₀ × Q₁ to ambient(M)/(M'₀ + M'₁) |
| `QuotientDifferenceLinear` | over any subring S of both charts, Q₀ and Q₁ are S-modules and c̄ is an S-linear map of Q₀ × Q₁ to Q₀₁ |
| `QuotientDifferenceOnto` | with M₀/M'₀ finite over k, every class of Q₀₁ is c̄ of a pair of classes |
| `PairDifferenceQuotient` | with Q₀, Q₁ finite, c̄ is k-linear onto Q₀₁ and dim ker c̄ + dim Q₀₁ = dim Q₀ + dim Q₁ |
| `SixTermMaps` | H⁰(M') ⊆ H⁰(M) → ker c̄ → H¹(M') → H¹(M) are homomorphisms over any subring of both charts |
| `SixTermH0Exact` | the sequence is exact at H⁰(M) |
| `ConnectingKernel` | the sequence is exact at ker c̄ |
| `ConnectingCokernel` | the sequence is exact at H¹(M'), and H¹(M') → H¹(M) is onto when c̄ is |

### The Euler characteristic of a sub-pair

| Member | Statement |
|---|---|
| `SixTermSequence` | with Q₀, Q₁ finite, over k: H⁰(M) → ker c̄ → H¹(M') → H¹(M) are k-linear, ker c̄ is finite, the kernel on H⁰(M) is H⁰(M'), the kernel of δ is the image of H⁰(M), the kernel on H¹(M') is δ's image, and H¹(M') maps onto H¹(M) |
| `EulerSubpairFinite` | with Q₀, Q₁ finite, M has finite cohomology exactly when M' does |
| `EulerAdditive` | with Q₀, Q₁ finite and M' finite, M is finite and χ(M) − χ(M') = dim Q₀ + dim Q₁ − dim Q₀₁ |
