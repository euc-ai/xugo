# invertible_lattice_pair — lattice pairs inside a field: scaling, chartwise products, the invertible pairs and their inverses, and the maps between them

A lattice pair inside a field L holding a biaffine datum
(scheme/lattice_pair) takes L for its container over the overlap's ring.
The field is one record `L:field_on(A)`; set positions use `L.carrier`,
elements combine by its operations `L.mul`, `L.inv`, …, and ring-level
constructions take its projection `field_ring(L)`. The definitions of the
products and inverses of fractional ideals are
`algebra/ring/fractional_ideal`'s. Inside a field the invertible pairs
form a commutative monoid under the chartwise product with the structure
pair (A₀, A₁) as unit (`InvertiblePairsCommMonoid`), each with the inverse
M⁻¹ (`InvertibleLatticeInverse`), and a map of invertible pairs is
multiplication by an element of the field: the maps from an invertible M
to N are the multiplications by the sections of N · M⁻¹.

## Members

### The definitions

| Member | Statement |
|---|---|
| `LatticePairMulDef` | `lattice_pair_mul(field_ring(L), A₀, A₁, M, N)`: the chartwise product of fractional ideals |
| `LatticePairInverseDef` | `lattice_pair_inverse(field_ring(L), A₀, A₁, M)`: the chartwise inverse of fractional ideals |
| `InvertibleLatticePairDef` | `invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, M)`: invertible on each chart, a lattice pair over the overlap |
| `LatticePairScaleDef` | `lattice_pair_scale(a, M)`: both charts multiplied by a |

### The field and the datum

| Member | Statement |
|---|---|
| `ChartRingsInField` | the biaffine datum puts A₀ and A₁ inside A₀₁ ⊆ L, and A₀₁, A₀ and A₁ are rings under the field's operations |

### Scaling

| Member | Statement |
|---|---|
| `ScaleOne` | one · M = M for a pair whose charts lie in the field |
| `ScaleScale` | b · (a · M) = (b · a) · M for a, b in the field and a pair whose charts lie in it |
| `ScaleCancel` | inv(a) · (a · M) = M for a ≠ zero in the field and a pair whose charts lie in it |
| `AmbientOfScale` | for the overlap a subring of L, a in L and the first chart of M inside L, the ambient of a · M is a times the ambient of M |
| `ScaleIsLattice` | for a ≠ zero in the field and charts inside it, a · M is a lattice pair iff M is |
| `ScaleOnAmbient` | for a in the field and M a lattice pair, multiplication by a on the ambient, zero off it, is an A₀₁-linear map of the ambient carrying each chart onto a times it |
| `ScaleIsomorphism` | multiplication by a ≠ zero on the ambient is an isomorphism M → a · M |

### Products

| Member | Statement |
|---|---|
| `AmbientOfMul` | for the overlap a subring of L holding A₀ and the first charts of M and N inside L, the ambient of M · N is the product of the ambients over the overlap |
| `MulIsLattice` | the chartwise product of two lattice pairs is a lattice pair |
| `MulAssoc` | (M · N) · Q = M · (N · Q) for chart rings that are subrings of L and pairs whose charts lie in it |
| `MulComm` | M · N = N · M for pairs whose charts lie in L |
| `MulOne` | (A₀, A₁) · M = M |
| `ScaleMulAssoc` | (a · M) · N = a · (M · N) = M · (a · N) for a in the field and pairs whose charts lie in it |

### Invertible pairs

| Member | Statement |
|---|---|
| `LatticePairChartsInField` | the charts of a lattice pair in the field lie in the field |
| `InvertibleChartsInField` | the charts of an invertible pair lie in the field |
| `InvertiblePairSwap` | exchanging the charts of an invertible pair gives an invertible pair over the exchanged charts, with the same ambient |
| `StructurePairInvertible` | the structure pair (A₀, A₁) is invertible |
| `AmbientInvertible` | for fst(M) an invertible fractional ideal of a subring A₀ of L inside the subring A₀₁, the ambient of M is an invertible fractional ideal of the overlap, its inverse the ambient of M⁻¹ |
| `InvertibleLatticeProduct` | the product of invertible pairs is invertible |
| `InvertiblePairsCommMonoid` | the invertible pairs form a commutative monoid under the product, with unit (A₀, A₁) |
| `InvertibleLatticeInverse` | M⁻¹ is invertible, M · M⁻¹ = (A₀, A₁) and (M⁻¹)⁻¹ = M |
| `InvertiblePairsGroup` | the invertible pairs are an abelian group under the product, with unit (A₀, A₁) and inverse M⁻¹ |
| `InvertibleLatticeScale` | for a ≠ zero, a · M is invertible iff M is |

### Maps out of an invertible pair

| Member | Statement |
|---|---|
| `H0MulInverse` | for an invertible M, H⁰(N · M⁻¹) is the members a of the field with a · fst(M) ⊆ fst(N) and a · snd(M) ⊆ snd(N) |
| `InvertibleHomIsScale` | the maps of lattice pairs from an invertible M to N are the multiplications by the members of H⁰(N · M⁻¹) |
| `SectionsAreMaps` | for an invertible pair M, any lattice pair N and a subring S of both charts, multiplication by a section of N · M⁻¹ is an S-isomorphism onto the maps M → N |
| `InvertibleIsoIffScale` | an invertible M is isomorphic to N iff N = a · M for some a ≠ zero — card |
| `SectionInclusion` | a nonzero section a of M puts the invertible pair a · (A₀, A₁) inside M chart by chart |
| `InverseHoldsOne` | one is a section of the inverse of a pair inside the structure pair |
