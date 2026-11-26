# module_dimension — the dimension of a module on a set over a field, and what it measures

Over a field every module on a set has a basis, and when one basis is
finite every basis is finite of the same size (`BasisSizeUnique`, the
replacement theorem read both ways). `finite_dimensional(R, M)` says `M`
has a finite basis, and `module_dim(R, M)` is the size of a basis,
chosen: `εn. ∃S. module_basis(R, M, S) ∧ has_size(S, n)`. The definition
asks nothing more, because uniqueness is a theorem; for a
finite-dimensional `M` over a field the choice has one value it can make
(`DimBasis`), and where `M` has no finite basis the dimension is a
number nothing is said about. The infinite case is left out: comparing
infinite bases is a statement about cardinals, not numbers.

The dimension bounds independent sets from above and spanning sets from
below, and a set of the right size of either kind is a basis. A
submodule has at most the dimension of the module, and only the module
itself has the full dimension. A homomorphism's kernel and image have
dimensions summing to the module's (`RankNullity`); the quotient by a
submodule is the image of the projection, so a submodule's dimension
and the quotient's do too (`QuotientDim`). Isomorphic modules have one
dimension, and the free module on a finite set has the set's size as
its dimension: the indicators of its points are a basis
(`FreeModuleDim`), which is what reads a polynomial of degree below `n`
as a vector with `n` coordinates.

The dimension results are over a field — `ring_subfield(R, inv, R.carrier)`,
the module's own ring a field on its carrier with an inverse beside it
(field's `RingSubfieldDef`) — and are read under `module_on(R, M)`, the
ring and the module each one value of its record (module_record). A
submodule `N` is a module of its own as `restrict_module(M, N)`, the
quotient by it as `quotient_module(M, N)`, and a second module is a
second record `N : module_ops(A, C)`.

Linear splittings need no dimension: over a field every linear map has a
linear inner inverse, and a surjection a linear section, whatever the
dimensions.

## The definitions

| member | statement |
|---|---|
| `FiniteDimensionalDef` | `finite_dimensional(R, M)` ⇔ `∃S. finite(S) ∧ module_basis(R, M, S)` |
| `ModuleDimDef` | `module_dim(R, M) = εn. ∃S. module_basis(R, M, S) ∧ has_size(S, n)` |

## Bases have one size

| member | statement |
|---|---|
| `BasisSizeUnique` | beside a finite basis, every basis is finite of the same size |
| `IndexedBasisSizeUnique` | over a field, two indexed bases have the same length |
| `DimBasis` | `module_basis(R, M, S) ∧ finite(S) ⇒ module_dim(R, M) = card(S)` |
| `FiniteBasisDim` | a finite basis makes `M` finite-dimensional, of dimension its size |
| `FiniteDimensionalSpanning` | `finite_dimensional(R, M)` ⇔ a finite subset spans `M.carrier` |
| `FiniteDimensionalBasis` | in a finite-dimensional `M` every basis is finite, of size `module_dim(R, M)` |

## What the dimension bounds

| member | statement |
|---|---|
| `IndependentBound` | an independent subset of a finite-dimensional `M` has at most `module_dim(R, M)` members |
| `SpanningBound` | a finite spanning subset has at least `module_dim(R, M)` members |
| `IndependentFullBasis` | in a finite-dimensional `M`, an independent subset with `module_dim(R, M)` members is a basis |
| `SpanningFullBasis` | a set spanning M with `module_dim(R, M)` members is a basis |
| `DimZero` | for a finite-dimensional `M`, `module_dim(R, M) = 0 ⇔ M.carrier = {M.zero}` |
| `LineDim` | a module spanned by one nonzero vector over a field is finite-dimensional of dimension one |
| `DimTwo` | over a field, a finite-dimensional module has dimension two exactly when two of its vectors have only the trivial relation and any three have a nontrivial one |
| `ZeroSubmoduleDim` | over a field, {M.zero} is finite-dimensional of dimension 0 |
| `FiniteCarrierFiniteDimensional` | A module with finitely many elements over a field is finite-dimensional |

## Submodules, kernels and images, quotients

| member | statement |
|---|---|
| `SubmoduleDim` | a submodule `N` of a finite-dimensional `M` is finite-dimensional with `module_dim(R, restrict_module(M, N)) ≤ module_dim(R, M)` |
| `SubmoduleDimEq` | a submodule of a finite-dimensional `M` of full dimension is `M.carrier` |
| `RankNullity` | for a finite-dimensional `M`, the kernel's and the image's dimensions, each read as a module by `restrict_module`, sum to `module_dim(R, M)` |
| `ImageDim` | over a field, the image of a finite-dimensional M under a linear map is finite-dimensional, of dimension at most `module_dim(R, M)` |
| `InjectiveImageDim` | a one-to-one linear map keeps finite dimension and the dimension |
| `QuotientDim` | for a finite-dimensional `M`, `module_dim(R, restrict_module(M, N)) + module_dim(R, quotient_module(M, N)) = module_dim(R, M)` |
| `DimFiniteIffSubAndQuotient` | over a field, M is finite dimensional exactly when N and M/N are finite dimensional |
| `DimFiniteOfKernelAndImage` | over a field, a linear map whose kernel and image are finite-dimensional has a finite-dimensional source |
| `QuotientDimZeroIff` | over a field, `J ⊆ I` submodules ⇒ (`I/J` is finite-dimensional of dimension zero ⇔ `I = J`) |
| `QuotientEnlargeMap` | `J ⊆ I' ⊆ I` submodules ⇒ `x + J ↦ x + I'` is linear from `I/J` to `I/I'`, onto, and `I/J` restricted to its kernel is `I'/J` |
| `QuotientChainDim` | over a field, `J ⊆ I' ⊆ I` submodules with `I/J` finite-dimensional ⇒ `I/I'` and `I'/J` are finite-dimensional and `dim(I/J) = dim(I/I') + dim(I'/J)` |
| `QuotientChainExtend` | over a field, `J ⊆ I' ⊆ I` submodules with `I/I'` and `I'/J` finite-dimensional ⇒ `I/J` is finite-dimensional and `dim(I/J) = dim(I/I') + dim(I'/J)` |
| `IsomorphismDim` | over a field, an isomorphism `f` of a finite-dimensional `M` onto `N` makes `N` finite-dimensional, of the dimension of `M` |
| `IsomorphicDim` | over a field, an isomorphic module is finite-dimensional of the same dimension |
| `FreeModuleDim` | over a field, `finite(S) ⇒ module_dim(R, free_module_record(R, S)) = card(S)` |
| `FreeModuleFiniteDim` | over a field, `finite(S) ⇒` `free_module_record(R, S)` is finite-dimensional of dimension `card(S)`: the point masses are a finite basis |

The homomorphism in `RankNullity` is
`module_homomorphism(R, M, N, f)` between two module records over one
ring record, the two modules' structure written beside it.

## The standard pairing and annihilators

On the coordinate space R^S of a finite S, $\langle v, a \rangle = \sum_{i \in S} v(i) \cdot a(i)$ is bilinear and nondegenerate. Pairing against finitely many vectors is a linear map into their coordinates, onto when they are independent. Its kernel is their annihilator, so a span and its annihilator have dimensions adding to |S|. Over ℝ the kernel vector is a nonzero solution of a homogeneous system with more unknowns than equations, and when the unknowns are a strict majority H of an index set V it can be taken supported on H with every row outside H killing it.

| Member | Statement |
|---|---|
| `StandardPairingBilinear` | over a commutative ring, the standard pairing on R^S, S finite, is `bilinear_map` into `regular_module(R)` |
| `StandardPairingNondegenerate` | only the zero vector of R^S pairs to zero with every vector of R^S |
| `StandardPairingVanishesOnSpan` | a vector pairing to zero with every member of X ⊆ R^S pairs to zero with the span of X |
| `PairingMapLinear` | for a finite X ⊆ R^S, `a ↦ (u ↦ COND(u ∈ X, ⟨u, a⟩, 0))` is linear from R^S into R^X |
| `PairingKernelVector` | over a field, fewer than `card(S)` coordinate rows have a common nonzero kernel vector |
| `SmallRowsKernel` | over ℝ, a homogeneous system with rows indexed by a finite K and unknowns by a finite H, `card(K) < card(H)`, has a solution supported on H and nonzero there |
| `MajorityKernelVector` | for finite V ⊇ H with `card(V) < 2·card(H)`, some real v supported on H and nonzero there is killed by every row of M indexed in V ∖ H |
| `IndependentPairingsOnto` | over a field, pairing against an independent B ⊆ F^S maps F^S onto F^B |
| `AnnihilatorSubspace` | over a commutative ring, the vectors of R^S pairing to zero with every member of V ⊆ R^S form a submodule |
| `AnnihilatorDimension` | over a field, the span of V ⊆ F^S and the vectors pairing to zero with all of V have dimensions adding to `card(S)` |

## A change of scalars, and codimension one

Vectors whose coordinates lie in a subfield span over the field a space no larger than over the subfield: a basis over the subfield still spans over the field. Restricting the scalars along a one-to-one ring homomorphism keeps the dimension over its image. A submodule of codimension at most one leaves no room for two independent directions outside it.

| member | statement |
|---|---|
| `SubfieldRankBound` | over a field `R` with a subfield `L`, vectors with coordinates in `L` span over `R` a space no larger than they span over `L` (`dim_R span_R W ≤ dim_L span_L W` in `free_module_record`) |
| `ScalarRestrictionDim` | restricting the scalars of a module along a one-to-one ring homomorphism keeps its dimension over the image |
| `PairDependentModuloCodimOne` | over a field, `N` a submodule of a finite-dimensional `M` with `dim M ≤ dim N + 1` ⇒ any `u, w ∈ M` have `c • u + d • w ∈ N` with `c, d` not both zero |

## Linear splittings

| member | statement |
|---|---|
| `LinearMapInnerInverse` | every linear map over a field has a linear inner inverse |
| `LinearMapSection` | every surjective linear map over a field has a linear section |

## The product and the dual

| member | statement |
|---|---|
| `DimProduct` | over a field, `M`, `N` finite-dimensional ⇒ `product_module(M, N)` finite-dimensional and `module_dim(R, product_module(M, N)) = module_dim(R, M) + module_dim(R, N)` |
| `DualDim` | over a field, the dual `hom_module(R, M, R)` of a finite-dimensional `M` is finite-dimensional with `module_dim` equal to `module_dim(R, M)` |

## A chain of images

| member | statement |
|---|---|
| `ImageChainStabilizes` | over a field, for an endomorphism `f` of a finite-dimensional `M`, the images `W(0) = M.carrier`, `W(n + 1) = image(f, W(n))` are constant from some `m` on |
| `BoundedChainUnion` | over a field, a module covered by an increasing chain of submodules of dimension at most b is finite-dimensional, of dimension at most b |
| `ScalarPowerImagesStabilize` | over a field k ⊆ S, the images of a module finite over k under the powers of c ∈ S stop shrinking |

## An ideal of colength one

| member | statement |
|---|---|
| `IdealQuotientModuleOn` | `k ⊆ R.carrier` a field under the ring's operations, `I` an ideal ⇒ `R`, `I` and `R/I` are modules over `k` |
| `QuotientOneNonzero` | `I` a proper ideal ⇒ the class of one is a nonzero vector of `R/I` |
| `FieldResiduesColength` | `k ⊆ R.carrier` a field, `I` an ideal that is `R` or the ideal of a k-rational point (`rational_ideal(R, k, R.carrier, I)`) ⇒ `R/I` is finite-dimensional over `k` of dimension `COND(I = R.carrier, 0, 1)` |
| `IdealColengthOneRational` | `k ⊆ R.carrier` a field, `I` an ideal with `R/I` finite-dimensional of dimension one over `k` ⇒ `I` is the ideal of a k-rational point (`rational_ideal(R, k, R.carrier, I)`) |
| `RationalIffColengthOne` | `k` a field inside a subring `S` of `R`, `I` an ideal of `S` ⇒ `I` is the ideal of a k-rational point of `S` exactly when `S/I` is finite-dimensional of dimension one over `k` |

## Finite-set traces

The coordinate and trace results hold over any commutative scalar ring; the image-rank formula asks for a field. A finite set basis supplies normalized coordinate functionals. The trace is their diagonal finite sum, independent of the basis by exchanging a double sum. At an idempotent it is the natural multiple of one measured by the image dimension, in every characteristic.

| Member | Statement |
|---|---|
| `ModuleBasisCoordinatesDef` | The normalized coefficient function of a vector in a finite set basis. |
| `ModuleBasisTraceDef` | The sum of the diagonal coordinate functionals in a finite set basis. |
| `ModuleTraceDef` | The common finite-basis trace of an endomorphism. |
| `BasisCoordinatesSpec` | The chosen coefficients lie in the scalar ring, vanish off the basis and expand the vector. |
| `BasisCoordinatesUnique` | A normalized finite-basis expansion has the chosen coefficient function. |
| `BasisCoordinatesRestrict` | A basis of M over R that is also a basis of a part S over a subring P gives each vector of S the same coordinates over R as over P. |
| `BasisCoordinatesAdd` | The coordinates of a sum are the pointwise sum of the coordinates. |
| `BasisCoordinatesSmul` | The coordinates of a multiple are the pointwise multiple of the coordinates. |
| `BasisCoordinateLinear` | Each coordinate is a linear functional on the module. |
| `HomBasisExpansion` | A linear map into any module is the coordinate combination of its values on a finite basis |
| `IndexedBasisExpansion` | A vector is the sum over an indexed basis of its coordinates times the basis vectors: `v = Σ_{i<n} coord_e(v, e(i)) • e(i)` |
| `IndexedFunctionalExpansion` | A linear functional is the sum over an indexed basis of its values times the coordinates: `h(v) = Σ_{k<n} h(e(k)) * coord_e(v, e(k))` |
| `IndexedImageCoordinates` | The coordinates of `f(v)` in a finite basis `E` are those of the images `f(e(k))` of an indexed basis, weighted by the coordinates of `v` |
| `BasisCoordinateDelta` | A basis vector has its Kronecker coordinate function. |
| `BasisTraceInCarrier` | The diagonal coordinate sum belongs to the scalar ring. |
| `BasisTraceIndependent` | Two finite set bases give the same trace. |
| `TraceFromBasis` | Any finite basis computes the basis-independent trace. |
| `TraceCongruence` | Endomorphisms that agree on the module have the same trace. |
| `TraceAdd` | The trace of the pointwise sum of two endomorphisms of a finite-dimensional module is the sum of their traces |
| `TraceScale` | The trace of a scalar multiple of an endomorphism of a finite-dimensional module is the scalar times its trace |
| `IdempotentTraceIsRank` | The trace of an idempotent is the field multiple of one given by its image dimension. — card |

### Direct sums and complements

| Member | Statement |
|---|---|
| `DirectSumDim` | dim(U + W) = dim U + dim W when U ∩ W ⊆ {0} |
| `ProperSubmoduleDimLess` | a proper subspace W of a subspace V of a finite-dimensional space has smaller dimension: dim W + 1 ≤ dim V |
| `QuotientComplementBasis` | an independent T ⊆ U complementing W gives the classes of T as a basis of U/W, one per member of T |
| `QuotientComplementDim` | over a field, a finite such T gives dim U/W = card(T) |
| `QuotientComplementLift` | a finite-dimensional U/W has such a T with card(T) = dim U/W |
| `QuotientDirectSumDim` | dim (U₁ + U₂)/(W₁ + W₂) = dim U₁/W₁ + dim U₂/W₂ when U₁ ∩ U₂ ⊆ {0} |
| `HomSetAgreeOnBasis` | Two maps of a hom set that agree on a finite basis are equal |
| `LinearKernelVector` | A homomorphism of finite-dimensional spaces over a field into a space of smaller dimension kills a nonzero vector |
