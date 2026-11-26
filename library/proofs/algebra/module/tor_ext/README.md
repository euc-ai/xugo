# tor_ext — canonical Tor and Ext, functoriality and Tor balance

`tor(R,M,N,n)` and `ext(R,M,N,n)` use the canonical free resolution of
M. The ring and modules are records, and neither definition takes a
resolution or a size hypothesis. `tor_module` and `ext_module` hold
their quotient operations as well as their carriers. The zero cosets
are `tor_zero` and `ext_zero`; the degree-zero identification theorems
are `TorZero` and `ExtZero`.

For a scalar type A and M's carrier type B, the resolution uses the
fixed index type `I(A,B)=set(prod(num,prod(A,B)))`. Its terms live at
`I(A,B)→A`. Tensoring a free term with N becomes finitely supported
N-valued functions on the term's basis. Mapping the free term into N
becomes all N-valued functions on the basis, extended by zero outside
it. Tor is the homology of the first complex and Ext the cohomology
of the second. Both layers live in
[`chain_complex`](../chain_complex/README.md); this chapter uses their
induced and connecting maps. The function modules and the transpose
`hom_precompose` are [`function_module`](../function_module/README.md)'s;
`hom_coboundary` and `hom_precompose` keep the outside zero guard
explicitly. The Hom complex of a free resolution is the dual, with
coefficients in N, of the free complex based by the identity
(`HomComplexDualAgreement`; [`free_complex_duality`](../free_complex_duality/README.md)).
Through it the Hom complex is a cochain complex, a chain map of free
complexes transposes to a cochain map of their Hom complexes, and Ext is
independent of the resolution because a homotopy equivalence of
resolutions dualizes to one of their Hom complexes; the identity and
composite laws of the first-variable maps come from those of the
transpose and of the map on cohomology.

The arbitrary-resolution constructions remain named
`tor_of_resolution(R,S,d,N,n)` and `ext_of_resolution(R,S,d,N,n)`.
`TorIndependent` and `ExtIndependent` compare any free resolution,
at any index type, with the canonical definition. These are
cross-type module isomorphisms, not equalities of carriers.

`Ext¹(M, N)` classifies the extensions of `M` by `N` up to isomorphism
(algebra/module/yoneda_ext), read on the first two terms of the
canonical resolution.

## Arbitrary resolutions

| member | statement |
|---|---|
| `FiniteSuppTensorIso`, `FunModuleHomIso` | identify free tensor and free Hom with the function modules `finite_supp_module` and `function_module` of [`function_module`](../function_module/README.md) — card |
| `TensorBoundaryDef`, `FiniteSuppMapDef`, `TensorComplexOf`, `TorOfResolutionDef` | explicit tensor boundary, tensor map and resolution-dependent Tor |
| `TensorBoundaryAsFiniteSuppMap` | the tensor boundary `tensor_boundary(R, N, d, n)` is d(n) tensored with N, `finite_supp_map(R, N, d(n))` |
| `FiniteSuppMapHom` | a homomorphism k of the free modules on S and T, tensored with N, is a homomorphism `finite_supp_map(R, N, k)` of `finite_supp_module(N, S)` into `finite_supp_module(N, T)` |
| `HomCoboundaryDef`, `HomComplexOf`, `extOfResolutionDef` | guarded Hom coboundary and resolution-dependent Ext |
| `TensorComplex` | tensoring a free chain complex with N gives a chain complex: the finitely supported N-valued functions on S(n), with boundary d(n) ⊗ 1 |
| `HomComplexDualAgreement` | the Hom complex is the dual of the free complex based by the identity, for every boundary — card |
| `HomComplex` | mapping a free chain complex into N gives a cochain complex: the N-valued functions on S(n), zero off it, with coboundary g ↦ ĝ ∘ d(n + 1) on the generators |
| `HomCochainMap` | a chain map of free complexes transposes to a cochain map of their Hom complexes, in the opposite direction |
| `TensorChainMap`, `TensorHomotopy` | chain maps and homotopies induce tensor maps and homotopies — card |
| `TorIndependent` | comparison of Tor with the canonical definition — card |
| `ExtIndependent` | comparison of Ext with the canonical definition |

## Canonical values and maps in the second variable

`tor_map(R,M,L,f,n)` and `ext_map(R,M,L,f,n)` apply f pointwise,
then pass to the quotient for the target module L. L is explicit:
a total function f alone does not determine its target module's
operations. The map needs no arbitrary choice of cycle representative.
The identity and composition statements of `tor_map` are pointwise on
quotient carriers, where the maps are mathematically specified.

`short_exact_modules(R,N',N,N'',i,p)` binds the entire short exact
sequence under `∀S:short_exact_modules(A,C,D,E)`. Its two strong
homomorphisms include all three module laws. The induced complexes
are degreewise short exact. `tor_connecting(R,M,N',N,i,p,n)` goes
from degree n+1 to n; `ext_connecting` goes from n to n+1.

| member | statement |
|---|---|
| `CanonicalTensorComplexDef`, `CanonicalHomComplexDef` | the fixed complexes of M and N |
| `TorDef`, `ExtDef`, `TorModuleDef`, `ExtModuleDef`, `TorZeroDef`, `extZeroDef` | canonical carriers, operations and zero classes |
| `CanonicalTensorComplex`, `CanonicalHomComplex` | the canonical complexes are a chain and a cochain complex |
| `TorAsHomology`, `ExtAsCohomology` | Tor and Ext are the homology and cohomology of the canonical complexes |
| `TorModuleOn`, `ExtModuleOn` | canonical Tor and Ext are modules — card |
| `TorZero`, `ExtZero` | degree zero is tensor product, respectively Hom — card |
| `TorZeroNatural` | the identification of Tor₀ with the tensor product commutes with the maps a homomorphism of the second variable induces: tor_map at degree zero is M ⊗ g through it — card |
| `TorMapDef`, `ExtMapDef`, `TorConnectingDef`, `ExtConnectingDef` | the named induced and connecting maps |
| `TorMapHom`, `TorMapIdentity`, `TorMapCompose` | second-variable linearity and functoriality — card |
| `TensorComplexesExact`, `HomComplexesExact` | short exact sequences of the canonical complexes — card |
| `TorLongExactMiddle`, `TorLongExactQuotient`, `TorLongExactSub`, `TorLongExactEnd` | the second-variable long exact sequence, ending onto in degree zero — card |
| `ExtLongExactStart`, `ExtLongExactMiddle`, `ExtLongExactQuotient`, `ExtLongExactSub` | the second-variable long exact sequence, starting injective in degree zero — card |

## The first variable

The canonical resolution is strictly functorial relative to the one
fixed `index_embedding` for each pair of types. Degree zero freely
pushes basis generators along f; each next degree pushes the current
kernel generators along the already defined map. Injectivity of the
fixed encodings cancels decoding in the identity and composite laws.
The equalities hold on each source free carrier, not on arbitrary
values of the underlying total functions.

`tor_map_left(R,M,L,f,N,n)` tensors this canonical chain map with the
identity of N. `ext_map_left` precomposes, so it reverses the arrow:
`Ext(L,N)→Ext(M,N)`. The concrete carrier of a module supplies free
generators here. An abstract abelian category does not, merely from
its axioms, supply this free-on-underlying-set construction; mathlib's
abstract Tor API instead uses derived functors and projective
resolutions. This is a difference in the level of generality, not an
obstruction to a concrete construction in a module category.

| member | statement |
|---|---|
| `TorMapLeftDef`, `ExtMapLeftDef` | named covariant Tor and contravariant Ext maps |
| `TorMapLeftHom`, `TorMapLeftIdentity`, `TorMapLeftCompose` | linearity, identity and composition on quotient carriers — card |
| `ExtMapLeftHom`, `ExtMapLeftIdentity`, `ExtMapLeftCompose` | the corresponding laws with reversed composition |

## Balance of Tor

For the resolutions of M and N, the (p,q) cell is the free module on
`S_M(p)×S_N(q)`. The total basis retains the bidegree:
`(p,(x,y))` with `p≤n`, `x∈S_M(p)` and `y∈S_N(n−p)`.
All degrees live at functions on
`prod(num,prod(I(A,B),I(A,C)))`. The tag is necessary: an untagged
union would identify distinct summands when their generators coincide.
The differential is `d_M⊗1 + (−1)^p 1⊗d_N`.

Currying the tagged coefficients identifies this total with the
general finite-diagonal total in `chain_complex`. Slicing a cell as
`x↦(y↦u(x,y))` identifies its vertical boundary and augmentation with
pointwise maps of the resolution of N. FreeTensorExact applied to the
kernel short exact sequences gives exact augmented columns. The
general AugmentedAssembly theorem therefore makes the left edge a
quasi-isomorphism. Signed transposition with sign $(-1)^{pq}$ gives
the right edge and is an involution.

`tor_balance` is the right homology edge after
`inverse_on(homology(total_complex(R, M, N), n), left_edge)`. The
left edge's isomorphism makes this carrier inverse an isomorphism in
the reverse direction (`IsomorphismInverse`), so its composite with
the right edge is an isomorphism.
Naturality follows from the explicit total map that keeps p and
replaces δ_x by its canonical lift under f. The two edge squares
commute, so transporting the second-variable long exact sequence
identifies its arrows with the named first-variable maps. Involution
also gives the opposite naturality square.

| member | statement |
|---|---|
| `TensorFreeIsFreeOnProduct`, `FreeTensorExact` | product-basis freeness and exactness of the finite-support functor — card |
| `totalBasisDef`, `totalCellsDef`, `totalHorizontalDef`, `totalVerticalDef`, `totalTaggedBasisDef`, `totalBoundaryDef`, `totalComplexOf` | the commuting double complex and its tagged total |
| `ResolutionDoubleComplex`, `TotalComplex`, `TotalCurryIso` | validity and the currying identification — card |
| `totalSwapDef` | the signed transposition |
| `TotalSwapChain`, `TotalSwapInvolution` | its chain-map and involution laws — card |
| `totalLeftAugmentationDef`, `totalLeftEdgeDef`, `totalRightEdgeDef` | the two augmented edges |
| `TotalRightEdgeChain` | the right edge is a chain map — card |
| `TotalLeftAugmentationOnto` | the left augmentation maps the bottom row of cells linearly onto the tensor complex — card |
| `TotalLeftColumnsExact` | the augmented columns of the tensor double complex are exact — card |
| `TotalLeftAugmentationSquare` | the left augmentation commutes with the horizontal boundary out of the bottom row — card |
| `TotalLeftQuasiIsomorphism` | the left edge induces isomorphisms from the total complex's homology onto Tor: currying, then the augmented assembly |
| `TotalRightQuasiIsomorphism` | the right edge induces isomorphisms onto Tor of the swapped pair — card |
| `torBalanceDef` | the named balance map |
| `TorBalanceMapIso`, `TorBalance` | its isomorphism law, and the existence of a cross-type isomorphism — card |
| `TorBalanceInvolution`, `TorBalanceNaturalLeft` | balance is involutive and natural — card |
| `torConnectingLeftDef` | the connecting map transported through balance |
| `TorLongExactLeftMiddle`, `TorLongExactLeftQuotient`, `TorLongExactLeftSub`, `TorLongExactLeftEnd` | the first-variable long exact sequence — card |

## The cost and what stays out

The fixed embedding uses choice, and its decoders are only inverse on
specified images. Tor's carrier type depends on M's carrier type;
changing that type gives an isomorphic module rather than the same
set. Maps keep the module records needed to determine operations.
Balance remains a theorem proved by the two augmented edges; it is
not part of the definition of Tor.

The chapter states no Ext balance, no injective resolutions and no
first-variable long exact sequence for Ext. Enough injectives needs
divisible groups and modules of the form `Hom_ℤ(R,D)` inside an ambient
construction whose size is bounded and which keeps all degrees in one
type; a naive product indexed by `Hom(M,ℚ/ℤ)` does not by itself give a
fixed type through repeated cokernels.
