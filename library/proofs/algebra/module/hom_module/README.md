# hom_module — the module of homomorphisms, and the left exactness of Hom

The homomorphisms from a module `M` to a module `N` over one ring,
read as zero off `M`, form a set of functions `hom_set(R, M, N)` closed
under the pointwise operations, and those make it a module over the
same ring. Composing after a homomorphism `g: N → L` is a homomorphism
`Hom(M, N) → Hom(M, L)`; it is one-to-one when `g` is, and for a
left-exact `N → L → K` the sequence of homomorphism modules is exact
in the middle. The derived functors Ext are the cohomology of
`Hom(P, N)` for a free resolution `P`; there the homomorphisms out of a
free module are read as functions on its index set.

## Members

| member | statement |
|---|---|
| `HomSetDef` | `hom_set(R, M, N) = {f \| module_homomorphism(R, M, N, f) ∧ f = 0 off M}` |
| `InHomSet` | `g ∈ hom_set(R, M, N)` exactly when `g` is a homomorphism `M → N` that is zero off `M` |
| `HomModuleDef` | `hom_module(R, M, N)`: `hom_set(R, M, N)` under the pointwise operations of `N` |
| `HomSetModuleOn` | a module under the pointwise operations |
| `PostComposeHom` | `f ↦ g ∘ f` is a homomorphism `Hom(M, N) → Hom(M, L)` |
| `PostComposeInjective` | one-to-one on `Hom(M, N)` when `g` is one-to-one on `N`, linear or not |
| `HomLeftExact` | exact in the middle for a left-exact `N → L → K`, `p` linear or not as long as it keeps zero |

`M` and `N` are `module_ops` records. `HomModuleDef` packages the
pointwise operations and `hom_set(R,M,N)` as `hom_module(R,M,N)`.
The zero-outside-source condition is part of the carrier, and
postcomposition keeps it: off `M`, `g ∘ f` takes the value
`g(N.zero) = L.zero`.

## The maps out of the ring

Evaluation at one identifies `Hom(R, W)` with `W`: a map of the regular
module is determined by its value at one, and every vector of `W` is
such a value.

| member | statement |
|---|---|
| `RegularHomIsScalarMap` | a map `ψ ∈ hom_set(R, regular_module(R), W)` is `x ↦ x · ψ(R.one)` on `R`, zero off it |
| `ScalarMapIsRegularHom` | for `module_on(R, W)` and `v ∈ W.carrier`, `x ↦ x · v` on `R`, zero off it, lies in `hom_set(R, regular_module(R), W)` |

## Restriction and coextension of scalars

| member | statement |
|---|---|
| `RestrictScalarsModuleOn` | for a ring map `f: R → T` and `module_on(T, N)`, `scalar_restriction(f, N)` is a module over `R` |
| `ScalarRestrictionIndependent` | a set is independent over `R` acting through a one-to-one ring map `f` exactly when it is independent over the image of `f` |
| `CoextendScalarsDef` | `coextend_scalars(R, T, f, M)`: the R-linear maps `T → M` (T over R through f), zero off `T`, added pointwise, `(t · φ)(x) = φ(t * x)` on `T` |
| `CoextendScalarsModuleOn` | `f` a ring map, `module_on(R, M)` ⇒ `module_on(T, coextend_scalars(R, T, f, M))` |
| `CoextendScalarsAdjunction` | for `module_on(T, N)`, `φ ↦ (n ↦ φ(n)(T.one))` is an isomorphism over `R` from `Hom_T(N, coextend_scalars(R, T, f, M))` to `Hom_R(N, M)`, `N` read over `R` through `f` |
