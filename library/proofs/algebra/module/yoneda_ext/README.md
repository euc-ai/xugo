# yoneda_ext — the extensions of a module by a module classified by Ext¹, with both directions explicit

For modules `M` and `N` over `R`, the isomorphism classes of extensions
of `M` by `N` (algebra/module/module_extension) are the members of
`Ext¹(M, N)`, the cohomology in degree 1 of the Hom complex of the
canonical resolution (algebra/module/tor_ext). This chapter reads that
cohomology on the canonical resolution's first two terms, then joins it
to the extension constructions; it does not restate `tor_ext`.

The canonical resolution (algebra/module/resolution) has in degree 0 the
free module `F₀` on the codes of `M`'s elements, augmented by
`canonical_eps` with kernel `K`. In degree 1 its basis is `K` itself
under the index embedding `j`, and the boundary sends the generator at
`j(k)` to `k`. So a 1-cochain `g`, a function on the generators of degree
1, is a cocycle exactly when its linear extension kills the kernel of
that boundary, and `syzygy_map(R, M, N, g)`, `k ↦ g(j(k))`, is then a
homomorphism `K → N`. Conversely `syzygy_cocycle(R, M, N, φ)`,
`x ↦ φ(j⁻¹(x))`, is a cocycle for every homomorphism `φ` on `K`. The two
are linear, and inverse as functions: `j⁻¹ ∘ j` on `K`, `j ∘ j⁻¹` on the
generators, both `N.zero` elsewhere. The coboundary of a 0-cochain `h` is
the cochain of the restriction to `K` of `h`'s linear extension, so the
coboundaries are the restrictions of the homomorphisms `F₀ → N`. Hence
`Ext¹(M, N) ≅ Hom(K, N) / image(Hom(F₀, N))`: every class is
`syzygy_class(R, M, N, φ)`, and two maps on `K` have one class exactly
when their difference extends to `F₀`.

From an extension to a class. `F₀` is free, so the augmentation lifts
through the projection of every extension `E` (`FreeLiftThrough`). A
lift reads a map on `K`, and `yoneda_class(R, M, N, E)` is its class.
Two lifts differ by a homomorphism `F₀ → N` restricting to the difference
of their maps, so every lift gives the one class, and an isomorphism of
extensions carries a lift to a lift with the same map.

From a class to an extension, and back. `yoneda_realization(R, M, N, ξ)`
is the graph extension `(F₀ ⊕ N)/J_φ` of `φ = syzygy_map(g)`, `g` a
cocycle chosen in `ξ`; the canonical lift `u ↦ [(u, 0)]` reads `φ` back,
so its class is `ξ`. The realization of the class of `E` is isomorphic
to `E`, through the shear joining the two maps on `K` and the lift's sum
map, and two extensions on any two types are isomorphic exactly when
their classes are equal. Only this bijection is stated; the Baer sum and
the module structure it puts on the extensions are not.

The mechanism is the square-zero classification's
(algebra/cotangent/square_zero_classification) with the cotangent data
replaced: the kernel of a presentation, maps on it, their restrictions
from the free term, the graph and the shear, the first isomorphism
theorem. It is cheaper here because the basis of degree 1 is the kernel
itself, so the bridge needs no representative τ and no derivations.

## The conversions and the classes

| member | statement |
|---|---|
| `syzygyMapDef` | `syzygy_map(R, M, N, g, k)` = `g(j(k))` for `k` in `K`, `N.zero` off `K` |
| `syzygyCocycleDef` | `syzygy_cocycle(R, M, N, φ, x)` = `φ(j⁻¹(x))` for `x` a generator of degree 1, `N.zero` off them |
| `syzygyClassDef` | `syzygy_class(R, M, N, φ)` = the coset of `syzygy_cocycle(R, M, N, φ)` modulo the coboundaries of degree 1 |
| `YonedaClassDef` | `yoneda_class(R, M, N, E)` = `syzygy_class` of `extract_syzygy_map` at a lift chosen among the lifts of the augmentation to `E` |
| `yonedaRealizationDef` | `yoneda_realization(R, M, N, ξ)` = `module_extension_graph` over `F₀` at `syzygy_map(R, M, N, g)`, `g` chosen in `ξ` |

## Cocycles and homomorphisms on the kernel

| member | statement |
|---|---|
| `ExtCocycleSyzygyMap` | `g` a cocycle ⇔ its linear extension kills the kernel of the boundary of degree 1; a cocycle gives the homomorphism `syzygy_map(R, M, N, g)` on `K` — card |
| `ExtSyzygyCocycle` | `φ` a homomorphism on `K` ⇒ `syzygy_cocycle(R, M, N, φ)` is a cocycle — card |
| `SyzygyCocycleLinearInverse` | `syzygy_map ∘ syzygy_cocycle = id` on the homomorphisms on `K`, `syzygy_cocycle ∘ syzygy_map = id` on the 1-cochains; both keep sums, negatives and multiples — card |
| `ExtCoboundaryRestriction` | `δ⁰h` is the cochain of the restriction of `h`'s linear extension to `K`, and the cochain of `φ` is a coboundary ⇔ `φ = f\|_K` for a homomorphism `f: F₀ → N` — card |

## Ext¹ as homomorphisms on the kernel modulo restrictions

| member | statement |
|---|---|
| `ExtClassRepresented` | the class of a homomorphism on `K` is in `Ext¹(M, N)`, and every member of `Ext¹` is such a class — card |
| `SyzygyClassEqIffExtends` | two homomorphisms on `K` have one class ⇔ `φ₂ − φ₁ = f\|_K` for a homomorphism `f: F₀ → N` — card |

## The class of an extension, the realization, and back

| member | statement |
|---|---|
| `YonedaClassWellDefined` | an extension has a lift; its class is in `Ext¹(M, N)`, it is the class of every lift's map, and isomorphic extensions have one class — card |
| `YonedaRealizeClass` | `ξ` in `Ext¹(M, N)` ⇒ its realization is an extension with class `ξ` — card |
| `YonedaRealizeRoundTrip` | every extension `E` is isomorphic to the realization of its class — card |
| `YonedaIsoIffSameClass` | two extensions on any two types are isomorphic ⇔ they have the same class — card |
