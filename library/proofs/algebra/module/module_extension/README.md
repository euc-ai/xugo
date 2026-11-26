# module_extension — extensions of a module by a module, built from maps on the kernel of a presentation and read back through lifts

An extension of a module `M` by a module `N` over `R` is a short exact
sequence `N → X → M`: an injective homomorphism `i` of `N` onto the
kernel of a homomorphism `p` of `X` onto `M`. The three pieces are one
value of the record `module_extension_ops(A, B, C, D)`,
`mk_module_extension(X, i, p)`, read as `E.module`, `E.inclusion` and
`E.projection`; the module sits on a type `C` of its own, and
`module_extension(R, M, N, E)` is `short_exact_modules` at its parts
(algebra/module/module_homomorphism). Two extensions, on two types, are
isomorphic (`module_extension_isomorphism`) when an isomorphism of their
modules is the identity on `N` and over `M`.

The chapter works over a module `F` with a linear map `ε` onto `M` and
kernel `K` — any presentation, before a free one is chosen. The product
`F ⊕ N`, `product_module(F, N)` of algebra/module/submodule, has the
pairs `(u, n)` for its members; it is a module, and the inclusions of
`F` and `N` and the projection onto `F` are homomorphisms
(`ProductModuleOn`, algebra/module/module_homomorphism). A homomorphism `φ` from `K` to `N` twists it: the
graph of `−φ` over `K`, `twisted_graph(N, K, φ)`, is a submodule `J_φ`,
and the quotient `E_φ = module_extension_graph(F, M, ε, N, φ)` is an
extension in which `(k, 0)` and `(0, φ(k))` are one coset. A homomorphism `h` from `F` to
`N` shears `F ⊕ N` by `(u, n) ↦ (u, n − h(u))`, an automorphism fixing
`N`, and the shear carries $J_{\varphi_1}$ onto $J_{\varphi_2}$ when `φ₂ − φ₁` is `h`
on `K`: then $E_{\varphi_1} \cong E_{\varphi_2}$.

Back from an extension `E`: a lift `s` of `ε` to `E`
(`module_extension_lift`) carries `K` into the kernel of the projection,
and `φ_s(k) = i⁻¹(s(k))` (`extract_syzygy_map`) is a homomorphism on
`K`. `(u, n) ↦ s(u) + i(n)` maps `F ⊕ N` onto `E` with kernel $J_{\varphi_s}$,
so $E_{\varphi_s} \cong E$ by the first isomorphism theorem for modules, its value
on each coset named. Two lifts differ by one homomorphism `F → N` whose
restriction to `K` is the difference of their maps. Every isomorphism
here is a named map induced on cosets, so a later statement computes
with it.

The graph and the shear read only `N`'s sum and negation; the square-zero
extensions of algebra/ring/square_zero_extension are built from the same
two maps, there an ideal of `P ⋉_ε N` and a ring automorphism. The
classification of the extensions by `Ext¹(M, N)` is
algebra/module/yoneda_ext, which takes `F` to be the degree-0 term of the
canonical resolution; nothing here reads a resolution or a cohomology.

## The record and the structure

| member | statement |
|---|---|
| `ModuleExtensionOpsData` | the record `module_extension_ops(A, B, C, D)`: `mk_module_extension(X, i, p)`, its projections `E.module`, `E.inclusion`, `E.projection` and the derived principles |
| `ModuleExtension` | `module_extension(R, M, N, E)` ⇔ `short_exact_modules(R, N, E.module, M, E.inclusion, E.projection)` |
| `ModuleExtensionIsomorphismDef` | `module_extension_isomorphism(R, N, E, E', φ)`: a module isomorphism with `φ ∘ i = i'` and `p' ∘ φ = p` |
| `ModuleExtensionLiftDef` | `module_extension_lift(R, F, ε, E, s)`: `s` a homomorphism from `F` to `E.module` with `p ∘ s = ε` |

## The constructions over F

| member | statement |
|---|---|
| `TwistedGraphDef` | `twisted_graph(N, I, γ) = image(λx. (x, −γ(x)), I)` |
| `DerivationShearDef` | `derivation_shear(N, d, z) = (fst(z), snd(z) − d(fst(z)))` |
| `ModuleExtensionGraphDef` | `module_extension_graph(F, M, ε, N, φ)`: `quotient_module(F ⊕ N, J_φ)` with inclusion `n ↦ [(0, n)]`, projection `[(u, n)] ↦ ε(u)` |
| `ExtractSyzygyMapDef` | `extract_syzygy_map(F, M, ε, N, E, s, x)` = `i⁻¹(s(x))` on the kernel of `ε`, `N.zero` off it |

## The graph

| member | statement |
|---|---|
| `TwistedGraphSubmodule` | `φ` a homomorphism on `K` ⇒ `J_φ` is a submodule of `F ⊕ N` — card |
| `GraphModuleExtension` | `ε` onto, `φ` a homomorphism on `K` ⇒ `E_φ` is an extension of `M` by `N`, its projection reads `[(u, n)]` as `ε(u)`, and `[(k, 0)] = i(φ(k))` for `k` in `K` — card |

## The shear by a homomorphism

| member | statement |
|---|---|
| `ShearModuleExtensionIso` | `h` a homomorphism `F → N` ⇒ the shear is an automorphism of `F ⊕ N` with inverse the shear by `−h`, fixing `(0, n)`; `φ₂ − φ₁ = h` on `K` ⇒ it carries $J_{\varphi_1}$ onto $J_{\varphi_2}$ and induces $E_{\varphi_1} \cong E_{\varphi_2}$, `[z] ↦ [shear(z)]` — card |

## Lifts and the map on the kernel they read

| member | statement |
|---|---|
| `LiftExtractSyzygy` | `s` a lift to an extension ⇒ `φ_s` is a homomorphism on `K` — card |
| `LiftSumQuotientIso` | `ε` onto ⇒ `(u, n) ↦ s(u) + i(n)` is a homomorphism onto `E.module` with kernel $J_{\varphi_s}$, and its induced map is an isomorphism $E_{\varphi_s} \cong E$, `[(u, n)] ↦ s(u) + i(n)` — card |
| `LiftDifferenceHom` | two lifts ⇒ `s₂ − s₁ = i ∘ h` for one homomorphism `h: F → N`, with $\varphi_{s_2} - \varphi_{s_1} = h$ on `K` — card |
