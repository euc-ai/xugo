# square_zero_extension — square-zero extensions of an algebra by a module, built from conormal maps of a presentation and read back through lifts

A square-zero extension of an algebra `S` over `R`, through `f`, by a
module `N` over `S` is a ring `X` over `R` with a projection onto `S`
whose kernel is `N`: an additive injection `i` of `N` onto the kernel,
on which `X` acts through the projection as `S` acts on `N`, so that the
kernel has square zero. The four pieces are one value of the record
`square_zero_ops(A, B, C, D)`, `mk_square_zero(X, k, i, p)`, read as
`E.ring`, `E.structure`, `E.inclusion` and `E.projection`; the ring sits
on a type `C` of its own, and `square_zero_extension(R, S, f, N, E)` is
the structure on it. Two extensions, on two types, are isomorphic
(`square_zero_isomorphism`) when a ring isomorphism of their rings is
over `R`, the identity on `N` and over `S`.

The chapter works over an algebra `P` over `R`, through `h`, with a ring
map `ε` onto `S` and kernel `I` — any presentation, before a polynomial
one is chosen. The split extension `P ⋉_ε N`
(`split_square_zero(P, ε, N)`) has the pairs `(u, n)` for its members,
multiplied by `(u, n)(v, m) = (uv, ε(u) • m + ε(v) • n)`. A conormal map
`γ` of `ε` into `N` (algebra/ring/partial_derivative) twists it: the
graph of `−γ` over `I`, `twisted_graph(N, I, γ)`, is an ideal `J_γ`,
and the quotient `E_γ = square_zero_graph(P, h, S, ε, N, γ)` is a
square-zero extension in which `(x, 0)` and `(0, γ(x))` are one coset.
A derivation `d` of `P` into `N` shears `P ⋉_ε N` by
`(u, n) ↦ (u, n − d(u))`, an automorphism over `P` fixing `N`, and the
shear carries $J_{\gamma_1}$ onto $J_{\gamma_2}$ when `γ₂ − γ₁` is `d` on `I`: then
$E_{\gamma_1} \cong E_{\gamma_2}$. Over `S` itself, with `ε` the identity and the structure map
`a ↦ (f(a), 0)`, it is the extension `«split»(S, f, N)` of the chapter's
table.

Back from an extension `E`: on the kernel of the projection the
inclusion `i` has an inverse `i⁻¹`, the coefficient in `N` that
`inverse_on` chooses, additive and linear over the projection. A lift
`s` of `ε` to `E` (`square_zero_lift`) carries `I` into that kernel, and
`γ_s(x) = i⁻¹(s(x))` (`extract_conormal`) is a conormal map.
`(u, n) ↦ s(u) + i(n)` maps `P ⋉_ε N` onto `E` with kernel $J_{\gamma_s}$,
so $E_{\gamma_s} \cong E$ by the first isomorphism theorem
(algebra/ring/quotient_ring, `QuotientFirstIso`), its value on each
coset named. Two lifts differ by a derivation, unique on `P`, whose
restriction to `I` is the difference of their conormal maps. Every
isomorphism here is a named map: the shear's through `QuotientAutoIso`,
the lift's through `QuotientFirstIso`, so a later statement computes
with it on cosets.

The graph `twisted_graph(N, I, γ)` and the shear `derivation_shear(N, d)`
are algebra/module/module_extension's: they read only `N`'s sum and
negation, and the extensions of a module by a module are built from the
same two maps.

Two extensions `E`, `E'` of `S` by `N` add: their Baer sum
`square_zero_baer_sum(N, E, E')` is the fibre product
`square_zero_fiber_product(E, E')`, the pairs `(e, e')` over one member
of `S`, modulo the pairs `(i(n), −i'(n))`. The sum is an extension
again, and up to the named isomorphisms it is commutative and
associative, the split extension `S ⋉ N` is its unit and `E` with the
inclusion negated is the inverse of `E`. It localizes chartwise: the sum
localized at a pair of lifts is the sum of the localizations.

The classification of the extensions by `D^1(S/R, N)` is
algebra/cotangent/square_zero_classification, which takes `P` to be the
standard presentation `R[S]`; nothing here reads a resolution or a
cohomology. Constitution §Structures has the conventions for a structure
held in a record.

## The record and the structure

| member | statement |
|---|---|
| `SquareZeroOpsData` | the record `square_zero_ops(A, B, C, D)`: `mk_square_zero(X, k, i, p)`, its projections `E.ring`, `E.structure`, `E.inclusion`, `E.projection` and the derived principles |
| `SquareZeroExtension` | `square_zero_extension(R, S, f, N, E)`: `E.structure` a ring map from `R`, `E.projection` one onto `S` with `p ∘ k = f`, `N` a module over `S`, `E.inclusion` additive, injective, onto the kernel of the projection, `i(n) i(m) = 0` and `e i(n) = i(p(e) • n)` |
| `StructureHomomorphism` | `E.structure` is a ring map from `R` |
| `ProjectionHomomorphism` | `E.projection` is a ring map to `S` |
| `ProjectionOnto` | `image(E.projection, E.ring.carrier) = S.carrier` |
| `ProjectionOverBase` | `p(k(a)) = f(a)` on `R`'s carrier |
| `CoefficientModule` | `module_on(S, N)` |
| `InclusionAdd` | `i(n + m) = i(n) + i(m)` |
| `InclusionInjective` | `injective_on(N.carrier, E.inclusion)` |
| `InclusionImage` | the image of `N` is the kernel of the projection |
| `InclusionSquareZero` | `i(n) i(m) = 0` |
| `InclusionAction` | `e i(n) = i(p(e) • n)` |
| `SquareZeroIsomorphismDef` | `square_zero_isomorphism(R, N, E, E', φ)`: a ring isomorphism of the rings with `φ ∘ k = k'`, `φ ∘ i = i'` and `p' ∘ φ = p` |
| `SquareZeroLiftDef` | `square_zero_lift(R, P, h, ε, E, s)`: `s` a ring map from `P` to `E.ring` with `s ∘ h = k` and `p ∘ s = ε` |

## The constructions over P

| member | statement |
|---|---|
| `SplitSquareZeroDef` | `split_square_zero(P, ε, N)`: the pairs of `set_cross(P.carrier, N.carrier)`, componentwise sum, `(u, n)(v, m) = (uv, ε(u) • m + ε(v) • n)`, one `(1, 0)` |
| `SquareZeroGraphDef` | `square_zero_graph(P, h, S, ε, N, γ)`: `ideal_quotient_ring(P ⋉_ε N, J_γ)` with structure map `a ↦ [(h(a), 0)]`, inclusion `n ↦ [(0, n)]`, projection `[(u, n)] ↦ ε(u)` |
| `ExtractConormalDef` | `extract_conormal(P, S, ε, N, E, s, x)` = `i⁻¹(s(x))` on the kernel of `ε`, `N.zero` off it |

## The split extension and the graph

| member | statement |
|---|---|
| `SplitSquareZeroRing` | `P ⋉_ε N` is a commutative ring, `u ↦ (u, 0)` and `(u, n) ↦ ε(u)` are ring maps, `(0, n)` lies in it with `(0, n) + (0, m) = (0, n + m)` and `z (0, n) = (0, ε(fst z) • n)` |
| `TwistedGraphIdeal` | `γ` a conormal map ⇒ `J_γ` is an ideal of `P ⋉_ε N` — card |
| `GraphQuotientExtension` | `ε` onto, `γ` a conormal map ⇒ `E_γ` is a square-zero extension of `S` by `N` over `R`, its projection reads `[(u, n)]` as `ε(u)`, and `[(x, 0)] = i(γ(x))` for `x` in `I` — card |

## The shear by a derivation

| member | statement |
|---|---|
| `DerivationShearAutomorphism` | `d` a derivation ⇒ the shear is a ring automorphism of `P ⋉_ε N` with inverse the shear by `−d`, fixing `(h(a), 0)` and `(0, n)` — card |
| `ShearGraphExtensionIso` | `γ₂ − γ₁ = d` on `I` ⇒ the shear carries $J_{\gamma_1}$ onto $J_{\gamma_2}$ and induces $E_{\gamma_1} \cong E_{\gamma_2}$, `[z] ↦ [shear(z)]` — card |

## The inclusion and its inverse on the kernel

| member | statement |
|---|---|
| `InclusionIn` | `n ∈ N` ⇒ `i(n) ∈ E.ring.carrier` |
| `InclusionAdditive` | `i` is a homomorphism of the additive groups of `N` and `E.ring` |
| `InclusionZero` | `i(0) = 0` |
| `InclusionNeg` | `n ∈ N` ⇒ `i(−n) = −i(n)` |
| `InclusionInverse` | `e` in the kernel of the projection ⇒ its coefficient `i⁻¹(e) = inverse_on(N.carrier, i, e)` lies in `N` and `i(i⁻¹(e)) = e` |
| `InclusionInverseLeft` | `n ∈ N` ⇒ `i⁻¹(i(n)) = n` |
| `InclusionInverseAdd` | `e₁`, `e₂` in the kernel ⇒ `i⁻¹(e₁ + e₂) = i⁻¹(e₁) + i⁻¹(e₂)` |
| `InclusionInverseSub` | `e₁`, `e₂` in the kernel ⇒ `i⁻¹(e₁ − e₂) = i⁻¹(e₁) − i⁻¹(e₂)` |
| `InclusionInverseMul` | `x ∈ E.ring`, `e` in the kernel ⇒ `i⁻¹(x e) = p(x) • i⁻¹(e)` |

## Lifts and the conormal map they read

| member | statement |
|---|---|
| `LiftExtractConormal` | `s` a lift to an extension ⇒ `γ_s` is a conormal map — card |
| `LiftSumSurjectiveHom` | `ε` onto ⇒ `(u, n) ↦ s(u) + i(n)` is an algebra map over `R` from `P ⋉_ε N` onto `E.ring` — card |
| `LiftSumKernelAndQuotientIso` | `ε` onto ⇒ the kernel of the sum map is $J_{\gamma_s}$, and its induced map is an isomorphism $E_{\gamma_s} \cong E$, `[(u, n)] ↦ s(u) + i(n)` — card |
| `LiftDifferenceDerivation` | two lifts ⇒ `s₂ − s₁ = i ∘ d` for a derivation `d`, unique on `P`, with $\gamma_{s_2} - \gamma_{s_1} = d$ on `I` |

## Localization at a lift

| member | statement |
|---|---|
| `SquareZeroLocalizationDef` | `square_zero_localization(N, S', ρ, N', ν, E, t')`: the fraction classes of `E.ring` at the powers of `t'`, structure map `a ↦ k(a)/1`, inclusion `m ↦ i(n)/v` for a chosen `(n, v)` with `ρ(p(v)) • m = ν(n)`, projection `e/v ↦ ρ(p(e))/ρ(p(v))`; `S'`, `N'` any localizations of `S`, `N` at the powers of `p(t')`, as fractions or in place |
| `SquareZeroLocalizationIsExtension` | `t'` a lift of `t`, `S'` and `N'` localizations of `S` and `N` at the powers of `t` ⇒ `E` localized at `t'` is a square-zero extension of `S'` by `N'` over `R` — card |
| `SquareZeroLocalizationIndependent` | two lifts `t₁`, `t₂` of `t` ⇒ $\frac{e}{t_1^k} \mapsto \frac{e(2t_2 - t_1)^k}{t_2^{2k}}$ is an isomorphism of the two localizations — card |
| `SpanIsModuleLocalization` | in place: `R = ring_away(R, A₀, t)`, `t` a unit, `M₀` an `A₀`-submodule of a module `V` over `R` ⇒ the span of `M₀` over `R`, with the identity, is the localization of `M₀` at the powers of `t` (`is_module_localization_on`) — card |
| `SplitSquareZeroLocalization` | `S ⋉ N` localized at `(t, 0)` ≅ `S' ⋉ N'`, the class of `((a, m), (s, 0))` going to `(ρ(a)/ρ(s), ν(m)/ρ(s))` — card |

## The Baer sum

| member | statement |
|---|---|
| `SquareZeroFiberProductDef` | `square_zero_fiber_product(E, E')`: the pairs `(e, e')` of the two rings with `p(e) = p'(e')`, componentwise operations |
| `SquareZeroBaerSumDef` | `square_zero_baer_sum(N, E, E')`: the fibre product modulo the pairs `(i(n), −i'(n))`, structure map `a ↦ [(k(a), k'(a))]`, inclusion `n ↦ [(i(n), 0)]`, projection `[(e, e')] ↦ p(e)` |
| `BaerSumIsExtension` | the fibre product is a commutative ring, the antidiagonal an ideal, `E ⊕ E'` a square-zero extension of `S` by `N` over `R`, `[(e, e')]` projecting to `p(e)`, `[(0, i'(n))]` the inclusion of `n` — card |
| `BaerSumIsomorphism` | `φ : E ≅ X`, `φ' : E' ≅ X'` ⇒ `[(e, e')] ↦ [(φ(e), φ'(e'))]` is an isomorphism `E ⊕ E' ≅ X ⊕ X'` — card |
| `BaerSumSplitUnit` | `S ⋉ N` is an extension, and `[(e, (y, n))] ↦ e + i(n)` is an isomorphism `E ⊕ (S ⋉ N) ≅ E` — card |
| `BaerSumComm` | `[(e, e')] ↦ [(e', e)]` is an isomorphism `E ⊕ E' ≅ E' ⊕ E` — card |
| `BaerSumAssoc` | `[([(e, e')], e'')] ↦ [(e, [(e', e'')])]` is an isomorphism `(E ⊕ E') ⊕ E'' ≅ E ⊕ (E' ⊕ E'')` — card |
| `BaerSumInverse` | `E⁻` (inclusion `n ↦ −i(n)`) is an extension, and `[(e, e')] ↦ (p(e), i⁻¹(e − e'))` is an isomorphism `E ⊕ E⁻ ≅ S ⋉ N` — card |
| `BaerSumLocalizes` | lifts `t₀`, `t₀'` of `t`, `S'` and `N'` localizations of `S` and `N` at the powers of `t` ⇒ `E ⊕ E'` localized at `[(t₀, t₀')]` ≅ the Baer sum of the localizations, `[(e, e')]/τᵏ ↦ [(e/t₀ᵏ, e'/t₀'ᵏ)]` — card |
