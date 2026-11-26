# algebra_deformation — the deformations of an algebra over a square-zero thickening, their obstruction in D^2 and their torsor under D^1, read through pullbacks and pushouts of square-zero extensions

A square-zero extension moves along a map in two ways. Over a tower
`R → S → T`, through `f` and `g`, an extension `E` of `T` by `N` over `R`
pulls back along `g` to the extension `g*E = square_zero_pullback(S, f,
g, E)` of `S` by `N`: the pairs `(s, e)` with `g(s) = p(e)`. Its sections
over `R` are the lifts of `g` to `E`, and an extension has a section
exactly when its class is zero, so the class of `g*E` in `D^1(S/R, N)` is
the obstruction to lifting `g`; the lifts, when there are any, are a
torsor under the derivations of `S` over `R` into `N`, a derivation `d`
moving a lift `s` to `s + i ∘ d`. An extension `E` of `S` by `N` pushes
out along a linear map `ι : N → N'` to `ι_*E = square_zero_pushout(N, N',
ι, E)`, the ring `E.ring ⋉ N'` modulo the pairs `(i(n), −ι(n))`, whose
class is the image of `E`'s under composition with `ι`.

The cohomology sequence of the tower (algebra/cotangent/transitivity)
is read through these. Its right map `D^1(T/R, N) → D^1(S/R, N)` is the
pullback. When `f` is onto, `D^0(S/R, N)` vanishes and the left map
`D^1(T/S, N) → D^1(T/R, N)` is injective. An extension `S'` of `S` is the
pullback of an extension of `T` exactly when the connecting map kills
its class in `D^2(T/S, N)`, and the classes of those extensions are then
a torsor under `D^1(T/S, N)`. The classification
(algebra/cotangent/square_zero_classification) states its classes with
coefficients over the algebra itself and the sequence with coefficients
over `T`; the two have the same classes, the same zero and the same sum
(`CohomologyCoefficientRestriction`).

A thickening is a ring map `f` from `R` onto `R₀` whose kernel `J` has
square zero: `R` is then an extension of `R₀` by `J` over `R`, a member of
`R₀` acting on `J` through any preimage (`thickening_kernel`). Over an
algebra `T` over `R₀` through `g`, a module `M` over `T` and a map `ι` from
`J` to `M` linear over `R₀`, the thickening class `ξ = thickening_class(R,
R₀, f, M, ι)` is the class of `R` pushed along `ι`, and a deformation
(`algebra_deformation`) is an extension `E` of `T` by `M` over `R` whose
structure map on `J` is the inclusion after `ι`, equivalently whose
pullback along `g` has class `ξ`. This is Illusie's theorem in the form
the sequence gives it: a deformation exists exactly when `∂¹(ξ)`
(`algebra_deformation_obstruction`) vanishes in `D^2(T/R₀, M)`; the
classes of the deformations are a torsor under `D^1(T/R₀, M)`, acting
through the left map; and the automorphisms of one are the derivations
of `T` over `R₀` into `M`. No 2-cocycle is built: the obstruction is the
connecting map. The action is the Baer sum
(algebra/ring/square_zero_extension): the class of a Baer sum is the sum
of the two classes, an extension of `T` over `R₀` read over `R` keeps its
class under the left map, and a deformation plus such an extension is a
deformation whose class has moved by the extension's.

The tower is three rings on three types with ring maps `f` onto `R₀` and
`g`, not `R₀` written as the quotient `R/J`. Every surjection with
square-zero kernel is a thickening — the quotient by `J` with its
projection, the first projection of a split extension `P ⋉ N` — and three
rings on three types have their universes in one host by one cite of
`ConcreteUniverse`, a quotient by `QuotientCotangentUniverse`. The
coefficients are any pair `(M, ι)`, not $J \otimes_{R_0} T$ itself: the
obstruction, the torsor and the automorphisms hold for every pair, and
the flat deformations of `T`, for `T` flat over `R₀`, are the case
$M = J \otimes_{R_0} T$ with `ι(j) = j ⊗ 1`. A statement that reads a class carries
`cotangent_universe` for the rings whose standard resolutions it reads,
and an extension it asserts exists is at `set(prod(U, D))`, the type of
the realizations.

## The definitions

| member | statement |
|---|---|
| `ThickeningKernelDef` | `thickening_kernel(R, S, f)`: the kernel `J` of `f` under `R`'s sum, `b` in `S` acting by multiplication with a chosen preimage |
| `SquareZeroPullbackDef` | `square_zero_pullback(S, f, g, E)`: the pairs `(s, e)` with `g(s) = p(e)` under the componentwise operations, structure map `a ↦ (f(a), k(a))`, inclusion `n ↦ (0, i(n))`, projection the first component |
| `SquareZeroPushoutDef` | `square_zero_pushout(N, N', ι, E)`: `E.ring ⋉ N'` modulo the pairs `(i(n), −ι(n))`, structure map `a ↦ [(k(a), 0)]`, inclusion `m ↦ [(0, m)]`, projection `[(e, m)] ↦ p(e)` |
| `ThickeningClassDef` | `thickening_class(R, S, f, N, ι)` = `square_zero_class` of the thickening `R → S` pushed along `ι` |
| `AlgebraDeformationDef` | `algebra_deformation(R, R₀, f, T, g, M, ι, E)` ⇔ `E` is a square-zero extension of `T` by `M` over `R` with `E.structure(j) = i(ι(j))` on `J` |
| `AlgebraDeformationObstructionDef` | `algebra_deformation_obstruction(R, R₀, f, T, g, M, ι)` = `co_transitivity_connecting` in degree 1 at `ξ` |

## Pullbacks and lifts

| member | statement |
|---|---|
| `PullbackIsExtension` | `g*E` is a square-zero extension of `S` by `N` read over `S`, and the second projection is a ring map to `E.ring` — card |
| `PullbackSplitsIffLift` | a section `σ` of `g*E` over `R` gives the lift `snd ∘ σ` of `g`, and a lift `s` the section `y ↦ (y, s(y))` — card |
| `SplitExtensionClassZero` | `S ⋉ N` is an extension with a section; an extension has a section ⇔ its class is zero ⇔ it is isomorphic to `S ⋉ N` — card |
| `LiftExistsIffObstructionZero` | `g` lifts to `E` ⇔ the class of `g*E` in `D^1(S/R, N)` is zero — card |
| `LiftsTorsorUnderDerivations` | a derivation `d` moves a lift `s` to `s + i ∘ d`, two lifts differ by one derivation, determined on `S` — card |

## Pushouts

| member | statement |
|---|---|
| `PushoutIsExtension` | `ι_*E` is a square-zero extension of `S` by `N'`, `e ↦ [(e, 0)]` a ring map, `[(e, m)]` projecting to `p(e)`, `[(i(n), 0)] = i'(ι(n))` — card |
| `PushoutClassIsCoefficientMap` | the class of `ι_*E` is the image of `E`'s class under composition with `ι` — card |

## The cohomology sequence of a tower

| member | statement |
|---|---|
| `CohomologyCoefficientRestriction` | `D^n(S/R, N')` through `k ∘ g` has the classes, zero and sum of `D^n(S/R, N)` with `N'` read over `T` along `k` — card |
| `SurjectiveBaseDerivationsZero` | `f` onto ⇒ `D^0(S/R, N)` is zero — card |
| `RestrictionMapInjective` | `f` onto ⇒ the left map `D^1(T/S, N) → D^1(T/R, N)` is injective — card |
| `RightMapIsPullback` | the right map sends the class of `E` to the class of `g*E` — card |
| `TowerExtensionObstruction` | `S' ≅ g*T'` for some extension `T'` of `T` ⇔ the connecting map kills the class of `S'` — card |
| `TowerExtensionTorsor` | `f` onto ⇒ the classes over `T` whose pullback is the class of `S'` are a torsor under `D^1(T/S, N)`, `ζ ↦ ζ + i*(η)` — card |

## Deformations

| member | statement |
|---|---|
| `ThickeningIsExtension` | `f` onto with square-zero kernel ⇒ `thickening_kernel(R, R₀, f)` is a module over `R₀` and `R` an extension of `R₀` by it — card |
| `DeformationIffPullbackClass` | `E` is a deformation ⇔ the class of `g*E` is `ξ`; then `[(a, m)] ↦ (f(a), k(a) + i(m))` is an isomorphism from the pushed thickening onto `g*E` — card |
| `DeformationKernelGenerated` | `ι(J)` spans `M` ⇒ the kernel of a deformation's projection is the ideal `J·E` — card |
| `DeformationIffFlat` | `J² = 0`, `T` flat over `R/J`, `M ≅ T ⊗ J` through `ι`: an algebra `X` over `R` onto `T` is flat with kernel `J·X` exactly when some inclusion of `M` makes it a deformation — card |
| `DeformationObstruction` | a deformation exists ⇔ `∂¹(ξ) = 0` in `D^2(T/R₀, M)` — card |
| `DeformationsTorsor` | the classes of the deformations are a torsor under `D^1(T/R₀, M)`, `[E] ↦ [E] + i*(η)` — card |
| `DeformationAutomorphisms` | the automorphisms of an extension of `T` by `M` over `R` are `e ↦ e + i(d(p(e)))` for the derivations `d` of `T` over `R₀`, composition the sum — card |

## Localization

| member | statement |
|---|---|
| `SquareZeroLocalizationClass` | the class of `E` localized at a lift of `t` is the restriction of the class of `E` to `S'`, coefficients carried by `ν` — card |
| `DeformationLocalizes` | a deformation of `T` localized at a lift of `t` is a deformation of `T'` with coefficients `(M', ν ∘ ι)` — card |

## The Baer sum

| member | statement |
|---|---|
| `BaerSumClass` | the class of `E ⊕ E'` in `D^1(S/R, N)` is the sum of the two classes — card |
| `LeftMapIsRestrictionOfScalars` | an extension `E` of `T` over `S`, read over `R` through `f`, is an extension, and the left map sends the class of `E` to its class — card |
| `DeformationBaerSum` | a deformation `E` plus an extension `X` over `R₀` read over `R` is a deformation of class `[E] + i*[X]`; for two deformations, `E' ≅ E ⊕` the realization of the one `η` with `[E'] = [E] + i*(η)` — card |
