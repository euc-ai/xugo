# free_module — the free module on a set: its generators, its universal property, the pushforward along a map of basis sets and the transpose of a linear map

The free module on a set `S` over a ring `R`, its carrier `c = R.carrier`, is the set of
functions from the index type to the ring with finite support, zero off
`S` and valued in `c`, `finite_supp(zero, c, S)`, added, negated and
scaled pointwise. The pointwise operations, finite support and the
modules of functions into a module are
[`function_module`](../function_module/README.md)'s, and the free module
is its `finite_supp_module` at the ring as a module over itself. Its
generators are the indicators `delta_at(x)` of the points of `S`,
every member is the finite sum of its values scaling them, and they are
a basis: read at a point `y`, a combination of them is the coefficient of
`delta_at(y)`. A map `phi` of `S` into a module `M` extends to one
homomorphism, the sum `Σ f(x) • phi(x)` over the support, `free_lift`
read at the ring's zero and at `M`'s addition, zero and scaling. The
extension of the identity of a set `E` spanning `M` maps the free module
on `E` onto `M`: a finitely generated module is a quotient of a free
module on finitely many generators, and every module, spanned by its own
carrier, is a quotient of a free one. When `E` is a basis the extension is
an isomorphism, so values prescribed on a basis extend to a linear map.
A free module is projective: a homomorphism out of it lifts along any
homomorphism whose image contains its image, one preimage chosen per
generator. The free modules on subsets of one index type all live in one type,
which is what lets a resolution be a sequence.

A linear map Φ from the free module on S to the free module on S' has a
transpose with coefficients in N, `hom_precompose(R, N, S, Φ)`: a function
u on S' goes to `s ↦ Σ_t Φ(δ_s)(t) • u(t)` on S, and to `N.zero` off S.
Read as homomorphisms out of the free modules, it is precomposition with
Φ. Pairing a member v of the free module with an N-valued function u by
`free_lift(R.zero, N.add, N.zero, N.smul, u, v)`, the transpose is adjoint
to Φ, and its laws — linear, determined by Φ on the free module,
contravariant, linear in Φ, natural in N — are what a statement about a
dual complex reduces to: the dual of a based complex
([`free_complex_duality`](../free_complex_duality/README.md)), the Hom
complex of a free resolution ([`tor_ext`](../tor_ext/README.md)), the
cochain complex of the cotangent complex.

## The module

`free_module_record(R, S)` packs the pointwise operations and the
carrier `finite_supp(R.zero, R.carrier, S)` into one `module_ops` value.

| member | statement |
|---|---|
| `FreeModuleRecordDef` | the free module with its operations |
| `FreeModuleRecordFiniteSupp` | `free_module_record(R, S) = finite_supp_module(regular_module(R), S)` |
| `FreeModuleOn` | `comm_ring_on(R) ⇒ module_on(R, free_module_record(R, S))` |
| `CoordinateProjectionLinear` | `comm_ring_on(R) ⇒` reading a member of the free module on `S` at one index `x` is a linear functional, `module_homomorphism(R, free_module_record(R, S), regular_module(R), λv. v(x))` |
| `CoordinateRelation` | a coordinate of a vanishing finite combination of a family of the free module vanishes: `Σ_{t∈T} c(t) • e(t) = 0` gives `Σ_{t∈T} c(t) * e(t, x) = R.zero` at every `x` |

## Generators and the universal property

| member | statement |
|---|---|
| `DeltaAtDef` | `delta_at(zero, one, x, y) = COND(y = x, one, zero)` |
| `DeltaAtIn` | `x ∈ S ⇒ delta_at(x) ∈ finite_supp(zero, c, S)` |
| `DeltaAtCoefficientIn` | `r ∈ R.carrier ∧ x ∈ S ⇒ delta_at(R.zero, r, x) ∈ finite_supp(zero, c, S)`: the function r at x and zero elsewhere, for any r in the carrier |
| `DeltaAtInjective` | `R.one ≠ R.zero ⇒ injective_on(S, delta_at(R.zero, R.one))`: distinct points have distinct generators |
| `HomDeltaIn` | a homomorphism k of the free module on S into the free module on T: `x ∈ S ⇒ k(delta_at(R.zero, R.one, x)) ∈ finite_supp(R.zero, R.carrier, T)` |
| `FreeModuleExpand` | `f = Σ_{supp f} f(x) • delta_at(x)` |
| `DeltaAtBasis` | `comm_ring_on(R) ⇒ module_basis(R, free_module_record(R, S), image(delta_at(R.zero, R.one), S))`: the generators are a basis |
| `FreeHomExpand` | a homomorphism h out of the free module on S: `h(f) = Σ_{supp f} f(x) • h(delta_at(x))` |
| `FreeLiftDef` | `free_lift(zero, add, zero', smul, phi, f) = Σ_{supp f} smul(f(x), phi(x))`, the sum taken under `add` from `zero'` |
| `FreeLiftHom` | the extension is a homomorphism into `M` |
| `FreeLiftDelta` | `free_lift(R.zero, M.add, M.zero, M.smul, phi, delta_at(x)) = phi(x)` |
| `FreeLiftOver` | `T` finite holding the support of `f`, `f` in `R` and `phi` in `M` on `T` ⇒ `free_lift(R.zero, M.add, M.zero, M.smul, phi, f) = module_sum(M.add, M.zero, T, λx. f(x) • phi(x))` |
| `FreeLiftUnique` | homomorphisms agreeing on the generators agree |
| `FreeLiftMapLinear` | the extension is linear in the function it extends: with `FreeLiftHom`, `free_lift` is the bilinear pairing of the free module with the `M`-valued functions — card |
| `FreeLiftOntoSpanning` | for `E ⊆ M.carrier` with `module_span(R, M, E) = M.carrier`, `image(free_lift(R.zero, M.add, M.zero, M.smul, λu. u), finite_supp(R.zero, R.carrier, E)) = M.carrier`: `M` is the image of the free module on `E` |
| `FreeLiftOnto` | `image(free_lift(R.zero, M.add, M.zero, M.smul, λu. u), finite_supp(R.zero, R.carrier, M.carrier)) = M.carrier`: every module is the image of the free module on its own carrier |
| `BasisFreeLiftIsomorphism` | for any basis E of M, extending its identity gives an isomorphism from the free module on E to M |
| `BasisLinearExtension` | any assignment of values in N to a basis E of M extends to an R-linear map from M to N |
| `FreeModuleLift` | a homomorphism out of a free module lifts along any homomorphism whose image contains its image: a free module is projective |

## The pushforward along a map of basis sets

`free_pushforward(R,k)` is the free extension of `x ↦ delta_at(k(x))`. It
sums coefficients when different generators have the same image. Thus it
needs no injectivity hypothesis.

| member | statement |
|---|---|
| `FreePushforwardDef` | linear extension of a map of generators |
| `FreePushforwardHom`, `FreePushforwardDelta` | linearity and the value on a generator — card |
| `FreePushforwardIdentity`, `FreePushforwardCompose` | strict equality on the source free carrier — card |

## The transpose

| member | statement |
|---|---|
| `HomPrecomposeDef` | `hom_precompose(R, N, S, Φ, u, x)`: free_lift of u at `Φ(δ_x)` for `x ∈ S`, `N.zero` off `S` |
| `HomPrecomposeHom` | the transpose of a linear map of free modules is linear between the function modules — card |
| `HomPrecomposePairing` | `⟨Φ(v), u⟩ = ⟨v, Φᵗ(u)⟩` under the pairing `free_lift` — card |
| `HomPrecomposeCongruence` | maps equal on the free module have the same transpose — card |
| `HomPrecomposeIdentity`, `HomPrecomposeCompose` | the identity transposes to the identity, a composite to the reversed composite — card |
| `HomPrecomposeLinear` | the transpose is linear in the map: zero, sums, negatives, scalings and finite combinations — card |
| `HomPrecomposeCoefficientNatural` | a linear map of coefficient modules commutes with the transpose — card |
