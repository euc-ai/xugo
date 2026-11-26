# flat_module — flat modules over a commutative ring, read through Tor, and flatness across a square-zero thickening

A module `M` over `R` is flat when tensoring with it keeps one-to-one
maps one-to-one. The chapter defines it through Tor
([`tor_ext`](../tor_ext/README.md)): `flat_module(R, M)` says `M` is a
module over `R` and `Tor₁(M, R/I)` is the zero module for every ideal
`I`, where `R/I` is the quotient of the regular module by `I` and zero
reads `tor(R, M, N, 1) = {tor_zero(R, M, N, 1)}`, the boundaries the one
class. The definition tests only the cyclic modules `R/I` because a
constant cannot range over modules at a type it does not carry; the
general statements are theorems. `FlatTorVanishes` gives
`Tor_n(M, N) = 0` for every module `N` at every type in every positive
degree, `FlatTensorInjective` the exactness of `M ⊗ −` at every pair of
types, and `FlatIdealCriterion` the classical form, one-to-one maps
`M ⊗ I → M ⊗ R`. A converse over arbitrary test types is not a
statement: at a one-point type every module is zero and every map
one-to-one.

Tor against free modules is where the arguments start. Tensoring the
canonical resolution with `R` gives the resolution back, so `Tor_n(M, R)`
vanishes above degree zero; and the tensor complex at a finitely
supported sum `finite_supp_module(N, S)` is the sum of the complexes at `N`,
slice by slice, so Tor commutes with it.

The second half reads flatness across a square-zero thickening
`R → R₀ = R/J`, `J² = 0`. `R₀` is `ideal_quotient_ring(R, J)`, the
corpus's quotient ring, whose members are the cosets of `J`, and a
module over `R₀` is a module record whose scalars are those cosets. Two
passages connect the levels, and both are free of choice. Down: the
chapter's `ideal_quotient_module(R, J, M)` is `M/JM` over `R₀`, a coset
`a + J` acting on `x + JM` by the products of their members pushed onto
`JM` — the coset `a • x + JM`, no representative chosen, as the quotient
ring's own product chooses none. Up: a module `N` over `R₀` is read over
`R` through `a ↦ a + J`, written in each statement as
`scalar_restriction(ideal_quotient_projection(R, J), N)`. The
other passage up — an `R`-module killed by `J` read over `R₀` — would
have to choose a representative of each coset to act by, so the chapter
never takes it. `J` itself, when `J² = 0`, is
`ideal_quotient_module` at `J` read as a module over `R`
(`restrict_module(regular_module(R), J)`), whose span `J·J` is
`{R.zero}`: its members are the singletons `{j}`. Tensor products put `M` first, as Tor
does, the second variable being the one its long exact sequence moves.

The thickening's criterion turns on the map
$\mu : M/JM \otimes_{R_0} J \to M$, `(v + JM) ⊗ {j} ↦ j • v`, whose image is `JM`.
The long exact sequence of `0 → J → R → R/J → 0`, with `Tor₁(M, R) = 0`,
makes `Tor₁(M, R/J)` the kernel of `M ⊗_R J → M`, and
`TensorSquareZeroBaseChange` identifies $M \otimes_R J$ with
$M/JM \otimes_{R_0} J$, so the kernel of `μ` is `Tor₁(M, R/J)`.
`SquareZeroFlatCriterion` follows: `M` is flat over `R` exactly when
`M/JM` is flat over `R₀` and `μ` is one-to-one. No finiteness is asked
of `R` or `M`; the nilpotence of `J` carries the converse, every module
sitting in `0 → JN → N → N/JN → 0` with both ends killed by `J`.

## The definitions

| member | statement |
|---|---|
| `FlatModuleDef` | `flat_module(R, M)` ⇔ `module_on(R, M)` and `Tor₁(M, R/I)` is zero for every ideal `I` of `R` |
| `IdealQuotientModuleDef` | `ideal_quotient_module(R, J, M)`: the cosets of `JM`, added as sets, a coset `s` of `J` acting on a coset `X` by `{c • x \| c ∈ s, x ∈ X} + JM` |

## Tor against free modules

| member | statement |
|---|---|
| `TorFreeSecondVariableZero` | `Tor_n(M, R) = 0` for `n ≥ 1` — card |
| `TorFiniteSuppSecondVariable` | `Tor_n(M, N) = 0 ⇒ Tor_n(M, finite_supp_module(N, S)) = 0`, in every degree — card |

## Flatness through Tor and the tensor product

| member | statement |
|---|---|
| `FlatTorVanishes` | `flat_module(R, M)` ⇒ `Tor_n(M, N) = 0` for every module `N` at every type and every `n ≥ 1` — card |
| `FlatIsomorphic` | a module isomorphic to a flat module is flat — card |
| `FlatTensorInjective` | `flat_module(R, M)` and `i : N' → N` one-to-one ⇒ the map `M ⊗ N' → M ⊗ N`, `u ⊗ v ↦ u ⊗ i(v)`, is one-to-one — card |
| `FlatIdealCriterion` | `flat_module(R, M)` ⇔ `module_on(R, M)` and `M ⊗ I → M ⊗ R` is one-to-one for every ideal `I` — card |

## Modules over the quotient ring

| member | statement |
|---|---|
| `IdealQuotientModuleOn` | `ring_ideal(R, J)` ⇒ `module_on(ideal_quotient_ring(R, J), ideal_quotient_module(R, J, M))` |
| `TensorOverQuotient` | for `N` over `R/J`: $M \otimes_R N \cong M/JM \otimes_{R/J} N$ over `R`, `v ⊗ u ↦ (v + JM) ⊗ u` — card |
| `TensorSquareZeroBaseChange` | `J² = 0` ⇒ $M \otimes_R J \cong M/JM \otimes_{R/J} J$ over `R`, `v ⊗ j ↦ (v + JM) ⊗ {j}` — card |
| `FlatQuotientBaseChange` | `flat_module(R, M)` ⇒ `flat_module(ideal_quotient_ring(R, J), ideal_quotient_module(R, J, M))` for every ideal `J` — card |

## Flatness across a square-zero thickening

| member | statement |
|---|---|
| `SquareZeroFlatForward` | `flat_module(R, M)`, `J² = 0` ⇒ `μ` is one-to-one with image `JM` — card |
| `SquareZeroFlatConverse` | `J² = 0`, `Tor₁(M, R/J) = 0` and `M/JM` flat over `R/J` ⇒ `flat_module(R, M)` — card |
| `SquareZeroFlatCriterion` | `J² = 0` ⇒ (`flat_module(R, M)` ⇔ `M/JM` flat over `R/J` and `μ` one-to-one) — card |
