# cohomology_one — the first André–Quillen cohomology D^1(S/R, N) as the conormal maps of the standard presentation modulo the restrictions of derivations

The cotangent cochain complex (algebra/cotangent/cotangent_complex) holds
in degree `n` the functions on the names of degree `n` of the standard
resolution with values in `N`, a module over `S` itself. In degree 1
those names are the members of the standard presentation `P = R[S]`,
the free algebra on the tags of `S`'s elements, with augmentation
`ε : P → S` and kernel `I`. This chapter reads the cochains of degrees 0
and 1 as derivations, through the derivation of a free algebra with
given values at its variables (`free_algebra_derivation`,
algebra/ring/partial_derivative), and the 1-cocycles as conormal maps
`I → N`.

On the variable `[u]` of `u ∈ P` the two faces are `u` and
`τ(u) = [tag ε(u)]` (`standard_representative`,
algebra/cotangent/standard_resolution). So the coboundary of a 0-cochain
`h` is `u ↦ D_h(u) − D_h(τ(u))`, `D_h` the derivation of `P` with values
`h`. On the variable `[w]` of `w ∈ P_1` the faces are `w`, `[d_0 w]`
and `[d_1 w]`, so the coboundary of a 1-cochain `c` is
`w ↦ D_c(w) − c(d_0 w) + c(d_1 w)`, `D_c` the derivation of `P_1`
through the augmentation read in degree 1. A 1-cochain is a cocycle
exactly when `D_c(w) = c(d_0 w) − c(d_1 w)` on `P_1`.

Two conversions join the cocycles and the conormal maps.
`cocycle_to_conormal` sends `c` to `x ↦ c(x) − c(0)` on `I`, and
`conormal_to_cocycle` sends `γ` to `u ↦ γ(u − τ(u))` on `P`; both are
`N.zero` off their domains, so they are inverse as functions of the
host. A cocycle gives a conormal map through the two test 1-simplices
`v̂(x) + v̂(y)` and `[u] v̂(x)`, `v̂(x) = [x] − [0]` the extra degeneracy.
A conormal map gives a cocycle because `w ↦ γ(d_0 w − d_1 w)` is the
derivation with its values, and `τ(d_0 w) = τ(d_1 w)`. The coboundaries
are the conormal maps that restrict a derivation of `P` over `R` into
`N`. So `D^1(S/R, N)` is `Hom_P(I, N)` modulo `Der_R(P, N)|_I`: every
class is the class `conormal_class(R, S, f, N, γ)` of a conormal map, and
two conormal maps have one class exactly when their difference is a
derivation on `I`. Those two statements, `ConormalClassSurjective` and
`ConormalClassEqIffDerivation`, are what the classification of
square-zero extensions (algebra/cotangent/square_zero_classification)
reads; it does not reopen the coboundary formulas. No module `I/I²` is
formed and no Hom module is built. The chain-side boundaries of degrees
1 and 2 are cotangent_examples' `StandardDifferentialBoundaryOne` and
`StandardDifferentialBoundaryTwo`; this chapter reads the cochain
definition directly and does not import that chapter.

Every statement carries `cotangent_universe(R, 𝕌⟨A:U⟩) ∧
cotangent_universe(S, 𝕌⟨A:U⟩)`, as the cotangent complex's do.

## The conversions and the class

| member | statement |
|---|---|
| `CocycleToConormalDef` | `cocycle_to_conormal(R, S, f, N, c, x)` = `c(x) − c(0)` for `x` in `I`, `N.zero` off `I` |
| `ConormalToCocycleDef` | `conormal_to_cocycle(R, S, f, N, γ, u)` = `γ(u − τ(u))` for `u` in `P`, `N.zero` off `P` |
| `ConormalClassDef` | `conormal_class(R, S, f, N, γ)` = the coset of `conormal_to_cocycle(R, S, f, N, γ)` modulo the coboundaries of degree 1 |

## The coboundaries in degrees 0 and 1

| member | statement |
|---|---|
| `CotangentLowCoboundaries` | `δ⁰h(u) = D_h(u) − D_h(τ(u))` on `P`, `δ¹c(w) = D_c(w) − c(d_0 w) + c(d_1 w)` on `P_1`, and `c` a cocycle ⇔ `D_c(w) = c(d_0 w) − c(d_1 w)` on `P_1` — card |

## Cocycles and conormal maps

| member | statement |
|---|---|
| `CocycleToConormal` | `c` a 1-cocycle ⇒ `cocycle_to_conormal(R, S, f, N, c)` is a conormal map — card |
| `ConormalToCocycle` | `γ` a conormal map ⇒ `conormal_to_cocycle(R, S, f, N, γ)` is a 1-cocycle — card |
| `CocycleConormalLinearInverse` | `G ∘ C = id` on the conormal maps and `C ∘ G = id` on the 1-cocycles; `C` keeps sums, negatives and multiples by `S` on every function, `G` on the 1-cochains — card |

## Coboundaries and derivations

| member | statement |
|---|---|
| `CotangentCoboundaryConormal` | `δ⁰h = C(D_h\|_I)`, and for a conormal map `γ`, `C(γ)` is a coboundary ⇔ `γ = d\|_I` for a derivation `d` of `P` over `R` into `N` — card |

## D^1 as conormal maps modulo derivations

| member | statement |
|---|---|
| `ConormalClassSurjective` | the class of a conormal map is in `D^1(S/R, N)`, and every member of `D^1` is such a class — card |
| `ConormalClassEqIffDerivation` | two conormal maps have one class ⇔ `γ₂ − γ₁ = d\|_I` for a derivation `d` — card |
