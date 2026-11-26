# partial_derivative — partial derivatives in a free algebra, derivations into a module, conormal maps, and the Jacobian of an algebra map

A polynomial is a function from exponent functions to coefficients, and
its partial derivative in a variable `x` is read off coefficient by
coefficient: the coefficient at a monomial `m` is the coefficient of the
polynomial at `m` with the exponent of `x` raised by one, times the
numeral `m(x) + 1`, the ring's one added to itself that many times
(`polynomial_algebra_partial`). The free algebra hosts its polynomials
in a type through an injection `ι`, and the derivative of a member of
the host is the derivative of its polynomial carried back along `ι`
(`free_algebra_partial`) — one function of the host, whatever set of
variables the member is taken in, as every operation of the free algebra
is. It keeps the algebra on a set of variables, is additive, kills the
constants, takes a variable to one or zero, obeys the Leibniz rule, and
only finitely many variables of a member have a nonzero derivative, all
of them among its variables. On the algebra on one variable it is the
corpus's formal derivative of a polynomial in one variable: the free
algebra's map from the sequences of coefficients onto the algebra on
`{x}` carries `polynomial_derivative(p)` to `∂_x` of the image of `p`,
both `n · xⁿ⁻¹` on `xⁿ`.

A derivation of an algebra over `R` into a module over the algebra is an
additive map obeying the Leibniz rule and vanishing on the constants
(`derivation_on(R, S, f, N, D)`, the algebra `S` a ring record, `f` its
structure map from `R`, `N` a module record over `S`); the predicate
conjoins that `f` is a ring map and `N` a module, so a derivation fact
carries the whole structure. A derivation along a ring map is a
derivation into the target module restricted along the map. On a free
algebra a derivation is fixed by its values at the variables, and that
one fact gives the chain rule for an algebra map `Φ` over a coefficient
map `φ`: `∂_t Φ(u) = Σ_s Φ(∂_s u) * ∂_t Φ(var s)`, both sides being
derivations of `u` that agree at the variables. A map that sends some
variables to the coefficients and renames the others commutes with the
derivatives in the renamed ones. Conversely, values `v(s)` in a module
`N` over a ring `K`, given at the variables of `S`, are the values of a
derivation of the free algebra into `N` along a ring map `ε` into `K`:
`free_algebra_derivation(ι, R, S, ε, N, v)`, at a member `u` the sum of
`ε(∂_s u) • v(s)` over the finitely many `s` with a nonzero derivative,
and `N.zero` off the algebra. Every derivation is the one with its own
values.

A conormal map of a ring map `ε` from `P` to `S` into a module `N` over
`S` (`conormal_hom(P, S, ε, N, γ)`) is a map on the kernel `I` of `ε`
that is additive and linear over `P` through `ε`, `γ(u * x) = ε(u) •
γ(x)`, and `N.zero` off `I`: a homomorphism `I → N` of modules over `P`,
read on `I` itself, with no quotient `I/I²` formed. A derivation of `P`
into `N` along `ε`, restricted to `I`, is one, the second Leibniz term
vanishing there. The predicate fixes no presentation; the cotangent
chapters read it at the standard presentation.

The Jacobian of an algebra map `Φ` from the algebra on `S` to the
algebra on `T` is the matrix of the derivatives `∂_t Φ(var s)`, its
entries carried by a ring map `ε` into the scalars of a module `N` and
applied to the finitely supported functions on `S` with values in `N`
(`free_algebra_jacobian`): the differentials of a polynomial simplicial
algebra tensored down to its coefficients, with no general module of
differentials built. Two name sets bound it, the columns read (`S`) and
the rows written (`T`), so the block of the matrix between two parts of
the variables is one application. It is linear, takes a generator to its
column, is the identity for a map fixing the variables, composes by the
chain rule — the Jacobian of `Φ' ∘ Φ` at `ε` is the Jacobian of `Φ'`
after the Jacobian of `Φ` at `ε ∘ Φ'` — and is block triangular for a
map keeping the algebra on part of the variables. Its transpose pulls
the functions on `T` with values in `N` back along the same matrix, for
the cochain side.

The hosts, rings and name types are free: an algebra map may change the
coefficient ring and the host, as the map from a polynomial algebra over
`A` to one over `B` that sends some variables to coefficients does.

## The partial derivative

| member | statement |
|---|---|
| `PolynomialAlgebraPartialDef` | `polynomial_algebra_partial(R, x, f, m) = (m(x) + 1)·1 * f(m + monomial_var(x))` |
| `FreeAlgebraPartialDef` | `free_algebra_partial(ι, R, x, u) = ι(polynomial_algebra_partial(R, x, preimage of u))` |
| `PartialIn` | `u` in the algebra on `S` ⇒ so is `∂_x u` |
| `PartialAdd` | `∂_x (u + v) = ∂_x u + ∂_x v` — card |
| `PartialConst` | `∂_x` of a constant of `R`'s carrier is zero — card |
| `PartialVar` | `∂_x (var y)` is one when `x = y`, zero otherwise |
| `PartialLeibniz` | `∂_x (u * v) = u * ∂_x v + v * ∂_x u` — card |
| `PartialSupportFinite` | the variables where `∂_x u` is nonzero are finitely many, all in `S` |
| `PartialEvalTimesVar` | `θ(x) · ∂ₓP(θ) = Σ_m m(x) · P(m) · θ^m` over the monomials of a polynomial `P` of `S` with coefficients in `k ⊆ R`, `θ` in the carrier on `S` and at `x` |
| `PolynomialPartialIn` | ∂ₓ keeps the polynomials of `S` |
| `PolynomialPartialSupportFinite` | for `f` a polynomial of `S`, the variables where `∂ₓf` is nonzero are finitely many, all in `S` |
| `PolynomialPartialLinear` | `∂ₓ(f ± g) = ∂ₓf ± ∂ₓg` on the polynomials |
| `PolynomialPartialVarMul` | `∂ₓ(X_y·f) = X_y·∂ₓf + δₓᵧ f` on the polynomials |
| `TaylorModuloSquare` | `x(i) − y(i) ∈ I` for all `i` ⇒ `P(x) − P(y) − Σᵢ ∂ᵢP(x)(x(i) − y(i)) ∈ I²` |
| `PolynomialPartialConst` | ∂ₓ of a constant is zero |
| `PolynomialPartialVar` | ∂ₓ of the variable `y` is the constant δₓᵧ |
| `PartialDerivativeTransport` | `p` a polynomial over `R`'s carrier ⇒ the image in the algebra on `{x}` of `polynomial_derivative(p)` is `∂_x` of the image of `p` — card |
| `PolynomialPartialMap` | `∂ₓ` commutes with carrying the coefficients along a ring homomorphism `f`: `∂ₓ(λm. f(p(m))) = λm. f(∂ₓp(m))` for `p` with coefficients in `R` |

## Derivations and the chain rule

| member | statement |
|---|---|
| `DerivationOn` | `derivation_on(R, S, f, N, D)`: `f` a ring map from `R` to `S`, `N` a module over `S`, `D` additive, `D(u * v) = u • D(v) + v • D(u)`, `D(f(a)) = 0` |
| `DerivationUniqueOnGenerators` | two derivations of the algebra on `S` into one module that agree at the variables of `S` agree on the algebra — card |
| `ChainRule` | `Φ` an algebra map over `φ` ⇒ `∂_t Φ(u) = Σ_s Φ(∂_s u) * ∂_t Φ(var s)`, over the `s` of `S` with `∂_s u ≠ 0` — card |
| `PartialBaseChange` | `Φ` sending the variables of `X` to constants and each `y` of `Y` to `var h(y)` ⇒ $\partial_t \Phi(u) = \sum_{y \in Y, h(y) = t} \Phi(\partial_y u)$ — card |
| `FreeAlgebraDerivationDef` | `free_algebra_derivation(ι, R, S, ε, N, v, u)` = $\sum_{s \in S, \partial_s u \ne 0} \varepsilon(\partial_s u) • v(s)$ on the algebra on `S`, `N.zero` off it |
| `FreeAlgebraDerivationFromValues` | `ε` a ring map, `v` valued in `N` on `S` ⇒ `free_algebra_derivation` is a derivation along `ε` with value `v(s)` at `var s` — card |
| `FreeAlgebraDerivationRepresentation` | a derivation `d` along `ε` is `free_algebra_derivation` at `s ↦ d(var s)` on the algebra — card |

## Conormal maps

| member | statement |
|---|---|
| `ConormalHom` | `conormal_hom(P, S, ε, N, γ)`: on the kernel `I` of `ε`, `γ` is valued in `N`, additive and `γ(u * x) = ε(u) • γ(x)`; `γ` is `N.zero` off `I` |
| `DerivationRestrictionConormal` | a derivation of `P` along `ε`, restricted to `I` and `N.zero` off it, is a conormal map — card |

## The Jacobian

| member | statement |
|---|---|
| `FreeAlgebraJacobianDef` | `free_algebra_jacobian(ι, ι', R, R', S, T, Φ, ε, N, u, t)` = $\sum_{s \in S, u(s) \ne 0} \varepsilon(\partial_t \Phi(\operatorname{var} s)) • u(s)$ at `t ∈ T`, zero elsewhere |
| `FreeAlgebraJacobianTransposeDef` | `free_algebra_jacobian_transpose(ι, ι', R, R', S, T, Φ, ε, N, w, s)` = $\sum_{t \in T} \varepsilon(\partial_t \Phi(\operatorname{var} s)) • w(t)$ at `s ∈ S`, zero elsewhere |
| `JacobianHom` | the Jacobian is a homomorphism `finite_supp_module(N, S) → finite_supp_module(N, T)` over the scalar ring — card |
| `JacobianDelta` | the Jacobian of the generator at `s` with value `n` is `t ↦ ε(∂_t Φ(var s)) • n` — card |
| `JacobianIdentity` | a map fixing the variables of `S` has the identity as Jacobian — card |
| `JacobianCompose` | the Jacobian of `Φ' ∘ Φ` at `ε` is the Jacobian of `Φ'` at `ε` after the Jacobian of `Φ` at any `ε'` equal to `ε ∘ Φ'` on the algebra on `T` — card |
| `JacobianBlockTriangular` | `Φ` keeping the variables of `S₁` in the algebra on `T₁`, `T₁`, `T₂` disjoint ⇒ the Jacobian carries functions on `S₁` to functions on `T₁`, and its `S₂`-to-`T₂` block is the map on the quotients — card |
| `JacobianCongruence` | the Jacobian and its transpose read `Φ` only at the variables of `S` and `ε` only on the algebra on `T` — card |
| `JacobianTransposeHom` | the transpose is a homomorphism `function_module(N, T) → function_module(N, S)` — card |
| `JacobianTransposeCompose` | the transpose of the Jacobian of `Φ' ∘ Φ` is the transpose for `Φ` after the transpose for `Φ'` — card |
| `JacobianTransposeAgreement` | `hom_precompose` of the Jacobian with coefficients in the scalar ring is `free_algebra_jacobian_transpose` with coefficients in `N` — card |

## Derivations on a localization

| member | statement |
|---|---|
| `DerivationLocalizationDef` | `derivation_localization(S, S', ρ, N, d, y)`: the quotient rule `ρ(s)⁻² • (ρ(s) • d(a) − ρ(a) • d(s))` at a chosen `y · ρ(s) = ρ(a)`, `ρ(s)` a unit |
| `DerivationExtendsUniquely` | `ρ` a localization of `S`, `N` a module over it ⇒ a derivation of `S` into `N` read along `ρ` extends by the quotient rule to a derivation of the localization, agreeing with it on `S`, and no other derivation does — card |
