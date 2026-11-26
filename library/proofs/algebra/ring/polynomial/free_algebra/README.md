# free_algebra — the free commutative algebra on a set of variables, the polynomials of polynomial_algebra hosted in a type by an injection

The model — the polynomials as finitely supported functions of monomials,
and the commutative ring they form — is `polynomial_algebra`'s; their
evaluation and their generation by the constants and the variables are
`polynomial_algebra_evaluation`'s. This chapter hosts the model in a type of one's
choosing.

**The host.** In the model, a polynomial whose variables are themselves
polynomials has a type of its own, and every iteration — the standard
resolution of an algebra is one polynomial algebra over the previous —
would need a new one. The interface fixes a host type `E` and an injection
`ι : ((D → num) → A) → E`; `free_algebra_embedding(R, ι)` says that `ι` is
injective on the polynomials over `R` in every variable,
`polynomial_algebra(R, 𝕌)`, and so on the polynomials of every set of
variables. The room the host needs is that of `R`'s carrier, not of its
type: when the variables are the subsets of `prod(num, B)` and the carrier
injects into them, so do its polynomials
(`PolynomialCarrierIntoPowerSet`), and so do the corpus's polynomials in
one variable (`UnivariatePolynomialCarrierCardLe`). The constructions
below read `ι` on these polynomials — at the constants of the carrier, at
the variables, and at the members of the algebra — and nowhere else need
it be injective. The algebra on `S` is the image `free_algebra(ι, R, S)`,
and one ring's operations, transported along `ι` from the polynomials in
every variable (the ring_transport chapter), serve the algebra on every
set of variables: `free_algebra_ring(ι, R, S)` and `free_algebra_ring(ι,
R, T)` differ in their carriers only, so along an embedding every free
algebra in a host is a subring of the one on `𝕌`, under one sum and one
product. The constants
`free_algebra_const` and the variables `free_algebra_var` are `ι` of the
model's; the evaluation `free_algebra_eval` and the coefficients
`free_algebra_coefficient_at` read the model through the preimage among
all polynomials; `free_algebra_map` is the evaluation into a second host
at the constants after `φ` and the variables after a map `h` of the
variables, and `free_algebra_substitute` the evaluation into the same host
that puts `c` for `y`. When the variables are members of the host itself
(`D = E`), the algebra on the members of an algebra is again a set of the
host's members, and `free_algebra_mult` flattens a polynomial of
polynomials by evaluating it at the identity. `free_algebra_homomorphism`
says that a map between two free algebras is a ring homomorphism of their
records that carries each constant `a` to the constant `φ(a)`: an algebra
map over `φ`.

**The laws.** Along an embedding the algebra on `S` is a commutative ring,
`ι` an isomorphism onto it from the polynomials of `S`, and the algebra on
`𝕌` a module over `R` with each algebra on a set as a submodule. The
evaluation is the one ring homomorphism with given values on the
constants and the variables, it reads its data on the carrier and on `S`
only, and a homomorphism applied after it is an evaluation again. The
induced maps are algebra maps, functorial in the coefficient map and in
the map of the variables. The variables and the multiplication make a
monad on the host's subsets: `μ ∘ η` and `μ ∘ F(η)` are identities, `μ`
is associative and natural, and an evaluation after `μ` evaluates the
outer polynomial at the evaluations of its variables. Over disjoint `X`
and `S` the algebra on `X ∪ S` is the algebra on `S` with coefficients in
the algebra on `X`: each member is, in exactly one way, a finite sum of
coefficients in the algebra on `X` times monomials of `S`, and an algebra
map that fixes the variables of `S` and keeps the algebra on `X` acts
coefficient by coefficient. For `c` not involving `y`, the monic linear
factor `var y − c` divides every member with the substitution `y := c`
as remainder, is not a zero divisor, and divides exactly the members
that the substitution sends to zero — over every commutative ring.

**One variable.** The corpus's polynomials in one variable are sequences
of coefficients `p : num → A`, zero from some index on, multiplied by the
convolution `polynomial_mul`, the ring record `polynomial_ring(R)`.
The sequence `p` goes to `ι` of the coefficient function that reads `p`
at the exponent `m(x)` on the monomials `m` of `{x}` and is `R.zero` at
every other exponent function; along an embedding this is a ring
isomorphism onto the algebra on `{x}`, stated as its three conjuncts: a
ring homomorphism, one-to-one, onto. The monomial `xⁿ` is the exponent
function with `n` at `x`, and both products are convolutions of
coefficients. It is the one bridge between the corpus's `A[x]` and the
free algebra on one variable.

## The room a host needs

| member | statement |
|---|---|
| `PolynomialCarrierIntoPowerSet` | `card_le(R.carrier, 𝕌⟨set(prod(num, B))⟩)` ⇒ the polynomials over `R` in the variables of that powerset inject into it — card |
| `UnivariatePolynomialCarrierCardLe` | `card_le(R.carrier, 𝕌⟨set(prod(num, B))⟩)` ⇒ the polynomials over `R`'s carrier inject into that powerset — card |

## The host: definitions

| member | statement |
|---|---|
| `FreeAlgebraEmbeddingDef` | `free_algebra_embedding(R, ι)` ⇔ `injective_on(polynomial_algebra(R, 𝕌), ι)` |
| `FreeAlgebraDef` | `free_algebra(ι, R, S) = image(ι, polynomial_algebra(R, S))` |
| `FreeAlgebraRingDef` | `free_algebra_ring(ι, R, S)` = the operations of `transport_ring(ι, polynomial_algebra_ring(R, 𝕌))` with the carrier `free_algebra(ι, R, S)` |
| `FreeAlgebraConstDef`, `FreeAlgebraVarDef` | `free_algebra_const(ι, R, a)` and `free_algebra_var(ι, R, x)` are `ι` of the constant and of the variable |
| `FreeAlgebraModuleDef` | `free_algebra_module(ι, R)` = the algebra on `𝕌` under its sum, `r` acting as the product with the constant `r` |
| `FreeAlgebraEvalDef` | `free_algebra_eval(ι, R, R', φ, θ, u)` = the polynomial evaluation of the preimage of `u` among all polynomials |
| `FreeAlgebraMapDef` | `free_algebra_map(ι, ι', R, R', φ, h, u)` = the evaluation into the algebra on `𝕌` over `R'` at the constants of `φ(a)` and the variables `h(x)` |
| `FreeAlgebraMultDef` | `free_algebra_mult(ι, R, u)` = the evaluation into the host's algebra on `𝕌` at the constants and at each variable itself |
| `FreeAlgebraSubstituteDef` | `free_algebra_substitute(ι, R, y, c, u)` = the evaluation into the host's algebra at the constants, `c` at `y` and each other variable itself |
| `FreeAlgebraHomomorphismDef` | `free_algebra_homomorphism(ι, ι', R, R', φ, S, T, F)` ⇔ `F` is a ring homomorphism from `free_algebra_ring(ι, R, S)` to `free_algebra_ring(ι', R', T)` carrying the constant `a` to the constant `φ(a)` |
| `FreeAlgebraCoefficientAtDef` | `free_algebra_coefficient_at(ι, R, X, S, u, m)` = `ι` of the polynomial of `X` whose coefficient at `n` is `u`'s at `n + m`, for `m` a monomial of `S`; the host's zero otherwise |

## The host: the ring, the module, constants and variables

| member | statement |
|---|---|
| `FreeAlgebraEmbeddingDecode` | along an embedding, the preimage among all polynomials reads `ι(f)` back as `f` for every polynomial `f` in every variable, and a member of the algebra on `S` back as a polynomial of `S` with that image |
| `FreeAlgebraRingIsomorphism` | along an embedding, over a commutative ring, `ι` is a ring isomorphism from the polynomials of `S` onto the algebra on `S` |
| `FreeAlgebraCommRingOn` | along an embedding, over a commutative ring, `free_algebra_ring(ι, R, S)` is a commutative ring on `free_algebra(ι, R, S)` |
| `FreeAlgebraModuleOn` | `free_algebra_module(ι, R)` is a module over `R`, and the algebra on each `S` a submodule — card |
| `FreeAlgebraOpsIndependentOfVariables` | the six operations of `free_algebra_ring(ι, R, S)` and of `free_algebra_ring(ι, R, T)` are the same |
| `FreeAlgebraSubset` | `S ⊆ T` ⇒ `free_algebra(ι, R, S) ⊆ free_algebra(ι, R, T)` |
| `FreeAlgebraNoVariables` | `free_algebra(ι, R, ∅) = image(free_algebra_const(ι, R), R.carrier)` — card |
| `FreeAlgebraConstHom` | along an embedding, over a commutative ring, the constants are a ring homomorphism from `R` into the algebra on `S` |
| `FreeAlgebraVarIn` | `x ∈ S` ⇒ `free_algebra_var(ι, R, x) ∈ free_algebra(ι, R, S)` |

## The host: evaluation and induced maps

| member | statement |
|---|---|
| `FreeAlgebraEvalHom` | along an embedding, `φ` a ring homomorphism, `θ` valued in `R'` on `S` ⇒ the evaluation is a ring homomorphism from the algebra on `S` to `R'` |
| `FreeAlgebraEvalConst`, `FreeAlgebraEvalVar` | along an embedding, `φ` a ring homomorphism: for `a ∈ R.carrier` the constant `a` evaluates to `φ(a)`; for `θ(x) ∈ R'.carrier` the variable `x` evaluates to `θ(x)` |
| `FreeAlgebraEvalUnique` | along an embedding, over a commutative ring, two ring homomorphisms out of the algebra on `S` agreeing on the constants and on the variables of `S` agree on it |
| `FreeAlgebraEvalCongruence` | the evaluation on the algebra on `S` reads `φ` on the carrier and `θ` on `S` only — card |
| `FreeAlgebraEvalNatural` | `ψ` a ring homomorphism ⇒ `ψ` after the evaluation at `φ`, `θ` is the evaluation at `ψ ∘ φ`, `ψ ∘ θ` — card |
| `FreeAlgebraMapHom` | `h` carries `S` into `T` ⇒ the induced map is an algebra map over `φ` from the algebra on `S` to the algebra on `T` — card |
| `FreeAlgebraMapConst`, `FreeAlgebraMapVar` | the induced map carries the constant `a` to the constant `φ(a)` and the variable `x` to the variable `h(x)` — card |
| `FreeAlgebraMapCongruence` | the induced map on the algebra on `S` reads `φ` on the carrier and `h` on `S` only — card |
| `FreeAlgebraMapIdentity`, `FreeAlgebraMapCompose` | the identities induce the identity, and induced maps compose as their data do — card |
| `FreeAlgebraEvalMap` | an evaluation after an induced map is the evaluation at the composed data — card |

## The host: the multiplication

| member | statement |
|---|---|
| `FreeAlgebraMultHom` | `μ = free_algebra_mult(ι, R)` is an `R`-algebra map from the algebra on `free_algebra(ι, R, S)` to the algebra on `S` — card |
| `FreeAlgebraMultVar` | `μ ∘ η = id` on the algebra on `S` — card |
| `FreeAlgebraMultUnitRight` | `μ ∘ F(η) = id` on the algebra on `S` — card |
| `FreeAlgebraMultNatural` | `F(h) ∘ μ = μ ∘ F(F(h))` on the algebra over the algebra on `S` — card |
| `FreeAlgebraMultAssoc` | `μ ∘ F(μ) = μ ∘ μ` on the algebra over the algebra over the algebra on `S` — card |
| `FreeAlgebraEvalMult` | an evaluation after `μ` is the evaluation of the outer polynomial at the evaluations of its variables — card |

## The host: coefficients, substitution and a monic linear factor

| member | statement |
|---|---|
| `FreeAlgebraDisjointCoefficients` | `X ∩ S = ∅`, `u` in the algebra on `X ∪ S` ⇒ `u` is the finite sum of `free_algebra_coefficient_at(ι, R, X, S, u, m)` times the monomial `m` of `S`, the coefficients in the algebra on `X`; and any such expansion has these coefficients — card |
| `FreeAlgebraBaseMapCoefficientwise` | an algebra map from the algebra on `X ∪ S` to the algebra on `X' ∪ S` fixing the variables of `S` and carrying the algebra on `X` into that on `X'` takes each coefficient of `u` to the coefficient of its image — card |
| `FreeAlgebraSubstituteHom` | `c` in the algebra on `S ∖ {y}` ⇒ `y := c` is an `R`-algebra map from the algebra on `S` to the algebra on `S ∖ {y}`, fixing the latter — card |
| `FreeAlgebraMonicLinearDivision` | `y ∈ S` ⇒ `u = (var y − c) * q + u(y := c)` for some `q` in the algebra on `S` — card |
| `FreeAlgebraMonicLinearRegular` | `(var y − c) * u = 0` ⇒ `u = 0` — card |
| `FreeAlgebraMonicLinearDivides` | `u(y := c) = 0` ⇔ `var y − c` divides `u` in the algebra on `S` — card |

## One variable

| member | statement |
|---|---|
| `PolynomialOneVariableHomomorphism` | `p ↦ ι(m ↦ COND(m ∈ monomials({x}), p(m(x)), R.zero))` is a ring homomorphism from `polynomial_ring(R)` to `free_algebra_ring(ι, R, {x})` — card |
| `PolynomialOneVariableInjective` | that map is one-to-one on the polynomials over `R`'s carrier — card |
| `PolynomialOneVariableOnto` | its image of the polynomials over `R`'s carrier is `free_algebra(ι, R, {x})` — card |

## Quotients: eliminating a variable, reducing modulo a monic quadratic

| member | statement |
|---|---|
| `FreeAlgebraSubstitutionQuotient` | `y ∈ S`, `c` in the algebra on `S ∖ {y}` ⇒ the algebra on `S` modulo `(g, var y − c)` is isomorphic to the algebra on `S ∖ {y}` modulo `g(y := c)`, by `u + I ↦ u(y := c) + J` — card |
| `FreeAlgebraMonicQuadraticReduction` | `f` in the algebra on `S ∖ {y}` ⇒ every `u` is `p + q · var y` modulo `var y · var y − f` with `p`, `q` in the algebra on `S ∖ {y}`, and `p`, `q` are determined by the value — card |
