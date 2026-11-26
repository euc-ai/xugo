# simplicial_ring — the host type of the cotangent domain and the polynomial simplicial algebras in it, their augmentations and resolutions

The cotangent complex of an algebra is computed from a resolution of it
by free algebras: a simplicial algebra, free over the base ring in each
degree, augmented onto the algebra. This chapter lays the ground the
cotangent domain stands on. It fixes one host type `U` in which every
free algebra of the domain lives, under the hypothesis
`cotangent_universe(R, 𝕌⟨A:U⟩)` that `U` has room for the ring's
carrier, its polynomials in names of `U` and a copy of `U` for each
natural number, so that the resolutions of the rings of a tower are
sets of one type and a theorem relating them is a statement in one
type.

In that host it defines the polynomial simplicial algebras over a
commutative ring, their augmentations onto an algebra, the resolutions —
augmented algebras whose underlying simplicial module is acyclic over
the algebra, with no Kan condition asked — and the maps and homotopies
between them. The standard resolution
(algebra/cotangent/standard_resolution) and the comparison of
resolutions (algebra/cotangent/resolution_comparison) are built on
these definitions.

## The conventions of the domain

Every free algebra of the cotangent domain lives in one host type `U`, a
type variable of every constant that builds one, so the standard
resolutions of `B` over `A`, of `C` over `A` and of `C` over `B` are sets of
the same type and a theorem relating them is a statement in one type. The
room `U` must have is a hypothesis, `cotangent_universe(R, 𝕌⟨A:U⟩)`, asked
of each ring `R` a statement reads: the ring's carrier, every polynomial
over `R` in variables of `U`, and num-many disjoint copies of `U` inject
into `U`. Under it the injection of the polynomials,
`universe_embedding(R)`, the tags `universe_tag(i)` and the naming
of a carrier's elements, `carrier_tag(S.carrier)`, are chosen once by ε —
the embedding once per ring, the naming once per carrier, so one carrier
has one set of names in every statement — and no later
constant takes an embedding as an argument: the free algebra over `R` on a
set `S` of names in `U` is `universe_algebra(R, S)`, the free algebra of
algebra/ring/polynomial/free_algebra read through `universe_embedding(R)`.
Statements read it through that interface at the universe — its ring
record, constants, variables, module, evaluation, induced maps,
multiplication and algebra maps, `universe_algebra_ring`, …,
`universe_algebra_homomorphism`; the coefficients along a second set of
names and the substitution of one variable keep free_algebra's spelling
at `universe_embedding(R)` — and never through the encoding. Every
theorem whose objects are read through these choices carries the
hypothesis for each ring it reads, as an antecedent. The room is asked
for a ring's carrier, not its type: no type has room for the type of its
own subsets, but a quotient of a ring on `U`, a ring on `set(U)`, has its
carrier no larger than the ring's, and so has room in `U`. At a powerset
host `set(prod(num, D))` the hypothesis is the room for the carrier
alone, and it passes from a ring to its polynomial ring, its quotients,
its localizations and the free algebras of the host, so a tower is
resolved in the host chosen for its base ring and every ring built from
it keeps a universe there. The concrete type
`set(prod(num, prod(A, prod(B, C))))` meets it for every ring of a tower
of rings on `A`, `B`, `C` at once, a convenience for a statement at
three given rings.

The operations of the free algebra on `S` do not depend on `S`: there is one
ring of polynomials over `R` in all of `U`, and every free algebra on a set of
names is a subring of it under the same six operations. A polynomial
simplicial algebra is therefore a simplicial set of name sets `X(n)` with
the free algebras on them as its terms, its faces and degeneracies
functions `U → U` restricted to them, and the maps and homotopies between
such algebras are functions of `U` too. An algebra over a polynomial
algebra `P` is never built with `P` as its coefficient ring: the
coefficients stay in `R`, and the names of `P`, tagged by
`universe_tag(0)`, join the algebra's own names, tagged by
`universe_tag(1)`, in one set of variables, so that the differentials of
the relative resolution are finitely supported functions on a disjoint
union and its exact sequences are inclusions and projections. Rings are
records `R : ring_ops(A)`; a commutative ring is `comm_ring_on` at the
record's six operations and its carrier, and a ring map between two
records is `ring_homomorphism` at both records' operations and carriers.

## Polynomial simplicial algebras

A polynomial simplicial algebra over a commutative ring `R` is
`polynomial_simplicial_algebra(R, X, d, s)`: the free algebras on the
name sets `X(n)` form a simplicial set under `d` and `s`,
`polynomial_simplicial_set(R, X, d, s)`, every face and
degeneracy is an algebra map over `R`, a ring map fixing the constants,
and every degeneracy carries the variable of a name to the variable of a
name. The generators are the variables, members of the algebras; a name
is an arbitrary member of `U` and need not lie in any of them. The last
condition is what the comparison of resolutions builds maps on: a
variable that is not a degeneracy of a lower one is free to be sent
anywhere.

An augmentation carries the algebra in degree 0 onto an algebra `S` over
`R`: `augmented_polynomial_algebra(R, X, d, s, S, f, ε)` asks the structure
map `f` to be a ring map, `ε` a ring map agreeing with `f` on the
constants, and `ε d_0 = ε d_1` in degree 1. `augmentation_at(d, ε, n)` reads
the augmentation in degree `n` through the 0-th faces. A resolution,
`polynomial_resolution(R, X, d, s, S, f, ε)`, is an augmented algebra whose
underlying simplicial module over `R` is acyclic over `S`: the Moore
complex — the simplices whose faces but the 0-th vanish, with `d_0` as
differential — is exact in positive degrees, and `ε` reads the degree-0
algebra modulo `d_0` of the Moore 1-simplices onto `S`. No Kan condition and
no homotopy group enters the definition. Maps of polynomial simplicial
algebras over one ring and the homotopies between them are the
simplicial ones whose components are algebra maps over `R`. The constant
algebra on a name set is spelled where it is used: the same set in every
degree, every face and degeneracy the identity.

In a universe for `R` the algebra maps are linear, so a polynomial
simplicial algebra is a simplicial module over `R` and its maps and
homotopies are linear simplicial maps and homotopies; as a simplicial
module it is a Kan complex, by Moore's horn filling. The augmentation
read through the 0-th faces may be read through any face, from
`ε d_0 = ε d_1` and the face identities alone, and it is an algebra map in
every degree. The constant algebra on a name set resolves its own free
algebra through the identity.

## The universe

| member | statement |
|---|---|
| `CotangentUniverseDef` | `cotangent_universe(R, V)`: `R.carrier`, `polynomial_algebra(R, 𝕌⟨A:U⟩)` and `prod(num, U)` each inject into `V` |
| `UniverseEmbeddingDef` | `universe_embedding(R) = εj. free_algebra_embedding(R, j)` |
| `UniverseTagDef` | `universe_tag = εt. t(i, u) = t(j, v) ⇒ i = j ∧ u = v` |
| `CarrierTagDef` | `carrier_tag(C) = εj. injective_on(C, j)`, a naming of the members of `C` in `U` |

## The free algebra in the universe

| member | statement |
|---|---|
| `UniverseAlgebraDef` | `universe_algebra(R, S) = free_algebra(universe_embedding(R), R, S)` |
| `UniverseAlgebraRingDef` | `universe_algebra_ring(R, S)`, its ring record |
| `UniverseAlgebraConstDef`, `UniverseAlgebraVarDef` | `universe_algebra_const(R, a)`, `universe_algebra_var(R, x)`, the constant `a` and the variable of the name `x` |
| `UniverseAlgebraModuleDef` | `universe_algebra_module(R)`, the free algebra on all of `U` as a module over `R` |
| `UniverseAlgebraEvalDef` | `universe_algebra_eval(R, R', φ, θ, u)`, evaluation in a ring `R'` with coefficients through `φ` and the names at `θ` |
| `UniverseAlgebraMapDef` | `universe_algebra_map(R, R', φ, h, u)`, the map to the free algebra over `R'` carrying `a` to `φ(a)` and the variable of `x` to the variable of `h(x)` |
| `UniverseAlgebraMultDef` | `universe_algebra_mult(R, u)`, the multiplication flattening a polynomial of polynomials |
| `UniverseAlgebraHomomorphismDef` | `universe_algebra_homomorphism(R, S, T, F)`, `F` an algebra map over `R` from the free algebra on `S` to the one on `T` |

## What the choices satisfy

| member | statement |
|---|---|
| `UniverseEmbeddingHost` | in a universe for `R`, `universe_embedding(R)` is a `free_algebra_embedding(R, ·)` |
| `TagPairInjective` | in a universe, `universe_tag(i, u) = universe_tag(j, v)` only when `i = j` and `u = v` |
| `TagInjective`, `TagsDisjoint` | in a universe, each `universe_tag(i)` is injective, and two different tags never take one value |
| `CarrierTagInjective` | `card_le(C, 𝕌⟨A:U⟩) ⇒ injective_on(C, carrier_tag(C))` |
| `CarrierTagDecode` | the preimage in `C` of a name of `C` lies in `C` and carries that name; when `C` injects into `U`, it is the member named — card |

## The powerset host

| member | statement |
|---|---|
| `PowerSetUniverse` | `set(prod(num, D))` is a universe for every ring whose carrier injects into it — card |
| `ConcreteUniverse` | `set(prod(num, prod(A, prod(B, C))))` is a universe for every ring of a tower on `A`, `B`, `C` — card |
| `FreeAlgebraCotangentUniverse` | every free algebra in `set(prod(num, D))` has a universe there — card |
| `PolynomialRingCotangentUniverse` | a universe there for `R` is one for the polynomials over `R` — card |
| `QuotientCotangentUniverse` | a universe there for `R` is one for every `ideal_quotient_ring(R, I)` — card |
| `LocalizationCotangentUniverse` | a universe there for `R` is one for every localization of `R` — card |

## Polynomial simplicial algebras, augmentations, resolutions

| member | statement |
|---|---|
| `PolynomialSimplicialSetDef` | `polynomial_simplicial_set(R, X, d, s) = mk_simplicial(λn. universe_algebra(R, X(n)), d, s)`: the free algebras on the name sets, with the faces `d` and the degeneracies `s` |
| `PolynomialSimplicialAlgebra` | `R` a commutative ring, `simplicial_set(polynomial_simplicial_set(R, X, d, s))`, faces and degeneracies algebra maps over `R`, each `s(n, i)` carrying the variables of `X(n)` into the variables of `X(n + 1)` |
| `AugmentedPolynomialAlgebra` | `f : R → S` a ring map, `ε` a ring map from degree 0 to `S` with `ε ∘ const = f`, `ε d_0 = ε d_1` in degree 1 |
| `AugmentationAtDef` | `augmentation_at(d, ε, 0) = ε`, `augmentation_at(d, ε, n + 1) = augmentation_at(d, ε, n) ∘ d(n + 1, 0)` |
| `PolynomialResolution` | augmented, and `acyclic_augmentation` of the underlying simplicial module `polynomial_simplicial_set(R, X, d, s)` in `universe_algebra_module(R)` over `S.carrier` |
| `SimplicialAlgebraMap` | a simplicial map of the free algebras, `simplicial_map(polynomial_simplicial_set(R, X, d, s), polynomial_simplicial_set(R, Y, d', s'), F)`, whose every component is an algebra map over `R` |
| `SimplicialAlgebraHomotopy` | a simplicial homotopy between two algebra maps, `simplicial_homotopy(polynomial_simplicial_set(R, X, d, s), polynomial_simplicial_set(R, Y, d', s'), F, G, H)`, whose every component is an algebra map over `R` |

## The underlying simplicial module

| member | statement |
|---|---|
| `PolynomialAlgebraSimplicialModule` | in a universe for `R`, `simplicial_module(R, universe_algebra_module(R), polynomial_simplicial_set(R, X, d, s))` — card |
| `AlgebraMapIsModuleMap`, `AlgebraHomotopyIsModuleHomotopy` | in a universe for `R`, algebra maps and algebra homotopies are linear simplicial maps and homotopies — card |
| `PolynomialAlgebraKan` | in a universe for `R`, `kan_complex(polynomial_simplicial_set(R, X, d, s))` — card |

## The augmentation in every degree

| member | statement |
|---|---|
| `AugmentationAtFaceIndependent` | `augmentation_at(d, ε, n) ∘ d(n + 1, i) = augmentation_at(d, ε, n + 1)` on degree `n + 1`, for every `i ≤ n + 1` — card |
| `AugmentationAtHom` | `augmentation_at(d, ε, n)` is a ring map from the free algebra on `X(n)` to `S` carrying the constant `a` to `f(a)` — card |
| `AugmentedAlongRingMap` | an augmented polynomial simplicial algebra over `S` is augmented over `T` through any ring map `g` out of `S` — card |

## The constant algebra

| member | statement |
|---|---|
| `ConstantPolynomialAlgebra` | in a universe for a commutative ring `R`, the name set `W` in every degree with identity faces and degeneracies is a polynomial simplicial algebra — card |
| `ConstantPolynomialResolution` | it resolves `universe_algebra_ring(R, W)` through the identity, the constants the structure map — card |
