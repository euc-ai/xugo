# cotangent_complex — the cotangent complex of an algebra with coefficients in a module, and André–Quillen homology

The cotangent complex of an algebra `S` over a commutative ring `R` is
the module of Kähler differentials of a free resolution of `S`, taken
degreewise. Here the resolution is a polynomial simplicial algebra
(algebra/cotangent/simplicial_ring): in degree `n` the free algebra over
`R` on a set of names `X(n)`. The differentials of a free algebra form
the free module on its variables. With coefficients in a module `N`,
they are therefore the finitely supported functions on `X(n)` with
values in `N`, `differential_terms(X, N, n)`. No general module of
Kähler differentials is built along the way.

A face or degeneracy of the algebra acts on these functions by its
Jacobian (algebra/ring/partial_derivative). The matrix of partial
derivatives has its entries carried into the scalars of `N` by the
augmentation read in the target degree. In degree `n + 1` that
augmentation is the one in degree `n` after any face, and this is what
lets the chain rule compose the Jacobians. So the Jacobians make the
functions a simplicial module, and its alternating face sum is a chain
complex, `differential_complex(R, X, d, S, ε, N)`, over the ring the
augmentation lands in.

An algebra map that covers the identity of the augmentation target acts
by its Jacobians as a chain map, functorially. An algebra homotopy acts
as the chain homotopy Σ (−1)^j J(H(n, j)). By the comparison theorem
(algebra/cotangent/resolution_comparison), two polynomial resolutions of
one algebra are therefore chain homotopy equivalent through their
complexes of differentials, whatever ring the coefficients are carried
to.

The cotangent complex `cotangent_complex(R, S, f, T, g, N)` is this
complex at the standard resolution of `S` over `R`
(algebra/cotangent/standard_resolution). Its augmentation onto `S` is
followed by a ring map `g` into a ring `T`, and `N` is a module over
`T`. The homology modules over `T` are the André–Quillen homology
`D_n(S/R, N)`, written `cotangent_homology(R, S, f, T, g, N, n)`. A
module over `S` itself is the case `T = S`, `g = λx. x`. The general
case lets the three complexes of a tower `R → S → T`, with coefficients
in one module over `T`, live over the same ring.

Any polynomial resolution of `S` computes the cotangent complex up to
chain homotopy equivalence, and this is how a small resolution computes
it. An algebra map over `R` induces a chain map through the standard
resolutions, functorially. An isomorphism over `R` induces a chain
isomorphism, also between rings on different types, which is how an
algebra presented on another type — a quotient, a field adjunction, a
localization — carries its homology across. A linear map of
coefficients induces a chain map. A module over a ring `T'` that `T`
maps to gives the same homology as the module it restricts to over
`T`: the two complexes have the same terms and the same boundaries,
only the ring the homology is a module over changes. Over a tower,
changing the base ring
from `R` to `S` maps the cotangent complex of `T` over `R` to that of `T`
over `S`.

The cochain complex `cotangent_cochain(R, S, f, T, g, N)` holds, in each
degree, all functions on the names with values in `N`, under the
transposed Jacobians. Its cohomology `cotangent_cohomology` is
`D^n(S/R, N)`. It is the dual with coefficients in `N` of the cotangent
complex with coefficients in `T` itself, a complex based on the standard
names ([`free_complex_duality`](../../module/free_complex_duality/README.md)):
the two have the same terms, the same coboundary on them and the same
cohomology modules, so the laws of the dual — functoriality, homotopy
invariance, the long exact sequence of a split zigzag — apply to
`D^n` as `cotangent_cohomology` names it. In degree 1 it is the conormal
maps of the standard presentation modulo the restrictions of derivations
(algebra/cotangent/cohomology_one), which classifies the square-zero
extensions of `S` by `N` (algebra/cotangent/square_zero_classification).
In degree 0 the homology is the module of Kähler
differentials of `S` over `R` (algebra/ring/kaehler), and with
coefficients in `N` it is that module tensored with `N`. That
isomorphism crosses types: `D_0` is a module of classes of functions on
the host `U`, $\Omega_{S/R}$ one of cosets of functions on `S`'s carrier, and
the tag of an element is carried to the element.

Every statement that computes with the standard resolution carries
`cotangent_universe(R, 𝕌⟨A:U⟩) ∧ cotangent_universe(S, 𝕌⟨A:U⟩)`, and the
one about the change of base ring also carries
`cotangent_universe(T, 𝕌⟨A:U⟩)`; the restriction of coefficients, which
compares two complexes term by term, reads none. Under these hypotheses the free
algebras in the one host type `U` are free algebras, the tags of a
ring's elements are injective, and the augmentation reads a tag back as
its element. The host letter `U` is carried by no argument of the
cotangent constants: a text where nothing else fixes it writes
`cotangent_complex⟨U:U⟩`.

## The differentials of a polynomial simplicial algebra

| member | statement |
|---|---|
| `DifferentialTermsDef` | `differential_terms(X, N, n) = finite_supp(N.zero, N.carrier, X(n))` |
| `DifferentialFaceDef` | `differential_face(R, X, d, ε, N, n, i)` = the Jacobian of `d(n, i)` from the free algebra on `X(n)` to the one on `X(n - 1)`, at `augmentation_at(d, ε, n - 1)` |
| `DifferentialDegeneracyDef` | `differential_degeneracy(R, X, d, s, ε, N, n, j)` = the Jacobian of `s(n, j)` from `X(n)` to `X(n + 1)`, at `augmentation_at(d, ε, n + 1)` |
| `DifferentialBoundaryDef` | `differential_boundary(R, X, d, S, ε, N, n)` = `face_boundary` of the differential faces, Σ_{i ≤ n} (−1)^i • `differential_face(…, n, i)` |
| `DifferentialComplexDef` | `differential_complex(R, X, d, S, ε, N)`: the terms `differential_terms(X, N)` under `N`'s operations pointwise, with `differential_boundary` as differential |
| `DifferentialMapDef` | `differential_map(R, X, Y, d', ε', F, N, n)` = the Jacobian of `F(n)` from `X(n)` to `Y(n)`, at the target's augmentation in degree `n` |
| `DifferentialFaceHom`, `DifferentialDegeneracyHom` | each face and degeneracy of the differentials is a homomorphism of modules over `S` — card |
| `DifferentialSimplicialModule` | the differentials under the Jacobians of the faces and degeneracies are a simplicial module over `S` — card |
| `DifferentialScalarBased` | with scalar coefficients, the differentials of any augmented polynomial algebra are based by its names, with identity coordinates — card |
| `DifferentialComplexChain` | `chain_complex(S, differential_complex(R, X, d, S, ε, N))` — card |

## Algebra maps, homotopies and resolutions

| member | statement |
|---|---|
| `DifferentialMapChainMap` | an algebra map covering the identity of `S` induces a chain map of the differential complexes — card |
| `DifferentialMapIdentity`, `DifferentialMapCompose` | the identity induces the identity, a composite the composite — card |
| `DifferentialHomotopyChainHomotopy` | an algebra homotopy from `F` to `G` induces the chain homotopy $\sum_{j \le n} (-1)^j J(H(n, j))$ from the map of `F` to the map of `G` — card |
| `ResolutionMapChainHomotopyEquivalence` | a map of polynomial resolutions of `S` over its identity induces a chain homotopy equivalence, with inverse the Jacobians of a map back, coefficients over any `T` — card |

## The cotangent complex and its homology

| member | statement |
|---|---|
| `CotangentComplexDef` | `cotangent_complex(R, S, f, T, g, N)` = the differential complex of the standard resolution of `S` over `R`, its augmentation followed by `g` |
| `CotangentHomologyDef` | `cotangent_homology(R, S, f, T, g, N, n)` = `homology_module(cotangent_complex(R, S, f, T, g, N), n)`, i.e. `D_n(S/R, N)` |
| `CotangentChainComplex` | `chain_complex(T, cotangent_complex(R, S, f, T, g, N))` — card |
| `CotangentScalarBased` | with coefficients in `T` itself the cotangent complex is a based complex, the identity on the standard names — card |
| `CotangentHomologyModuleOn` | `module_on(T, D_n(S/R, N))` — card |
| `CotangentResolutionIndependence` | every polynomial resolution of `S` maps to the standard one over the identity, the map's Jacobians a chain homotopy equivalence onto the cotangent complex — card |

## Functoriality

| member | statement |
|---|---|
| `CotangentFunctorialMap` | an algebra map `φ : S → S'` over `R` induces a chain map $L_{S/R} \otimes N \to L_{S'/R} \otimes N$ through the standard resolutions; with `S' = T`, `φ = g` it is the left map of the transitivity triangle — card |
| `CotangentFunctorialIdentity`, `CotangentFunctorialCompose` | the identity induces the identity, a composite the composite — card |
| `CotangentIsomorphismInvariance` | an isomorphism over `R` between rings on different types induces a chain isomorphism and `D_n(S/R, N) ≅ D_n(S'/R, N)` — card |
| `CotangentCoefficientMap` | a linear map `N → N'` over `T` induces a chain map by composition — card |
| `CotangentCoefficientRestriction` | for a ring map `k : T → T'` and a module `N'` over `T'`, `D_n(S/R, N')` through `k ∘ g` has the carrier and the zero of `D_n(S/R, N')` with `N'` restricted to `T` along `k` — card |
| `CotangentBaseChangeMap` | over `R → S → T`, a map of the standard resolution of `T` over `R` to the one over `S` that changes the coefficients along `f` induces a chain map $L_{T/R} \otimes N \to L_{T/S} \otimes N$ — card |

## Cohomology

| member | statement |
|---|---|
| `CotangentCochainDef` | `cotangent_cochain(R, S, f, T, g, N)`: all functions on the names of degree `n` with values in `N`, coboundary the alternating sum of the transposed Jacobians of the faces |
| `CotangentCohomologyDef` | `cotangent_cohomology(R, S, f, T, g, N, n)` = `cohomology_module(cotangent_cochain(…), n)`, i.e. `D^n(S/R, N)` |
| `CotangentCochainComplex` | `cochain_complex(T, cotangent_cochain(R, S, f, T, g, N))` — card |
| `CotangentDualAgreement` | the dual of the cotangent complex with coefficients in `T`, taken with coefficients in `N`, is `cotangent_cochain`: the same terms, the same coboundary on them, the same cohomology modules — card |
| `CotangentMapsDualAgreement` | the duals of the map `g` induces and of the change of base are their transposed Jacobians, cochain maps between the cochain complexes — card |
| `CotangentCohomologyModuleOn` | `module_on(T, D^n(S/R, N))` — card |
| `CotangentCohomologyCoefficientLongExact` | a short exact sequence `0 → N' → N → N'' → 0` over `T` gives the long exact sequence `0 → D^0(S/R, N') → D^0(S/R, N) → D^0(S/R, N'') → D^1(S/R, N') → …`, its maps composition with `i` and `p` and the connecting map of the cochain complexes — card |

## Degree zero

| member | statement |
|---|---|
| `CotangentDegreeZero` | `D_0(S/R, S) ≅ kaehler_module(R, S, f)` as modules over `S` — card |
| `CotangentDegreeZeroCoefficients` | `D_0(S/R, N) ≅ kaehler_module(R, S, f) ⊗_S N` for a module `N` over `S` — card |
