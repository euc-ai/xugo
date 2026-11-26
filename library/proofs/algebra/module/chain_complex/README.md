# chain_complex — chain and cochain complexes, homology, the long exact sequences, cones and double complexes

A complex is a `complex_ops(A,B)` record P containing the shared
operations, the degree carriers `P.terms(n)`, and the boundary `P.d(n)`.
`chain_complex(R,P)` asserts module laws in each degree, `P.d(n+1)` a
module homomorphism and two-boundary vanishing. No common ambient module is
required. The boundary out of degree zero is not used: every element
of `P.terms(0)` is a cycle. Homology is the quotient of cycles by
boundaries, represented by cosets; `homology_module(P,n)` packages its
operations.

A chain map induces a map on homology by sending the whole class to its
image and adding the target boundaries. The connecting map of a short exact
sequence chooses a lift and a pull-back; its coset theorem makes the
class independent of those choices. Each map is read on representatives
as a relation closed under addition and scaling — for a chain map the
graph of f(n) on the cycles, for the connecting map the lift and
boundary equations — and `module_homomorphism.QuotientRelationHom`
turns its coset formula into linearity on homology. Short exact sequences bind their
records and maps under the letter S. The underlying functions are total,
and all linearity, exactness and inverse assertions are on the specified
carriers.

## Complexes and homology

| member | statement |
|---|---|
| `ComplexOpsData`, `ComplexModuleDef` | complex records and their degree module records |
| `ChainComplex` | `chain_complex(R, P)` ⇔ modules, boundary homomorphisms, `d ∘ d = 0` — a structure, its subject `P` |
| `ComplexModules`, `ComplexBoundaryHom`, `ComplexBoundaryTwice` | its three axioms |
| `CyclesDef`, `BoundariesDef`, `HomologyDef`, `HomologyModuleDef` | `cycles(P, n)`, `boundaries(P, n)`, `homology(P, n) = left_cosets(+, cycles, boundaries)` |
| `CyclesKernel` | above degree 0 the cycles are the kernel of the boundary map |
| `CyclesZero` | `cycles(P, 0) = P.terms(0)` |
| `CyclesSubmodule` | cycles form a submodule of `P.terms(n)` |
| `BoundariesSubmodule` | boundaries form a submodule of `P.terms(n)` |
| `CyclesSubsetTerms` | `cycles(P, n) ⊆ P.terms(n)` |
| `BoundariesSubsetCycles` | `boundaries(P, n) ⊆ cycles(P, n)` |
| `InHomology` | a class of `homology(P, n)` is exactly the coset of a cycle by the boundaries |
| `CycleCorrection` | a cycle minus a boundary is a cycle, and a boundary only if the cycle is one |
| `HomologyModuleOn` | homology is a module on a set |
| `HomologyTrivialIffExact` | one point ⇔ every cycle a boundary — card |

## Chain maps and homotopy

| member | statement |
|---|---|
| `ChainMapDef` | `chain_map(P, Q, f)` ⇔ homomorphisms commuting with the boundaries |
| `ChainMapHom`, `ChainMapSquare` | the degreewise homomorphisms and commuting squares of a chain map |
| `ChainMapIdentity`, `ChainMapCompose` | the identity is a chain map, and chain maps compose |
| `HomologyMapDef` | `homology_map(Q, f, n, s) = image(f(n), s) + boundaries(Q, n)` |
| `ChainMapCycles` | a chain map carries cycles to cycles and boundaries to boundaries |
| `HomologyMapCoset` | the map on homology sends the class of `u` to the class of `f(n)(u)` |
| `HomologyMapHom` | the map on homology is a homomorphism of homology modules |
| `HomologyIsomorphismCriterion` | a chain map that is onto on cycles and reflects boundaries induces an isomorphism on homology |
| `HomologyMapIdentity` | the identity chain map induces the identity on every homology class |
| `HomologyMapCompose` | on every class the map on homology of a composite chain map is the map of the second after the map of the first |
| `ChainHomotopyDef` | `f − g = e ∘ h + h ∘ d` |
| `HomotopicSameHomologyMap` | homotopic chain maps agree on homology |
| `ChainHomotopyCalculus` | homotopies pre- and postcompose with chain maps, reverse by negation and concatenate by addition, with the witnesses — card |

## The long exact sequence

| member | statement |
|---|---|
| `ExactComplexesDef`, `ShortExactComplexes` | degreewise exactness; three complexes and two chain maps, exact — a structure with no subject, its laws under the letter, `∀S:short_exact_complexes(A, B, C, D)` |
| `ShortExactSubComplex`, `ShortExactMiddleComplex`, `ShortExactQuotientComplex` | the three complexes of a short exact sequence |
| `ShortExactInclusionMap`, `ShortExactProjectionMap`, `ShortExactDegreewise` | its two chain maps and degreewise short exactness |
| `CycleLiftPullback` | every quotient cycle at `n+1` has a lift whose boundary pulls back to a cycle at `n` |
| `ConnectingHomDef` | `connecting_hom(P', P, i, p, n, s)`: lift, bound, pull back, take the class |
| `ConnectingHomCoset` | the connecting map sends the class of a cycle to the class of any pull-back of any lift |
| `ConnectingHom` | the connecting map is a homomorphism `H(n+1)(P'') → H(n)(P')` |
| `LongExactMiddle` | exactness at `H(n)(P)`: `image(i*) = kernel(p*)` |
| `LongExactQuotient` | exactness at `H(n+1)(P'')`: `image(p*) = kernel(δ)` |
| `LongExactSub` | exactness at `H(n)(P')`: `image(δ) = kernel(i*)` |

## The five lemma

Two complexes read as rows at degrees 4 down to 0, a chain map between
them, and exactness of a row at a degree as `cycles = boundaries`.

| member | statement |
|---|---|
| `FourLemmaInjective` | `P` exact at 2, `Q` exact at 3, `f(4)` onto, `f(3)` and `f(1)` one-to-one ⇒ `f(2)` one-to-one |
| `FourLemmaSurjective` | `P` exact at 1, `Q` exact at 2, `f(3)` and `f(1)` onto, `f(0)` one-to-one ⇒ `f(2)` onto |
| `FiveLemma` | `P` exact at 2 and 1, `Q` exact at 3 and 2, `f(4)` onto, `f(0)` one-to-one, `f(3)` and `f(1)` isomorphisms ⇒ `f(2)` an isomorphism |

## The cone and the comparisons of complexes

`chain_shift(P)` moves P up one degree and negates its boundary;
degree 0 holds `P.zero` alone. The cone of a chain map `f: P → Q`,
`chain_cone(P, Q, f)`, sits at the pair type: degree n holds the pairs
`(x, y)` with x in the shift and y in `Q.terms(n)`, and its boundary is
`(x, y) ↦ (−P.d(x), f(x) + Q.d(y))`, with `P.zero` in the first place
out of degree 1. It is a complex, and with the inclusion
`y ↦ (P.zero, y)` and the projection `(x, y) ↦ x` it is the middle of a
short exact sequence `Q → cone → shift(P)`. The connecting map of that
sequence is f on homology, so the long exact sequence says that the
cone is exact in every degree exactly when f is an isomorphism on
homology in every degree; degree 0 is where `H₀(f)` is onto.

A chain map compares two complexes in three ways, in decreasing
strength. `chain_isomorphism(R, P, Q, f)` is an isomorphism of the
degree modules; `chain_homotopy_equivalence(R, P, Q, f, g)` is a pair of
chain maps whose two composites are homotopic to the identities — the
inverse g is part of the data, so "f is an equivalence" is `∃g` and
"P and Q are equivalent" is `∃f g`; and `quasi_isomorphism(R, P, Q, f)`
is an isomorphism on homology in every degree. Quasi-isomorphisms
compose, and they keep exactness both ways; a square of chain maps with
quasi-isomorphisms down its sides induces one between the cones of its
rows. In a short exact sequence with a section in each degree, the cone
of the inclusion maps onto the quotient by a quasi-isomorphism: the
third term is the cone of the first map. A contraction of the cone of f
reads off a homotopy inverse of f and both homotopies, and a chain
homotopy equivalence cancels from either side of a homotopy.

| member | statement |
|---|---|
| `ChainShiftDef` | `chain_shift(P)`: P one degree up, the boundary negated, `P.zero` alone in degree 0 |
| `ChainConeDef` | `chain_cone(P, Q, f)`: the pairs `(x, y)`, boundary `(x, y) ↦ (−P.d(x), f(x) + Q.d(y))` |
| `QuasiIsomorphismDef` | `quasi_isomorphism(R, P, Q, f)` ⇔ a chain map inducing isomorphisms of the homology modules |
| `ChainIsomorphismDef` | `chain_isomorphism(R, P, Q, f)` ⇔ a chain map that is an isomorphism in every degree |
| `ChainHomotopyEquivalenceDef` | `chain_homotopy_equivalence(R, P, Q, f, g)` ⇔ chain maps both ways, `g ∘ f` and `f ∘ g` homotopic to the identities |
| `ShiftChainComplex` | the shift of a complex is a complex — card |
| `ConeChainComplex` | the cone of a chain map is a complex — card |
| `ConeShortExact` | `Q → chain_cone(P, Q, f) → chain_shift(P)` is short exact — card |
| `ConeQuasiIffAcyclic` | f is a quasi-isomorphism ⇔ its cone is exact in every degree — card |
| `ConeContractibleHomotopyInverse` | a contraction of the cone of f gives a homotopy inverse of f, `y ↦ fst(H(n)(P.zero, y))`, and both homotopies — card |
| `DegreewiseSplitThirdTermCone` | a short exact sequence with a section in each degree: `cone(i) → P''`, `(x, y) ↦ p(y)`, is a quasi-isomorphism — card |
| `ConeMapQuasiIsomorphism` | a commuting square with quasi-isomorphisms α, β down its sides: `(x, y) ↦ (α(x), β(y))` is a quasi-isomorphism of the cones — card |
| `QuasiIsomorphismCompose` | quasi-isomorphisms compose |
| `QuasiIsomorphismAcyclic` | complexes joined by a quasi-isomorphism are exact together — card |
| `ChainIsomorphismQuasiIsomorphism` | a chain isomorphism is a quasi-isomorphism — card |
| `ChainHomotopyEquivalenceQuasiIsomorphism` | both maps of a chain homotopy equivalence are quasi-isomorphisms |
| `ChainHomotopyEquivalenceCancel` | a chain homotopy equivalence cancels from either side of a homotopy; a strict section of it is a homotopy inverse — card |

## Cochain complexes and the long exact sequence

Cochain complexes use the same `complex_ops(A,B)` records, with
`Q.d(n)` going from degree n to n+1. Every cocycle is in the kernel
of this coboundary. Coboundaries at degree zero are the zero submodule;
at n+1 they are the image of `Q.d(n)`. Cohomology is their quotient,
with operations in `cohomology_module(Q,n)`. The connecting map raises
degree by one. Chain and cochain proofs share the quotient relation theorem and
express their lift and pull-back constructions in the corresponding
cycle laws.

| member | statement |
|---|---|
| `CochainComplex` | `cochain_complex(R, Q)` — a structure, its subject `Q`; `CochainModules`, `CochainCoboundaryHom`, `CochainCoboundaryTwice` its axioms |
| `CocyclesDef`, `CoboundariesDef`, `CohomologyDef`, `CohomologyModuleDef` | cocycles, coboundaries (`{0}` at degree 0), cohomology |
| `CochainMapDef`, `CochainHomotopyDef`, `CohomologyMapDef` | cochain maps, cochain homotopies, the map on cohomology |
| `CochainHomotopyEquivalenceDef` | `cochain_homotopy_equivalence(R, Q, Q', f, g)` ⇔ cochain maps both ways, both composites cochain homotopic to the identities |
| `ShortExactCochainComplexes` | `short_exact_cochain_complexes(R, Q', Q, Q'', i, p)` — a structure with no subject, its laws under the letter, `∀S:short_exact_cochain_complexes(A, B, C, D)` |
| `CoboundariesSucc` | `coboundaries(Q, n+1) = image(Q.d(n), Q.terms(n))` |
| `CocyclesSubmodule` | cocycles form a submodule of `Q.terms(n)` |
| `CoboundariesSubsetCocycles` | `coboundaries(Q, n) ⊆ cocycles(Q, n)` |
| `InCohomology` | a class of `cohomology(Q, n)` is exactly the coset of a cocycle by the coboundaries |
| `CocyclesKernel` | cocycles are the kernel of the coboundary map, for arbitrary complex records |
| `CochainMapHom`, `CochainMapSquare` | the degreewise homomorphisms and commuting squares of a cochain map |
| `CochainMapIdentity`, `CochainMapCompose` | the identity is a cochain map, and cochain maps compose |
| `ShortExactCochainSubComplex`, `ShortExactCochainMiddleComplex`, `ShortExactCochainQuotientComplex` | the three cochain complexes of a short exact sequence |
| `ShortExactCochainInclusionMap`, `ShortExactCochainProjectionMap`, `ShortExactCochainDegreewise` | its two cochain maps and degreewise short exactness |
| `CocycleLiftPullback` | every quotient cocycle at `n` has a lift whose coboundary pulls back to a cocycle at `n+1` |
| `CoconnectingHomDef` | the connecting map $H^n(Q'') \to H^{n+1}(Q')$ |
| `CohomologyModuleOn` | cohomology is a module — card |
| `CochainMapCocycles` | a cochain map carries cocycles to cocycles and coboundaries to coboundaries |
| `CohomologyMapCoset` | the map on cohomology carries the class of `u` to the class of `f(n)(u)` |
| `CohomologyMapHom` | the map on cohomology is a homomorphism — card |
| `HomotopicSameCohomologyMap` | homotopic cochain maps agree on cohomology |
| `CohomologyMapIdentity`, `CohomologyMapCompose` | the map on cohomology keeps identities and composites — card |
| `CohomologyMapCongruence` | cochain maps that agree on the terms have the same map on cohomology — card |
| `CochainHomotopyCongruence` | a cochain homotopy between two maps is one between any two maps that agree with them on the terms |
| `CochainHomotopyEquivalenceIsomorphism` | a cochain homotopy equivalence is an isomorphism on cohomology |
| `CoconnectingHomCoset` | the connecting map sends the class of a cocycle to the class of any pull-back of any lift |
| `CoconnectingHom` | the connecting map is a homomorphism $H^n(Q'') \to H^{n+1}(Q')$ |
| `CoLongExactStart` | the sequence starts one-to-one: `i*` on `H^0(Q')` |
| `CoLongExactMiddle` | exactness at `H^n(Q)`: `image(i*) = kernel(p*)` |
| `CoLongExactQuotient` | exactness at `H^n(Q'')`: `image(p*) = kernel(δ)` |
| `CoLongExactSub` | exactness at $H^{n+1}(Q')$: `image(δ) = kernel(i*)` |
| `CoconnectingNaturality` | a map of short exact sequences of cochain complexes commutes with the connecting maps — card |

## First-quadrant double complexes

`double_complex(R,V,D,h,v)` uses submodules `D(p,q)` of one ambient
module V, horizontal and vertical boundaries that square to zero and
commute. Its subject is D. `double_total` takes the finite diagonal:
a function u on natural indices has `u(p)∈D(p,n−p)` for `p≤n` and is
zero afterwards. Its boundary at coordinate p is
`h(p+1,n−p−1)(u(p+1)) + s(p) • v(p,n−p)(u(p))`, for `p<n`, and zero
otherwise, s being the sign on the vertical boundary of the column p;
a total degree is a module at any sign. From the total complex on,
every statement takes comm_ring's alternating sign, `alternating_sign(p)`
= (−1)^p, a sign under which the boundary squares to zero; the
chapter names that total «doubleTotal»,
`double_total(V, D, h, v, alternating_sign)`.

| member | statement |
|---|---|
| `DoubleComplex` | `double_complex(R, V, D, h, v)` ⇔ V a module, submodules D(p, q), horizontal and vertical boundary homomorphisms, each squaring to zero, the two commuting — a structure, its subject D |
| `DoubleAmbientModule`, `DoubleSubmodules`, `DoubleHorizontalHom`, `DoubleVerticalHom`, `DoubleHorizontalTwice`, `DoubleVerticalTwice`, `DoubleCommute` | the structure's seven axioms: V a module, each D(p, q) a submodule, h and v homomorphisms between them, each squaring to zero, and the two commuting |
| `DoubleTotalTermsDef`, `DoubleBoundaryDef`, `DoubleTotalDef`, `DoubleEdgeDef` | finite diagonal total and its edge augmentation |
| `DoubleTotalTermsMember` | u is a total term of degree n exactly when `u(p) ∈ D(p, n − p)` for `p ≤ n` and `u(p) = V.zero` for `p > n` |
| `DoubleBoundaryCoordinate` | the total boundary out of degree p + q + 1, at the coordinate p of the diagonal of degree p + q it lands on, is `h(p + 1, q, u(p + 1)) + s(p) • v(p, q + 1, u(p))` |
| `DoubleBoundaryPast` | the total boundary out of degree n + 1 vanishes at every coordinate p > n, past the top of the diagonal of degree n it lands on |
| `DoubleTotalCoordinate` | a total term of degree p + q has its coordinate p in `D(p, q)` |
| `DoubleTotalPast` | a total term of degree n vanishes at every coordinate p > n |
| `DoubleTotalModule` | with V a module and every D(p, q) a submodule of it, each total degree `complex_module(double_total(V, D, h, v, s), n)` is a module, at any sign s |
| `DoubleTotalComplex` | the total at the alternating sign, «doubleTotal», is a chain complex |
| `AcyclicAssembly` | exact rows, including surjectivity at the zero edge, make the total acyclic — card |
| `ColumnCycleVanishing` | with exact columns, a total cycle vanishing from a coordinate m ≤ n on is a boundary — card |
| `AugmentedCycleLift` | with exact augmented columns, every cycle of E is the edge a(n)(u(n)) of a total cycle — card |
| `AugmentedAssembly` | exact augmented columns and commuting horizontal augmentation give a homology isomorphism onto the edge complex |

Assembly removes a cycle one finite diagonal component at a time.
There is no infinite sum or spectral-sequence convergence assumption.

### The transpose: assembly along the columns

Transposing a double complex trades its rows and columns: `D(q, p)` at
`(p, q)`, with v horizontal and h vertical. No constant names the
transpose; a statement spells it in place, `V, (λp q. D(q, p)),
(λp q. v(q, p)), (λp q. h(q, p))`. The two total complexes are
isomorphic by the sign `alternating_sign(p·q) = (−1)^(pq)` on the
coordinate `(p, q)`, which reconciles the original total boundary's
`alternating_sign(p)` on v with the transpose's `alternating_sign(q)`
on h. Through it each assembly law has its mirror:
exact columns, the vertical boundary onto `D(p, 0)` included, make the
total complex exact, and rows exact and augmented at `p = −1` by maps
`b(q): D(0, q) → E(q)` onto a complex E give the quasi-isomorphism
`u ↦ b(n)(u(0))` onto E.

| member | statement |
|---|---|
| `TransposeDoubleComplex` | the transpose is a double complex — card |
| `TransposeTotalIsomorphic` | the two total complexes are chain isomorphic, `alternating_sign((n − q)·q)` on the coordinate q — card |
| `AcyclicAssemblyColumns` | exact columns, including the vertical boundary onto `D(p, 0)`, make the total exact — card |
| `AugmentedAssemblyRows` | exact rows augmented at `p = −1` by `b(q)` commuting with v give the quasi-isomorphism `u ↦ b(n)(u(0))` onto E — card |

### Maps of double complexes and the columnwise cone

A map of double complexes is a family of homomorphisms `F(p, q)`
commuting with both boundaries; read on the diagonals it is the chain
map `double_total_map(F)`, `F(p, n − p)` on the coordinate p. A column is
a complex, `double_column(V, D, v, p)`. The cone of F is taken in every
column at once: the product `product_module(V, V')`
(algebra/module/submodule), `double_cone_terms`, `double_cone_horizontal`
and `double_cone_vertical` are the four components of a double complex
at the pair type whose column p is the cone of `F(p, ·)`, and its total
complex is the cone of the total map, up to the sign `(−1)^p` on the first
component of the coordinate p. So a map
that is a quasi-isomorphism on every column is one on the total
complexes: the cones of the columns are exact, assembly along the
columns makes the total of the double cone exact, and that total is the
cone of the total map. Short exactness at every `(p, q)` is short
exactness of the total complexes, a diagonal being a finite sum.

| member | statement |
|---|---|
| `DoubleColumnDef` | `double_column(V, D, v, p)`: the column p as a complex |
| `DoubleComplexMapDef` | `double_complex_map(R, V, D, h, v, V', D', h', v', F)` ⇔ homomorphisms commuting with h and with v |
| `DoubleTotalMapDef` | `double_total_map(F, n, u, p) = F(p, n − p, u(p))` |
| `doubleConeTermsDef`, `doubleConeHorizontalDef`, `doubleConeVerticalDef` | the columnwise cone in `V × V'`: the pairs `D(p, q − 1) × D'(p, q)` (`{V.zero}` first at q = 0), `h × h'`, each column's cone boundary |
| `DoubleColumnChainComplex` | every column of a double complex is a complex — card |
| `DoubleComplexMapTotal` | a map of double complexes is a chain map of the total complexes — card |
| `DoubleShortExactTotal` | short exact at every `(p, q)` ⇒ short exact on the total complexes — card |
| `DoubleConeDoubleComplex` | the columnwise cone is a double complex — card |
| `DoubleConeTotal` | its total complex is chain isomorphic to the cone of the total map — card |
| `ColumnQuasiIsomorphismTotal` | a quasi-isomorphism on every column gives one of the total complexes — card |
