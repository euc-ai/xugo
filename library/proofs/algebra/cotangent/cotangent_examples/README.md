# cotangent_examples — the cotangent complex computed: polynomial algebras, quotients, regular quotients and étale hypersurfaces

The cotangent complex of algebra/cotangent/cotangent_complex, computed
on rings whose resolutions are small enough to read: a free algebra,
which resolves itself; the quotient of a ring by one element, which the
Koszul algebra resolves when the element is not a zero divisor; the
quotient by any ideal, whose first André–Quillen homology is the
conormal module I/I²; and the étale hypersurfaces R[x]/(g), with a
simple separable field extension and the localization at one element as
instances. The statements about `D_n` are cards.

## The Koszul algebra of an element

For a member `g` of a commutative ring `R`, the Koszul algebra is the polynomial simplicial algebra free on one generator `x` of degree 1 with `d_0 x = g` and `d_1 x = 0`. In degree `n` it is the free algebra on `x_1, …, x_n`, the pullbacks of `x` along the surjections of `[n]` onto `[1]`. Each `x_j` has one name, `koszul_name(j)`, in every degree, so the algebra of degree `n − 1` is a subring of the one of degree `n`, and only the faces and degeneracies tell the degrees apart. The face `d_i` for `1 ≤ i < n` sets $x_i = x_{i+1}$, `d_n` sets `x_n = 0`, and `d_0` sends `x_1` to the constant `g` and lowers every other index. The degeneracy `s_i` raises the indices above `i`. So `g` enters through `d_0` alone. The degree-0 algebra is the constants, and the algebra is augmented over `R/(g)`, the record `koszul_quotient(R, g)`, through the projection.

The Moore complex has a closed form. The faces `d_1, …, d_n` each kill one factor of $\Pi_n = (x_1 - x_2) \cdots (x_{n-1} - x_n) \cdot x_n$. Every factor is monic of degree one in a variable the rest does not involve, so dividing a Moore term by one factor at a time shows that the Moore terms of degree `n` are exactly the multiples of `Π_n`, over every commutative ring. `d_0` sends $\Pi_{n+2}$ to $(g - x_1) \cdot \Pi_{n+1}$, which is monic in `x_1` whatever `g` is, so a Moore cycle of degree at least 2 is `Π_n·(x_1 − g)·q`. In degree 1, `d_0 Π_1` is the constant `g` and the cycle condition reads `g·q(g) = 0`. It gives the same shape only when `g` is not a zero divisor; with `g = 0` every multiple of `x_1` is a cycle and `x_1` is no boundary. Every cycle of that shape is `d_0` of the Moore term $-\Pi_{n+1} \cdot s_0(q)$, and the boundaries of degree 0 are the constants of the multiples of `g`. So when `g` is not a zero divisor, the Koszul algebra is a polynomial resolution of `R/(g)`.

### The Koszul algebra

| member | statement |
|---|---|
| `koszulNameDef`, `koszulIndexDef`, `koszulNamesDef` | `koszul_name(j)`, the name of `x_j` in `U`; `koszul_index`, the index a name reads back to; `koszul_names(n) = image(koszul_name, 1 .. n)` |
| `koszulFaceValueDef`, `koszulFaceDef` | `koszul_face_value(R, g, n, i, k)`, the value of `d_i` at `x_k`; `koszul_face(R, g, n, i)`, the algebra map fixing the constants with those values |
| `koszulDegeneracyDef` | `koszul_degeneracy(R, i)`, the algebra map renaming `x_k` to `x_k` for `k ≤ i` and to $x_{k+1}$ above |
| `koszulSimplicialSetDef` | `koszul_simplicial_set(R, g) = mk_simplicial(λn. universe_algebra(R, koszul_names(n)), koszul_face(R, g), λn. koszul_degeneracy(R))`, the Koszul algebras as one simplicial set |
| `koszulProductDef` | `koszul_product(R, n) = Π_n = (x_1 − x_2)⋯(x_{n−1} − x_n)·x_n`, with `Π_0 = 1` |
| `KoszulQuotientDef`, `KoszulProjectionDef`, `koszulAugmentationDef` | `R/(g)` as a ring record, the projection `a ↦ a + (g)`, the augmentation of the constants onto `R/(g)` |

### The simplicial algebra

| member | statement |
|---|---|
| `KoszulNames` | in a universe, `koszul_index(koszul_name(j)) = j`: the names of degree `n` are `n` distinct members of `U` — card |
| `KoszulFaces`, `KoszulFacesHom` | `d_i` fixes the constants and sends `x_k` to `koszul_face_value(R, g, n, i, k)`; each `d_i` is an algebra map from degree `n + 1` to degree `n` — card |
| `KoszulDegeneracies`, `KoszulDegeneraciesHom` | `s_i` fixes the constants and sends `x_k` to `x_k` for `k ≤ i` and to $x_{k+1}$ above; each `s_i` is an algebra map from degree `n` to degree `n + 1` — card |
| `KoszulSimplicial`, `KoszulPolynomialAlgebra` | the Koszul algebras form a simplicial set, `simplicial_set(koszul_simplicial_set(R, g))`, and a polynomial simplicial algebra over `R` — card |
| `KoszulAugmented` | augmented over `R/(g)` through the projection — card |

### The Moore complex

| member | statement |
|---|---|
| `KoszulProductRegular` | `Π_n` lies in the algebra of degree `n` and is not a zero divisor there — card |
| `KoszulMooreTerms` | the Moore terms of degree `n` are the multiples of `Π_n`, over every commutative ring — card |
| `KoszulBoundaryOfProduct` | `d_0 Π_1 = g` and $d_0 \Pi_{n+2} = (g - x_1) \cdot \Pi_{n+1}$ — card |
| `KoszulCycleDivisible` | in degree `n + 2`, if `Π·q` is a Moore cycle then `x_1 − g` divides `q`, for every `g` — card |
| `KoszulCycleDegreeOne` | `g` not a zero divisor: if `x_1·q` is a Moore cycle then `x_1 − g` divides `q` — card |
| `KoszulPreimage` | $-\Pi_{n+2} \cdot s_0(q)$ is a Moore term with `d_0` equal to $\Pi_{n+1} \cdot (x_1 - g) \cdot q$ — card |
| `KoszulDegreeZero` | the Moore boundaries of degree 0 are the constants `g·a`; the augmentation is onto `R/(g)`, its fibres the cosets of those boundaries — card |
| `KoszulAcyclic` | `g` not a zero divisor: the Koszul algebra is a `polynomial_resolution` of `R/(g)` — card |

## The cotangent complex from a resolution of one's own

The André–Quillen homology is defined on the standard resolution, but any polynomial resolution computes it, and a small resolution makes it visible. The free algebra on a set of names W, in the universe, resolves itself: the constant algebra on W, with every face the identity. Its differentials form the face complex of a constant simplicial module, so D_0(R[W]/R, N) is finite_supp(N, W), the direct sum of copies of N indexed by W, and every higher D_n vanishes. The constants of a ring resolve the ring over itself, and all of D_n(R/R, N) vanishes. The free algebra here is the universe's own, a ring on U. The room it asks of U is for U itself, which every infinite universe has, so the hypothesis is the reflexive instance of PowerSetUniverse.

The Koszul algebra of g has, as its differentials with coefficients in a module N over R/(g), the reduced chains of the simplicial circle Δ[1]/∂Δ[1] tensored with N. Its homology is N in degree 1 and zero elsewhere, whatever g is. When g is not a zero divisor the Koszul algebra resolves R/(g), so D_1(R/(g) / R, N) is N, m standing for the class of the conormal cycle of g with coefficient m, and every other D_n vanishes. At p prime this gives the whole cotangent complex of 𝔽_p over ℤ: 𝔽_p in degree 1.

| member | statement |
|---|---|
| `ConstantDifferentialComplex` | the differentials of the constant algebra on W: no boundaries in degree 0, exact above — card |
| `PolynomialCotangentDegreeZero` | `D_0(R[W]/R, N) ≅ finite_supp(N, W)` — card |
| `PolynomialCotangentVanishes` | `n ≥ 1 ⇒ D_n(R[W]/R, N) = 0` — card |
| `PolynomialCohomologyVanishes` | `n ≥ 1 ⇒ Dⁿ(R[W]/R, N) = 0` for every module N over R[W] — card |
| `EmptyNamesResolution` | the constants of R, the algebra on no names, resolve R over itself through evaluation — card |
| `IdentityCotangentVanishes` | `D_n(R/R, N) = 0` for every n — card |
| `KoszulDifferentialFaces` | `d_i(dx_k ⊗ m)` is `dx_j ⊗ m` when `d_i` sends `x_k` to `x_j`, zero when it sends it to a constant — card |
| `KoszulDifferentialHomologyOne` | the Koszul differentials have homology N in degree 1, `m ↦ [dx_1 ⊗ m]` — card |
| `KoszulDifferentialHomologyVanishes` | the Koszul differentials are exact in every degree but 1 — card |
| `RegularQuotientCotangent` | g no zero divisor ⇒ `D_1(R/(g) / R, N) ≅ N` and `D_n = 0` for `n ≠ 1` — card |
| `RegularQuotientFirstHomology` | g no zero divisor ⇒ `m ↦` the class of the conormal cycle of g with coefficient m is an isomorphism `N → D_1(R/(g) / R, N)` — card |
| `FpOverZ` | `n ≥ 2 ⇒ D_n(𝔽_p/ℤ, 𝔽_p) = 0` — card |

## The conormal module

For a ring map f from R onto S, with kernel I, the first André–Quillen homology D_1(S/R, S) is I/I² as a module over S, and D_0 vanishes. This is one statement for every quotient ring of the corpus at once. The conormal module conormal_module(R, S, f) is the cosets of I² = ideal_mul(I, I) in I, where s acts through its fibre r + I as rx + I².

The conormal map sends x in I to the class of conormal_cycle(R, S, x). That is the differential of the 1-simplex var(x) − var(0) of the standard resolution, which lifts x through the 0-th face. The map is additive, f-linear and kills I², each law by an explicit boundary of degree 2.

Its inverse is read off the standard resolution up to degree 2. The retraction conormal_retraction gives each name of an element of S a preimage in R and sends a differential Σ ẑ(u) du to Σ ẑ(u)(e(u) − ê(u)). Modulo I² it does not depend on the choices, it kills the boundaries by Taylor's formula to first order, and every cycle is homologous to the conormal cycle of its retraction. No module J/J² of the presentation R[S] → S is minted: the one definition conormal_retraction carries the comparison up to degree 2.

The quotient by an ideal I, the ring record ideal_quotient_ring(R, I) of algebra/ring/quotient_ring, is such an S. The Koszul algebra's R/(g), `koszul_quotient(R, g)`, and the hypersurface R[x]/(g), `hypersurface_ring(R, g)`, are minted on their own; KoszulQuotientIdealQuotient identifies the first with `ideal_quotient_ring` at the ideal g generates, and HypersurfaceKoszulQuotient the second with the first over the ring R[x]. At a local ring and its maximal ideal m of non-units it gives the Zariski cotangent space m/m² over the residue field. At a principal ideal generated by a non-zero-divisor g, (g)/(g²) is R/(g), so D_1(𝔽_p/ℤ, 𝔽_p) is 𝔽_p.

| member | statement |
|---|---|
| `ConormalModuleDef` | `conormal_module(R, S, f)`: `I/I²` over S, `I = ring_kernel(S.zero, R.carrier, f)` |
| `conormalCycleDef` | `conormal_cycle(R, S, x) = δ_{c(x)} − δ_{c(0)}`, the differential of `var(c(x)) − var(c(0))` |
| `conormalMapDef` | `conormal_map(R, S, f, x)`: the class of `conormal_cycle(R, S, x)` in `D_1(S/R, S)` |
| `conormalRetractionDef` | `conormal_retraction(R, S, f, z) = Σ_u ẑ(u)·(e(u) − ê(u))`, preimages chosen |
| `StandardDifferentialBoundaryOne` | the boundary of `du ⊗ m` out of degree 1: `Σ_t ε(∂_t u)·m dt − m d(tag(ε(u)))` — card |
| `StandardDifferentialBoundaryTwo` | the boundary of `dv ⊗ m` out of degree 2: `dv ⊗ m − m d(d_0 v) + m d(d_1 v)` — card |
| `ConormalDegreeZero` | f onto S ⇒ `D_0(S/R, N) = 0` — card |
| `ConormalModuleOn` | f onto S ⇒ `module_on(S, conormal_module(R, S, f))` — card |
| `ConormalCycleIsCycle` | `x ∈ I ⇒ conormal_cycle(R, S, x)` is a cycle of degree 1 — card |
| `ConormalMapHom` | the conormal map lands in `D_1`, is additive, and `x ↦ r·x` goes to `f(r)•` — card |
| `ConormalMapKillsProducts` | `x, y ∈ I ⇒ conormal_map(x·y) = 0` — card |
| `ConormalMapKillsSquare` | `x ∈ I² ⇒ conormal_map(x) = 0` — card |
| `ConormalRetraction` | the retraction lands in I, is additive and f-linear modulo I², and returns x from `conormal_cycle(x)` modulo I² — card |
| `ConormalRetractionKillsBoundaries` | the retraction sends the boundaries of degree 1 into I² — card |
| `ConormalCycleReduction` | a cycle z of degree 1 has the class `conormal_map(conormal_retraction(z))` — card |
| `ConormalMapInjective` | `x ∈ I ∧ conormal_map(x) = 0 ⇒ x ∈ I²` — card |
| `ConormalMapOnto` | every class of `D_1(S/R, S)` is `conormal_map(x)` for some `x ∈ I` — card |
| `ConormalModule` | f onto S ⇒ `induced_map(conormal_map)` is an isomorphism of S-modules `I/I² → D_1(S/R, S)` — card |

| member | statement |
|---|---|
| `KoszulQuotientIdealQuotient` | `koszul_quotient(R, g) = ideal_quotient_ring(R, (g))`, and the projections agree — card |
| `QuotientByIdealCotangent` | `ring_ideal(R, I) ⇒ D_1(R/I / R, R/I) ≅ I/I²` and `D_0 = 0` — card |
| `ZariskiCotangentSpace` | at a local ring, `D_1(k/R, k) ≅ m/m²` for the residue field k and the non-units m — card |
| `PrincipalConormalModule` | g no zero divisor ⇒ `(g)/(g²) ≅ R/(g)` over R/(g) — card |
| `FpOverZLowDegrees` | `D_1(𝔽_p/ℤ, 𝔽_p) ≅ 𝔽_p` and `D_0(𝔽_p/ℤ, 𝔽_p) = 0` — card |

## The étale hypersurfaces: R[x]/(g) and its two instances

An étale hypersurface over a ring R is the quotient R[x]/(g), `hypersurface_ring(R, g)`. Here R[x] is the polynomial chapter's one-variable polynomials, sequences `num → A`, not the free algebra. The quotient is a ring record on the cosets of the ideal `hypersurface_ideal(R, g)` that g generates, with the quotient ring's operations read at the polynomial ring's, so it lives on `set(num → A)`. `hypersurface_projection(R, g)` is the quotient map and `hypersurface_constant(R, g)` the constants, which make the quotient an R-algebra. A member of the ideal is a multiple of g, and two classes agree when g divides their difference. A ring map from R[x] that kills g induces one from the quotient, the map `induced_map` the quotient group chapter uses for its first isomorphism theorem. g is separable exactly when its derivative is a unit in the quotient, which is the étale condition the cotangent complex reads.

Two rings from other chapters are such quotients, each by an isomorphism across types. The simple algebraic extension K(a), `field_adjoin(L, K, {a})`, is K[x] modulo the minimal polynomial of a: evaluation at a induces an isomorphism of K-algebras, and the minimal polynomial is a non-zero-divisor whose derivative, when it is separable, is a unit. The localization of R at the powers of f, `ring_localization(R.mul, R.carrier, monoid_powers(R.mul, R.one, f))`, is R[x] modulo f·x − 1. The quotient with its constants satisfies the localization chapter's `is_localization_on`, so the two rings are isomorphic as R-algebras, with a / 1 going to the constant a and 1 / f to the class of x. f·x − 1 is a non-zero-divisor and separable. So in both instances g satisfies what the vanishing of the cotangent complex of an étale hypersurface asks of it.

### The quotient R[x]/(g)

| member | statement |
|---|---|
| `hypersurfaceIdealDef` | `hypersurface_ideal(R, g)` = the ideal g generates among the polynomials over R |
| `HypersurfaceRingDef` | `hypersurface_ring(R, g)` = the cosets of `hypersurface_ideal(R, g)` with the quotient ring's operations at the polynomial ring's, as one record |
| `hypersurfaceProjectionDef` | `hypersurface_projection(R, g, p)` = p + (g) |
| `hypersurfaceConstantDef` | `hypersurface_constant(R, g, a)` = the class of the constant a • basis_vector(0) |
| `HypersurfaceIdealDivides` | p ∈ (g) ⇔ g divides p over R — card |
| `HypersurfaceRingOn` | R[x]/(g) is a commutative ring on its cosets — card |
| `HypersurfaceProjectionHomomorphism` | the projection is a ring homomorphism from the polynomials over R onto R[x]/(g) — card |
| `HypersurfaceClassEq` | the classes of p and q agree ⇔ g divides p − q over R — card |
| `HypersurfaceConstantHomomorphism` | a ↦ the class of the constant a is a ring homomorphism R → R[x]/(g) — card |
| `HypersurfaceInducedMap` | a ring homomorphism φ from R[x] with φ(g) = 0 induces `induced_map(φ)` from R[x]/(g), taking the class of p to φ(p) — card |
| `SeparableIffDerivativeUnit` | g is separable over R ⇔ the class of its derivative is a unit of R[x]/(g) — card |

### K(a) as a quotient of K[x]

| member | statement |
|---|---|
| `MinimalPolynomialRegular` | the minimal polynomial of an algebraic a is a non-zero-divisor among the polynomials over K — card |
| `SeparableDerivativeUnit` | a separable minimal polynomial's derivative is nonzero at a and a unit of K(a) |
| `AdjoinEvaluationKernel` | the polynomials over K vanishing at a are the ideal of the minimal polynomial — card |
| `AdjoinIsomorphicQuotient` | the map evaluation induces is an isomorphism of K-algebras from K[x]/(minimal polynomial) onto K(a) — card |

### The localization at the powers of f as a quotient of R[x]

| member | statement |
|---|---|
| `FxMinusOneRegular` | f·x − 1 is a polynomial over R and a non-zero-divisor — card |
| `FxMinusOneSeparable` | f·x − 1 is separable — card |
| `FxMinusOneInverts` | modulo f·x − 1 the class of x inverts the constant f — card |
| `FxMinusOneFractions` | modulo f·x − 1 every element times some fⁿ is a constant — card |
| `FxMinusOneKernel` | a constant vanishing modulo f·x − 1 is killed by some fⁿ — card |
| `FxMinusOneIsLocalization` | R[x]/(f·x − 1) with its constants is a localization of R at the powers of f — card |
| `LocalizationIsomorphicQuotient` | the fractions with denominators among the powers of f are isomorphic to R[x]/(f·x − 1) as R-algebras, a / 1 ↦ the constant a, 1 / f ↦ the class of x — card |

## The étale hypersurfaces: the cotangent side

The tower R → R[x] → R[x]/(g), with coefficients in a module N over T = R[x]/(g), has the long exact sequence of algebra/cotangent/transitivity, and both outer columns are known. R[x] over R has its homology in degree 0 alone: D_0(R[x]/R, N) is N on the differential dx, and there the differential of a polynomial p is dx with coefficient p′, read through the one-variable bridge of algebra/ring/polynomial/free_algebra and its derivative. T is the Koszul chapter's quotient of the ring R[x] by g, so when g is no zero divisor its homology over R[x] is N in degree 1 alone, on the conormal class of g. The sequence keeps five terms, 0 → D_1(T/R, N) → D_1(T/R[x], N) → D_0(R[x]/R, N) → D_0(T/R, N) → 0, and D_n(T/R, N) vanishes above degree 1.

The connecting map of every tower R → S → T sends the conormal class of an element x of S that T kills to its differential dx. A lift of the class to the middle total has a vertical boundary with no second-tag part, and what is left is dx less d0, whose second term is a boundary; no sign enters. At the hypersurface the connecting map sends the conormal class of g to dx with coefficient g′. When the class of g′ is a unit of T, which is when g is separable, both ends are N and the map is multiplication by a unit, an isomorphism. Then every D_n(T/R, N) vanishes: T is étale over R.

K(a) over K, for a separable algebraic, is K[x] modulo the minimal polynomial of a, and the localization of R at the powers of f is R[x] modulo f·x − 1. Each carries the vanishing across its isomorphism with the quotient, its coefficients restricted along the isomorphism (algebra/cotangent/cotangent_complex). Their statements fix the host from A alone: the subsets of prod(num, prod(A, A)). The proofs read R[x] on num → A and R[x]/(g) on set(num → A) beside the two rings named, the second a type the host need not fit; their carriers have room wherever the base ring's does, which the host is chosen for (algebra/cotangent/simplicial_ring).

| member | statement |
|---|---|
| `HypersurfaceKoszulQuotient` | `hypersurface_ring(R, g) = koszul_quotient(R[x], g)`, with the same projection — card |
| `CorpusPolynomialCotangent` | `D_0(R[x]/R, N) ≅ N` by `m ↦ [dx ⊗ m]`, and `D_n(R[x]/R, N) = 0` for `n ≥ 1`, the coefficients over any ring R[x] maps to — card |
| `CorpusPolynomialDifferential` | `[dp ⊗ m] = [dx ⊗ p′·m]` in `D_0(R[x]/R, N)` — card |
| `TransitivityConnectingConormal` | over any tower, the connecting map `D_1(T/S, N) → D_0(S/R, N)` sends the conormal class of x with coefficient m to `[dx ⊗ m]` — card |
| `HypersurfaceTriangle` | g no zero divisor ⇒ `0 → D_1(T/R, N) → D_1(T/R[x], N) → D_0(R[x]/R, N) → D_0(T/R, N) → 0` is exact and `D_n(T/R, N) = 0` for `n ≥ 2` — card |
| `HypersurfaceConnectingMap` | the connecting map sends the conormal class of g with coefficient m to `[dx ⊗ g′·m]` — card |
| `UnitMultipleIsomorphism` | g no zero divisor and g′ a unit modulo g ⇒ the connecting map `D_1(T/R[x], N) → D_0(R[x]/R, N)` is an isomorphism — card |
| `EtaleHypersurfaceVanishes` | g no zero divisor and separable ⇒ `D_n(R[x]/(g) / R, N) = 0` for every n — card |
| `SimpleSeparableExtensionCotangentVanishes` | a separable algebraic over K ⇒ `D_n(K(a)/K, N) = 0` for every n — card |
| `LocalizationCotangentVanishes` | `D_n(R_f/R, N) = 0` for every n — card |

## Plane curves: R[x, y]/(F)

The tower R → R[x, y] → A = R[x, y]/(F) computes the plane curve's
cotangent complex in two pieces: R[x, y] contributes the free module on
dx and dy, A over R[x, y] the free module on the conormal class of F,
and the connecting map sends that class to dF = F_x dx + F_y dy. So
$L_{A/R}$ is the two-term complex [A → A²], 1 ↦ (F_x, F_y); dualized, D⁰
is the kernel and D¹ the cokernel of (n_x, n_y) ↦ F_x n_x + F_y n_y, and
nothing is left above degree one.

| member | statement |
|---|---|
| `PlaneCurveCotangentComplex` | F in R[x, y] not a zero divisor ⇒ the cotangent complex of A = R[x, y]/(F) over R is quasi-isomorphic to the two-term complex [A → A²], 1 ↦ (F_x, F_y) — card |
| `PlaneCurveCohomologyLowDegrees` | the same, x ≠ y ⇒ D¹(A/R, N) ≅ N/(F_x·N + F_y·N), and D⁰(A/R, N) ≅ the pairs (n_x, n_y) with F_x·n_x + F_y·n_y = 0, the derivations — card |
| `PlaneCurveCohomologyVanishes` | the same ⇒ Dⁿ(A/R, N) = 0 for every n ≥ 2 and every module N over A — card |

## The cohomology of a localization

| member | statement |
|---|---|
| `LocalizationCohomologyVanishes` | `S'` a localization of `S` at the powers of `t` ⇒ `D^n(S'/S, N) = 0` for every n — card |
| `LocalizationRightMapIsomorphism` | the same, over `R` ⇒ the right map `D^n(S'/R, N) → D^n(S/R, N)` is an isomorphism for every n — card |
| `CotangentCohomologyRestrictionHom` | `ν` linear over `S` ⇒ the restriction `D^n(S/R, N) → D^n(S'/R, N')` is linear over `S`, and the right map takes it back to composition with `ν` — card |
| `RestrictionCompatibleTorsor` | over `R → R₀ → T`, `T'` a localization of `T`: `res_R ∘ i* = i*' ∘ res_{R₀}` on `D^1(T/R₀, M)`, and `res_R(ζ + i*(η)) = res_R(ζ) + i*'(res_{R₀}(η))` — card |
