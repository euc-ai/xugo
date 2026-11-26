# de_rham_betti — Betti numbers and the de Rham Euler characteristic

The chapter counts. `de_rham_betti` is the dimension of a cohomology
module of [de_rham](../de_rham/README.md), and `de_rham_euler` is the
alternating sum of the Betti numbers, a real number. The first section
has their values and the readings of χ through a homogeneous basis and
through traces. The second has invariance under cohomology
isomorphisms, diffeomorphisms and homotopy equivalences,
inclusion–exclusion over a two-open cover
([de_rham_cover](../de_rham_cover/README.md)), and multiplicativity on
compact products ([de_rham_kunneth](../de_rham_kunneth/README.md)).

## Betti numbers and the Euler characteristic

`de_rham_betti⟨n⟩(T,𝒜,k)` is the natural dimension of the degree-k
cohomology module. A finite basis computes it by its cardinality.
The underlying `module_dim` is a choice operator: on a module with no
finite basis it is one fixed unknown number, the same for every such
module. An equation of Betti numbers therefore says something about
dimension only beside a finiteness hypothesis, and the dimension
comparisons carry one. Compact smooth manifolds supply
finite-dimensional cohomology in every degree without an orientation.

The ordinary de Rham Euler characteristic is

$$
\chi(T,\mathcal{A})=\sum_{q=0}^n(-1)^q b_q(T,\mathcal{A}).
$$

`de_rham_euler⟨n⟩(T,𝒜)` takes values in the reals, with the Betti
numbers coerced to real before summing, so it can be compared directly
with a form integral. Its interpretation as an Euler characteristic
requires finite-dimensional cohomology. Above n the cohomology module
is zero, so any larger finite summation bound gives the same result.

χ is the alternating sum of the identity traces on the cohomology
modules: the trace and the coerced dimension both sum one over a
finite basis.
No nondegenerate pairing or Poincaré duality enters this formula.

The empty manifold has χ=0 in every dimension. A nonempty convex
Euclidean open has χ=1, including dimension zero; this is ordinary
cohomology, not compact-support cohomology. A compact zero-manifold
has a finite discrete carrier, its degree-zero cohomology is the real
function space on that carrier, and χ is its number of points.

| Member | Statement |
|---|---|
| `BettiDef` | degreewise dimension of de Rham cohomology |
| `EulerDef` | real-valued signed Betti sum from degree zero through n |
| `BettiAboveDimension` | cohomology above n is finite-dimensional with Betti number zero — card |
| `BettiBasis` | a finite cohomology basis computes the Betti number — card |
| `BettiIsomorphic` | a cohomology isomorphism transfers finiteness and the Betti number — card |
| `BettiHomogeneousBasis` | the degree fibres of a homogeneous basis count Betti numbers — card |
| `CompactZeroDimensionBetti` | a compact zero-manifold has finite carrier and only degree-zero Betti number, its cardinality — card |
| `EulerFiniteRange` | extending the finite sum beyond the manifold dimension preserves χ — card |
| `EulerEmpty` | all Betti numbers and χ vanish on the empty manifold — card |
| `EulerConvexOpen` | χ is one on a nonempty convex Euclidean open and zero on the empty open — card |
| `EulerZeroDimension` | χ counts the points of a compact zero-manifold — card |
| `EulerIdentityTrace` | χ is the alternating sum of identity traces on finite cohomology — card |

## Invariance, covers and products of Euler characteristics

Isomorphisms in every cohomological degree preserve χ when cohomology
is finite-dimensional. The manifold dimensions may differ: extend both
sums to a common bound and use high-degree vanishing. A diffeomorphism
supplies such isomorphisms by pullback. More generally, maps whose two
composites are smoothly homotopic to the respective identities do so;
a one-sided retraction only gives a direct summand and does not identify
Euler characteristics. The homotopies use an open time neighbourhood
of the unit interval.

A two-open cover with its short-exact cover complex supplied satisfies

$$
\chi(M)+\chi(U\cap V)=\chi(U)+\chi(V).
$$

when U, V and U∩V have finite-dimensional cohomology. Exactness then
also gives finite-dimensional cohomology of M. Rank-nullity along the
long exact sequence cancels internal image dimensions; the injective
degree-zero start and the vanishing tail remove the end terms.
For a disjoint open cover, the smooth indicator functions of its clopen
pieces supply the partition themselves and the intersection has zero
cohomology, giving ordinary additivity. These statements do not assume
a general partition theorem for noncompact manifolds.

For two compact smooth manifolds, finite-basis Künneth gives

$$
b_k(M\times N)=\sum_{p=0}^k b_p(M)b_{k-p}(N),
\qquad
\chi(M\times N)=\chi(M)\chi(N).
$$

The degree guard p≤k prevents truncated subtraction from inventing
negative-degree terms. The coefficient-module basis places a basis
vector in one active coordinate and zero in the others. Counting that
basis gives the convolution; high-degree vanishing and the factorization
of the sign give multiplicativity. Empty, disconnected and nonorientable
compact factors are included. No product orientation is needed.

| Member | Statement |
|---|---|
| `EulerCohomologyIsomorphic` | degreewise cohomology isomorphisms transfer finiteness and preserve χ — card |
| `EulerDiffeomorphism` | smooth diffeomorphisms preserve χ for finite cohomology — card |
| `EulerHomotopyEquivalence` | a smooth homotopy equivalence preserves χ for finite cohomology — card |
| `EulerMayerVietoris` | a short-exact cover complex with finite local cohomology gives global finiteness and inclusion–exclusion — card |
| `EulerDisjointOpenUnion` | χ adds across a disjoint open cover with finite cohomology — card |
| `CompactProductBetti` | Betti numbers of compact products satisfy the degree convolution — card |
| `EulerCompactProduct` | Euler characteristics multiply on compact products — card |
