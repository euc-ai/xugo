# algebraic_curve — curves finite over the projective line, held by the coordinate rings of two charts inside their function field

A curve here is its function field L over a subfield k together with the
coordinate rings of two affine charts inside L: A₀, which contains k[t]
for a transcendental t and is free of finite rank over it, and A₁, which
contains k[1/t] and is free of finite rank over it, glued along their
common localization A₀[1/t] = A₁[t]. Nothing is transported and nothing
is glued by an isomorphism: every ring and every invertible pair is a
subset of L, and the structure sheaf is the lattice pair (A₀, A₁). That the only
functions regular on both charts are the constants, A₀ ∩ A₁ = k, is part
of the datum — the curve is complete and connected by hypothesis. The
genus is the dimension of H¹ of the structure pair.

The field is held by a `field_ops(A)` record L. The curve predicate and
dualizing pair take L; ring-valued constructions such as genus, degree
and the dualizing module take `field_ring(L)`.

The datum is symmetric in its charts: read from chart 1, with 1/t in
place of t, it is again a curve (`CurveSwap`), so what holds of one chart
holds of the other. A basis of A₀ over k[t] is a basis of the overlap over
k[t, 1/t] and of L over k(t), so both charts have rank [L : k(t)].

Finiteness of cohomology is read off the projective line. Each chart of
an invertible pair M is a finitely generated torsion-free module over its
polynomial ring, k[t] or k[1/t], a principal ideal domain, so it is free
of finite rank (`InvertibleFreeBasis`); the datum gives the structure
pair its bases outright. In a basis E of fst(M) over k[t] the ambient of
M is the k[t, 1/t]-span of E and snd(M) lies between the chart-1 modules
of the free line pairs O(−N)^E and O(N)^E for one N
(`InvertibleSandwichChart`), so H⁰(M) is a subspace of H⁰(O(N)^E) and H¹(M)
a quotient of H¹(O(−N)^E), both finite-dimensional on the line; H⁰(O)
is k, and χ(O) = 1 − g. A finitely generated k[t]-submodule of L inside
the k(t)-span of another has a common denominator d ∈ k[t] carrying it
into the other, so a chart ring modulo a nonzero principal ideal, and
the quotient of an invertible pair by a smaller one, are quotients of a
quotient by d, which a basis over k[t] counts: finite-dimensional over
k. An invertible pair M also meets O in a lattice pair K that contains a
principal ideal on each chart while M has a common denominator on each
chart, so O/K and M/K have finite chart quotients, which is how the
degree is shown additive. K need not be invertible — the curve may be
singular — and nothing but its chart quotients is asked of it.

The degree of an invertible pair, its divisors and Pic⁰ are
scheme/curve_degree; the dualizing pair, Serre duality and Riemann–Roch
are scheme/serre_duality.

## Members

### The definitions

| Member | Statement |
|---|---|
| `CurveOverLineDef` | `curve_over_line(L, k, t, A₀, A₁, A₀₁)`: two chart rings, finite free over k[t] and k[1/t], glued along A₀₁, with constants as global functions and L the fraction field of A₀ |
| `CurveGenusDef` | `curve_genus(field_ring(L), k, A₀, A₁, A₀₁)`: dim_k H¹ of the structure pair |

### The datum and its two charts

| Member | Statement |
|---|---|
| `CurveOverItsLine` | the datum read over its line: k a subfield of L and a field; t nonzero and transcendental over k, as inv(t) is; the biaffine datum, its clauses read inside L, with A₀₁, A₀ and A₁ subrings of L; k[t] ⊆ A₀, k[1/t] ⊆ A₁, A₀ ∩ A₁ = k, both charts free of finite rank; and the line's own biaffine datum k[t], k[1/t] along k[t, 1/t] inside L, with L a module over k, k[t], k[1/t] and k[t, 1/t] |
| `CurveLatticeData` | the structure pair is an invertible lattice pair over the overlap's ring, gluing to A₀₁, and k is a field inside both charts |
| `FractionFieldBothCharts` | L is the fraction field of A₀, of A₁ and of A₀₁ |
| `CurveSwap` | the datum with 1/t for t and the charts exchanged is a curve |
| `ProjectiveLineCurve` | when L = k(t), the projective line's charts k[t] and k[1/t] are a curve over the line |
| `GenusZeroLine` | the projective line is a curve of genus zero |
| `BasisSpansOverlap` | a basis of A₀ over k[t], or of A₁ over k[1/t], is a basis of A₀₁ over k[t, 1/t] |
| `LaurentRingInOverlap` | the overlap A₀₁ holds the line's overlap k[t, 1/t] |
| `CoordinateSpansOverlap` | a part of chart 0 holding t generates the whole overlap as an ideal |
| `CurvePairOnLine` | a lattice pair of the curve is a lattice pair on the line, over k[t] and k[1/t], with the same ambient and H¹ |

### The function field over k(t)

| Member | Statement |
|---|---|
| `ChartBasisSpansFunctionField` | a finite basis of chart 0 over k[t] spans L over k(t) |
| `FiniteOverRationalFunctions` | L is a finite extension of k(t) = `field_adjoin(L, k, {t})`, a basis of either chart over its polynomial ring being a basis of L, of size [L : k(t)] |
| `ElementAlgebraicOverRationalFunctions` | every element of L is algebraic over k(t) |

### The structure pair's cohomology

| Member | Statement |
|---|---|
| `StructureH0` | H⁰(O) = k, of dimension one over k |
| `StructureH1Finite` | H¹(O) is finite-dimensional over k |
| `StructureFinite` | the structure pair's cohomology is finite-dimensional, as every invertible pair's |
| `StructureEuler` | χ(O) = 1 − g |

### Chart quotients and invertible pairs

| Member | Statement |
|---|---|
| `PrincipalColengthFinite` | each chart ring modulo the principal ideal of any of its nonzero members is finite-dimensional over k |
| `NonzeroIdealFiniteColength` | a chart ring modulo a nonzero ideal is finite-dimensional over k |
| `InvertibleFreeBasis` | each chart of an invertible pair has a finite basis over its polynomial ring, k[t] or k[1/t] |
| `InvertibleSandwich` | in a finite basis E of fst(M) over k[t], the ambient of an invertible pair M is the k[t, 1/t]-span of E and snd(M) lies between the chart-1 modules of O(−N)^E and O(N)^E for one N; the same with the charts exchanged |
| `InvertibleSandwichChart` | the sandwich read from chart 0: in a finite basis E of fst(M) over k[t] the ambient is the k[t, 1/t]-span of E and snd(M) lies between the k[1/t]-spans of inv(t)ᴺ · E and tᴺ · E |
| `InvertibleFinite` | every invertible lattice pair has finite-dimensional cohomology |
| `TwistFinite` | twisting an invertible pair at a regular point keeps its cohomology finite-dimensional — card |
| `InvertibleMeetStructure` | an invertible pair M meets O in a lattice pair whose chart quotients inside O and inside M are finite-dimensional |
| `InvertibleQuotientFinite` | between invertible pairs M ⊆ N the chart quotients are finite-dimensional |

### The multiples of the divisor of poles of t

| Member | Statement |
|---|---|
| `PolePairLattice` | each (A₀, tʲ·A₁) is a lattice pair with ambient A₀₁ |
| `PolePairEuler` | (A₀, tʲ·A₁) has finite cohomology and χ = j·n + 1 − g, n = dim_k A₀/t·A₀ |
| `PolePairH1Vanishes` | H¹(A₀, tʲ·A₁) = 0 from some j on |
| `PolePairSections` | ℓ(A₀, tʲ·A₁) + g = j·n + 1 from some j on |
