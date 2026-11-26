# euclidean — ℝⁿ: the norm, the distance, and the orthogonal decomposition

The generic chapters read at the real ring. The family binds the ring's
components once — `WithInstance(comm_ring.CommRing, real_ring.CommRing)` reads
`add ↦ real_add`, `zero ↦ &0`, … off the instance theorem — so a statement here
spells `u + v`, `c • u`, `⟪u, v⟫_n` and means `vec_add(real_add, u, v)`,
`vec_scalar_mul(real_mul, c, u)`, `dot⟨n⟩(real_add, real_mul, u, v)`; a sum of vectors
is `Σ_{i∈s} F(i)`, the fold at `vec_add`, and a sum of reals is `Σ_{i<n} f(i)`,
the Σ chapter's `real_sum`. What ℝ adds is its order, and with it the square root.
`‖u‖_n` — the norm `vec_norm⟨n⟩(u)`, whose notation the definition declares — is
the root of `⟪u, u⟫_n`, and `vec_dist⟨n⟩(u, v)` is the norm of the difference.

On the Go side a member's vectors are `*Vec[Real, DimN]` parameters WHERE AN
OPERATION READS THEM AT THE DIMENSION — the dimension rides the type,
anchored to the binder `n` — and a cite writes it off the vector: `NormPow2.At(u)`, `CauchySchwarz.At(u, v)`; `LinearBasisEstimate`
pairs its argument with its membership once (`proof.Inhabit`) and
`vec_space.BasisExpansion.Read(real_ring.CommRing).At(xM)` carries the evidence
(constitution §"The typed surface", the dimension refinement). Where a
statement mentions a sequence without ever reading it at the dimension —
the `x` of the decomposition, which appears only in `x = y + z` — the plain
`*Expr[Fun[Nat, Real]]` is the honest spelling, since a `Vec` would assert
an anchoring the statement does not make. A generic law
of the module or the form is READ at ℝ where it is cited —
`dot.AddLeft.Read(real_ring.CommRing)` is the law with the ring's components
pinned and its hypothesis discharged, one value for a `By` premise, a `Simp`
rule and the typed cite (constitution §Structures, "Readings"); the chapter
states no member whose whole body is such a reading. A `Normalized` in a premise list is shaping with no mathematical content (constitution §"Citation forms"), declared only where a premise-complete close still fails on goal form.

What this chapter needs of ℝ it needs in two instalments. First its ORDER,
and the square root the order buys: positivity of the form, the norm's vanishing exactly at the zero
vector, Cauchy–Schwarz and the triangle inequality are theorems about ℝ,
and they are stated at ℝ. A carrier without an order (ℂ as a ℂ-module) has no
chapter of this shape; ℂ's own norm is this chapter read at ℝ² through the
identification of a complex vector with a real one.

And then its FIELD. Splitting a vector against a direction divides by that
direction's own square, so the decomposition below needs an inverse where
the inequalities needed only a root. The inverse is TOTAL — `real_inv(&0)`
is `&0` — and that is what lets the projection be written without asking
first whether the direction vanishes, which in turn is what keeps the
induction free of a case split.

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `vec_norm⟨n⟩(u)`, written `‖u‖_n` | `real_sqrt(dot⟨n⟩(u, u))` |
| `vec_dist⟨n⟩(u, v)` | `‖vec_sub(u, v)‖_n` |
| `vec_op_norm⟨n, m⟩(L)` | `sup({‖L(u)‖_m \| u \| vec⟨n⟩(u) ∧ ‖u‖_n ≤ &1})` — the operator norm; for a linear L the set holds ‖L(vec_zero)‖ and is bounded (`LinearBasisEstimate`), so the value is the least nonnegative factor by which L stretches the n-vectors (`OpNormLessEqIff`) |

## The form at ℝ (dot.go)

| member | statement |
|---|---|
| `DotIsSum` | `⟪u, v⟫_n = Σ_{i<n} u(i) * v(i)` — the bridge from the fold to the Σ chapter's sum |
| `DotPosLe` | `&0 ≤ ⟪u, u⟫_n` — every summand is a square |
| `NullVectorOrthogonal` | `⟪u, u⟫_n = &0 ⇒ ⟪u, v⟫_n = &0` — a vanishing sum of squares has every entry zero on the range |
| `DotEqZero` | `vec⟨n⟩(u) ⇒ (⟪u, u⟫_n = &0 ⇔ u = vec_zero)` — on a dimension the form is definite: `dot.Definite` read at ℝ, whose one hypothesis — a null vector is orthogonal to everything — is `NullVectorOrthogonal` |

## The norm (norm.go)

| member | statement |
|---|---|
| `NormPow2` | `real_pow(‖u‖_n, 2) = ⟪u, u⟫_n` — the root of the form squares back to it (`real_sqrt.SqrtPowTwo`), the form being nonnegative (`DotPosLe`) |
| `NormNonneg` | `&0 ≤ ‖u‖_n` — the root of a nonnegative real is nonnegative (`real_sqrt.SqrtNonneg`) |
| `NormVecZero` | `‖vec_zero‖_n = &0` — the form at the zero vector vanishes (`dot.ZeroLeft`) and the root of zero is zero (`real_sqrt.SqrtZero`) |
| `NormBasisVector` | `j < n ⇒ ‖basis_vector(j)‖_n = &1` — a basis vector inside the range is a unit vector: the form pairs it with itself to its coordinate at j (`dot.BasisVectorLeft`), which is 1, and 1 is its own root (`real_sqrt.SqrtUnique`) |
| `NormSmul` | `‖c • u‖_n = real_abs(c) * ‖u‖_n` — scaling scales the norm by the size of the scalar: the form at the scaled vector is `c * (c * ⟪u, u⟫_n)`, and `\|c\|·‖u‖` is nonnegative and squares to that, so it is the root (`real_sqrt.SqrtUnique`); no case on the sign of c |
| `NormNormalize` | `‖u‖_n ≠ &0 ⇒ ‖real_inv(‖u‖_n) • u‖_n = &1` — a vector of nonzero norm, scaled by the inverse of its norm, has norm 1: `NormSmul` at 1/‖u‖, whose size is itself, the norm being nonnegative (`NormNonneg`) |
| `ComponentLeNorm` | `i < n ⇒ real_abs(u(i)) ≤ ‖u‖_n` — a coordinate in the active range is no larger in size than the norm: one square is at most the sum of the squares (`real_sum.TermBound` with the bound taken to be the sum itself), and a size whose square is under the form is under its root (`real_sqrt.SqrtLowerBound`) |
| `CoordinateNormBound` | `(∀i. i < n ⇒ real_abs(u(i)) ≤ b) ⇒ ‖u‖_n ≤ &n * b` — a vector whose coordinates below n are at most b in size has norm at most n·b: the squared norm is the sum of the n squares (`DotIsSum`), each at most b² (`real_sum.Bound`), and n·b² is at most (n·b)² |
| `CauchySchwarz` | `⟪u, v⟫_n ≤ ‖u‖_n * ‖v‖_n` — the form is nonnegative at `‖v‖_n • u - ‖u‖_n • v`, which bilinearity expands to `2(‖u‖‖v‖)² − 2‖u‖‖v‖⟪u, v⟫`; through `NormPow2`, `NormNonneg` and `NullVectorOrthogonal` |

## The triangle inequality, along a fold, and the convex ball (triangle.go)

| member | statement |
|---|---|
| `NormTriangle` | `‖u + v‖_n ≤ ‖u‖_n + ‖v‖_n` — square both sides, expand the left square by bilinearity, bound the cross term by Cauchy–Schwarz, carry the bound back through the root; through `CauchySchwarz`, `NormPow2`, `NormNonneg` |
| `NormIterateLe` | `finite(s) ⇒ ‖Σ_{i∈s} F(i)‖_n ≤ Σ_{i∈s} ‖F(i)‖_n` — the two-term inequality carried along a sum: one induction over the index set, the vectors' fold and ℝ's stepping together, `NormTriangle` at each new term |
| `SegmentInBall` | `‖u − c‖_n < r ∧ ‖w − c‖_n < r ∧ &0 ≤ t ∧ t ≤ &1 ⇒ ‖u + t • (w − u) − c‖_n < r` — an open ball is convex: the offset from the centre is the weighted average (1 − t)•(u − c) + t•(w − c) |

## The distance, and the n-vectors as a metric space (dist.go)

The distance is the norm of the difference. Statements write it
`dist⟨n⟩(u, v)`, the overloaded word `vec_dist` declares, and the instance
passes it as the function `vec_dist⟨n⟩` of two vectors. Three facts make it a
distance on the n-vectors — the axioms of `topology/metric_space`, read
on the carrier `{u | vec⟨n⟩(u)}`. It vanishes exactly between equal
vectors, and that holds only on a dimension: the form looks at the
entries below n alone, so two sequences agreeing there are at distance
zero. It is the norm's definiteness read at the difference. It reads the
same both ways, the form of the difference with itself not seeing the
order of the two vectors. And it obeys the triangle inequality, which
is the norm's, read at the two steps u − v and v − w whose sum is u − w.

| member | statement |
|---|---|
| `NormEqZero` | `vec⟨n⟩(u) ⇒ (‖u‖_n = &0 ⇔ u = vec_zero)` — a norm of zero squares to a form of zero, the root of a zero form is zero, and on a dimension the form vanishes exactly at the zero vector (`DotEqZero`) |
| `DistEqZero` | `vec⟨n⟩(u) ∧ vec⟨n⟩(v) ⇒ (dist⟨n⟩(u, v) = &0 ⇔ u = v)` — `NormEqZero` at the difference, itself an n-vector (`vec_space.VecSub`) |
| `NormSubRefl` | `‖u - u‖_n = &0` — on a dimension or not: `u - u` is the zero vector (`vec_space.SubEqZero`), of norm zero (`NormVecZero`) |
| `LineThroughPoint` | `vec⟨n⟩(c) ∧ vec⟨n⟩(u) ⇒ c + &0 • u = c ∧ (∀t. vec⟨n⟩(c + t • u) ∧ c + t • u - c = t • u ∧ ‖c + t • u - c‖_n = \|t\| * ‖u‖_n)` — the line through c in the direction u starts at c, and its point at t is an n-vector t•u from c, at distance \|t\|‖u‖ (`NormSmul`) |
| `DistSym` | `dist⟨n⟩(u, v) = dist⟨n⟩(v, u)` |
| `DistTriangle` | `dist⟨n⟩(u, w) ≤ dist⟨n⟩(u, v) + dist⟨n⟩(v, w)` — `NormTriangle` at the two steps |
| `EuclideanMetric` | `metric_space({u \| vec⟨n⟩(u)}, vec_dist⟨n⟩)` — the instance, one case per axiom |

## Orthogonality and the decomposition (orthogonal.go)

Fix a family and look at the span of its first k members. Every sequence is
the sum of a vector lying in that span and a vector the form sends to `&0`
against everything in it — and the statement speaks of the SPAN, not of the
family, because orthogonality to k directions already settles orthogonality
to everything they combine into — which is `dot.OrthogonalToSpan`, stated
over the ring, since that crossing needs neither the order nor the field.

The two halves of the decomposition part company over hypotheses, and that is
the section's one idea. Existence carries NONE: the part in the span is built
by induction on k out of linearity alone, and the coefficient it corrects by
is written with a total inverse, so no direction is ever tested for vanishing
and no case splits on one. Uniqueness carries ONE and cannot do without it —
the subspace must lie inside the n-vectors. The form only ever looks below n,
so two splittings differing past n pair identically against everything, and
without the confinement the claim is simply false.

The induction is where the construction lives, and it reads its own
hypothesis TWICE: once at the sequence being split, and once at the family's
next member, whose remainder against the earlier ones is the direction the
step corrects along. That is why no orthogonal basis is constructed and no
Gram–Schmidt constant is minted — the correction is a formula, applied to
whatever the hypothesis just produced.

The chapter proves that a splitting exists and that a splitting is unique; the
theorem a reader actually reaches for is that both hold at once, of the span of
a family. That is the closing statement, and it is where the asymmetry becomes
visible in one place: it carries a hypothesis its existence half does not.

| member | statement |
|---|---|
| `ResidualOrthogonal` | `⟪x - ⟪x, g⟫_n * real_inv(⟪g, g⟫_n) • g, g⟫_n = &0` — subtracting from x its component along g leaves a vector orthogonal to g, with NO hypothesis on g. Where `⟪g, g⟫_n` is invertible the coefficient cancels it; where it vanishes x was orthogonal to g already, and the value `real_inv(&0)` takes never enters |
| `ProjectionExists` | `∃y. y ∈ vec_span(k, e) ∧ (∀i. i < k ⇒ ⟪x - y, e(i)⟫_n = &0)` — the construction, by induction on k with the hypothesis read twice. Nothing is asked of the family, of x, or of n |
| `OrthogonalDecomposition` | `∃y z. y ∈ vec_span(k, e) ∧ (∀w. w ∈ vec_span(k, e) ⇒ ⟪z, w⟫_n = &0) ∧ x = y + z` — the theorem, in the form a reader wants: it speaks of the subspace, not of the family presenting it |
| `DecompositionUnique` | at ANY `vec_subspace` confined to the n-vectors, the two parts are determined. Everything turns on the difference of the two candidate subspace parts: it lies in the subspace, so both orthogonal parts pair to zero against it, hence it pairs to zero against itself and definiteness makes it the zero vector |
| `SpanDecomposition` | existence and uniqueness in ONE statement, at the span of a family of n-vectors. `OrthogonalDecomposition` supplies the pair with no hypothesis at all; `DecompositionUnique` compares any second pair with it, read at the span — which needs only that a span is a subspace (`vec_space.SpanSubspace`) and that a span of n-vectors is made of n-vectors (`vec_space.SpanVec`), the one place the hypothesis on the family is spent |

## The bound (bounded.go)

A linear map on a finite-dimensional space is bounded, and the bound is
explicit. Write eᵢ for the basis vectors; a vector x of dimension m is its own
basis expansion, f carries that expansion through to the fold of the images
x(i)·f(eᵢ), the norm of a fold is at most the sum of the norms, each term prices
as |x(i)|·‖f(eᵢ)‖, and |x(i)| ≤ ‖x‖ on the range — so Σᵢ ‖f(eᵢ)‖ bounds f, at
every x of that dimension at once. A consumer asking only for "some bound"
cites this estimate: the existential form is the estimate with its bound
quantified away, and one cite of it closes it.

A map of two arguments, linear in each separately, needs no estimate of its own.
Fixing the first argument at x leaves a linear map, so ‖h(x, y)‖ is within
(Σⱼ ‖h(x, eⱼ)‖)·‖y‖; fixing the second at eⱼ leaves a linear map again, so each
‖h(x, eⱼ)‖ is within (Σᵢ ‖h(eᵢ, eⱼ)‖)·‖x‖. Summing the second estimate over j
and taking ‖x‖ back out of the sum bounds the first estimate's sum, and ‖y‖ is
nonnegative, so it carries that bound through the product. The bound is then the
total size of the images of the basis PAIRS, and it holds at every pair of
arguments of the two dimensions at once.

That second step is why the bound above is stated as a formula rather than as an
existence claim. Summing over j needs a term to put under the Σ, and a bound that
exists only behind an ∃ supplies none — it would have to be chosen for each j and
the choices assembled into a sequence before the sum could even be written. An
explicit bound applies twice; an existential one does not apply at all.

| member | statement |
|---|---|
| `LinearBasisEstimate` | `vec_linear(f) ∧ vec⟨m⟩(x) ⇒ ‖f(x)‖_n ≤ (Σ_{i<m} ‖f(basis_vector(i))‖_n) * ‖x‖_m` — the bound depends on f and the dimension alone, and the claim is made only for x in the m-dimensional subspace, since an unrestricted sequence has infinitely many components. Five members carry the steps: `vec_space.BasisExpansion` and `vec_space.LinearIterate` (read at ℝ where they are cited) turn the argument into a fold of images before the calculation starts, and `NormIterateLe`, `ComponentLeNorm` and `NormSmul` (the norm's own) are what its three legs stand on |
| `BilinearBasisBound` | `vec_bilinear(h) ⇒ vec⟨m⟩(x) ⇒ vec⟨n⟩(y) ⇒ ‖h(x, y)‖_k ≤ (Σ_{j<n} Σ_{i<m} ‖h(basis_vector(i), basis_vector(j))‖_k) * ‖x‖_m * ‖y‖_n` — two applications of `LinearBasisEstimate`, one at h with its first argument fixed and one at h with its second fixed at a basis vector, joined by a sum estimate over the second dimension (`real_sum.Monotone`, `real_sum.ScalarRight`) and carried through the product by `NormNonneg` |

## The operator norm (opnorm.go)

A supremum speaks only of a nonempty set bounded above. For a linear L
the zero vector lies in the unit ball and the basis estimate bounds the
images of the ball, so every law is stated for a linear L, and
`OpNormUnitBall` is the one place that boundedness is spent. A vector h
scaled by 1/‖h‖ lies in the unit ball, which gives the stretch bound; the
operator norm is the least nonnegative factor bounding every stretch,
and the basis total is one such factor.

| member | statement |
|---|---|
| `OpNormUnitBall` | `vec_linear(L) ∧ vec⟨n⟩(u) ∧ ‖u‖_n ≤ &1 ⇒ ‖L(u)‖_m ≤ vec_op_norm⟨n, m⟩(L)` — the images of the unit ball are bounded by the basis total, so their supremum bounds each (`real_sup_inf.MemberLessEqSup`) |
| `OpNormBound` | `vec_linear(L) ∧ vec⟨n⟩(h) ⇒ ‖L(h)‖_m ≤ vec_op_norm⟨n, m⟩(L) * ‖h‖_n` — h scaled by 1/‖h‖ lies in the unit ball; at norm 0 the basis estimate gives 0 |
| `OpNormNonneg` | `vec_linear(L) ⇒ &0 ≤ vec_op_norm⟨n, m⟩(L)` — at the zero vector |
| `OpNormLessEqIff` | `vec_linear(L) ∧ &0 ≤ B ⇒ (vec_op_norm⟨n, m⟩(L) ≤ B ⇔ ∀h. vec⟨n⟩(h) ⇒ ‖L(h)‖_m ≤ B * ‖h‖_n)` — the least nonnegative such factor; the sign of B is needed only in dimension 0 (`real_sup_inf.SupLessEqBound`) |
| `LinearBasisBound` | `vec_linear(f) ⇒ vec_op_norm⟨m, n⟩(f) ≤ Σ_{i<m} ‖f(basis_vector(i))‖_n` — the basis total bounds every stretch (`LinearBasisEstimate`), and the operator norm is the least such factor |
| `OpNormTriangle` | `vec_linear(L) ∧ vec_linear(K) ⇒ vec_op_norm⟨n, m⟩(λv. L(v) + K(v)) ≤ vec_op_norm⟨n, m⟩(L) + vec_op_norm⟨n, m⟩(K)` — `NormTriangle` and `OpNormBound` at each vector |
| `OpNormSmul` | `vec_linear(L) ⇒ vec_op_norm⟨n, m⟩(λv. c • L(v)) = \|c\| * vec_op_norm⟨n, m⟩(L)` — `NormSmul` each way, through 1/\|c\| for c ≠ 0 |
