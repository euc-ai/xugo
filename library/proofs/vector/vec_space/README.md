# vec_space — vectors over a commutative ring, as sequences

A vector is a sequence `num → A`; the vector operations read a scalar
operation pointwise. `u + v` is the sequence `i ↦ u(i) + v(i)`, `c • u`
is `i ↦ c * u(i)`, `-u` is `i ↦ -u(i)`, `u - v` is `i ↦ u(i) - v(i)`, and
`vec_zero` is the constant sequence at `zero`. Each operation reads the scalar operation as its first argument —
the definition spells it, `vec_add(add, u, v)` — and a law stated under
a ring record, `∀R:comm_ring(A).`, leaves it implicit: there `vec_add(u, v)`
IS `vec_add(R.add, u, v)`, `vec_zero` is `vec_zero(R.zero)`, and a bare `vec_add` is `vec_add(R.add)`,
the record being in scope and the parser completing the application from
its fields by name (constitution §Structures, "Implicit component
arguments"). The operations declare their notations at their
definitions, and the text writes them: `u + v` at a vector type is
`vec_add(R.add, u, v)`, `c • u` is `vec_scalar_mul(R.mul, c, u)`, and a
vector `+` beside the ring's own `+` in one statement are two
operators, each resolved by its operands' type — the record's fields
carry their symbols (`c + d` is `R.add(c, d)`), the vectors' constants
declare theirs. A sum of vectors is `Σ_{i∈s} F(i)` — the fold
`iterated_op(vec_add, s, λi. F(i))`, no vector sum being minted (the fold
section says why) — a sum of scalars under the ring is the fold at `add`
written the same way, and `Σ_{i<m}` runs over the half-open range
`{i | i < m}`. So the chapter states its laws once, and every carrier — ℝ, ℂ,
ℤ — applies them by citing its own ring instance, or reads them at it as one
value (`vec_space.BasisExpansion.Read(real_ring.CommRing)`); a chapter working at
an instance binds the record and its fields once at its family, as the
domain's ℝ chapters do.

The dimension is a term, and it lives in one predicate: `vec⟨n⟩(u)`
says the sequence is `zero` from index `n` on, so its ACTIVE range is
`0 .. n-1`. The padding element is the ring's own zero, not an arbitrary
junk value, and that is the chapter's one design decision: zero plus zero
is zero and a scalar times zero is zero, so the sum, the negation and the
scaling of n-vectors are n-vectors by the ring's laws alone, with no
truncation step in any operation and no membership hypothesis in any
algebraic identity. That `vec⟨n⟩(·)` is a subspace of the sequences is a
theorem of the chapter rather than a manner of speaking (`VecSubspace`), so
everything said below of a subspace in general is said of the vectors of a
dimension; and the subspaces are nested — an n-vector is an (n+1)-vector.

Two consequences shape the statements. The pointwise identities are
unconditional: commutativity, associativity, the identity and inverse laws,
the distributive laws of the scalar action hold for ALL sequences, because
they hold at every index. And where a statement does name a dimension, it is
because the mathematics reads the active range — extensionality says two
n-vectors are equal exactly when their active entries agree, since past the
range neither has anything of its own to say.

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `vec_zero` | the zero vector |
| `vec_add(u, v)`, written `u + v` | pointwise sum |
| `vec_neg(u)`, written `-u` | pointwise negation |
| `vec_sub(u, v)`, written `u - v` | pointwise difference |
| `vec_scalar_mul(c, u)`, written `c • u` | the scalar action |
| `vec⟨n⟩(u)` | u is zero from index n on — an n-vector |
| `basis_vector(k)` | the k-th standard basis vector: `one` at index k, `zero` elsewhere |
| `vec_linear(f)` | f is a module homomorphism: it carries the pointwise sum to the pointwise sum and commutes with the scalar action |
| `vec_bilinear(h)` | h is linear in each argument separately: fixing either one leaves a module homomorphism |
| `vec_subspace(s)` | s holds the zero vector and is closed under the pointwise sum and the scalar action |
| `vec_span(k, e)` | the span of the first k members of the family e: the sequences `Σ_{i<k} c(i) • e(i)`, the coefficient sequence ranging over everything |

## The pointwise laws (laws.go)

Each is a ring law read at every index: the proof opens the two sides
pointwise, unfolds the operation, and closes by the scalar law at the
entry. Stated under `∀R:comm_ring(A).`; the additive laws
need only the ring's additive group, which the ring chapter projects.
Two members read no entry: `AbelianGroup` and `ModuleOn` assemble the
laws into structure predicates.
The carrier twins (`…On`) state nine of the same laws under
`∀R:comm_ring_on(A).`: a ring on its carrier `R.carrier` gives its laws
there alone, so each asks every entry of its sequences to lie in
`R.carrier`.
The twins carry the proofs: the four additive laws, `SubAddNeg` and the
four scaling laws are each the view of their twin at 𝕌, where every entry
lies. The scaling twins also ask the scalars to lie in `R.carrier`, and at
𝕌 every scalar lies there too.

| member | statement |
|---|---|
| `AddComm` | `u + v = v + u` |
| `AddAssoc` | `u + (v + w) = (u + v) + w` |
| `AddLeftZero` | `vec_zero + u = u` |
| `AddLeftNeg` | `-u + u = vec_zero` |
| `SmulAddLeft` | `c • (u + v) = c • u + c • v` |
| `SmulAddRight` | `(c + d) • u = c • u + d • u` |
| `SmulMul` | `(c * d) • u = c • (d • u)` |
| `SmulOne` | `R.one • u = u` |
| `SmulZero` | `c • vec_zero = vec_zero` |
| `ZeroSmul` | `R.zero • u = vec_zero` |
| `AbelianGroup` | `abelian_group(mk_group(vec_add, vec_zero, vec_neg, 𝕌))` — the four additive laws assembled into the structure predicate, so the abelian group chapter's laws, and through it the group chapter's, apply to vectors at any carrier |
| `ModuleOn` | `module_on(restrict_ring(R, 𝕌), mk_module(vec_add, vec_zero, vec_neg, vec_scalar_mul, {u \| vec⟨n⟩(u)}))` at every n — the n-vectors are a module on the set of them: the membership laws close the set, and the laws above are the axioms |
| `SubAddNeg` | `u - v = u + -v` — `SubAddNegOn` at 𝕌 |
| `NegIsSmul` | `-u = -R.one • u` — the negation is the scalar action at minus one, which is why a set closed under the sum and the scalar action is closed under differences |
| `SubEqZero` | `u - v = vec_zero ⇔ u = v` — two vectors agree exactly when their difference vanishes; read at the vectors' own additive group rather than at an entry |
| `AddSubCancel` | `u + (v - u) = v` — what was subtracted, added back |
| `AddSubCancelRight` | `(u + v) - v = u` — what was added, subtracted again; both are the additive laws above, nothing read entrywise |
| `AddCommOn` | `(∀i. u(i) ∈ R.carrier) ∧ (∀i. v(i) ∈ R.carrier) ⇒ u + v = v + u` — `AddComm` at a ring on a set; `AddComm` is its view at 𝕌 |
| `AddAssocOn` | `(∀i. u(i) ∈ R.carrier) ∧ (∀i. v(i) ∈ R.carrier) ∧ (∀i. w(i) ∈ R.carrier) ⇒ u + (v + w) = (u + v) + w` |
| `AddLeftZeroOn` | `(∀i. u(i) ∈ R.carrier) ⇒ vec_zero + u = u` |
| `AddLeftNegOn` | `(∀i. u(i) ∈ R.carrier) ⇒ -u + u = vec_zero` |
| `SubAddNegOn` | `(∀i. u(i) ∈ R.carrier) ∧ (∀i. v(i) ∈ R.carrier) ⇒ u - v = u + -v` — the ring's subtraction axiom on `R.carrier`, read at every index |
| `SmulAddLeftOn` | `a ∈ R.carrier ∧ (∀i. u(i) ∈ R.carrier) ∧ (∀i. v(i) ∈ R.carrier) ⇒ a • (u + v) = a • u + a • v` |
| `SmulAddRightOn` | `a ∈ R.carrier ∧ b ∈ R.carrier ∧ (∀i. u(i) ∈ R.carrier) ⇒ (a + b) • u = a • u + b • u` |
| `SmulMulOn` | `a ∈ R.carrier ∧ b ∈ R.carrier ∧ (∀i. u(i) ∈ R.carrier) ⇒ (a * b) • u = a • (b • u)` |
| `SmulOneOn` | `(∀i. u(i) ∈ R.carrier) ⇒ R.one • u = u` |

## Membership (membership.go)

What the dimension says. The subspace is closed under the operations, and
two n-vectors are equal exactly when they agree on the active range.

The members stated for ANY `zero`, not under the ring, spell it: an
explicit component is the visible sign that no ring law is spent.

| member | statement |
|---|---|
| `VecZero` | `vec⟨n⟩(zero, vec_zero(zero))` |
| `VecAdd` | `vec⟨n⟩(u) ∧ vec⟨n⟩(v) ⇒ vec⟨n⟩(u + v)` |
| `VecNeg` | `vec⟨n⟩(u) ⇒ vec⟨n⟩(-u)` |
| `VecSub` | `vec⟨n⟩(u) ∧ vec⟨n⟩(v) ⇒ vec⟨n⟩(u - v)` |
| `VecAddOn`, `VecNegOn`, `VecSubOn` | the same three closures at a ring on a set — only the padding is read, so no entry is asked to lie in `R.carrier`; `VecAdd`, `VecNeg` and `VecSub` are their views at 𝕌 |
| `VecSmulOn` | `a ∈ R.carrier ∧ vec⟨n⟩(u) ⇒ vec⟨n⟩(a • u)` — the scaling at a ring on a set; only the scalar is asked to lie in `R.carrier`, and `VecSmul` is its view at 𝕌 |
| `VecSmul` | `vec⟨n⟩(u) ⇒ vec⟨n⟩(c • u)` |
| `VecBasisVector` | `k < m ⇒ vec⟨m⟩(zero, basis_vector(zero, one, k))` — a basis vector below the dimension is a vector of that dimension. Stated for ANY two values, not under the ring: its zero and one enter only as the two values the basis vector takes, so no ring law is spent |
| `VecMono` | `m ≤ n ⇒ vec⟨m⟩(zero, u) ⇒ vec⟨n⟩(zero, u)` — the dimensions are nested |
| `Extensionality` | `vec⟨n⟩(zero, u) ∧ vec⟨n⟩(zero, v) ⇒ (u = v ⇔ ∀i. i < n ⇒ u(i) = v(i))` |
| `VecDimZero` | `vec⟨0⟩(zero, u) ⇒ u = vec_zero(zero)` — a 0-vector is the zero sequence |

## The subspace and the span (subspace.go)

A subspace of the sequences holds the zero vector and is closed under the
pointwise sum and the scalar action — three conditions, and deliberately not
a fourth: closure under differences follows, because the negation is the
scalar action at minus one.

`vec_span(k, e)` is the span of a family's first k members: the values
`Σ_{i<k} c(i) • e(i)` takes as the coefficient sequence ranges over
everything. Nothing is asked of the family — no dimension, no independence —
so a span is available wherever a family is, and a dimension reaches an
element of one only through the family it is combined from.

A vector enters a span one way, as a combination (`CombinationInSpan`),
and leaves it one way, the definition read at the vector handing over its
coefficients. Every member below that puts a vector in a span or takes
one out goes through those two doors.

The section runs from what a span holds to what it is. A span holds its
family, grows with the bound, and is a subspace; the vectors of a dimension
are a subspace too, and a subspace is closed under differences and under
sums of any length. The scalar action and the sums of any length make the
span the least subspace holding its family. At the vectors of a dimension,
the sums of any length keep a fold of n-vectors in dimension n, and
leastness keeps a span of n-vectors there; at another span, leastness
compares two spans by their families, and from that the span does not
depend on the order of the family. None of these proofs inducts on the
bound.

| member | statement |
|---|---|
| `CombinationInSpan` | `Σ_{i<k} c(i) • e(i) ∈ vec_span(k, e)` — a combination of the family lies in its span: the definition, read the way in |
| `SpanMember` | `j < k ⇒ e(j) ∈ vec_span(k, e)` — a span holds what spans it. The Kronecker coefficients realize the vector, and the delta sum collapses the fold |
| `SpanMono` | `k ≤ m ⇒ x ∈ vec_span(k, e) ⇒ x ∈ vec_span(m, e)` — the spans grow with the bound. The coefficients extend by zero, and the summands this adds are silent, so the fold over the larger range stops where the smaller one does (`monoidal.BelowTruncate`) |
| `SpanSubspace` | `vec_subspace(vec_span(k, e))` — a span is a subspace. Each condition is a coefficient sequence: the constant zero, the pointwise sum of two, one scaled; `monoidal.EqNeutral`, `monoidal.Pointwise` and `SmulIterate` then do the work |
| `VecSubspace` | `vec_subspace({u \| vec⟨n⟩(u)})` — the vectors of a dimension are a subspace: the three closure laws of membership, read through the set-builder |
| `SubspaceSub` | `vec_subspace(s) ⇒ u ∈ s ⇒ v ∈ s ⇒ u - v ∈ s` — the fourth condition the definition does not ask for |
| `SubspaceIterate` | `vec_subspace(s) ⇒ (∀i. i ∈ t ⇒ F(i) ∈ s) ⇒ Σ_{i∈t} F(i) ∈ s` — a subspace holds every sum of its vectors. `monoidal.Closed` carries membership in s along the fold: the fold starts from the zero vector, which s holds, s is closed under the sum, and every summand lies in s by hypothesis. No finiteness is asked of t, a fold over an infinite support being the zero vector itself |
| `VecIterate` | `(∀i. i ∈ s ⇒ vec⟨m⟩(F(i))) ⇒ vec⟨m⟩(Σ_{i∈s} F(i))` — a fold of m-vectors is an m-vector: `SubspaceIterate` at the m-vectors, which are a subspace (`VecSubspace`) |
| `SpanLeast` | `vec_subspace(s) ⇒ (∀i. i < k ⇒ e(i) ∈ s) ⇒ vec_span(k, e) ⊆ s` — the span lies in every subspace holding the family. Each summand of a combination is a scalar multiple of a family vector the subspace holds, and `SubspaceIterate` puts their sum in it. With `SpanSubspace` and `SpanMember` it makes the span the least subspace holding the family |
| `SpanVec` | `(∀i. i < k ⇒ vec⟨n⟩(e(i))) ⇒ x ∈ vec_span(k, e) ⇒ vec⟨n⟩(x)` — a span of n-vectors is made of n-vectors: `SpanLeast` at the n-vectors. This is what confines a span to a dimension, and so what a uniqueness statement about it needs |
| `SpanSubset` | `(∀i. i < k ⇒ e(i) ∈ vec_span(m, f)) ⇒ vec_span(k, e) ⊆ vec_span(m, f)` — a span lies in any span that holds its family: `SpanLeast` at the other span, which is a subspace (`SpanSubspace`) |
| `SpanPermute` | `(∀i. i < k ⇒ p(i) < k) ⇒ (∀i j. i < k ∧ j < k ∧ p(i) = p(j) ⇒ i = j) ⇒ vec_span(k, λi. e(p(i))) = vec_span(k, e)` — the span does not see the order of the family. Each inclusion is `SpanSubset`; the harder one needs p onto the range, and an injective self-map of the numbers below k is onto them (`num_segment.BelowStrictInjectiveOnto`), which is why the hypothesis asks only for injectivity |
| `SpanSwap` | `t < m ⇒ j < m ⇒ vec_span(m, λi. f(COND(i = t, j, COND(i = j, t, i)))) = vec_span(m, f)` — exchanging two members of the family leaves its span unchanged: the transposition of t and j keeps the range and is one-to-one, so `SpanPermute` applies |

## How the vectors reach the fold (fold.go)

The chapter mints no sum of its own. `iterate/monoidal` is carrier-free — it asks
of an operation only that it commute, associate and have a neutral element — so
a sum of vectors IS `iterated_op(vec_add, s, λi. F(i))`, which the text writes
`Σ_{i∈s} F(i)`, and two facts are the entire translation. Both are the
pointwise laws re-read.

| member | statement |
|---|---|
| `NeutralVecAdd` | `neutral_elem(vec_add) = vec_zero` — the element the fold starts from is the zero vector (an identity is unique) |
| `MonoidalVecAdd` | `monoidal_op(vec_add)` — pointwise addition folds; with it every law of the mechanism holds at vectors |

## The fold in the vector world (fold.go)

How a fold of vectors reads at one index. That is the mechanism speaking across
two carriers: evaluation at an index is a homomorphism from the vectors to the
ring, and `monoidal.Homomorphic` carries the fold across it. The first things the
coordinatewise reading buys are the two halves of the standard basis: a
combination of basis vectors has its coefficients as coordinates, and a vector
is the combination with its own coordinates.

| member | statement |
|---|---|
| `IterateAt` | `finite(s) ⇒ (Σ_{i∈s} F(i))(j) = Σ_{i∈s} F(i, j)` — a fold of vectors is computed coordinatewise, the right side being the ring's own fold at `R.add`. `monoidal.Homomorphic` read at evaluation; its obligations are that evaluation fixes the element the fold starts from and crosses the sum, both `vec_add`'s and `vec_zero`'s definitions at one index. No induction of its own |
| `BasisCombinationAt` | `j < m ⇒ (Σ_{i<m} c(i) • basis_vector(i))(j) = c(j)` — a combination of basis vectors has its coefficients as coordinates. `IterateAt` crosses to the scalar fold, the summand collapses to a Kronecker delta by the ring's unit and zero laws, and `monoidal.Delta` reads it off |
| `BasisExpansion` | `vec⟨m⟩(x) ⇒ x = Σ_{i<m} x(i) • basis_vector(i)` — a vector is the sum of its coordinates scaling the basis vectors. `Extensionality` frames it: both sides are m-vectors (the sum by `VecIterate` over `VecSmul` and `VecBasisVector`), so they need only agree below m, and there the sum reads x's own coordinates (`BasisCombinationAt`). The membership hypothesis is spent once, in the framing |

## Linear maps (linear.go)

A linear map is a module homomorphism, and what the chapter says about one is
what a homomorphism does to the two things the fold is built from: it fixes the
identity, and it commutes with the fold itself. Both use additivity alone.
The scalar action commutes with the fold as well, and that one is the
exception: it is proved by reading the action as a linear map, which asks
the map to commute with EVERY scaling, and so is the one place the ring's
multiplication is used as a commutative one. The operations a derivative's rules perform
on linear maps keep them linear: the zero map, a difference, a sum, a
multiple and a composite; the multiple, like the scaling above, asks
the ring to commute. The law itself is true over
any ring — a scalar passes a finite sum on left distributivity alone — and
commutativity is the price of the route, not of the theorem.

The chapter also defines what it is to be linear in each of two arguments
(`vec_bilinear`) and proves nothing about it. That is deliberate: bilinearity is a
property of a map between modules, so it is stated where the module is, while
everything worth saying about a bilinear map here — that it is bounded on
finite-dimensional subspaces — needs a norm, and so belongs to a chapter with an
ordered field under it. The definition is written through `vec_linear` twice, which
is what lets that chapter apply the linear theory to each slot in turn.

| member | statement |
|---|---|
| `LinearVecZero` | `vec_linear(f) ⇒ f(vec_zero) = vec_zero` — a homomorphism fixes the identity: the zero vector is its own sum, so its image is, and one copy cancels |
| `LinearZeroMap` | `vec_linear(λu. vec_zero)` |
| `LinearSub` | `vec_linear(f) ⇒ f(u - v) = f(u) - f(v)` |
| `LinearAdd` | `vec_linear(f) ∧ vec_linear(g) ⇒ vec_linear(λu. f(u) + g(u))` |
| `LinearScale` | `vec_linear(f) ⇒ vec_linear(λu. a • f(u))` — uses commutativity |
| `LinearCompose` | `vec_linear(f) ∧ vec_linear(g) ⇒ vec_linear(g ∘ f)` |
| `LinearIterate` | `vec_linear(f) ⇒ finite(s) ⇒ f(Σ_{i∈s} F(i)) = Σ_{i∈s} f(F(i))` — a homomorphism carries a sum to the sum of the images. No induction of its own: `monoidal.Related` carries a relation along a fold, and at `R x y ⇔ f(x) = y` its two obligations are additivity and `LinearVecZero`. Homogeneity is never used |
| `SmulIterate` | `finite(s) ⇒ c • Σ_{i∈s} F(i) = Σ_{i∈s} c • F(i)` — a scalar passes through a sum of arbitrarily many vectors. Scaling by a fixed `c` is itself a linear map, so this is `LinearIterate` applied at that map: no induction, no fold law of its own |
