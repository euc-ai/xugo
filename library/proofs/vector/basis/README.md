# basis — independence, bases, and the dimension

A family of vectors is a sequence `e : num → num → A`, and a statement
speaks of its first k members — the convention `vec_space`'s span already
keeps, where `vec_span(k, e)` is the set of combinations
`Σ_{i<k} c(i) • e(i)`. Those k members are INDEPENDENT when the only
combination of them that vanishes is the one with every coefficient on the
range zero, and they are a BASIS of a set s when they are independent and
span exactly s. The dimension of s is the length of a basis of it.

That last sentence is a claim, and the chapter is its proof: two bases of
one set have the same length. The claim fails outright only over the
one-element ring, where every family is independent and the zero space has
a basis of every length; over any other commutative ring it holds, by
determinants or by passing to a residue field. The argument written here is
the exchange of one vector for another: exchanging one member at a time
gives the replacement theorem (`Steinitz`) — k independent vectors in the
span of m vectors number at most m — and two bases, each in the other's
span, then bound each other's length. Winning the exchanged member back
divides by its coefficient, so from there on the chapter is stated under
`∀F:field(A).`, a field record (algebra/field/field). What holds over
any commutative ring is stated under `∀R:comm_ring(A).`, with
`R.one ≠ R.zero` as a hypothesis where it is needed.

The dimension is defined by choice, `εk. ∃e. vec_basis(k, e, s)`: some
length at which s has a basis. The definition asks nothing more, because
uniqueness is a theorem; over a field, where s has a basis the choice has
one value it can make, and where it has none the dimension is a number
nothing is said about.

`vec_basis` is the predicate, "these k vectors are a basis of s"; the
standard basis is one family it holds of, `vec_space`'s `basis_vector`,
whose k-th member is one at index k and zero elsewhere.

The components are implicit in the text, as in vec_space and dot: under
a law over the ring or the field `vec_independent(k, e)` is
`vec_independent(R.add, R.zero, R.mul, k, e)`, completed from the
record's fields (constitution §Structures,
"Implicit component arguments").

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `vec_independent(k, e)` | `∀c. Σ_{i<k} c(i) • e(i) = vec_zero ⇒ ∀i. i < k ⇒ c(i) = zero` — only the zero combination vanishes |
| `vec_basis(k, e, s)` | `vec_independent(k, e) ∧ vec_span(k, e) = s` |
| `vec_dim(s)` | `εk. ∃e. vec_basis(k, e, s)` — the length of a basis, chosen |

## What independence forbids, and the standard basis (independence.go)

Stated over any commutative ring; where the argument needs a coefficient
to be nonzero, one being distinct from zero is a hypothesis.

| member | statement |
|---|---|
| `IndependentNotInEarlierSpan` | `R.one ≠ R.zero ⇒ vec_independent(k, e) ⇒ t < k ⇒ e(t) ∉ vec_span(t, e)` — no member of an independent family lies in the span of those before it. Were it one, its coefficients below t, minus one at t and zero past it, would combine the first k members to the zero vector, and independence would make minus one zero |
| `ReplacementPivot` | `R.one ≠ R.zero ⇒ vec_independent(k, e) ⇒ t < k ⇒ t ≤ m ⇒ (∀i. i < t ⇒ g(i) = e(i)) ⇒ e(t) = Σ_{i<m} c(i) • g(i) ⇒ ∃j. t ≤ j ∧ j < m ∧ c(j) ≠ R.zero` — expand a member of an independent family in a family that agrees with it below that member's index, and some coefficient at or past the index is nonzero: were they all zero, the expansion would stop at t and put e(t) in the span of the members before it |
| `StandardBasis` | `vec_basis(n, basis_vector, {u \| vec⟨n⟩(u)})` — the first n standard basis vectors are a basis of the n-vectors: a combination of them has its coefficients as coordinates (`vec_space.BasisCombinationAt`), so only the zero combination vanishes, and every n-vector is the combination with its own coordinates (`vec_space.BasisExpansion`) |

## The exchange, over a field (exchange.go)

| member | statement |
|---|---|
| `SolveForMember` | `vec_subspace(s) ⇒ j < k ⇒ Σ_{i<k} c(i) • e(i) ∈ s ⇒ (∀i. i < k ∧ i ≠ j ⇒ e(i) ∈ s) ⇒ c(j) ≠ F.zero ⇒ e(j) ∈ s` — a linear relation is solved for any member whose coefficient is nonzero: split the j-th summand off, the subspace holds the rest and the combination less the rest, and e(j) is that difference scaled by the inverse of its coefficient |
| `Exchange` | `j < k ⇒ y = Σ_{i<k} c(i) • e(i) ⇒ c(j) ≠ F.zero ⇒ vec_span(k, λi. COND(i = j, y, e(i))) = vec_span(k, e)` — the exchange lemma: each span lies in the other by `vec_space.SpanSubset`, the replaced member being won back from y and the members that stay by `SolveForMember` |
| `ReplacementStep` | `vec_independent(k, e) ⇒ t < k ⇒ t ≤ m ⇒ (∀i. i < t ⇒ g(i) = e(i)) ⇒ e(t) ∈ vec_span(m, g) ⇒ suc(t) ≤ m ∧ ∃h. vec_span(m, h) = vec_span(m, g) ∧ (∀i. i < suc(t) ⇒ h(i) = e(i))` — one step of replacement: `ReplacementPivot` finds a nonzero coefficient at some j with t ≤ j < m, `Exchange` puts e(t) in at j, and `vec_space.SpanSwap` moves it to t, neither changing the span. Stated in the replacement theorem's own terms, so each step of that induction is this lemma read at the family built so far, then one rewrite of that family's span to the original one |
| `Steinitz` | `vec_independent(k, e) ⇒ (∀i. i < k ⇒ e(i) ∈ vec_span(m, f)) ⇒ k ≤ m ∧ ∃g. vec_span(m, g) = vec_span(m, f) ∧ (∀i. i < k ⇒ g(i) = e(i))` — the replacement theorem: k independent vectors in the span of m number at most m, and some m vectors with that span have them as their first k. By induction on how many have been put in, each step `ReplacementStep` read at the family built so far |

## The dimension (dimension.go)

Its centre is the replacement theorem read twice: a basis of s lies in the
span of any other basis of s, both spans being s, so each length bounds the
other. The standard basis ties the dimension to `vec⟨n⟩(·)`.

| member | statement |
|---|---|
| `BasisLengthUnique` | `vec_basis(k, e, s) ⇒ vec_basis(m, f, s) ⇒ k = m` — two bases of one set have the same length: each lies in the other's span, and `Steinitz` read each way round bounds each length by the other |
| `DimBasis` | `vec_basis(k, e, s) ⇒ vec_dim(s) = k` — the dimension is well defined: the choice picks some basis of s, which s has, and `BasisLengthUnique` gives it the length of the one in hand |
| `DimVec` | `vec_dim({u \| vec⟨n⟩(u)}) = n` — the n-vectors have dimension n, the standard basis being a basis of them; the chapter's dimension and vec_space's dimension predicate agree |
| `IndependentBound` | `(∀i. i < k ⇒ vec⟨n⟩(e(i))) ⇒ vec_independent(k, e) ⇒ k ≤ n` — there are at most n independent n-vectors: they lie in the span of the first n standard basis vectors (`StandardBasis`), and `Steinitz` bounds them by n |
