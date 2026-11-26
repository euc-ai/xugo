# dot — the bilinear form, and the map that moves across it

`⟪u, v⟫_n` — the form `dot⟨n⟩(u, v)`, whose notation the definition
declares — is the fold, with the ring's addition, of the pointwise
products `mul(u(i), v(i))` over the active range `{i | i < n}`.
It is defined through `iterated_op` (iterate/monoidal), so its laws are the
fold mechanism's laws read at the ring: the range is finite for every n,
the fold's recursion adds one index on top of the range, and what the ring
contributes is commutativity of the product (symmetry of the form) and
distributivity (linearity in each argument).

The index set is the half-open range, not the closed interval `0 .. n-1`:
the interval cannot be empty at n = 0 (its lower end cannot retreat below
0), the range is, and every law holds at n = 0 without a guard.

Past the algebra the chapter says three further things, and they build on
each other. The form reads COORDINATES: pairing against the basis vector
at an index gives that index's entry, and from there an n-vector is
determined by how it pairs with the n-vectors — the form is
non-degenerate on a dimension. The form crosses a FOLD: a sum of
arbitrarily many vectors pairs as the sum of the pairings. And with those
two, a linear map has an ADJOINT — the map carrying what `f` does to the
form's first argument over to its second. That is what the chapter is for,
and why the adjoint lives here rather than beside the linear maps: it is
built out of the form, coordinate by coordinate off the basis, and every
fact about it is a fact about the form.

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `dot⟨n⟩(u, v)`, written `⟪u, v⟫_n` | `Σ_{i<n} u(i) * v(i)`, the fold at the ring's addition |
| `adjoint(m, n, f, y, j)` | the j-th coordinate of the adjoint of `f` at `y`: `⟪f(basis_vector(j)), y⟫_n` inside the range below m, and the ring's zero past it. Coordinate-valued, and read at three arities — `adjoint(m, n, f, y)` is the vector whose entries those are, `adjoint(m, n, f)` the map `vec_linear` asks about — each a partial application of this one equation. Two dimensions, each earning its place: `m` counts the coordinates the value has, `n` is the dimension the form is read at. The guard is not bookkeeping — membership in dimension m says exactly "zero from index m on", so the guard IS the membership condition, and `AdjointVec` is that sentence read back |

## The laws (laws.go)

Stated under `∀R:comm_ring(A).`, and read at a carrier
as one value — `dot.AddLeft.Read(real_ring.CommRing)` — wherever the law
is wanted as a premise, a rewrite or a typed cite; every left-handed proof unfolds
`dot` and reads the fold mechanism — congruence, the pointwise law,
relation transfer, or the vanishing law — beside the ring law the
summands obey. The right-handed laws are the left-handed ones through
symmetry, each turn one application of a law.

| member | statement |
|---|---|
| `Sym` | `⟪u, v⟫_n = ⟪v, u⟫_n` |
| `AddLeft` / `AddRight` | `⟪u + v, w⟫_n = ⟪u, w⟫_n + ⟪v, w⟫_n`, and on the right |
| `SmulLeft` / `SmulRight` | `⟪c • u, v⟫_n = c * ⟪u, v⟫_n`, and on the right |
| `NegLeft` / `NegRight` | `⟪-u, v⟫_n = -⟪u, v⟫_n`, and on the right |
| `SubLeft` / `SubRight` | `⟪u - v, w⟫_n = ⟪u, w⟫_n - ⟪v, w⟫_n`, and on the right |
| `ZeroLeft` / `ZeroRight` | `⟪vec_zero, v⟫_n = zero`, and on the right |

## The form against a set (span.go)

The laws above read the form against the OPERATIONS. This one reads it
against a SET of vectors — the first of that kind, and the reason it has a
file rather than a row in the laws table.

A span is the set of combinations of the first k members of a family, so a
vector of it is a fold of scalar multiples and nothing else: linearity in the
first argument crosses that fold and takes each coefficient out of its
summand, leaving only the pairings against the k members themselves.
Orthogonality to a family therefore reaches everything the family spans, and
a subspace presented by a family costs no more to test than the family does.

| member | statement |
|---|---|
| `OrthogonalToSpan` | `(∀i. i < k ⇒ ⟪z, e(i)⟫_n = zero) ⇒ ∀w. w ∈ vec_span(k, e) ⇒ ⟪z, w⟫_n = zero` — checking a vector against finitely many directions settles it against the whole subspace they span. `IterateLeft` crosses the fold, `SmulLeft` frees each coefficient, and a fold of zeros is zero |

## The adjoint, and the two readings it is built from (adjoint.go)

### Coordinates

What the form says about a vector's entries. One reading, and then the
determination that reading buys.

| member | statement |
|---|---|
| `BasisVectorLeft` | `j < n ⇒ ⟪basis_vector(j), u⟫_n = u(j)` — the form reads the j-th coordinate off the j-th basis vector. The hypothesis is the whole content: past the range the form never looks, and there is nothing for it to read |
| `Nondegenerate` | `vec⟨n⟩(u) ∧ vec⟨n⟩(v) ⇒ (u = v ⇔ ∀w. vec⟨n⟩(w) ⇒ ⟪w, u⟫_n = ⟪w, v⟫_n)` — the form is non-degenerate on a dimension. `vec_space.Extensionality` with "agree at every index below n" replaced by "pair alike against every n-vector"; one probe, the basis vector at an index, decides one coordinate. The probe is confined to the dimension along with the two vectors, which is the stronger reading and the one a consumer can supply |
| `Definite` | `(∀w v. ⟪w, w⟫_n = zero ⇒ ⟪w, v⟫_n = zero) ⇒ vec⟨n⟩(u) ⇒ (⟪u, u⟫_n = zero ⇔ u = vec_zero)` — on a dimension the form is definite as soon as a null vector is orthogonal to everything: a null u then pairs against every vector as the zero vector does, and `Nondegenerate` reads that agreement back as equality, the zero vector being an n-vector for every n. That hypothesis is the whole of what definiteness asks of the carrier — at an ordered carrier a consequence of the form's positivity, and the one place an order enters |

### The form across a fold

What the binary additivity of the laws becomes once the sum has
arbitrarily many summands.

| member | statement |
|---|---|
| `IterateLeft` | `finite(s) ⇒ ⟪Σ_{i∈s} F(i), y⟫_n = Σ_{i∈s} ⟪F(i), y⟫_n` — the two sums are folds at DIFFERENT operations: vectors on the left, ring elements on the right, the text writing both the same way and the type deciding which. That crossing is exactly what `monoidal.Homomorphic` is for, and this member is one application of it: pairing against `y` is a homomorphism from the vectors under addition to the ring under addition, and its two obligations are the chapter's own `ZeroLeft` (the element each fold starts from) and `AddLeft` (crossing the operation). No induction runs here |

### The adjoint

The adjoint of a map is the map carried to the other side of the form:
what `f` does to the first argument, `adjoint f` is to do to the second.
The chapter BUILDS it rather than demanding it. Demanding it is the
weaker move here: a vector is a sequence, so the demand would have to be
restricted to the vectors of the dimension in play, and a restricted
demand settles the coordinates below that dimension and leaves every one
past it open. Building settles all of them — and that is what makes the
adjoint of the adjoint a theorem rather than a wish.

The other route DEFINES the adjoint by Hilbert choice and recovers
this construction as the witness that makes the choice denote. Here the
witness is the definition, which is what makes the involution below a
theorem rather than a wish. Its guard is
the one design point, and the definitional table above says what it buys.

| member | statement |
|---|---|
| `AdjointVec` | `vec⟨m⟩(adjoint(m, n, f, y))` — the value is a vector of the dimension it is taken at. No hypothesis: an index past the range fails the guard on its own |
| `AdjointWorks` | `vec_linear(f) ⇒ vec⟨m⟩(x) ⇒ ⟪f(x), y⟫_n = ⟪x, adjoint(m, n, f, y)⟫_m` — the identity the construction was built for. Both sides descend to one fold over the coordinates of x and meet there: on the left through the basis expansion, linearity, and `IterateLeft`; on the right through the guard, decided by the range and by nothing else, which is where a fold's congruence earns its restriction to the index set. `vec⟨m⟩(x)` is what a type `real^M` would carry, and it is spent exactly once, in the expansion — without it the left side consults `f` at indices the right side never looks at, and the identity is false |
| `AdjointLinear` | `vec_linear(adjoint(m, n, f))` — and nothing about `f` is spent. Inside the range each coordinate is the form at a FIXED first argument, so linearity of the adjoint is the form's additivity and homogeneity in its SECOND argument; past the range both sides are built from the ring's zero. A Hilbert-choice definition needs `vec_linear(f)` in order to denote anything at all; a built adjoint needs nothing |
| `AdjointInvolutive` | `vec_linear(f) ⇒ vec⟨m⟩(x) ⇒ vec⟨n⟩(f(x)) ⇒ adjoint(n, m, adjoint(m, n, f), x) = f(x)` — taking the adjoint twice gives the map's own value back, and the definition is never unfolded: what the proof spends is `AdjointVec`, `AdjointWorks` and `AdjointLinear`, symmetry, and `Nondegenerate`. The dimensions swap on the outer adjoint, whose map is the inner one and so is linear for free. A function equality is not available and is not true — `f` is a map on all sequences and the double adjoint is built only out of what `f` does below m, so past that the two have no reason to agree. The third hypothesis is the pointwise remnant of a type `real^M -> real^N`: at THIS `x` the image has the dimension the outer adjoint is read at, which is all the pointwise statement needs |
