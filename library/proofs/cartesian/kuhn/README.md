# kuhn — the grid {0, …, p}ⁿ and its triangulation into Kuhn simplices

Cut the cube ⟦0, p⟧ⁿ into unit cells and each cell into n!
simplices, one per order of the coordinates: the simplex of a base point
v and an order τ runs from v to v + (1, …, 1), raising one coordinate at
each step, at step j (counted from 0) the coordinate i with τ(i) = j.
Nothing in the chapter is a real number.

A grid point is a tuple of naturals in `carrier`'s sense, its entries past
the dimension the junk element, so the grid `kuhn_grid(p, n)` is a finite
set of functions `num → num`. The simplices are the chains of `kuhn_le`,
the order in which y is x with some coordinates raised by one; it
triangulates the cube without a barycentric subdivision, which is why
Kuhn's route is the short one.

The faces are the triangulation's whole geometry and the chapter's
longest proofs: a simplex is rebuilt as the chain from its base point in
its order, and the second simplex through a face is found from that
chain.

`kuhn_labelling` labels the grid and counts the fully labelled simplices
through these faces: that is Kuhn's lemma, the discrete half of
Brouwer's fixed point theorem.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `kuhn_grid(p, n)` | `{x \| tuple(n, x) ∧ ∀i. i < n ⇒ x(i) ≤ p}` |
| `kuhn_le(n, x, y)` | `∀i. (i < n ⇒ x(i) ≤ y(i) ∧ y(i) ≤ x(i) + 1) ∧ (n ≤ i ⇒ y(i) = x(i))` |
| `kuhn_simplex(p, n, s)` | `s ⊆ kuhn_grid(p, n) ∧ has_size(s, n + 1) ∧ ∀x y. x ∈ s ∧ y ∈ s ⇒ kuhn_le(n, x, y) ∨ kuhn_le(n, y, x)` |

## One simplex (chain.go)

There are finitely many Kuhn simplices. Each runs from its least point
to that point raised in every coordinate. The extremes come from a
count: a point with nothing of the simplex strictly below it is least,
and the number of coordinates in which a point exceeds it tells the
n + 1 points apart, so it takes every value 0, …, n; the point where it
is n is the greatest. Between them the simplex is a chain: its least point v raised, after j steps, in the
coordinates i with τ(i) < j, for an order τ of the n coordinates; the
chapter's table names it «vertex»(v, τ, j) = λi. v(i) + COND(i < n ∧
τ(i) < j, 1, 0), j ≤ n. The
chain's vertices are ordered and distinct, a face is the chain less one
vertex, and a point squeezed between two consecutive vertices is one of
them. Vertex m with the steps m − 1 and m exchanged, «swapped»(v, τ, m) =
λi. v(i) + COND(i < n ∧ (τ(i) < m − 1 ∨ τ(i) = m), 1, 0), lies above
every vertex before m and below every vertex after it.

| member | statement |
|---|---|
| `KuhnSimplicesFinite` | `finite({s \| kuhn_simplex(p, n, s)})` |
| `KuhnSimplexExtrema` | `kuhn_simplex(p, n, s) ⇒ ∃a b. a ∈ s ∧ b ∈ s ∧ (∀x. x ∈ s ⇒ kuhn_le(n, a, x) ∧ kuhn_le(n, x, b)) ∧ ∀i. i < n ⇒ b(i) = a(i) + 1` |
| `KuhnSimplexChain` | `kuhn_simplex(p, n, s) ⇒ ∃v τ. (∀i. i < n ⇒ τ(i) < n) ∧ injective_on({i \| i < n}, τ) ∧ s = {«vertex»(v, τ, j) \| j \| j ≤ n}` |
| `KuhnLeRefl` | `kuhn_le(n, x, x)` |
| `KuhnChainOrdered` | `j ≤ l ⇒ kuhn_le(n, «vertex»(v, τ, j), «vertex»(v, τ, l))` |
| `KuhnChainDistinct` | `(∀i. i < n ⇒ τ(i) < n) ∧ injective_on({i \| i < n}, τ) ∧ j < l ∧ l ≤ n ⇒ «vertex»(v, τ, j) ≠ «vertex»(v, τ, l)` |
| `KuhnChainFaceVertices` | τ an order below n `∧ s = {«vertex»(v, τ, k) \| k \| k ≤ n} ∧ j ≤ n ∧ m ≤ n ∧ j ≠ m ⇒ «vertex»(v, τ, j) ∈ delete(s, «vertex»(v, τ, m))` |
| `KuhnChainFacePoints` | `s = {«vertex»(v, τ, k) \| k \| k ≤ n} ∧ x ∈ delete(s, «vertex»(v, τ, m)) ⇒ ∃j. j ≤ n ∧ j ≠ m ∧ x = «vertex»(v, τ, j)` |
| `KuhnChainAgree` | b, c between «vertex»(v, τ, j) and «vertex»(v, τ, l) in kuhn_le, `∧ (∀i. i < n ∧ j ≤ τ(i) < l ⇒ b(i) = c(i)) ⇒ b = c` |
| `KuhnChainSqueeze` | `injective_on({i \| i < n}, τ) ∧ l = j + 1 ∧ kuhn_le(n, «vertex»(v, τ, j), b) ∧ kuhn_le(n, b, «vertex»(v, τ, l)) ⇒ b = «vertex»(v, τ, j) ∨ b = «vertex»(v, τ, l)` |
| `KuhnEarlierBelowExchanged` | `j < m ⇒ kuhn_le(n, «vertex»(v, τ, j), «swapped»(v, τ, m))` |
| `KuhnExchangedBelowLater` | `m < j ⇒ kuhn_le(n, «swapped»(v, τ, m), «vertex»(v, τ, j))` |

## Faces, apexes and the counts (faces.go)

A face, the simplex less one vertex, lies in one simplex when it lies in
a boundary plane of the cube and in two otherwise. `«cofaces»`, an entry
of the chapter's table, is the set of simplices holding the face of s
opposite a.


A simplex through a face is the face with one point added, its apex;
replacing a vertex by a grid point off the simplex comparable with the
face gives a simplex. The face opposite vertex 0, vertex n or an inner
vertex m has, besides the removed vertex, one other candidate apex: the
chain's end raised once more at the first step's coordinate,
«lifted»(v, τ); the start lowered at the last step's, «lowered»(v, τ);
or vertex m with the two steps on either side of it, m − 1 and m,
exchanged, «swapped»(v, τ, m) — the chapter's table names all three.
Inside the cube the other candidate is a grid point off the simplex —
the raised end stays in the grid, the lowered start is no longer the
start — which is `KuhnFaceInterior`'s count of two. On a boundary plane the other candidate is no apex:
on x(j) = 0 the start lowered at j is the start itself, 0 − 1 being 0 in
ℕ, and on x(j) = p the end raised at j is p + 1 there, off the grid; so
the only apex is the vertex the face was cut from, and the face lies in
one simplex (`KuhnSingleCoface`).

| member | statement |
|---|---|
| `KuhnCofaceApex` | `u ∈ «cofaces» ⇔ ∃b. b ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(b, delete(s, a))) ∧ u = insert(b, delete(s, a))` |
| `KuhnSingleCoface` | `kuhn_simplex(p, n, s) ∧ a ∈ s ∧ (∀b. b ∉ delete(s, a) ∧ kuhn_simplex(p, n, insert(b, delete(s, a))) ⇒ b = a) ⇒ card(«cofaces») = 1` |
| `KuhnApexOppositeLeast` | `0 < n ∧` τ an order below n `∧` s the chain `∧ kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, 0)))) ⇒ b = «vertex»(v, τ, 0) ∨ b = «lifted»(v, τ)` |
| `KuhnApexOppositeGreatest` | `0 < n ∧` τ an order below n `∧` s the chain `∧ kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, n)))) ⇒ b = «vertex»(v, τ, n) ∨ b = «lowered»(v, τ)` |
| `KuhnApexOppositeInner` | `0 < m ∧ m < n ∧` τ an order below n `∧` s the chain `∧ b ∉ delete(s, «vertex»(v, τ, m)) ∧ kuhn_simplex(p, n, insert(b, delete(s, «vertex»(v, τ, m)))) ⇒ b = «vertex»(v, τ, m) ∨ b = «swapped»(v, τ, m)` |
| `KuhnSimplexReplace` | `kuhn_simplex(p, n, s) ∧ a ∈ s ∧ b ∈ kuhn_grid(p, n) ∧ b ∉ s ∧ (∀x. x ∈ delete(s, a) ⇒ kuhn_le(n, x, b) ∨ kuhn_le(n, b, x)) ⇒ kuhn_simplex(p, n, insert(b, delete(s, a)))` |
| `KuhnFaceZeroPlane` | `kuhn_simplex(p, n, s) ∧ a ∈ s ∧ j < n ∧ (∀x. x ∈ delete(s, a) ⇒ x(j) = 0) ⇒ card(«cofaces») = 1` |
| `KuhnFaceTopPlane` | `kuhn_simplex(p, n, s) ∧ a ∈ s ∧ j < n ∧ (∀x. x ∈ delete(s, a) ⇒ x(j) = p) ⇒ card(«cofaces») = 1` |
| `KuhnFaceInterior` | `0 < n ∧ kuhn_simplex(p, n, s) ∧ a ∈ s ∧ (∀j. j < n ⇒ the face leaves both x(j) = 0 and x(j) = p) ⇒ card(«cofaces») = 2` |

## The top face (top_face.go)

Raising a point to x(n) = p and truncating it to its first n coordinates
(`tuple_take`) undo each other between the grid and the plane x(n) = p
one dimension up, and they carry Kuhn's order across. So the faces of the
(n + 1)-simplices lying in that plane are exactly the raised n-simplices,
the one-for-one match the induction on the dimension counts through.

| member | statement |
|---|---|
| `KuhnGridExtend` | `x ∈ kuhn_grid(p, n) ∧ q ≤ p ⇒ (λi. COND(i = n, q, x(i))) ∈ kuhn_grid(p, n + 1) ∧ tuple_take(n, λi. COND(i = n, q, x(i))) = x` |
| `KuhnGridTake` | `y ∈ kuhn_grid(p, n + 1) ⇒ tuple_take(n, y) ∈ kuhn_grid(p, n) ∧ (λi. COND(i = n, y(n), tuple_take(n, y, i))) = y` |
| `KuhnLeExtend` | `kuhn_le(n, x, y) ∧ q ≤ r ∧ r ≤ q + 1 ⇒ kuhn_le(n + 1, λi. COND(i = n, q, x(i)), λi. COND(i = n, r, y(i)))` |
| `KuhnLeTake` | `kuhn_le(n + 1, x, y) ⇒ kuhn_le(n, tuple_take(n, x), tuple_take(n, y))` |
| `KuhnTopFaceTruncation` | a face delete(s, a) of an (n + 1)-simplex in the plane x(n) = p truncates to an n-simplex whose raise is the face |
| `KuhnRaisedSimplexFace` | `0 < p ∧ kuhn_simplex(p, n, f) ⇒` the raise of f is a face delete(s, a) of an (n + 1)-simplex, the corner below its least point added |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
