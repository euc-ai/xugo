# kuhn_labelling — the labelling of Kuhn's grid by reduced labels, the parity of fully labelled simplices, and Kuhn's lemma

Kuhn's combinatorial lemma is the discrete half of Brouwer's fixed point
theorem. On the grid {0, …, p}ⁿ and its triangulation into Kuhn
simplices, `kuhn`'s, label every grid point x and every coordinate
i < n with ⊥ or ⊤, ⊥ where x(i) = 0 and ⊤ where x(i) = p. Then some cell
holds, for each coordinate, a point labelled ⊥ there and a point
labelled ⊤ there. Nothing in the chapter is a real number. ℝⁿ's
topology chapter reads the lemma at the labelling a self-map of the
cube induces, and that is how the combinatorics reaches the fixed point.

The proof counts. Each point gets one vertex label in 0, …, n, its
`kuhn_reduced` label, the length of the run of ⊥ its labels start with.
A simplex is fully labelled when its n + 1 vertices carry all n + 1
values. Doors and rooms then give the parity: every face of the
triangulation lies in two simplices, or in one on the cube's boundary; a
fully labelled simplex has one face labelled 0, …, n − 1 and any other
simplex none or two; so the fully labelled simplices are as odd as the
boundary faces labelled 0, …, n − 1. Those all lie on the top face
x(n − 1) = p, where they are the fully labelled simplices one dimension
down, and induction on n starts from the one point of dimension 0.

## The definition (definitions.go)

| constant | reading |
|---|---|
| `kuhn_reduced(n, l, x)` | `card({k \| k < n ∧ ∀j. j ≤ k ⇒ ¬l(x, j)})` |

## The count and the lemma (labelling.go)

`KuhnSimplexLemma` reads the doors-and-rooms parity,
`nat_sum.DoorsAndRoomsParity`, at the Kuhn simplices, and counts a
simplex's doors by their opposite vertices: in
a fully labelled simplex the one door is the face opposite the vertex
labelled n + 1; in any other, a door forces the labels to be 0, …, n with
one label on two vertices, and the doors are the faces opposite those
two.

| member | statement |
|---|---|
| `KuhnReducedIff` | `kuhn_reduced(n, l, x) = k ⇔ k ≤ n ∧ (∀j. j < k ⇒ ¬l(x, j)) ∧ (k = n ∨ l(x, k))` |
| `KuhnSimplexLemma` | vertex labels in 0, …, n + 1 on the (n + 1)-simplices: an odd number of boundary faces labelled 0, …, n ⇒ an odd number of simplices labelled 0, …, n + 1 |
| `KuhnInduction` | the boundary conditions in dimension n + 1 and an odd number of n-simplices fully labelled by the labelling read on x(n) = p ⇒ an odd number of fully labelled (n + 1)-simplices |
| `KuhnCombinatorial` | the boundary conditions ⇒ `nat_odd(card({s \| kuhn_simplex(p, n, s) ∧ image(kuhn_reduced(n, l), s) = {k \| k ≤ n}}))` |
| `KuhnLemma` | the boundary conditions ⇒ some cell ⟦q, q + (1, …, 1)⟧ of the grid holds, for each i < n, two points whose labels at i differ |

The boundary conditions are `l(x, i)` ⊥ where `x(i) = 0` and ⊤ where
`x(i) = p`, for x in the grid and i < n. No `0 < p` is assumed: with
p = 0 and n > 0 the two conditions contradict at the cube's one point.

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
