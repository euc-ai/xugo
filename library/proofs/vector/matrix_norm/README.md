# matrix_norm — the measures a matrix gives a vector, compared with the Euclidean norm uniformly over a compact family

A matrix G measures a vector v in two ways beside its Euclidean norm:
by the quadratic form ⟪v, Gv⟫ when that form is positive, and by the
image norm ‖Gv‖ when G is injective. For one matrix, compactness of
the unit sphere bounds each of them above and below by a constant
times the Euclidean norm, squared for the quadratic form. This chapter
makes the two constants uniform over a family G(x) indexed by a
compact set K of an arbitrary topological space: continuity of the
entries on K, and positivity or injectivity at each x, give one pair
of constants for every x in K.

Both comparisons are one theorem read twice. A continuous function
f(x, v) on K × ℝⁿ that is homogeneous of a positive degree d in v and
positive at every nonzero vector lies between two positive multiples
of ‖v‖ᵈ uniformly over K: homogeneity at a positive degree makes it
zero at the zero vector, and on K times the unit sphere, a compact
set, it attains a positive least and a greatest value, which
homogeneity carries to every other vector. The quadratic
form is that function at degree 2, the image norm at degree 1. Their
continuity is read off the action (x, v) ↦ G(x)v, continuous on
K × ℝⁿ when the entries are continuous on K: each coordinate is a
finite sum of continuous products.

Continuity is asked only on K. The quadratic form need not come from
a symmetric matrix and reads only the entries below n, and the
injective matrices may be rectangular. An empty K and source dimension
zero are admitted; every pair of constants then satisfies the
estimate, and the statements still give 0 < a ≤ b.

| member | statement |
|---|---|
| `CompactPositiveHomogeneousBounds` | for a continuous f(x, v) on K × ℝⁿ, K compact, homogeneous of a positive degree d in v and positive at every nonzero vector, `∃a b. 0 < a ≤ b ∧ a‖v‖ᵈ ≤ f(x, v) ≤ b‖v‖ᵈ` for every x ∈ K and n-vector v |
| `MatrixActCoordinateContinuous` | when the entries of row i of G(x) are continuous on K, the i-th coordinate of `G(x)v` is continuous on K × ℝⁿ |
| `MatrixActContinuous` | for a family of m×n matrices whose entries are continuous on K, the action `(x, v) ↦ G(x)v` is continuous from K × ℝⁿ into ℝᵐ |
| `CompactPositiveQuadraticBounds` | for a continuous family of matrices on a compact K whose quadratic forms are positive, `∃a b. 0 < a ≤ b ∧ a‖v‖² ≤ ⟪v, G(x)v⟫ ≤ b‖v‖²` for every x ∈ K and n-vector v |
| `CompactInjectiveMatrixBounds` | for a continuous family of injective m×n matrices on a compact K, `∃a b. 0 < a ≤ b ∧ a‖v‖ ≤ ‖G(x)v‖ ≤ b‖v‖` for every x ∈ K and n-vector v |
