# euclidean_simplex — the standard simplices of ℝⁿ⁺¹, the affine maps between them that the singular simplices are read through, and the retraction of a simplex onto a horn

The standard n-simplex Δⁿ is the set of (n + 1)-vectors with
nonnegative coordinates summing to 1: `euclidean_simplex(n)`. Δ⁰ is the
point e₀, Δ¹ the segment from e₀ to e₁. It is compact and convex.

Two families of affine maps carry the standard simplices into one
another. The i-th coface, `euclidean_coface(i)`, inserts a zero
coordinate at i and moves the rest up: it carries Δⁿ onto the face of
Δⁿ⁺¹ where coordinate i vanishes. The i-th codegeneracy,
`euclidean_codegeneracy(i)`, adds coordinates i and i + 1 and moves the
rest down: it carries Δⁿ⁺¹ onto Δⁿ. Both are maps of sequences reading no
dimension, as every operation of vector/ reads its dimension off a term
and not a type, so the cosimplicial identities among them are equations
of maps true at every sequence — index arithmetic, three cases of each
definition — and only where a map lands asks for a dimension. Read
through precomposition they are the simplicial identities of the singular
simplices (simplicial/singular_set).

The horn Λᵏ of Δⁿ⁺¹ is the union of its faces but the k-th: the points
where some coordinate other than the k-th vanishes. The simplex retracts
onto it — subtract from each coordinate other than the k-th the least of
them, and add n + 1 times that least value to the k-th — which is what
makes every singular simplicial set a Kan complex.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `euclidean_simplex(n)` | `{t \| vec⟨n + 1⟩(t) ∧ (∀i. i ≤ n ⇒ &0 ≤ t(i)) ∧ Σ_{i<n + 1} t(i) = &1}` |
| `euclidean_coface(i)` | `λt. λj. COND(j < i, t(j), COND(j = i, &0, t(j - 1)))` |
| `euclidean_codegeneracy(i)` | `λt. λj. COND(j < i, t(j), COND(j = i, t(i) + t(i + 1), t(j + 1)))` |

## The simplex as a space (simplex.go)

| member | statement |
|---|---|
| `SimplexCompact` | `compact_in(euclidean_topology(n + 1), euclidean_simplex(n))` — card |
| `SimplexConvex` | `convex(euclidean_simplex(n))` — card |
| `CofaceSimplex` | `t ∈ euclidean_simplex(n) ⇒ euclidean_coface(i, t) ∈ euclidean_simplex(n + 1)` — card |
| `CofaceImage` | `i ≤ n + 1 ⇒ image(euclidean_coface(i), euclidean_simplex(n)) = {t \| t ∈ euclidean_simplex(n + 1) ∧ t(i) = &0}` — card |
| `CofaceContinuous` | `continuous_map(euclidean_topology(n + 1), euclidean_topology(n + 2), euclidean_coface(i))` — card |
| `CodegeneracySimplex` | `i ≤ n ∧ t ∈ euclidean_simplex(n + 1) ⇒ euclidean_codegeneracy(i, t) ∈ euclidean_simplex(n)` — card |
| `CodegeneracyContinuous` | `i ≤ n ⇒ continuous_map(euclidean_topology(n + 2), euclidean_topology(n + 1), euclidean_codegeneracy(i))` — card |
| `HornRetraction` | `k ≤ n + 1 ⇒ retract_of(subtopology(euclidean_topology(n + 2), euclidean_simplex(n + 1)), {t \| t ∈ euclidean_simplex(n + 1) ∧ ∃i. i ≤ n + 1 ∧ i ≠ k ∧ t(i) = &0})` — card |

## The cosimplicial identities (identities.go)

| member | statement |
|---|---|
| `CofaceCoface` | `i < j ⇒ euclidean_coface(j) ∘ euclidean_coface(i) = euclidean_coface(i) ∘ euclidean_coface(j - 1)` — card |
| `CodegeneracyCodegeneracy` | `i ≤ j ⇒ euclidean_codegeneracy(j) ∘ euclidean_codegeneracy(i) = euclidean_codegeneracy(i) ∘ euclidean_codegeneracy(j + 1)` — card |
| `CodegeneracyCofaceBelow` | `i < j ⇒ euclidean_codegeneracy(j) ∘ euclidean_coface(i) = euclidean_coface(i) ∘ euclidean_codegeneracy(j - 1)` — card |
| `CodegeneracyCofaceIdentity` | `euclidean_codegeneracy(j) ∘ euclidean_coface(j) = (λt. t) ∧ euclidean_codegeneracy(j) ∘ euclidean_coface(j + 1) = (λt. t)` — card |
| `CodegeneracyCofaceAbove` | `j + 1 < i ⇒ euclidean_codegeneracy(j) ∘ euclidean_coface(i) = euclidean_coface(i - 1) ∘ euclidean_codegeneracy(j)` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
