# nat_monus — truncated subtraction and distance

This chapter is ℕ's two compensations for having no negative
numbers: the monus `m - n`, which is zero when n exceeds m, and the
distance `nat_dist(m, n) = (m - n) + (n - m)`.

The chapter sits ABOVE the order. The operators themselves are plain
primitive recursion — predecessor and `-` are defined here by their clauses,
compiled against peano.Recursion, and `nat_dist` by its equation over the
pair — but every law worth stating is order-entangled:
`m - n = 0 ⇔ m ≤ n` is the chapter's load-bearing bridge, and because
monus is piecewise, the dist laws all proceed by case-splitting on
`nat_order.LessEqTotal`. Cites are typed both ways — `nat_arith.*` for the
`+`/`*` substrate, `nat_order.*` for the order — which is what the
nat_arith package split bought.

The mathematical development, file by file — which is also the
reading order:

- **Monus definitions**. predecessor and `-`, each one
  recursion; the projection lemmas the rest of the chapter rewrites
  with.
- **Monus laws**. The compensation laws: `m - n = 0 ⇔
  m ≤ n`, and `n ≤ m ⇒ (m - n) + n = m` with its mirror — subtraction
  undone by addition, exactly on the domain where nothing was
  truncated — and the unguarded pair `m + n - n = m`,
  `m + n - m = n` (`AddSubCancel`, `AddSubLeftCancel`, named for the
  summand that cancels), where
  addition came first and nothing can have been truncated. And a
  positive power is its base times the power one lower,
  $0 < k \Rightarrow m \cdot m^{k-1} = m^k$ (`MulPowSubOne`).
- **Sub-distributivity**. `·` distributes over the
  truncated difference from either side. Each is the LessEqTotal split
  in miniature: on one side both differences vanish, on the other the
  gap is named and ordinary distributivity finishes.
- **Distance definitions**. `nat_dist` and its immediate
  shape: symmetric, zero exactly on the diagonal.
- **Distance laws**. The metric facts (triangle
  inequality and its ≤-composed variants) and the estimate toolkit
  (translation invariance, pairwise bounds) the real tower's nadd
  construction consumes.
- **Distance and multiplication**. `·` slides through
  dist on either side — the homogeneity the slope chapter scales
  estimates with.
