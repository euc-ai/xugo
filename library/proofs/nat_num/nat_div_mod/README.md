# nat_div_mod — Euclidean division on ℕ

This chapter is Euclidean division on ℕ: both constants are minted
here, with their ε-free specification, uniqueness, value laws, bounds
and iteration laws developed in `nat_div_mod.go`.

The chapter sits ABOVE the order: `Division`'s specification states
the remainder bound `nat_mod(m, n) < n`, so the definitional layer already
needs `<`. The proofs use `nat_order` for order and `nat_arith` for
addition and multiplication.

The sections follow this reading order:

- **Definitions**. Quotient and remainder exist by
  well-ordering on the representable remainders (`DivModExist`, the
  chapter's one appeal to `nat_order.WellOrdering`); the specification door mints nat_div
  and nat_mod from that existence (`divModSpec`, the ε-free
  characterization); `Division` / `DivZero` / `ModZero` read the spec
  off at the points where its COND guard decides.
- **Uniqueness**. A bounded remainder pins the
  representation: any pair meeting the three conditions IS (nat_div, nat_mod).
  The lemma form does the work; `DivModUniq` / `DivUniq` / `ModUniq`
  are its projections.
- **Values**. The ground table: dividing zero,
  dividing by self, the remainder's bound, and the `nat_mod = 0` ⇔
  exact-division bridge.
- **Laws**. How nat_div and nat_mod interact with `·` and
  `+`: dividing out a factor, the multiply-add decomposition, and the
  congruence-flavoured `ModMultAdd`.
- **Bounds**. The order facts: the quotient never
  overshoots, dividing never grows, and the exact characterizations of
  a vanishing quotient. Doubling the dividend at most doubles the
  quotient and adds one: for d ≠ 0, div(2n, d) lies between
  2 · div(n, d) and 2 · div(n, d) + 1 (FloorDoubleBound).
- **Iteration**. Nested division: dividing twice is
  dividing by the product, and nat_mod is idempotent.
