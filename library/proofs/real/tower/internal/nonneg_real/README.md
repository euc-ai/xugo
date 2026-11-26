# nonneg_real — the nonnegative reals (the real tower's second level)

The nonnegative reals arise from slopes by **quotienting**: `hreal`
is the type of `nadd_eq`-equivalence classes of slopes. Where the
slope layer proved every law *up to equivalence* (`nadd_eq(lhs, rhs)`),
this layer converts each into an *identity* (`lhs = rhs`) — genuine
equality on the quotient type. Nothing mathematically new is proven
about the underlying approximation arithmetic; the chapter's whole
content is **transport**: carrying the slope layer's laws across the
quotient boundary.

The type and its arithmetic are the chapter's own definitions
(`definitions.go`). `hreal` is the quotient of `nadd` by `nadd_eq`,
declared through the quotient door (`family.DefineQuotient`, `HrealDef`)
on slope's `NaddEqEquivalence`: the class map `hreal_of_nadd` — written
`⁅x⁆`, the class of the slope x — takes a slope to its class, with
`mk_hreal` / `dest_hreal` the bijection underneath it, and the door
derives the seven facts a quotient comes with:

- **`HrealDef.Surjectivity`** — every hreal is a class: `∀q. ∃x. q = ⁅x⁆`.
- **`HrealDef.Induct`** — the same fact as the induction principle
  `hreal_induction`: a law over hreal is proved at `⁅x⁆` for a slope x,
  which is what `a.Induct("x")` on an hreal binder does.
- **`HrealDef.Sound`** / **`HrealDef.Exact`** / **`HrealDef.Eq`** —
  equivalent slopes have one class, equal classes have equivalent
  slopes, and the iff of the two, `⁅x⁆ = ⁅y⁆ ⇔ nadd_eq(x, y)`.
- **`HrealDef.ForallOnImage`** / **`HrealDef.ExistsOnImage`** — a
  quantifier over hreal is the quantifier over slopes at their classes.

Each operation is defined AT CLASSES, by what it does to representatives
(`HrealAddDef`: `⁅a⁆ + ⁅b⁆ = ⁅a + b⁆`, and `HrealMulDef`, `HrealInvDef`
alike; `HrealLeDef`: `⁅a⁆ ≤ ⁅b⁆ ⇔ a ≤ b`, a truth value rather than a
class). That such a rule defines a function is the respectfulness the
lift door asks for, and the slope chapter's well-definedness laws are
exactly that obligation — each definition's `Respects` is one cite. The
numeral is the class of the embedded slope (`HrealOfNumDef`).

With the door's facts in hand, every transported member is three
moves: induct each hreal binder to a representative, simplify with the
operations' definitions and `HrealDef.Eq` so the goal computes at the
classes, and cite the slope law it has become. The chapter develops
the ℕ-embedding morphism laws, the total order, the additive and
multiplicative laws (commutative semiring with cancellation), and the
multiplicative inverse — mirroring the slope chapter's tiers one floor
up. Those four headings are the chapter's parts.

This is machinery (`internal/`): its sole purpose is to deliver the
`nonneg_real_formal_diff` layer above it, and no theorem outside the real tower
should build on it.

(Notation notes for readers of the proof files: the text DSL folds
subscripts, so `x₀` and `x_0` are the SAME variable name. A
representative an induction introduces has no spelling until
`a.StepArgs("xr")` names it; a Skolem constant a strip mints is
`<binder>_0`, escalating (`x₁`, `x₂`) past names already free in the
goal. The statement constants live on the family's `hrealVocab`
(vocab.go), built by `ops(ctx)`.)
