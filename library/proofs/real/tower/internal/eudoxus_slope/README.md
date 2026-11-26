# eudoxus_slope — Eudoxus slopes (the real tower's first level)

A **slope** is a function `f : ℕ → ℕ` that is *nearly linear*: its
defining bound

```
∃B. ∀m n.  nat_dist(m·f(n), n·f(m)) ≤ B·(m+n)
```

says the "ratios" `f(n)/n` stabilize — without ever mentioning
division, limits, or rationals. Slopes are the Eudoxus construction
of the nonnegative reals: each slope *is* a real number in the making
(the number `lim f(n)/n`), and two slopes are **equivalent** when
they differ by a bounded amount (slope equivalence:
`∃B. ∀n. nat_dist(f(n), g(n)) ≤ B`). The next layer
up (`nonneg_real`) is exactly the quotient by that equivalence.

(Notation notes for readers of the proof files: the text DSL folds
subscripts, so `B₀` and `B_0` are the SAME variable name. Skolem
constants are minted as `<binder>_0` — an ∃B in a hypothesis
Skolemizes to `B_0` (printed B₀), a goal-side ∀n strips to `n_0`.

Two spellings reach them, and which one a body uses tells you what it
is doing. `w, f := a.Unpack(target)` eliminates an ∃ and hands back the
witness AND the instance as values, registering the minted name itself
— nothing to declare, and the hypothesis is named rather than re-found.
A bare `StripQuant()` mints the same constants but returns nothing, so
the body declares the frees it will build terms with via `ctx.Var`.
Use the second where the strip is part of a longer goal-surface move,
and the first where the proof needs the witness and its fact.

The term-building vocabulary (`at`, `d`, `sum`, `mul`, `le`) and the
statement constants live on the family's `slopeVocab` (vocab.go),
taken as a local by each body that builds terms. `rel` is there too, and
is the one member of it that builds no term: it reads a relation const
as the closure a `Calc` chain takes for its `Le` / `Eq` / `Rel` field,
so each chain says which relation it runs on and
which transitivity theorem knits it, and nothing about the two term
surfaces in between.)

The chapter develops, on the raw function type and up to slope
equivalence (`nadd_eq`) — one part per movement, named for it:

- **`definitions.go`** — the language: `is_nadd`, the defining bound;
  the type `nadd` ("nearly additive") it carves out of ℕ → ℕ, with
  `mk_nadd` / `dest_nadd` the bijection and the constantly-zero
  function the inhabitant it is stamped against; and the operations
  written through that bijection — equality and order up to a bound,
  the embedding of a number, sum, product, the candidate reciprocal
  and the reciprocal itself. The two
  facts the type definition comes with are its `Retraction` and
  `Membership` entries, and every operation's welldefinedness proof
  discharges through them;

- **Equivalence** — that `nadd_eq` is an equivalence relation. Every
  welldef lemma below, and every transport in the two layers above, is
  stated against these three;
- **`toolkit.go`** — the defining bound and its consequences: linear
  growth, near-multiplicativity, near-additivity, plus the `nat_dist`
  calculus that every later estimate runs on (and `ZeroIsSlope`, the
  defining bound at the constantly-zero function, which is the
  inhabitant the type definition is stamped against);
- **`order.go`** — the order (pointwise-up-to-a-bound) with its equivalence-compatibility (welldef)
  lemma, and its compatibility with `+` and `·`: each operation is
  monotone in either slot, and the right-hand product law
  (`LessEqMulRight`) is `LessEqMulLeft` conjugated by commutativity;
- **Addition** (`(f+g)(n) = f(n)+g(n)`) and **multiplication**
  (`(f·g)(n) = f(g(n))`, composition!) — the carrier-level operations
  with their commutativity / associativity / identity laws and welldef
  lemmas;
- **The ℕ-embedding** (`n ↦ (m ↦ n·m)`) and its morphism
  laws;
- **The growth bounds** — every nonzero slope grows at
  least linearly and never eventually vanishes, the Archimedean bridge
  from ℕ-arithmetic into the inverse construction (upper / lower linear
  envelopes, nonvanishing threshold);
- **The inverse** — the hard analytic core: the multiplicative inverse
  (the pseudo-division construction behind the field axiom
  `real_construction.MulLeftInverse`), through the arch/bound machinery.

This is machinery (`internal/`): its sole purpose is to deliver the
`nonneg_real` layer above it, and no theorem outside the real tower should
ever build on it.
