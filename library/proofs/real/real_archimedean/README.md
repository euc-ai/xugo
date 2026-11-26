# real_archimedean — ℕ is unbounded in ℝ

Every real is below some natural number. That one sentence is this
chapter, and everything else in it is a restatement of it: strictly
below rather than weakly, bounding a real on both sides at once, scaled
by an arbitrary positive step rather than by 1, or read backwards as a
statement about how small `1/n` can get.

## Why it is a chapter of its own

The other four theory chapters above the tower — `real_ring`,
`real_field`, `real_order_ring`, `real_order_field` — are all theories
of an **ordered field**. Every statement in them holds in any ordered
field, and none of them cites `tower/real_completeness`.

The Archimedean property is the first theorem above the tower that does
not. It is genuinely false in some ordered fields: in the field of
rational functions ℝ(x) ordered by eventual dominance, `x` is larger
than every constant `&n`, so no natural exceeds it. Proving it therefore
requires completeness, and this chapter is the step at which the reals
stop being "some ordered field" and become **the** reals.

That shows up in the dependency signature, which is unique in `real/`:
this is the only chapter reaching both `tower/real_completeness` and
`real_order_field`.

## The chapter's arc

**1. ℕ is unbounded (`ExistsNumAbove`).** The one analytic argument, and
the only place completeness is used: the naturals, if they were bounded,
would have a least upper bound with one to spare. The entry's own doc
comment carries the argument. Read at x and at −x, it puts every real
between −&n and &n for one natural n (`ExistsNumBounds`).

**2. The strict form (`ExistsNumStrictlyAbove`).** `x ≤ &n` upgrades to
`x < &(n+1)`, because adding one to a bound makes it strict and the
embedding carries the successor: `&(n+1) = &n + &1`.

**3. The Archimedean property proper (`Archimedean`).** For a positive
step `x`, the multiples `&n · x` exceed any target `y`. This is the
strict form applied to `y / x` and then multiplied back through: the
cross-multiplication law that clears a positive denominator is exactly
`real_order_field`'s, which is the chapter's second upward edge.

**4. The property read backwards (`PosIffExistsSmallInv`).** A real is
positive precisely when some `1/n` fits strictly under it. The forward
direction is the strict form applied to `1/e` — some `&n` exceeds it,
and inverting an inequality between positives reverses it. The
converse is transitivity: `1/n` is positive and below `e`.

**5. The reciprocal form (`ExistsReciprocalBelow`).** Every positive
real exceeds some `1/(n + 1)`: it exceeds some `1/m` with `m ≠ 0`, and
`1/(m + 1)` is smaller still. The successor form needs no side
condition, which is how sequences and level sets read it.

## What is not here

**The Archimedean property for POWERS** rather than for multiples — that
`(&1 + x) pow n` outruns any bound. It is this chapter's subject and it
is not stated here. Bernoulli's inequality,
`&1 + &n · x ≤ (&1 + x) pow n`, turns a multiple into a power and so
carries `Archimedean` across; it is proved in the power chapter
(`real_pow.Bernoulli`), which this chapter does not import. The
property's sequence form — the powers of a number below 1 in size tend
to 0 — is the sequences chapter's (`PowerTendsToZero`), proved there by
monotone convergence rather than through Bernoulli.

**Suprema and infima.** Completeness's other consumer is a chapter of
its own rather than a part of this one: it introduces constants defined
over SETS, so its definitional layer closes somewhere this chapter's
does not reach.

## Mechanics

- **Statements** are text, in the chapter's alphabet: `≤` and `<` as
  notation, the embedding `&n` — which every headline names — and the
  operations the chapter applies to it. The types come from the ℝ domain
  alphabet, `real/internal/realvocab`; `vocab.go` says which names this
  chapter uses.
- **Cites** are typed references to entry vars, all of them. Three of
  them — `real_order_ring`'s `LessThanSelfAddRight` and
  `LessThanAddOne`, and `nat_order`'s `PosIffNonzero` — were demoted
  members of their own chapters; this chapter citing them is what made
  them chapter API, so each is exported where it lives.
- **A cite that fires as a goal REWRITE takes no witnesses** and carries
  a `↦` comment naming the goal it lands on, never the mechanism that
  put it there. A cite consumed as a premise is ground at the instance
  the argument is about, and its comment states that instance. Those two
  forms are the whole citation vocabulary here; the `↦` arrow is what
  tells them apart at a glance.
- **The CNF cache** is one shared `real_archimedean.cnf.pb` for the
  family. `family.go` carries the record and GC recipes.
