# real_sequences — sequences of reals and their limits

A sequence is a function `a : ℕ → ℝ`, and `a ⟶ l` says its terms end
up within any positive distance of `l`: for every `ε > 0` there is an
index `N` past which `|a(n) − l| < ε`. This chapter is the first
above the tower to speak that language. Everything below it — the
ordered field, the Archimedean property, suprema and infima — is
about single numbers and sets of them; here a number is approached
by a process, and the proofs are the management of an `ε` and of the
index past which a tail is inside it.

The chapter has six movements.

**1. Two limits past one index: order, uniqueness and the squeeze.**
An argument that plays two limits against each other needs an index
past which both hold at once. Each limit answers `ε` with an index of
its own, and their sum is past both — where the larger of the two
would first have to be decided. Limits keep order: were `a` below `b`
past some index `N` while `a`'s limit lay above `b`'s, half the gap
between the two limits is an `ε`, and past `N` and the shared index
`a(n)` would lie above the midpoint of the limits and `b(n)` below
it — the tails would cross. Read for one sequence against itself, both
ways, that is uniqueness: each of two limits of a sequence is at most
the other. Uniqueness is what makes "the limit" a phrase the later
movements may use. And the squeeze pins a sequence between two: where
`a(n) ≤ b(n) ≤ c(n)` past `N` and `a` and `c` both tend to `l`, past `N`
and the index the outer limits share
`l − ε < a(n) ≤ b(n) ≤ c(n) < l + ε`, so `b` tends to `l` too. The
strict converse of keeping order: a level `c` lies below the limit
exactly when the late terms clear it by a fixed step, some
`1/(k + 1)` and some `N` with every term past `N` above
`c + 1/(k + 1)` (`LimitAboveIff`).

**2. The algebra of limits.** A constant sequence tends to its value,
any index answering any `ε`, and the negative of a sequence tends to the
negative of its limit, the same index answering the same `ε`, since
`|−a(n) − (−l)| = |a(n) − l|`. The sum: past the index the two limits
share at `ε/2`, `a(n)` is within `ε/2` of `l` and `b(n)` within `ε/2` of
`m`, and the triangle inequality puts `a(n) + b(n)` within `ε` of
`l + m`. The product: one tolerance `η` serves both limits past the
index they share, and the deviation of the product splits into three
terms,
`a(n)·b(n) − l·m = (a(n) − l)(b(n) − m) + l(b(n) − m) + m(a(n) − l)`, so
with `η ≤ 1` it is below `η·(|l| + |m| + 1)` — the product of the two
deviations is below `η·η ≤ η`, and the estimate needs no bound on either
sequence beyond the tolerance itself. The difference is the sum of `a`
and `−b`, and a scalar multiple the product with a constant sequence;
neither needs an `ε` of its own. With the sum and the difference in
hand, the squeeze reads on a distance: a sequence within `g(n)` of
`p(n)` at every index, where `g` tends to 0 and `p` to `l`, lies between
`p − g` and `p + g`, which both tend to `l`, so it tends to `l` as well.
The function-limits chapter proves the same algebra at a point, with a
punctured ball where this chapter has a tail; the product's estimate is
stated in each.

**3. Monotone and bounded means convergent — and the limit is the
extremum.** A rising sequence bounded above converges, and what it
converges to is `real_sup` of its range: the supremum's approximation
law hands, for any `ε`, a term `a(N)` above `real_sup − ε`, and
monotonicity carries every later term above it too, while the supremum
caps them all from above. So the tail past `N` lies in
`⟬real_sup − ε, real_sup⟧`. The falling sequence bounded below is the
mirror, at `real_inf`. The statement names the limit —
`a ⟶ real_sup(image(a, 𝕌))` — rather than asserting one exists, because
a named limit is what a later chapter composes with; the existential
form is the corollary — through the two-sided reading of a size bound,
`|a(n)| ≤ B` capping the terms at `B` and flooring them at `−B` — and it
is the classical sentence. The falling wing's first use is that the
powers of a number below 1 in size tend to 0: the powers of `|x|` fall
and stay above 0, so they converge, to some `L`; the shifted powers tend
both to `L` and to `|x|·L`, and a sequence has one limit, so
`(1 − |x|)·L = 0` and `L = 0`; and each `xⁿ` lies as far from 0 as
`|x|ⁿ` does.

This is where completeness is first *used* rather than restated: the
extrema chapter turns the completeness axiom into a calculus of
bounds, and this movement is the first consumer of `real_sup` and `real_inf`
outside that chapter — through `real_has_sup` and `real_has_inf`, the relations
that say a value IS the extremum, since "sup of the range is its
supremum" is one fact both the approximation law and the cap take as
their premise. The bridge the movement needs — a step-wise monotone
sequence is monotone between any two indices — is `order.MonotoneOnNatInterval` read at the real order. Its falling
mirror follows through negation: `-a` rises when `a` falls.

**4. A bounded sequence has a cluster point, and a cluster point is
the limit of a subsequence — Bolzano–Weierstrass.** A number is a
*cluster point* of a sequence, `real_cluster_point(a, l)`, when the sequence
comes back within any positive distance of it past every index. A
bounded sequence has one, and it can be named. Every tail of a bounded
sequence has its supremum and its infimum; the suprema,
`s(N) = sup {a(n) | n ≥ N}`, fall as `N` grows — each tail holds the
next — and stay above `−B`, so by the monotone movement they converge,
to their infimum: the upper limit `real_limsup(a)`. Mirrored, the tail
infima rise and converge to their supremum, the lower limit
`real_liminf(a)`; every term lies between its tail's infimum and supremum,
so, limits keeping order, `real_liminf(a) ≤ real_limsup(a)`. The upper limit is a
cluster point: past some index every tail supremum is within `ε` of it,
and such a supremum is approached from inside by a term of its tail —
and the lower limit is one too, mirrored. A cluster point is then the
limit of a subsequence. Choosing, for every `k` and every index, a
term past it within `1/(k + 1)` of the point is a function; primitive
recursion strings the choices into strictly rising indices `σ`; and a
sequence whose `k`-th term is within `1/(k + 1)` of a number tends to
it — the Archimedean property in sequence form, which the
function-limits chapter also cites. Together these are the classical
sentence: every bounded sequence has a convergent subsequence. A
subsequence of a CONVERGENT sequence needs no choosing: it tends to
the same limit, since a strictly increasing `σ` never falls below the
identity — `k ≤ σ(k)`, one induction in the order chapter of ℕ — so
the index that answers `ε` for `a` answers it for `a ∘ σ`. A sequence
and its shift by one have the same limits: the shift is the
subsequence `k ↦ k + 1`, and conversely the index at which the shift
settles, moved on by one, serves the sequence itself. The upper
and lower limits are minted as values — formulas from sup and inf,
which name a number wherever the sequence is bounded (definitions.go
says why they are minted where no `lim` is).

**5. Cauchy means convergent.** A sequence is *Cauchy*, `real_cauchy(a)`,
when its terms end up within any positive distance of EACH OTHER, no
limit named. A convergent sequence is Cauchy — two terms near the limit
are near each other. The converse needs completeness, and gets it
through the previous movement: a Cauchy sequence is bounded
— past some index every term is within `1` of one term, and the finitely
many before it are bounded by induction on their number — so its upper
limit is a cluster point; and a Cauchy sequence converges to any
cluster point it has, since every late term is near a late return. So a
Cauchy sequence converges, to its upper limit, and the Cauchy criterion
is an equivalence. A convergent sequence is bounded too: it is Cauchy,
and a Cauchy sequence is bounded.

**6. A bounded sequence converges exactly when its upper and lower
limits agree — to their common value.** `a ⟶ l` holds exactly when
`real_liminf(a) = l ∧ real_limsup(a) = l`. Forward, the previous two movements
meet: a convergent sequence is Cauchy, both limits are cluster points,
a Cauchy sequence converges to each of them, and a limit is one number.
Backward, every term lies between its tail's infimum and supremum,
both of which tend to `l` — the squeeze of the first movement. The
statement names the limit; that a bounded sequence converges when its
upper and lower limits agree is read off it.

Monotone convergence is where the tower's completeness is first used;
Bolzano–Weierstrass and the Cauchy criterion are the forms of
completeness that analysis quotes, and both are derived here from that
first use and the extrema laws.

## Members

| entry | statement |
|---|---|
| `RealConvergesToDef` | `a ⟶ l ⇔ ∀ε. &0 < ε ⇒ ∃N. ∀n. N ≤ n ⇒ real_abs(a(n) − l) < ε` |
| `LimitCommonIndex` | `a ⟶ l ∧ b ⟶ m ⇒ ∀ε. &0 < ε ⇒ ∃N. ∀n. N ≤ n ⇒ real_abs(a(n) − l) < ε ∧ real_abs(b(n) − m) < ε` |
| `LimitLessEq` | `(∀n. N ≤ n ⇒ a(n) ≤ b(n)) ∧ a ⟶ l ∧ b ⟶ m ⇒ l ≤ m` |
| `LimitLessEqBound` | `a ⟶ l ∧ (∀n. a(n) ≤ M) ⇒ l ≤ M` |
| `BoundLessEqLimit` | `a ⟶ l ∧ (∀n. M ≤ a(n)) ⇒ M ≤ l` |
| `LimitAboveIff` | `a ⟶ l ⇒ (c < l ⇔ ∃k N. ∀m. c + real_inv(&k + &1) < a(N + m))` |
| `LimitUnique` | `a ⟶ l ∧ a ⟶ m ⇒ l = m` |
| `LimitSqueeze` | `(∀n. N ≤ n ⇒ a(n) ≤ b(n) ∧ b(n) ≤ c(n)) ∧ a ⟶ l ∧ c ⟶ l ⇒ b ⟶ l` |
| `LimitEventuallyEqual` | `(∀n. N ≤ n ⇒ a(n) = b(n)) ∧ a ⟶ l ⇒ b ⟶ l` |
| `LimitConst` | `(λn. k) ⟶ k` |
| `LimitNeg` | `a ⟶ l ⇒ (λn. −a(n)) ⟶ −l` |
| `LimitAdd` | `a ⟶ l ∧ b ⟶ m ⇒ (λn. a(n) + b(n)) ⟶ l + m` |
| `LimitSub` | `a ⟶ l ∧ b ⟶ m ⇒ (λn. a(n) − b(n)) ⟶ l − m` |
| `LimitMul` | `a ⟶ l ∧ b ⟶ m ⇒ (λn. a(n) · b(n)) ⟶ l · m` |
| `LimitScale` | `a ⟶ l ⇒ (λn. k · a(n)) ⟶ k · l` |
| `LimitSqueezeDistance` | `(∀n. real_abs(c(n) − p(n)) ≤ g(n)) ∧ g ⟶ &0 ∧ p ⟶ l ⇒ c ⟶ l` |
| `IncreasingLessEq` | `(∀k. a(k) ≤ a(k + 1)) ⇒ ∀m n. m ≤ n ⇒ a(m) ≤ a(n)` |
| `DecreasingLessEq` | `(∀k. a(k + 1) ≤ a(k)) ⇒ ∀m n. m ≤ n ⇒ a(n) ≤ a(m)` |
| `IncreasingBoundedConvergesToSup` | `(∀n. a(n) ≤ a(n + 1)) ∧ (∀n. a(n) ≤ B) ⇒ a ⟶ real_sup(image(a, 𝕌))` |
| `DecreasingBoundedConvergesToInf` | `(∀n. a(n + 1) ≤ a(n)) ∧ (∀n. B ≤ a(n)) ⇒ a ⟶ real_inf(image(a, 𝕌))` |
| `MonotoneBoundedConvergent` | `((∀n. a(n) ≤ a(n + 1)) ∨ (∀n. a(n + 1) ≤ a(n))) ∧ (∀n. \|a(n)\| ≤ B) ⇒ ∃l. a ⟶ l` |
| `PowerTendsToZero` | `real_abs(x) < &1 ⇒ (λn. real_pow(x, n)) ⟶ &0` |
| `RealLimsupDef` | `real_limsup(a) = real_inf(image(λN. real_sup(image(a, {n \| N ≤ n})), 𝕌))` |
| `RealLiminfDef` | `real_liminf(a) = real_sup(image(λN. real_inf(image(a, {n \| N ≤ n})), 𝕌))` |
| `RealClusterPointDef` | `real_cluster_point(a, l) ⇔ ∀ε. &0 < ε ⇒ ∀N. ∃n. N ≤ n ∧ real_abs(a(n) − l) < ε` |
| `TailHasSup` | `(∀n. \|a(n)\| ≤ B) ⇒ ∀N. real_has_sup(image(a, {n \| N ≤ n}), real_sup(image(a, {n \| N ≤ n})))` |
| `TailHasInf` | `(∀n. \|a(n)\| ≤ B) ⇒ ∀N. real_has_inf(image(a, {n \| N ≤ n}), real_inf(image(a, {n \| N ≤ n})))` |
| `TailSupConvergesToLimsup` | `(∀n. \|a(n)\| ≤ B) ⇒ (λN. real_sup(image(a, {n \| N ≤ n}))) ⟶ real_limsup(a)` |
| `TailInfConvergesToLiminf` | `(∀n. \|a(n)\| ≤ B) ⇒ (λN. real_inf(image(a, {n \| N ≤ n}))) ⟶ real_liminf(a)` |
| `LiminfLessEqLimsup` | `(∀n. \|a(n)\| ≤ B) ⇒ real_liminf(a) ≤ real_limsup(a)` |
| `BoundedClusterPoint` | `(∀n. \|a(n)\| ≤ B) ⇒ real_cluster_point(a, real_limsup(a))` |
| `LiminfClusterPoint` | `(∀n. \|a(n)\| ≤ B) ⇒ real_cluster_point(a, real_liminf(a))` |
| `WithinReciprocalConverges` | `(∀n. real_abs(a(n) − c) < real_inv(&n + &1)) ⇒ a ⟶ c` |
| `ClusterPointSubsequence` | `real_cluster_point(a, l) ⇒ ∃σ. (∀k. σ(k) < σ(k + 1)) ∧ a ∘ σ ⟶ l` |
| `LimitSubsequence` | `(∀k. σ(k) < σ(k + 1)) ∧ a ⟶ l ⇒ a ∘ σ ⟶ l` |
| `LimitShift` | `(λn. a(n + 1)) ⟶ l ⇔ a ⟶ l` |
| `BolzanoWeierstrass` | `(∀n. \|a(n)\| ≤ B) ⇒ ∃σ l. (∀k. σ(k) < σ(k + 1)) ∧ a ∘ σ ⟶ l` |
| `RealCauchyDef` | `real_cauchy(a) ⇔ ∀ε. &0 < ε ⇒ ∃N. ∀m n. N ≤ m ∧ N ≤ n ⇒ real_abs(a(m) − a(n)) < ε` |
| `ConvergentImpCauchy` | `a ⟶ l ⇒ real_cauchy(a)` |
| `CauchyBounded` | `real_cauchy(a) ⇒ ∃B. ∀n. \|a(n)\| ≤ B` |
| `ConvergentBounded` | `a ⟶ l ⇒ ∃B. ∀n. \|a(n)\| ≤ B` |
| `CauchyClusterPointConverges` | `real_cauchy(a) ∧ real_cluster_point(a, l) ⇒ a ⟶ l` |
| `CauchyConverges` | `real_cauchy(a) ⇒ a ⟶ real_limsup(a)` |
| `CauchyIffConvergent` | `real_cauchy(a) ⇔ ∃l. a ⟶ l` |
| `ConvergesToIffLiminfLimsup` | `(∀n. \|a(n)\| ≤ B) ⇒ (a ⟶ l ⇔ real_liminf(a) = l ∧ real_limsup(a) = l)` |

## Mechanics

- **Statements** are text: the convergence relation written as its
  notation `⟶`, the ℝ names resolved through their mints, ℕ's universe
  `𝕌` pinned at the index type, and ℝ declared as the domain of an
  unanchored `&` (`vocab.go`).
- **Cites** are typed references to entry vars, all of them.
- **The CNF cache** is one shared `real_sequences.cnf.pb` for the
  family; `family.go` carries the record and GC recipes.
