# real_function_limits — limits of real functions at a point

A function `f : ℝ → ℝ` tends to `l` at `c`, written `f ⟶ l (at c)`,
when its values near `c` end up within any positive distance of `l`:
for every `ε > 0` there is a `δ > 0` such that every `x` with
`0 < |x − c| < δ` has `|f(x) − l| < ε`. The point `c` itself is
excluded — a limit is about the values NEAR a point, and `f(c)` plays
no part. This is the ε-δ chapter, the function-side twin of
`real_sequences`' ε-N: there the terms past an index lie within the
distance, here the values on a punctured ball around the point do, and
the proofs are the management of an `ε` and of the `δ` that answers it.

## How the chapter is organized

**The relation is the object.** `real_limit_at(f, c, l)` is a three-place
relation and every statement names the limit it is about — `f ⟶ l (at c)
∧ g ⟶ m (at c) ⇒ (λx. f(x) + g(x)) ⟶ l + m (at c)` — so no theorem
carries an existence side condition. "The same limit" is an equation
between the limit PREDICATES: `real_limit_at(f, c)`, the constant applied to
the function and the point, is the predicate "is a limit of f at c",
and `real_limit_at(f, c) = real_limit_at(g, c)` says the two functions have the
same limits — with uniqueness, the same limit or none — with no case on
whether a limit exists.

**No value operator is minted.** A `lim_at(f, c)` would be a chosen
value, meaningful only when a limit exists, and every theorem about it
would carry that existence as a hypothesis. Where one is wanted it is a
second definition beside this one — `lim_at(f, c)` the chosen `l` with
`f ⟶ l (at c)` — with two bridges, `f ⟶ l (at c) ⇒ lim_at(f, c) = l` by
uniqueness and `(∃l. f ⟶ l (at c)) ⇒ f ⟶ lim_at(f, c) (at c)` by
choice, the pairing the extrema chapter already has in `real_sup` and
`real_has_sup`. Nothing here moves when that is added.

**Local hypotheses are stated on a given radius.** "`f ≤ g` near `c`"
is written with the radius as an outer binder — `&0 < d ∧ (∀x. &0 <
|x − c| ∧ |x − c| < d ⇒ f(x) ≤ g(x)) ⇒ …` — never as `∃d`: the two say
the same thing, since `∀d. (P d ⇒ Q)` is `(∃d. P d) ⇒ Q`, and the
outer binder hands the proof its radius without an existential to open.

**Filters are not the route.** The chapter fixes `(at c)` as the
punctured neighbourhood of `c` directly. A limit along a filter — one
definition covering sequences, functions at a point and limits at
infinity — would have this chapter's relation as its instance at the
punctured neighbourhoods of `c`, and every statement here would read
the same.

## The movements

**1. Two limits on one ball.** An argument that plays two limits
against each other needs the ball the two share — for every `ε`, one
punctured ball on which both functions are within `ε` of their limits
— and, to reach a contradiction or a comparison, a POINT of it:
`c + d/2`, halfway out along a radius `d`. Each is a lemma of its own;
the algebra and the order movements stand on them.

**2. The elementary limits.** The two limits that need no other limit:
a constant function tends to its value, any radius answering any `ε`,
and the identity tends to the point, `ε` itself being the radius.

**3. The algebra of limits.** The negative: where `f ⟶ l (at c)`,
`(λx. −f(x)) ⟶ −l (at c)`, and the same radius answers the same `ε`,
since `|−f(x) − (−l)| = |f(x) − l|`. Two limits at one point share one
ball: for every `ε` the definition hands each its own punctured ball,
and the ball of the smaller radius serves both — on it both functions
are within `ε` of their limits. The sum: where `f ⟶ l (at c)` and
`g ⟶ m (at c)`, `(λx. f(x) + g(x)) ⟶ l + m (at c)`: on the ball the two
limits share at `ε/2` each function is within `ε/2` of its limit, and
the triangle inequality puts `f(x) + g(x)` within `ε/2 + ε/2 = ε` of
`l + m`. The difference is the sum of `f` and `−g`, whose limit
`l + (−m)` is `l − m`, so it needs no `ε` of its own. The product:
where `f ⟶ l (at c)` and `g ⟶ m (at c)`, `(λx. f(x) · g(x)) ⟶ l · m (at c)`.
For any sequence approaching `c` while avoiding it, the two composed
sequences tend to `l` and `m`. Their product tends to `l · m` by
`real_sequences.LimitMul`, and the sequential characterization gives
the function limit. A scalar multiple is the product with a
constant function:
`k · f` is `(λx. k) · f` and the constant tends to `k`, so it needs no
`ε` of its own. The reciprocal: where `f ⟶ l (at c)` and
`l ≠ 0`, `(λx. real_inv(f(x))) ⟶ real_inv(l) (at c)`. On one punctured
ball `f` stays within `|l|/2` of `l`, so `|f(x)|` exceeds `|l|/2`; on a
second, `f` is within $\eta = \frac{\varepsilon \cdot \lvert l \rvert \cdot \lvert l \rvert}{2}$ of `l`; on the smaller of the two,
$\lvert 1/f(x) - 1/l \rvert = \frac{\lvert f(x) - l \rvert}{\lvert f(x) \rvert \cdot \lvert l \rvert} < \frac{\eta}{(\lvert l \rvert / 2) \cdot \lvert l \rvert} = \varepsilon$.

**4. Order, uniqueness and locality.** Limits respect `≤` on a
punctured ball: where `f ≤ g` at every point of the punctured ball of
radius `d` around `c`, and `f ⟶ l (at c)`, `g ⟶ m (at c)`, then
`l ≤ m`. Were `m < l`, half the gap is an `ε`, and at a point of a
ball where both limits are within `ε` and `f ≤ g` the values would
cross — `f` above `l − ε` and `g` below `m + ε`, the same number. The
ball is the one the two limits share, cut down to the smaller of its
radius and `d`, and the point is the one halfway out along that
smaller radius. Uniqueness is its corollary: a function lies below
itself on every ball, so each of two limits of `f` at `c` is at most
the other — a limit is one number. The squeeze pins a value between two: where
`f ≤ g ≤ h` at every point of the punctured ball of radius `d`, and `f`
and `h` both tend to `l`, so does `g`. On the ball the two outer limits
share at `ε`, cut down to the smaller of its radius and `d`, both `f`
and `h` are within `ε` of
`l`, and `g` is pinned between them — `l − ε < f(x) ≤ g(x) ≤ h(x) < l + ε`
— so the same ball answers `ε` for `g`. Locality is the squeeze's
corollary: two functions that agree on a punctured ball around `c` have
the same limits there, `real_limit_at(f, c) = real_limit_at(g, c)`. A function
that agrees with `f` near `c` is pinned between `f` and `f`, so by the
squeeze at `(f, g, f)` every limit of `f` is a limit of `g`; the same
lemma read from `g` to `f` gives the converse, and function
extensionality equates the two predicates. Sign preservation runs the
order the other way, from the limit to the values: a function with a
positive limit at `c` is positive on some punctured ball around `c` —
the limit read at `ε = l` keeps `f(x)` within `l` of `l`, so above 0
(`real_derivative` reads it off the difference quotient).

**5. The sequential characterization.** A function limit read along
sequences — the bare `a ⟶ c` here is real_sequences' limit of a
sequence, and `f ∘ a` the sequence of values `f(a(n))`: where
`f ⟶ l (at c)`, every sequence `a` that tends to `c` without touching
it — `a(n) ≠ c` for every `n` — is carried by `f` to a sequence tending
to `l`, `f ∘ a ⟶ l`. The `δ` the function limit hands
over for `ε` is the `ε` the sequence limit is asked for: past the index
it answers with, every term is within `δ` of `c` and is not `c`, so it
lies in the punctured ball, where `f` is within `ε` of `l`. The converse
holds too: a function that carries every such sequence to a sequence
tending to `l` tends to `l` at `c`. It is proved by contradiction — an `ε`
the function limit fails at hands over, for every `n`, a point within
`1/(n + 1)` of `c`, not `c` itself, where `f` is at least `ε` from `l`;
those points form a sequence tending to `c` without touching it —
real_sequences' `WithinReciprocalConverges`, where the Archimedean
property makes `1/(n + 1)` shrink below every `ε` — which `f` carries
nowhere near `l`.

## Members

| entry | statement |
|---|---|
| `RealLimitAtDef` | `f ⟶ l (at c) ⇔ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < δ ⇒ real_abs(f(x) − l) < ε` |
| `PuncturedBallPoint` | `&0 < d ⇒ &0 < real_abs((c + d / &2) − c) ∧ real_abs((c + d / &2) − c) < d` |
| `LimitAtCommonRadius` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < δ ⇒ real_abs(f(x) − l) < ε ∧ real_abs(g(x) − m) < ε` |
| `LimitAtConst` | `(λx:real. k) ⟶ k (at c)` |
| `LimitAtId` | `(λx:real. x) ⟶ c (at c)` |
| `LimitAtNeg` | `f ⟶ l (at c) ⇒ (λx:real. −f(x)) ⟶ −l (at c)` |
| `LimitAtAdd` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ (λx:real. f(x) + g(x)) ⟶ l + m (at c)` |
| `LimitAtSub` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ (λx:real. f(x) − g(x)) ⟶ l − m (at c)` |
| `LimitAtMul` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ (λx:real. f(x) · g(x)) ⟶ l · m (at c)` |
| `LimitAtScale` | `f ⟶ l (at c) ⇒ (λx:real. k · f(x)) ⟶ k · l (at c)` |
| `LimitAtInv` | `f ⟶ l (at c) ∧ l ≠ &0 ⇒ (λx:real. real_inv(f(x))) ⟶ real_inv(l) (at c)` |
| `LimitAtLessEq` | `&0 < d ∧ (∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < d ⇒ f(x) ≤ g(x)) ∧ f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ l ≤ m` |
| `LimitAtUnique` | `f ⟶ l (at c) ∧ f ⟶ m (at c) ⇒ l = m` |
| `LimitAtSqueeze` | `&0 < d ∧ (∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < d ⇒ f(x) ≤ g(x) ∧ g(x) ≤ h(x)) ∧ f ⟶ l (at c) ∧ h ⟶ l (at c) ⇒ g ⟶ l (at c)` |
| `LimitAtLocal` | `&0 < d ∧ (∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < d ⇒ f(x) = g(x)) ⇒ real_limit_at(f, c) = real_limit_at(g, c)` |
| `LimitAtPositive` | `f ⟶ l (at c) ∧ &0 < l ⇒ ∃d. &0 < d ∧ ∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < d ⇒ &0 < f(x)` |
| `LimitAtImpSequential` | `f ⟶ l (at c) ∧ (∀n. a(n) ≠ c) ∧ a ⟶ c ⇒ f ∘ a ⟶ l` |
| `SequentialImpLimitAt` | `(∀a. (∀n. a(n) ≠ c) ∧ a ⟶ c ⇒ f ∘ a ⟶ l) ⇒ f ⟶ l (at c)` |

## Mechanics

- **Statements** are text: the limit relation written as its notation
  `f ⟶ l (at c)`, the sequence limit `a ⟶ l` of real_sequences and
  composition `∘` beside it, every name resolved through its mint; a
  pointwise-built function is a parenthesized λ, `(λx:real. f(x) + g(x))`.
- **Cites** are typed references to entry vars, all of them.
- **Two engine facts shape every ε-δ body** — the order of a proof's
  first steps and the restatement of an obtained radius's `∀` half;
  `definitions.go`'s header states them.
- **The CNF cache** is one shared `real_function_limits.cnf.pb` for the
  family; the family manifest carries the record and GC recipes.
