# `prover/solver/omega` — arithmetic automation for `num`, `real`, and `int`

`omega` is XuGo's arithmetic decision/normalization layer: the `ring`,
`linarith`, and `omega` of a Lean/Coq/Isabelle prover, built so every
result bottoms out in a real kernel `*Thm` (there is no kernel oracle). It closes
the large class of leaf goals that are pure linear/semiring arithmetic — the
`ring`/`omega`/`simp` one-liners a human closes without thought, which the engine
otherwise forces through manual lemma-chaining.

Everything is **proof-producing**: a decision procedure runs an *untrusted* model
to find a certificate, then **replays** that certificate as a real kernel
derivation. A miscomputed certificate degrades to "no proof", never to an unsound
one.

## What it decides

- **`num`** — semiring equalities and linear comparisons, with integer
  (Presburger-style) reasoning over `num`.
  - `ring` (linear + full multivariate) and `norm_num` (all six comparisons +
    `divides`), both proof-producing.
  - `linarith` decides `< ≤ = ≠ > ≥` over `num` via ℚ-Farkas refutation with
    real replay — over the **monomial basis**: each comparison side is read as
    a polynomial over canonical monomial atoms, so hypothesis equations with
    polynomial content (an induction IH like `2·A = n·suc(n)`) combine with
    the goal by linear reasoning alone (see
    [`linarith`](#linarith--ℚ-farkas-over-the-monomial-basis)).
  - The integer layer (Presburger-style reasoning *over* `num` — distinct from
    the `int` *type* below): gcd rounding cuts (`LessEqRightDivEq` +
    `DivModUniq`), exact elimination of equations ahead of Fourier–Motzkin
    (`n = 2·q + 1 ∧ 1 < n ⊢ 3 ≤ n`), `notDivides` (`ModEqZero`), and
    truncated subtraction (monus) via a `LessEqTotal` case split.
  - Operator coverage: monus, `nat_max`/`nat_min`, raw `COND`,
    `nat_div`/`nat_mod`, `nat_pow`, `factorial`, `predecessor`,
    `nat_even`/`nat_odd`, `nat_dist`, plus equality-hypothesis substitution
    and bounded-variable enumeration.
  - `nat_pow` with a LITERAL exponent is read in the monomial basis like
    `real_pow`/`int_pow` (`natPowChainUnfold`, wired in `pow_basis.go`):
    `nat_pow(a + b, 2) = nat_pow(a, 2) + 2·a·b + nat_pow(b, 2)` closes bare;
    the simp step itself unfolds only `c ≤ 1` (`expSimp`).
  - Exposed as a single engine move, `arith`.
- **Three passes shared by ℝ and ℤ, beside the linear layer.**
  - The **pairwise products** of the context's differences — the step Lean's
    `nlinarith` adds to `linarith` (`real_products.go`, `int_products.go`):
    every comparison the refutation holds, the negated goal included, is a
    nonnegative difference, and the product of two is nonnegative (LessEqMul /
    MulPos), injected as hypotheses for one linear run and cut back. Closes
    `x·y = &1 ∧ &0 < x ⊢ &0 < y`, `a ≤ b ∧ c ≤ d ⊢ a·d + b·c ≤ a·c + b·d`,
    a strict difference times a non-strict one `&0 ≤ t ∧ t ≤ &1 ∧ x < y ⊢
    x ≤ t·x + (&1 − t)·y` (the strict fact weakened, `realWeakenLt`, which
    reads neither side of it). Runs last in the decide
    chain, only where a constraint carries a product; twelve facts at most;
    and model first — the product rows are read as linear forms with no
    proof and a ℚ-Farkas refutation found there is the only reason to prove
    a product (one kernel FOIL per pair) and replay, which is what keeps a
    wide context's hundreds of declining questions at the linear layer's
    cost (the engine's TestInspect_ArithProbeOnWideRealContext times such a
    context; with every product proved first the same inspect took several
    times as long).
  - A **num hypothesis read through its cast** (`domain.go` liftHyp,
    `realLiftNumHyp` / `intLiftNumHyp`): `a ≤ b` is the row `&a ≤ &b`, the cast
    pushed to the leaves (`&(a + 1)` is `&a + &1`), a strict `a < b` also its
    integrality `&a + &1 ≤ &b`. So `a ≤ b ⊢ &a ≤ &b`, `b < a + 1 ⊢ &b ≤ &a` and a
    divisor bounded by a num fact (`4 ≤ n ∧ x·x ≤ &4 ⊢ x·x ≤ &n`) close with
    nothing cited. The goal-side of_num drop (`realProveOfNum`) stays hyp-free
    on purpose: the arith step drops a hypothesis decided ⊤ under the others,
    and a comparison of images decided from num facts the rows did not hold
    took with it what the refutation still needed (measured on
    real_trigonometry.CosTaylorBounds).
  - The ring normal form as a **rewrite** (`ring_nf.go`,
    `RingNormalizeRewrite`): every arithmetic subterm to the sum of monomials
    the normalizer reads, unit coefficients and a zero constant elided — the
    `ring_nf` engine move and the `RingNf()` step, beside the closer.
- **The zero test, at every carrier.** Whether a term is zero is asked on
  both sides of the turnstile, in either spelling of its equation, and of a
  product through its factors.
  - A target that **denies a variable a value** — `¬(v = e)`, and on ℕ a
    comparison `0 < v` implies linearly (`0 < v`, `1 ≤ v`, `v > 0`) — is
    decided by the value read into the hypotheses, the reading a hypothesis
    `v = e` gets (`denied_value.go`): the equation joins the context as the
    definition it would be there, and a hypothesis it then reads ⊥ refutes
    it. `0 < g·u ⊢ 0 < u` over ℕ, `g·u = &1 ⊢ ¬(u = &0)` over ℤ, ℝ and ℂ,
    `0 < r ∧ r = g·v ⊢ 0 < v`.
  - **On ℕ a product is zero exactly where a factor is** (`nat_products.go`,
    `nat_arith.MulEqZero`): a hypothesis `a·b = 0` splits into `a = 0 ∨ b = 0`,
    and a product of the sequent whose factors are shown positive joins
    the enrichment's facts as `0 < a·b`, for one more linear run and for
    the case split (so `a ≠ 0 ∧ t ≠ 0 ⊢ suc(a·t − 1) = a·t` closes in its
    monus's branch) — the twins of ℤ's and ℝ's MulEqZero split and sign
    rows, one law on ℕ.
  - **A power is zero only where its base is.** On ℕ a power of a base
    shown positive is positive, and joins the same facts
    (`nat_order.PowPositive`), and a hypothesis `bᵉ = 0` gives `b = 0` and
    `0 < e` (`nat_arith.PowEqZero`). Over ℝ the evidence that a term is not
    zero reads a power by its base (`real_nonzero.go` `realPowerNonzero`:
    `|x| > &0`, `PowPos`, `AbsPow`), so a divisor `rⁿ` cancels on r's
    evidence, and a hypothesis `xⁿ = &0` gives `x = &0`
    (`realProveZeroPower`). At a field's structure ring both are
    `field.PowEqZeroOn` (`structure_refute.go`).
  - **A zero on either side.** The folds that carry a zero test through an
    operator (`inv x = &0`, `−x = &0`, `¬(x = &0)`, `int_rem(m, n) = &0`)
    read their equation through one matcher (`zero_sided.go`), so
    `¬(&0 = g · inv q)` closes as `¬(g · inv q = &0)` does; the square
    `¬(x = &0) → &0 < x·x` is taken after the inverse and the negation have
    been folded away; and over ℝ a hypothesis `a / b = &0` splits as the
    zero product `a · inv b` it is.
  - **A structure ring refutes** (`structure_refute.go`): an equation that,
    joined to the context's equations, combines to one a resident
    disequality denies is decided ⊥, and a field denies `one = zero` by
    itself (`field.OneNotZeroOn`). At a field a product, an inverse and a
    quotient of terms that are not zero are not zero, and a zero product
    with a nonzero factor gives its cofactor. See
    [The structure ring](#the-structure-ring--the-ring-at-a-ring-or-field-record-fact).
  - **A modulus and its argument vanish together** (`modulus_zero.go`):
    what the carrier's ring shows of a modulus's argument is a fact for
    ℝ's rows, and what the rows show of a modulus is a fact for the ring.
    See [The modulus of another carrier](#the-modulus-of-another-carrier).
- **A common factor, scaled by and cancelled, at every carrier.** A
  comparison is read by the factors its two sides share, up to the order
  and the grouping of the products (`shared_factors.go`): `P·a ⋈ P·b`,
  P the product of the shared factors and a, b the products of the rest.
  - **ℕ** (`nat_scaling.go`): a goal `l ≤ r` or `l < r` follows from
    `a ⋈ b` (for `<` with P shown positive), two products with no common
    factor from their factors compared pairwise, and two sums summand by
    summand; a goal that is no comparison of two products follows from
    the hypotheses' comparisons scaled by the cofactors the sequent
    spells beside them (`natHypScalings`: for a hypothesis `a ≤ b` and a
    product that holds a's factors or b's with a cofactor F left over,
    `F·a ≤ F·b`, the products of each side multiplied out over its sums).
    A hypothesis `l = r` or `l ≤ r` gives `a ⋈ b` where P is shown
    positive (`nat_arith.MulEqLCancel`, `nat_order.LessEqMulCancel`), and
    `l < r` gives `a < b` and `0 < P` outright
    (`nat_order.LessThanMulCancel`); a negated order is read as the
    order it is. A goal `a ⋈ b` follows as well where the hypotheses
    prove `P·a ⋈ P·b` linearly and state it in no one of them
    (`natProveCancelled`), P ranging over the factors that put both
    scaled sides among the products the hypotheses spell. ℤ and ℝ have
    the pair in their monotone handlers, their cancellation and their
    products pass.
  - **An equation over ℝ** (`real_cancel.go` `realCancelEquation`) cancels
    a shared factor on any evidence that it is not zero
    (`real_ring.MulLeftCancel`), a factor at a time.
  - **At a field's structure ring** (`structure_refute.go`
    `cancelledEquations`) a context equation whose sides share a factor
    shown not zero gives the equation of the rest, by the cancellation
    that reads a zero product.
- **ℝ (`real`).** The algorithm/extraction code is a near-mechanical twin of
  the `num` stack (shared through the `Domain` seam).
  `serve.InstallRealBundle()` binds every `RealLemmaBundle` field to a
  theorem of the library over ℝ, and `initEngine`
  (`engine/cmd/xugo/main.go`) installs it at startup after the nat bundle.
  The engine's shape gate `goalHasArithContent` recognizes real `+` / `*` /
  comparison content when `omega.RealArithEnabled()` (a real bundle is
  installed), the decide leaves dispatch per atom by operand type, and a real
  leaf with no theorem bound panics at the placeholder seam (production
  installs no fabricator). See [The real (ℝ) layer](#the-real-ℝ-layer).
- **`int` (the integer *type*) — the linear core and the non-Cooper
  extensions.**
  A self-contained `Domain`-seam twin of the real layer (`int*.go`): `intDomain`
  + `IntLemmaBundle` + int ring / discharge / simp / signed-normalizer. It does
  **not** reduce through `real_of_int` — it runs the shared untrusted model on int
  vocabulary and replays with int-native order lemmas, depending on neither the real
  layer nor a `real_of_int` bridge. It covers the linear `+ − * < ≤ = ≠ > ≥`
  fragment with `&n = int_of_num` literals, **total subtraction/negation**
  (`int_sub`/`int_neg`, via a signed normalizer + relation move-across, goal- and
  hyp-side), **ℤ-discreteness** strengthening (`x < y ⊢ x + &1 ≤ y`), the **rank-1
  GCD-equality test** (general `Σcᵢxᵢ = k` with `gcd ∤ k`) and **gcd rounding cut**
  (`&4 ≤ 3·x ∧ 3·x ≤ &5 ⊢ ⊥`) — both integer-unsat though ℚ-satisfiable, built on
  discreteness with no int division — the **exact elimination of equations**
  (`n = &2·q + &1 ∧ &1 < n ⊢ &3 ≤ n`, the step shared with `num`), and a full set of **structural operator
  handlers**: the `int_abs`/`int_max`/`int_min`/
  `int_sgn` + raw-`COND` case splits, the disjunctive/`≠`/`⇒` **hypothesis splits**, a
  formula-level **boolean split** over comparison atoms, **`int_pow`** literal-exponent
  unfold, equality-hypothesis **substitution** into opaque atoms, and two-sided
  **bounded enumeration**. Beyond the linear core it also has the **full multivariate
  ring** (`(x+y)² = x²+2xy+y²`, shared with ℝ/num via the `ringVocab` seam) and its
  **signed** extension (`(x−y)² = x²−2xy+y²`, sub/neg in nonlinear position via a FOIL
  that keeps the `P+(−N)` invariant), the
  **`int_of_num` homomorphism collapse** + **`Image` sign split** (closing
  `&0 ≤ x·x`), **`int_divides`** (goal witness, `int_divides(&2,&1) ⊢ ⊥`, and the
  parity `2∣x ∧ 2∣(x+1) ⊢ ⊥` through the elimination of equations), and **Euclidean
  `div`/`rem`** (literal eval `div(&7,&2) = &3` via `DivModUnique`; the `&0 ≤ rem < n`
  bounds for a symbolic positive dividend via `DivisionIdentity`/`RemNonneg`/`RemBelowDivisor`,
  and the general `&0 ≤ rem < int_abs(n)` bound for a **negative / unknown-sign** divisor via
  `RemUpperAbs`, composing with the int_abs split), **monotone scaling / sign-of-product**
  (`a≤b ∧ &0≤c ⊢ c·a≤c·b` via `LessEqMulLeft`, and a product against its own BARE
  factor read as the scaling with `&1` in the empty slot — `&0<x ∧ x≤&1 ⊢ x·x≤x`,
  `intMonoScaleOne` / `realMonoScaleOne`; **all four sign combinations** of `x·y ⋈ &0`
  via `LessEqMul`/`MulPos` + the negation reduction; the two-sided product bound
  derived via `LessEqTrans`), and the **integral domain** (`MulEqZero`: `x·y=&0 ⊢ x=&0∨y=&0`,
  the square `x·x=&0 ⊢ x=&0`, and strict positivity `x≠&0 ⊢ &0<x·x`) — the sign-known
  fragment of nonlinear `< ≤`.
  The agent writes it through a first-class DSL surface (3-way operator
  dispatch + unary `−` + type-directed `&`). `serve.InstallIntLemmaBundle()`
  (called from `InstallIntBundle`) binds the `IntLemmaBundle`: library members
  directly (`fromEntry`), definitions (`defNorm`), general shapes
  (`fromGeneral`), and `omega.IntOfRealThm` lifts of sources over ℝ made at
  install. `initEngine` calls `serve.InstallIntBundle()` after the nat and
  real installs, the engine's shape gate (`goalHasArithContent`) recognizes
  int `+`/`*`/comparison content via `omega.IsIntArithContent` when
  `omega.IntArithEnabled()`, and `composeArithLeaves` dispatches per atom by
  operand type. The unified dispatch uses the **NoSignSplit** variant
  (`intArithDecideLeafNoSignSplit`): it drops `intImageSplit` and
  `intProveBoundedEnum`, which fan out 4-way × per-atom × multi-pass on goals
  carrying many `int_div`/`int_rem`/`int_abs`/COND subterms, and keeps every
  other handler (linear / ring / divrem / monotone / divides / Gaussian
  elim). The bool split's branches (`intProveBoolBranch`) take the same
  variant, for the same reason. The sign split and the bounded enumeration
  stay reachable through the explicit `IntArithDecideWithHyps` entry. Same
  soundness contract as nat / real: production installs no placeholder
  fabricator, so an int leaf with no theorem bound panics at the seam. See
  [The integer (`int`) type layer](#the-integer-int-type-layer).
- **Not decided.** Full ℤ completeness (an equation with no atom of
  coefficient ±1, cuts on rows Fourier–Motzkin itself derives, Cooper QE —
  beyond ℚ-Farkas, discreteness, the gcd-equality test, the rounding of a
  row and the elimination of equations) and multi / nested-denominator ℝ
  field clearing. See
  [Future work](#future-work).

## What it provides

### The `arith` engine move

The user/agent surface is one structural move, `arith`, shape-gated on the goal
containing any arithmetic content (a `+`/`*` subterm or a comparison atom,
anywhere — including buried atoms; real and int content count when their
bundle is installed). It is the composite `_Arith → _TrivialSimplify`:

- `_Arith` applies omega's hyp-aware decider to the goal — the conclusion under
  all hyps, each hypothesis under the *other* hyps only — as a single
  deep+fixpoint rewrite. A fully-decidable goal collapses to `⊢ ⊤`; a partial
  decision advances the conclusion to a simpler child.
- `_TrivialSimplify` closes the residual `⊢ ⊤`.

The decider's hypotheses pass through a hyp-FREE pre-simp first
(`NewArithCtxWithPolicy` → `preSimpHyps`): the identity/numeral folds, the
sub/neg move-across, and the decision of a GROUND comparison atom
(`groundComparisonDecide`: `1 ≤ 2`, `2 ≠ 0`, `&1 ≤ &2` → ⊤/⊥ with no
context), so a law's numeral guard is folded out of a Horn premise before the
case-split engine meets it. Nothing that consults a hypothesis may run there
— a hyp under its own assumption is trivially ⊤.

A cascade like `a + Cond(a=a, 0, 1) → a` resolves in one pass (decide `a=a→⊤`,
fold `Cond(⊤,0,1)→0`, reduce `a+0→a`). Each step records under its own proto tag
(`arith` / `trivial_simplify`), kept disjoint from `basic` so replay of omega's
own foundation theorems never re-enters omega.

### Algorithm entry points

The package also exposes the deciders directly:

| function | file | proves |
|---|---|---|
| `RingProve`, `RingProveFull` | `ring.go` | `⊢ e₁ = e₂` over the semiring (linear / full multivariate). `=` is ⊤-only — the ⊥ side is linarith/omega's job. |
| `LinProve(hyps, goal)` | `nat_linarith.go` | `< ≤ = ≠ > ≥` over ℚ-Farkas on the monomial basis |
| `OmegaProve(hyps, goal)` | `nat_linarith.go` | the integer extension (needs integrality / divisibility) |
| `ArithDecideWithHyps(hyps)` | `engine.go` | the unified deep+fixpoint `prop.Rewrite` behind `arith` |
| `Int/RealRingProve`, `Int/RealRingProveFull`, `Int/RealLinProve` | `ring.go`, `int_lemmas.go`, `int_linarith.go`, `real_linarith.go` | the ℤ/ℝ ring (linear **and** full multivariate) + linarith deciders |
| `Int/RealSignedNormalizeProof(t)` | `subneg.go` | `⊢ t = P + (−N)` (P,N positive) — total sub/neg → two-positive-sided form |

`prover/tactic` wraps these as `RingTactic` / `LinarithTactic` / `OmegaTactic` /
`ArithTactic`; the engine `arith` move is `ArithTactic` + `TrivialSimplify`.

## How it works

### Decision, then replay

The architecture everywhere is *untrusted model → kernel replay*:

1. compute a canonical form / refutation certificate with plain integer
   arithmetic (no `*Thm`);
2. replay it as real kernel congruence/inference, using the library's theorems
   as the material.

The model's integers are exact (`_Integer`, integer.go: a machine word, and
past it a big integer): a numeral's value, a coefficient, a Fourier–Motzkin
row entry and a Farkas multiplier are the numbers they denote at any size.
The replay evaluates numerals on their bit-trees, which have no bound, so a
model that wrapped at 2⁶³ or 2⁶⁴ would name a normal form the replay does not
reach and the kernel would refuse the step that joins them. A row holds its
entries as words (`_Vector`) until one outgrows a word, so elimination on
ordinary systems runs on plain machine arithmetic, checked. A machine word
on its own is kept only for a count that a cap already bounds — an exponent
to unfold, a range to enumerate (`BitsToUint`).

`omega` rests on `ring`: replaying a Farkas certificate requires proving "the
scaled-and-summed sides equal the canonical linear form", which *is* `ring`'s
job.

### `ring` — commutative-semiring normalizer

`ring.go` computes the canonical sum-of-monomials form (each monomial =
numeral coefficient × sorted product of variables) as an untrusted model,
then re-derives `⊢ t = canonical` with kernel congruence. The additive normal form is produced by this model-then-reprove layer
— **not** by the generic AC sorter, which cannot fold coefficients or merge like
terms; the prop AC engine is reused only for the monomial-factor sort
(`MulSortRewrite`, `ring.go`).

### `norm_num` — numeral evaluation

`nat_norm.go` does proof-producing `+ * < ≤ = > ≥ ≠` and `divides` over
`_0`/`bit0`/`bit1` literals via bit recursion, built from the digit-by-digit
laws the ℕ chapters state (`nat_arith.NumeralAdd`, `nat_arith.NumeralSuc`,
`nat_arith.NumeralEq`, `nat_order.NumeralLessThan`, `nat_order.NumeralLessEq`).
The multiplication leaves
are derived from `nat_arith.Bit0`/`nat_arith.Bit1` + `nat_arith.MulClauses` +
`nat_arith.RightAddDistrib` (going through `ring` here would be circular).

### `linarith` — ℚ-Farkas over the monomial basis

`linarith.go` extracts linear constraints (`linForm`), runs Fourier–Motzkin to
find non-negative Farkas coefficients (untrusted — re-checked by the replay), and
`nat_linarith.go` replays the certificate: scale each hypothesis by a
monotonicity lemma, sum pairwise (`LessEqAdd2`/`LessThanAdd2`), ring-normalize both
combined sides, and close on the numeric contradiction.

Over `num`, the extraction reads every comparison side as a **polynomial over
canonical monomial atoms** (`Domain.polyMul`, domain.go — the checked model
twin of the full ring's `mMul`): a nonlinear product `atom·atom` distributes
into Compare-sorted monomial product terms instead of being taken whole as one
spelling-keyed opaque atom. `m·p` and `p·m` are the SAME unknown, `suc` folds
inside products, and a hypothesis equation with polynomial content combines
with the goal in the shared basis — for instance the Gauss-sum induction leaf
`{2·A = n·suc(n)} ⊢ 2·(A+suc n) = suc(n)·suc(suc n)`, one
unit-λ Farkas combination once both sides live over `{A, n·n, n}`. The
decidable fragment this completes: goals whose refutation is a linear
combination of the (ring-normalized) premises over ℕ[atoms], plus the injected
`0 ≤ monomial` rows, plus the integer layer below. Deliberately OUT: scaling a
premise by a variable (Gröbner territory — search power, not conditioning) and
sign-free nonlinear monotonicity (`a≤b ⊢ a²≤b²`, true RCF; the sign-known int
fragment below covers the hypothesis-guarded cases).

The proof mirror stays branch-for-branch: `normalizeProof` expands the same
products through `mulProofFull` (asserting agreement with the model multiply),
so the discharge replay's normal forms coincide with the rows' by
construction. Resource fuse (`natPolyMul`, ring.go): a pathological monomial
count declines the expansion, and BOTH sides then fall back to the opaque-atom
reading of that product. Coefficients are exact at any size (`_Integer`,
integer.go), as the numerals the proof side evaluates are. `real` reads products over the same basis (`realRing.polyMul`, wired
in `real_lemmas.go`): with no nonnegativity rows a monomial is one more free
unknown, so the ℝ fragment is "linear combinations of ring-normalized
premises over ℝ[atoms]" — a product hypothesis combines with the goal
instead of being dropped, and an ordering leaf whose reasoning is linear over
a product closes without the product being named first. A monomial's SIGN reaches the rows too, through the sign-row pass
(`real_sign_rows.go`, below). `int` reads products over the basis the
same way (`intRing.polyMul`, wired in `int_lemmas.go`; a product of integers
is an integer, so the integer layer's cuts see a monomial as one more
integer unknown). The bounded-enumeration gates ask `genuinelyLinear` —
linear AND no product atom — so `x·x ≤ 4` under `0 ≤ x ≤ 2` is still
enumerated rather than handed to a linarith that cannot relate the unknown
`x·x` to x's bounds.

### The monomial sign rows (ℝ, ℤ)

Over ℝ a monomial is an unknown with NO sign — `buildAll` injects the
`0 ≤ x` row per atom only over `num`, where every term is nonnegative. So a
refutation that turns on `&0 ≤ a·b` finds no such row in the linear layer,
even when the context states both factors' signs: the sign-known handlers
(`realProveSignedProduct`) answer that question only about a GOAL.

`real_sign_rows.go` supplies exactly those rows, as extra constraints built
before `realBuildAll`. For each product monomial in the constraint set:

- the **square reading** — every base atom occurs an even number of times, so
  the monomial IS a square `t·t` (`RealRingProveFull` proves the regrouping)
  and SquareNonneg gives `&0 ≤ m` with no hypothesis at all. This is what
  closes `x·x ≤ y ⊢ &0 ≤ y` and `x·x + y·y = &0 ⊢ x·x = &0`;
- the **factors' signs** — every base atom has a sign among the constraints
  (`&0 < f`, `&0 ≤ f`, `f < &0`, `f ≤ &0`), folded pairwise through
  LessEqMul / MulPos and the neg-order flips, exactly as
  `realProveSignedProduct` folds a binary product on the goal side.

The same pass prices a `&n` coercion atom, which is nonnegative because `n`
is (the of_num order bridge read against num's `0 ≤ n`).

The derived proof is assembled from the SOURCE constraints' own proofs
(`realCanonAssume`, which already honours `Hyp`/`HypProof`), so its
hypotheses are theirs and the refutation's stay ⊆ the goal's — including when
a source was projected out of a conjunction.

A pair of factors differing in STRICTNESS (`&0 < a` with `&0 ≤ b`) folds to
the non-strict sign of the product, the strict fact weakened first
(`realWeakenLt`: the linear prover's `a < b ⊢ a ≤ b` over two variables,
instantiated at the fact's sides, so no bundle field is needed and no
normalizer reads the sides). An inverse standing ALONE in a linear form gets a
row as an inverse factor does, from its argument's sign, so `(M + &1) / x` —
the monomials M·inv(x) and inv(x) — is priced from `&0 ≤ M` and `&0 < x`. And a
product of inverses is priced from the product: the inverse basis reads
inv(a·b) as the monomial inv(a)·inv(b), so a sign the context states of a·b —
which says nothing of a or of b alone — is the sign of that pair of atoms
together (`realSignPieces`), and `&0 < a·b ∧ &0 ≤ x ⊢ &0 ≤ x / (a·b)` keeps its
row.

Deliberately out: the CONVERSE direction — a FACTOR's sign read off the
monomial's (`x·y = &1 ∧ &0 < x ⊢ &0 < y`) — which is division by a variable,
not a row.

`int_sign_rows.go` is the ℤ twin, identical down to both boundaries, over
LessEqMul / MulPos / SquareNonneg and the int of_num bridge. It runs
AFTER `intPositivizeConstraints`, so the atoms it reads are the ones the rows
below are extracted over. `num` needs no such pass: `buildAll` already injects
`0 ≤ x` per atom there, every num term being nonnegative.

### What the signed normalizer does NOT positivize

`moveAcrossCmp` (`subneg.go`) turns `a − b ⋈ c` into `a ⋈ c + b` so the linear
layer meets positive terms, and its signed FOIL expands a sub inside a product
along the way. That expansion is a LOSS for exactly one shape — a SQUARE. A
`(x−y)·(x−y)` is one unknown with a known sign (the sign rows price it
unconditionally), while its expansion `x² − 2xy + y²` needs `2xy ≤ x² + y²`,
a sum-of-squares fact outside the fragment. So an atom whose every sub sits
inside a square is left alone (`subNegOnlyInSquares`), and
`⊢ &0 ≤ (x−y)·(x−y)` and `(x−y)·(x−y) ≤ c ⊢ &0 ≤ c` both close.

Only a square. Every other product carrying a sub still expands, because there
the FOIL is what relates the product to its factors and nothing else does
(`x·(a−b) ≤ c ⊢ x·a ≤ c + x·b` closes only through it), and a sub in the
additive spine always moves across. The rule is shared by ℝ and ℤ. The
structure ring has no order reading and expands signed squares when
normalizing equations, including `(-x)·(-x) = x·x`.

### `&n` is an atom, not a malformed literal

`Domain.asLiteral` answers "is this a numeral literal", which is a question
about the coerced ARGUMENT — not about the coercion head. Answered on the
head, `&n` with a symbolic `n` would come back *numeral-shaped but inexact*,
which linOf reads as a decline, and a declined side DROPS the whole
constraint: `&n ≤ x ⊢ &0 ≤ x` would have no row to work from. So such a term
is an opaque atom like any other, and over ℝ the sign-row pass prices it (`&n` is
nonnegative because `n` is, through the of_num order bridge and num's own
`0 ≤ n`, needing no bundle field). A numeral-shaped but MALFORMED argument
(non-canonical tower, ≥2^64) still declines, as the field's contract requires:
there the `Refl` bridge the normalizers build for a literal would be invalid.

ℤ mirrors the atomization, and its own sign-row pass prices the atom the same
way.

### The pow basis

`real_pow(t, c)` / `int_pow(t, c)` / `nat_pow(t, c)` with a literal exponent
read as the monomial `t^c` (`pow_basis.go`, `domain.go` `powChainOf`), so a power and a
written-out product are ONE unknown: `real_pow(x, 2) ≤ y` and `x * x ≤ y`
are facts about the same thing. The TERM is untouched — only its linear form
expands — so the pow handlers (sign, base and exponent monotonicity, the
of_num bridge) go on meeting the spelling the author wrote, and none of the
term growth the simp step avoids by unfolding only `c ≤ 1` is incurred.

The lockstep is the **chain**: each domain's unfold proves
`pow(m, c) = m·(m·(…·1))`, the untrusted extraction reads that same chain, and
`normalizeProof` asserts the unfold's right-hand side against
`Domain.powChain` — so a drift in either half is a loud panic, never a silent
divergence between the model and the certificate. The exponent cap is the
unfold's own (`expUnfoldMax`).

`num` has its own chain unfold (`natPowChainUnfold`, `nat_exp.go`): the simp
step's `expUnfold` shortcuts c=1 and c=2 to their own shapes (`m`, `m·m`)
rather than the uniform chain, so the basis takes a separate unfold that
proves the chain for every c. The bounded-variable enumeration keys on a
comparison whose side is nonlinear, which a product monomial still is, so
`x·x ≤ 4` under `x ≤ 2` is enumerated all the same.

### `omega` — the integer layer

`OmegaProve` = `LinProve` over `IntRefuteProof` (`nat_omega.go`). Beyond ℚ-Farkas it adds gcd rounding cuts
(`roundedCut`: one `LessEqRightDivEq` instantiation + `DivModUniq` + `ring` per row)
and grounds gcd-equality contradictions through the nat-native divisibility layer
(`nat_omega.go`: `dvd(d,n) = ∃q. n = q·d`, kept inside pure `num` — it never touches
a divisibility defined through ℤ, which would drag in the int/ℝ subtype tower).
A row whose coefficients share no divisor is not cut: it stands in the terms
it is written in, and the refutation's last step normalizes it with the rows
it is summed with.

#### Equations are eliminated before Fourier–Motzkin

Fourier–Motzkin projects over ℚ, and an equation reaches it as two `≤` rows.
From `n = 2·q + r`, `r = 1` and `2 ≤ n ≤ 2` it eliminates q between the two
rows of the equation, which keeps the rational shadow — the system that
remains has a solution, where q = 1/2 was the only one — and no single input
row rounds. `eliminateEquations` (`equation_elimination.go`) runs first: it solves an
equation for an atom of coefficient ±1, substitutes it into every other row,
and rounds each substituted row by the gcd of its own coefficients
(`2·q ≤ 1` to `q ≤ 0`, `1 ≤ 2·q` to `1 ≤ q`). The atom is an integer whenever
the others are, so nothing is lost, and the rounding is where the
contradiction shows. An equation is an input equation or two inequalities
that meet (`1 ≤ r` and `r ≤ 1`); one with no atom of coefficient ±1
(`2·a = 3·b`) is left to its own two rounded rows.

A row is held as a non-negative combination of **nodes** — the input rows,
and the rows a rounding produced. Substituting adds combinations, which is
arithmetic on multipliers and no proof; only a rounding makes a node, whose
proof (the combination summed by `sumRows`, then `cutProv`) is built when the
final refutation takes it. Fourier–Motzkin's certificate over the eliminated
rows is turned into multipliers of the nodes and replayed as any Farkas
certificate is. The step is the same over ℤ (`intEliminationRefute`), where a
rounding is proved by discreteness.

`proveLinThenInt` and `proveDecAtom` memoize their answers per question for
the length of one arith step (`natLinMemo`, `natDecMemo`, released by
`ReleaseStepMemos`), as the ℝ provers do: a step decides each hypothesis
under the others and each atom once and once negated, round after round over
one context. On the five steps of `nat_parity.UpperHalfCountEven`, dense in
quotients and remainders, 161 of 282 decisions had been made before, and
without the memo the member's replay took twice the processor time.

### Operator handlers

Operators opaque to the linear core are each given a handler — a *simp*
reduction, an *enrichment* (inject derived bounds as hyps, re-run the prover, cut
them back), a *bridge* (rewrite into an already-handled operator), or a *case
split*:

| operator | handling | file |
|---|---|---|
| monus `a − b` | unconditional cancellation/truncation simp (`AddSubLeftCancel`/`SubEqZero`); irreducible `a−b` decided by an `LessEqTotal` case split | `nat_sub.go` |
| `nat_max` / `nat_min` / raw `COND` | split on the guard (excluded middle) | `nat_sub.go`, `engine.go` |
| `nat_div` / `nat_mod` | bounded-atom enrichment (`ModLessEq`/`DivLessEq`/…, and at a divisor shown nonzero Division's bound `nat_mod(m,n) < n` with its identity `m = nat_div(m,n)·n + nat_mod(m,n)`, for either atom) + residue/quotient simp + distribution leaves + symbolic-`n=0` split | `nat_divmod.go` |
| `nat_pow` | literal-exponent unfold to a product chain (auto for the size-safe cases; agent-driven `expand_exp` for `c ≥ 2`) | `nat_exp.go` |
| `factorial` | literal evaluation to a single numeral | `nat.go` |
| `predecessor` | bridge `predecessor n → n − 1` into the monus layer | `nat_sub.go` |
| `nat_even` / `nat_odd` | bridge to `nat_mod(n, 2)`; structural `EvenMul`/`EvenAdd` for nonlinear parity | `nat_sub.go` |
| `nat_dist` | bridge `nat_dist(m,n) → (m−n)+(n−m)` into the monus layer | `nat_sub.go` |
| `v = e` hyp, at every carrier | a target the hyps as written do not decide is decided with v read at e in the target and the context together: a value, or a definition, the definitions acyclic and a structure's own elements left alone | `variable_subst.go` |
| a target `¬(v = e)`, at every carrier; on ℕ `0 < v` in each spelling | the value is read into the hypotheses as the definition it would be there, and a hypothesis it reads ⊥ refutes it | `denied_value.go` |
| a product `a·b`, on ℕ | a hypothesis `a·b = 0` splits into `a = 0 ∨ b = 0` (`MulEqZero`); a product of the sequent with both factors shown positive is enriched with `0 < a·b`, for a linear run and for the case split | `nat_products.go` |
| a power `bᵉ`, on ℕ | a power of the sequent whose base is shown positive is enriched with `0 < bᵉ` (`PowPositive`); a hypothesis `bᵉ = 0` gives `b = 0` and `0 < e` (`PowEqZero`) | `nat_products.go` |
| a comparison of two products, on ℕ | a goal `P·a ⋈ P·b` from `a ⋈ b`, factor by factor for two products with nothing shared, summand by summand for two sums, and from the hypotheses' comparisons scaled by the cofactors in sight; a hypothesis `P·a ⋈ P·b` with P shown positive enriched with `a ⋈ b`; a goal `a ⋈ b` from a `P·a ⋈ P·b` the hypotheses prove linearly | `nat_scaling.go` |
| bounded var | `x ≤ c ⊢ …` nonlinear in `x` → split on `x ∈ {0…c}` | `nat_exp.go` |
| `¬(a < b)` / `¬(a ≤ b)` hyp | un-negate to the positive equivalent (`NotLessThan`/`NotLessEq`), carrying `{h} ⊢ positive` | `domain.go` |

### Negated comparison hypotheses

Nothing below `hypConstraints` is negation-aware — `linOf` reads positive atoms
only — so a negated comparison hypothesis is un-negated before it is read;
otherwise it would be dropped, and the same fact decided or not depending on
how it was spelled (`b ≤ a ⊢ …` against the equivalent `¬(a < b) ⊢ …`). The
`unnegateHyp` hook (`domain.go`, wired for all three domains in `subneg.go`'s
`init`) rewrites such a hyp through `NotLessThan` / `NotLessEq` and hands `parseHypConstraint` the positive
form, carrying `{h} ⊢ positive` as the constraint's `HypProof` so the
refutation's hypotheses stay ⊆ the goal's (the `IsStronger` contract) — the same
shape as the `moveAcrossHyp` sub/neg positivization it sits beside. The positive
form is run back through `moveAcrossHyp`, so `¬(a − b < c)` reaches the decider
positive on both counts.

Deliberately NOT handled: a negated EQUALITY `¬(a = b)`. That is a disjunction,
not a comparison; turning it into one linear row would be unsound. It belongs to
the case-split engine, whose `hypSplittable` ingests it via `LessThanTrichotomy`.

### The case-split engine

A shared disjunction-elimination engine (`engine.go`) backs every split:
`firstSplittable` selects a `splittableAtom` (a subterm/hyp plus a proved
`⊢ g₀ ∨ g₁` and two `splitBranch{guard, facts}`), `caseSplit` feeds each branch's
facts to the linear prover, discharges the guard, and recombines via
`prop.ByCases`. Clients: monus / `nat_max` / `nat_min` / raw `COND` (tautology
disjunctions) and *given* disjunctive / `≠` / `⇒` hypotheses (the linear core
drops those; the split puts them to work — `≠` via `LessThanTrichotomy`). Adding another
piecewise-by-comparison operator is one new kind constructor; the engine,
soundness gating, and recombination are shared.

A branch is asked of the linear prover first, then split further, and — where
nothing is left to split and the linear prover has declined — handed to the
domain's leaf prover (`natProveLeaf`, `intProveLeaf`, `realProveLeaf`): the
handlers of the decide chain that read the hypotheses and prove without
re-entering it. What a split adds to its branch is a fact no handler of the
root's chain could read, a hypothesis split's disjunct and an operator split's
guard and pin alike: `s = &1 ∨ s = −&1 ⊢ s·s = &1` closes there by the
products pass over the pin, and `|x| ≤ c ∧ &0 ≤ w ⊢ x·w ≤ c·w` by the
monotone scaling once `x ≤ c` is linear. A split made inside an enrichment
passes no leaf prover, so the enrichment is not re-entered through its own
split.

An operator's pin is an equation between the operator and its arm, and the
linear prover reads it where the operator is itself an unknown. Where a pinned
operator stands inside an unknown — a factor of a monomial, a divisor, the base
of a power, the argument of an opaque atom — the branch is read at its pins
before the two provers are asked again (`pin_reading.go`): the goal and the
hypotheses the provers read, each operator replaced by its arm, the pin's own
equation left out. `&0 < w ⊢ real_min(d, &1)·w ≤ w`, `d ≤ &1 ⊢
real_min(d, &1)·w = d·w` with no sign of `w`, and over ℕ `nat_min(d, 1)·w ≤ w`
close through the reading. The price is the leaf at the first open branch of a
decision that declines: on a wide ε-δ context, one more model of the products
pass beside the root's.

On ℕ the split's branches hold the `nat_div`/`nat_mod` facts of the
enrichment (`proveDecAtom` injects `divModFacts` around `proveSplit`): a
hypothesis `0 ≠ nat_mod(n, 2)` — what `nat_odd(n)` bridges to — is read by its
split alone and `nat_mod(n, 2) ≤ n` is a fact of the enrichment alone, so
`n ≠ 0` and `1 ≤ n` follow only in a branch that has both. With Division's
identity among those facts the branch `0 < nat_mod(n, 2)` of
`nat_odd(n) ∧ 1 < n ⊢ 3 ≤ n` is the system `n = 2·q + r`, `1 ≤ r ≤ 1`,
`2 ≤ n ≤ 2` of the elimination above.

## Soundness model

### The lemma bundle

Every leaf reads its named theorem from `NatLemmaBundle` (`nat_lemmas.go`) via a
nil-safe accessor. When the field is present it derives a real proof; the
compositions *around* the leaves are real kernel work, so omega is sound once
the bundle is populated. Wiring styles: direct bind, conjunct projection
(`projectMatch`), macro instantiation (`eqLeaf`/`implyLeaf`), and the
`PromiseForGeneral` seam (caller declares the general shape; `prop.Normalize`
gives the library lookup key + a reconstruct callback).

Production installs the bundle from the library
(`library/serve.InstallNatBundle()`, at `initEngine`). Because a non-test
build installs no placeholder fabricator, a missing/shape-mismatched named-lemma
field becomes a panic at the call site rather than a silent placeholder — no
separate "mode" flag, just the default when the test seam is absent.

### Two honesty seams (no `core.TestThm` in production)

A leaf that has no real theorem to instantiate must never fabricate a cert into a
production proof. Two seams enforce this, and neither puts `core.TestThm` in the
production build:

- **Bundle-nil named leaves** (`eqLeaf`/`implyLeaf`/`cmpLeaf`) degrade to a
  placeholder stand-in supplied by a **test-only** fabricator hook
  (`bundle.go`: `SetPlaceholderFabricator`, installed from each test
  package's `init` — the sole `core.TestThm` reference). Production installs no
  fabricator, so a degrade **panics** instead of fabricating: a leaf whose goals
  reach it must bind its real theorem. This is the *default* (no flag) — the
  panic-vs-placeholder choice is just "is the test fabricator installed?" — and
  it lets omega's algorithm unit tests exercise the kernel composition without
  the library layer above it (omega can't import it). A test that wants production
  behavior in a fabricator-installed package removes the fabricator for its
  duration (`withoutFabricator`).
- **Integer-frontier compositions** (the rank-1 gcd cut, general two-sided
  gcd-equality, `notDivides`, the `nat_div`/`nat_mod` evaluator) **decline** — return
  `ok=false`, no fabricated cert — when a needed integer theorem is absent. The
  "no proof" propagates up through the forward provers (`OmegaProve`/`LinProve`),
  and the tactic callers fall through cleanly. The *untrusted* decider
  (`IntUnsat`) builds its model independent of leaf supply, so it stays complete
  even when the proof path declines (`buildIntProv` splits model from proof).

The algorithm-level provers (`LinProve`/`OmegaProve`/`RingProveFull`) need no
outer guard: a leaf that can't derive a real cert returns `ok=false`, so a failed
atom is simply left undecided and never poisons its siblings.

## Built on the kernel

omega orchestrates existing machinery rather than reinventing it:

- **Term vocabulary** comes from `ext/dsl/arith.go` (operator consts + numeral
  encoders, alpha-key-compatible with the library's constants). The matchers are one-liners
  over `ext.MatchesBinaryOp` (`domain.go`).
- **The rewrite engine is `ext/prop`.** `ArithDecideWithHyps` stacks its
  shallow arith leaves on the standard basic rewrites in one
  `prop.BasicRewritesWithEnv` call (`composeArithLeaves`); the capture-aware
  `prop.DeepRewriteWithEnv` behind it supplies both the deep traversal and the
  fixpoint iteration.
- **The AC machinery is relation-generic.** `prop.AssocRewrite` / `ArrangeChain`
  / `BinaryOpSortRewrite` are instantiated for `*` to give `MulSortRewrite`.
- **Proof plumbing is prop's.** Case-split recombination is `prop.ByCases`,
  iff-introduction is `prop.Deduct`, conjunction elimination is
  `prop.HypAND0`/`HypAND1`, disjunction introduction is `prop.ConclOR0`/`ConclOR1`,
  conjunction flattening is `ext.DecomposesAND`.
- **The library is the material.** The chapter members the bundle binds
  (`nat_arith.AddAssoc`, `nat_arith.MulSym`, `nat_order.LessEqAdd2`,
  `nat_div_mod.DivModUniq`, …) are consumed as proven `*Thm`s; omega never re-derives an arithmetic
  fact a chapter states.

## The real (ℝ) layer

An ordered field has no divisibility, so ℝ has no Cooper/cut frontier: the
linear layer is clean ℚ-Farkas and the nonlinear frontier (RCF) is decidable.
The code is a near-mechanical twin of the `num` stack; what is its own is the
supply, the theorems over ℝ `serve.InstallRealBundle()` binds.

Its parts (in omega's own unit tests the bundle-nil leaves use the test-only
placeholder stand-in, `bundle.go`):

- the `Domain` seam (`domain.go`) — the operator vocabulary behind which the
  type-agnostic extraction (`linOf`, constraint parsing) and FM search run;
  `realDomain` (`domain.go`) is the ℝ instance;
- the proof skeleton — `RealLemmaBundle` (`real_lemmas.go`), the real leaves
  (`real_lemmas.go`), and the full certificate replay + forward prover
  (`real_linarith.go`), reusing the generic `eqLeaf`/`implyLeaf`;
- the real ring normalizer — `ring.go`'s composition machinery is
  domain-generic (`ringVocab`, the proof-bearing twin of the `Domain` seam);
  `realRing` instantiates it over the nine real AC/identity/distribution leaves,
  giving `realNormalizeProof` (the replay's transport step) and `RealRingProve`
  (the linear `⊢ e₁ = e₂` closer);
- the real deep-rewrite simp (`real.go`) — `RealArithDecideWithHyps`, the
  ℝ twin of the num `ArithDecideWithHyps`: identity-fold + atom-decide leaves on
  the shared `prop.BasicRewritesWithEnv`, so the bool/cond/neg cascade is free.
  Its leaves are also part of the unified `ArithDecideWithHyps` (the `arith`
  move's backend) — one deep rewrite whose leaves dispatch PER ATOM by operand
  type, the real ones present when a real bundle is installed and the proof's
  `ArithPolicy` admits them;
- the real formula-level bool-split (`real.go`, the ℝ twin section) —
  `realArithBoolLeaf`, mirroring the nat `arithBoolLeaf`: closes a goal whose
  validity is propositional over several contingent real comparison atoms (the
  real trichotomy, `(x≤y ⇒ x≤z) ∨ (z<y)`) by interleaved ExcludedMiddle case
  analysis. Reuses the type-generic split machinery (`splittableAtom`,
  `enrichAndCut`, `collectRawSubterms`, `ByCases`) and the shared
  `arithCollapseRewrite` (which dispatches real) — only the atom-domain
  primitives are real-specific;
- the DSL real vocabulary (`ext/dsl/arith.go`): the const metas carry the
  library's constant names (`real_add`/`real_lt`/…, so the library's
  statements over ℝ alpha-match omega's leaf shapes directly), while the agent surface stays the
  overloaded infix `+ * < ≤` — the parser disambiguates by operand type, the
  printer renders the names back as symbols — plus the `&n` (`real_of_num`)
  coercion prefix.

The real `norm_num` (`real_lemmas.go` `realNormNat*`) has no bit recursion of
its own: each evaluator lifts the `num` evaluator through the `real_of_num`
homomorphism bridge (`&m + &n → &(m+n) → &k`), so its supply is the five
`OfNum{Add,Mul,Lt,Le,Eq}` bridge theorems. Two genuine (non-mechanical) differences from `num`: real variables have
no default `xᵢ ≥ 0` bound, and scaling carries a `0 ≤ c` side condition
(discharged on the concrete coefficient; `realScale` does this through the
norm_num bridge). `serve.InstallRealBundle()` populates the bundle; the
binding tests (`TestInstallRealBundleBinding*`) pin every leaf — they run in a
fabricator-free package, so a degrade panics. Every bundle field binds a
theorem of the library, in the wiring styles of `InstallNatBundle`: a member
bound directly (`fromEntry`) for the ring / of_num / abs/sgn/inv/pow algebraic
/ sub-RCF leaves; `defNorm` for `NotLessEq` — real_lt's
normalized definition — and the `>`/`≥` bridges +
`real_sub`/`real_abs`/`real_max`/`real_min`/`real_sgn` defs; `CurryIffConj` for
`LessEqAntisym`; `fromGeneral` for the `*Add2`/`*AddLeft`/`*MulLeft` / sign-of-product /
move-across / pow-monotonicity families and `LessEqOfEq`, with `LessEqOfEqSwapped`
derived; `negDiv.derive` for the negative-divisor field-clearing variants.

`initEngine` (`engine/cmd/xugo/main.go`) calls `serve.InstallNatBundle()` and
`serve.InstallRealBundle()` at startup, so the engine's `arith` move and
`auto`'s arith fast-path decide real goals; `TestInitEngine_RealArithLive`
pins this. A real leaf with no theorem bound panics at the placeholder seam
(production installs no fabricator) — the same soundness contract as nat.

The move's shape gate (`goalHasArithContent`, engine/structural.go) recognizes
real `+`/`*`/comparison content, AND-gated on `omega.RealArithEnabled()` (a
real bundle present), so a real goal is offered the move only when dispatch
can act on it; real linear / ring / boolean goals then close through the same
unified backend as num ones.

### Real structural handlers — case splits + sign-known nonlinear

The real decide leaf (`realProveDecAtom`) mirrors the int handler chain past
the linear/ring core (`real_ops.go`), reusing the
type-generic case-split engine (`splittableAtom`/`enrichAndCut`/`prop.ByCases`)
and the shared signed normalizer (`subneg.go`, instantiated for `real`):

- **Operator case splits** (`real_ops.go`): `real_abs x = COND(&0 ≤ x, x, −x)`
  (AbsDef), `real_max`/`real_min` (`COND(a ≤ b, …)`), `real_sgn` (nested COND),
  and a bare real-typed `COND` — each split on its comparison guard, the operator
  pinned per branch (the `−x` arm through the signed normalizer). Closes
  `&0 ≤ |x|`, `a ≤ real_max a b`, `real_min a b ≤ b`, `−&1 ≤ real_sgn x ≤ &1`, ….
- **Hypothesis splits** (`real_ops.go`): a disjunctive `p ∨ q`, a real `≠`
  (trichotomy via LessThanTrichotomy), a real implication `p ⇒ q`, the integral-
  domain product-zero `a·b=&0 ⊢ a=&0 ∨ b=&0` (MulEqZero), and the quotient-zero
  `a/b=&0 ⊢ a=&0 ∨ b=&0`, the zero on either side (the quotient unfolded to
  `a·inv b` by DivDef, `inv b = &0` read `b = &0` by InvEqZero).
- **Monotone scaling / sign-of-product / integral domain** (`real_ops.go`):
  `a≤b ∧ &0≤c ⊢ c·a≤c·b` (LessEqMulLeft/LessThanMulLeft), all four sign combinations of
  `x·y ⋈ &0` (LessEqMul/MulPos + the negation reduction), the two-sided
  `a·c ≤ b·d` (derived via LessEqTrans), the `x·x=&0 ⊢ x=&0` square collapse and
  the strict square positivity `x≠&0 ⊢ &0<x·x` (MulEqZero + LessThanTrichotomy).
  A sign-of-product side condition whose factor is itself a product descends
  into it (`realProveFactorSign`), so `&0<a ∧ &0<b ⊢ &0 < &2·(a·b)` closes
  like `&0 < a·b`.
- **No-hyp square nonnegativity** (`real_ops.go` `realProveSquareNonneg`):
  `⊢ &0 ≤ x·x` with NO sign hypothesis (SquareNonneg), where the monotone handler
  (needing factor-sign hyps) declines. This is the ℝ analogue of `int`'s Image
  square split, but a **single lemma** — ℝ needs no sign split (a square is nonneg
  outright).
- **No-hyp abs nonnegativity** (`real_ops.go` `realProveAbsNonneg`):
  `⊢ &0 ≤ real_abs t` for any `t` via AbsNonneg — the single-lemma alternative
  to the abs case split, preempting its cost. Also threaded into
  `realLinProveSigned` so the sign-of-product handler discharges `&0 ≤ |x|·|y|`
  (the result of `realAbsSgnSimp` folding `|x·y|`) without a 4-way case split:
  the linarith-opaque `&0 ≤ |x|` / `&0 ≤ |y|` side conditions close directly,
  and LessEqMul closes the product.
- **Positive-factor cancellation from a HYPOTHESIS** (`real_cancel.go`
  `realProveCancelMul`): the converse of the monotone scaling above, and the one
  handler on the *hypothesis* side. In the monomial basis `P·a` and
  `P·b` are two distinct monomial UNKNOWNS, so the row `P·a ⋈ P·b` tells the
  linear layer nothing about `a ⋈ b` — relating them means scaling a premise by
  a VARIABLE, which is exactly what the Farkas fragment excludes. The handler
  reads such a hypothesis (`P·a ⋈ P·b`, or `a·P ⋈ b·P` with both sides commuted
  through MulSym — no right-factor field needed, the goal-side
  `realMonoScaleRight` trick run backwards), discharges `&0 < P` through
  `realProveFactorSign` (linarith, plus the sign-of-product descent for a
  compound factor), and injects the cancelled `a ⋈ b` for ONE linear run before
  cutting it back (`enrichAndCut`). So `&0 < p, p·a ≤ p·b ⊢ a ≤ b` closes. The
  sign premise is **strict**: `&0 ≤ P` cancels nothing, since `&0·a ≤ &0·b`
  holds for every `a` and `b` — the handler asks for `&0 < P` and declines
  otherwise. A `≥`/`>` hypothesis bridges to `≤`/`<` first, so the capability
  does not turn on how the fact was spelled. It sits last before the case-split
  fallback: the decline is a pure structural scan of the hypotheses, so a goal
  with no product-vs-product comparison pays a walk of the hyp list, nothing an
  earlier handler already closes changes route, and the cheap cancellation is
  tried before the exponential split. Supply: the `LessEqCancelMulLeft` /
  `LessThanCancelMulLeft` fields. The
  `int` twin is `int_cancel.go`, identical down to the
  strict boundary and the MulSym trick. ℤ states neither cancellation law, so
  its two fields are the REAL pair LIFTED through `IntOfRealThm` at install
  time — the `PowNonneg`/`PowPos` route, `liftReal(fromGeneral(<curried REAL
  shape>))`, since the lift carries a curried implication across unchanged
  (measured: it lands α-equal on the shape the leaf instantiates, with no
  hypotheses). A lifted field has no ℤ node in the dependency DAG to match, so
  it declares its roots explicitly — the ℝ source plus the construction
  bridges for the operators it mentions (`serve/int_bundle.go`), the shape
  `SquareNonneg` uses.

This is the sign-known sub-RCF fragment — the genuine RCF frontier (`a≤b ⊢ a²≤b²`
with no sign hypothesis) stays out, as for `int`. Supply: AbsDef / real_max /
real_min / real_sgn / LessEqMul / MulPos / MulEqZero / LessEqTrans /
NegNonnegativeIffNonpositive/NegPositiveIffNegative / LessThanTrichotomy / the two scalings LessEqMulLeft/LessThanMulLeft / the two
cancellations LessEqCancelMulLeft/LessThanCancelMulLeft / the six {LessEq,LessThan}SubAdd{Left,Right} and EqSub{Left,Right}Add
move-across / the five sub/neg primitives (SubDef / NegAdd / NegNeg / NegZero /
MulRightNeg) — all bound by `serve.InstallRealBundle`. The
`TestInstallRealBundleBindingStructural` suite is the soundness ground truth
(fabricator-free): it runs every leaf's composition over the bound theorems.

### Real `real_pow` and the field layer (`real_div` / `real_inv`)

- **`real_pow` literal-exponent unfold** (`real_ops.go`) — the real twin of `int_pow`
  / `nat_pow`: a literal num exponent `c` unfolds to a product chain `m · … · m` (`&1` for
  c=0). `c ≤ 1` auto-folds in `realArithSimpStep`; `ExpandRealPowRewrite` does the
  agent-driven `c ≥ 2`. So `real_pow x 2 = x·x` closes (expand then ring/reflexivity).
  Supply: the `real_pow` clauses (the `PowZero`/`PowSuc` fields).
- **`real_pow` ↔ `nat_pow` bridge** (`real_ops.go` `realPowSimp` OfNumPow clause) —
  `real_pow(&m, n) → &(nat_pow(m, n))` (OfNumPow) when the base is `&_`,
  opening the num-side fold on the wrapped `nat_pow`. End-to-end literal
  evaluator: a `&m pow &c` composes through `NormNatExp` (num's bit-recursion
  pow evaluator, `nat_norm.go`) to a single num literal, then the real_of_num
  bridge closes `real_pow &m &c = &k` directly (no agent intervention; the pow
  sibling of the OfNumAdd/OfNumMul bridges). Fires for symbolic `n` too.
  Carve-out: the base `&1` is skipped, so `realPowLawSimp`'s OnePow clause
  (`&1 pow n = &1`, OnePow) takes that case. Supply: OfNumPow (the
  `OfNumPow` field).
- **`real_pow` sign** (`real_ops.go` `realProvePowSign`) — the sign-known power
  fragment (NOT RCF: the input is a base-sign or even-exponent fact, the output
  a lemma instantiation or short composition). Single-lemma cases: `&0 ≤ x ⊢
  &0 ≤ x pow n` (PowNonneg, symbolic n), the no-hyp `&0 ≤ x pow 2`
  (PowTwoNonneg, an even square is nonneg), `&0 < x ⊢ &0 < x pow n`
  (PowPos). Two compositions extend the no-sign-hyp even-power fragment
  past `pow 2`: `realEvenPowNonneg` closes `&0 ≤ x pow &(2k)` for any literal
  even ≥ 4 via a perfect-square split (PowAdd at (x, k, k) rewrites
  `x pow (2k) = x^k · x^k`, then SquareNonneg); `realSymbolicEvenPowNonneg`
  closes `nat_even n ⊢ &0 ≤ x pow n` for SYMBOLIC n via EvenIffDouble skolemize
  (`n = 2·m₀`, fresh) → PowPow reshape `x pow (2·m₀) = (x pow 2) pow m₀`
  → PowTwoNonneg + PowNonneg close (the `chooseElim` ∃-elimination seam in
  `prop_helpers.go`; EvenIffDouble is a field of NatLemmaBundle).
  Supply: PowNonneg / PowPos / PowTwoNonneg / PowAdd / PowPow (`InstallRealBundle`)
  and EvenIffDouble (`InstallNatBundle`). The genuine RCF frontier stays
  out: `a ≤ b ⊢ a² ≤ b²` with no sign hypothesis on the bases.
- **Field layer** (`real_ops.go`) — ℝ-specific (no int twin; ℤ has Euclidean
  div/rem). Closes the field fragment reducing to ring/linear/sign WITHOUT RCF:
  simp folds (`x/&1 → x`, `inv &1 → &1`); inverse cancellation (`y·inv y → &1`,
  `inv y·y → &1`, `y/y → &1` for `y ≠ &0`, via MulRightInverse/MulLeftInverse/DivRefl); and
  **denominator clearing** — a comparison/equality atom `x ⋈ y/z` (or `x/z ⋈ y`) is
  cleared to a division-free `x·z ⋈ y` via {Eq,LessEq,LessThan}DivMul{Left,Right}, discharging
  the divisor's sign (`&0 < z` incl. a positive literal; `z < &0` the sign-flipped
  lemma; unknown `z ≠ &0` splits on `z<&0 ∨ &0<z`). The cleared atom recurses through
  the decider — a hyp-echo (a goal that is literally a hypothesis) closes a nonlinear
  cleared atom that ℝ-linarith would otherwise defer. Out of scope (field frontier):
  multiple/nested denominators, and a divisor with no derivable sign/nonzeroness.
  A POSITIVE LITERAL divisor also clears as a hypothesis-free REWRITE
  (`realClearLiteralDivSimp`, in the simp step), so it fires wherever the simp
  runs — on hypotheses in the pre-simp as well as on goals. The clearing
  handler PROVES a goal, so a division in a HYPOTHESIS never meets it, and
  without the rewrite linarith would read `x/&2` as an atom unrelated to `x`;
  with it `x/&2 ≤ y ⊢ x ≤ &2·y` closes. A
  SYMBOLIC divisor stays the handler's: its sign is a proof obligation, not a
  rewrite's business.
  The positive-divisor clearing lemmas (`{Eq,LessEq,LessThan}DivMul{Left,Right}`) are
  bound directly. The negative-divisor fields have no member to bind: the
  install derives them from the positive ones (`negDiv.derive`,
  `library/serve/real_bundle_neg_div.go`).

### The `real_of_num` homomorphism collapse

`&n` (n a num *variable*) is opaque to linarith (real variables carry no default
bound) and the ring atomizes it, so neither sees `&n·&n = &(n·n)` nor `&0 ≤ &n`.
`real_ops.go`'s `realOfNumNormalize` collapses a real term whose leaves are
`&`-coerced nums (combined by `real_neg` / `real_mul` / same-sign `real_add`) to a
**signed num image** `±&(num expr)`, running the `OfNumAdd/OfNumMul` homomorphism
as proof rewrites (over arbitrary num args, not just literals) and tracking the sign
through `MulRightNeg` / `NegNeg`. The decide leaf `realProveOfNum`: an `=`
goal closes when both sides collapse to the same signed image (the of_num twin of
`RealRingProveFull`, which atomizes `&n`); a `≤` / `<` goal whose sides are
**nonnegative** images drops to the num comparison via `OfNumLessEq/OfNumLessThan`, closed
by num's default-nonneg bound — so `&0 ≤ &n·&n` reduces to `0 ≤ n·n` and the bare
`&0 ≤ &n` to `0 ≤ n`. Sign-mixed addition declines (it is
real subtraction — the signed normalizer's job). It is the exact twin of
`int`'s `intOfNumNormalize`, and reads only the `OfNum*`/`Neg*` leaves — it has
no bundle field of its own.

### abs / sgn algebraic laws

The homomorphism / identity rewrites that push `real_abs` / `real_sgn` toward the
leaves (`real_ops.go` `realAbsSgnSimp`, a leaf in `realArithSimpStep` so the
deep+fixpoint rewrite folds every redex). Distinct from the case split
([structural handlers](#real-structural-handlers--case-splits--sign-known-nonlinear)),
which eliminates a *piecewise-by-guard* `abs x` / `real_sgn x` at a **leaf** (a bare
variable); these fold abs/sgn of a **compound** argument by its operator structure:

- `abs(x·y) = abs x · abs y` (AbsMul), `abs(−x) = abs x` (AbsEven),
  `abs(abs x) = abs x` (AbsIdempotent), `abs(x/y) = abs x / abs y` (AbsDiv),
  `abs(inv x) = inv(abs x)` (AbsInv), `abs(x pow n) = abs x pow n`
  (AbsPow), `abs(&n) = &n` (AbsOfNum);
- `real_sgn(x·y) = real_sgn x · real_sgn y` (SgnMul),
  `real_sgn(−x) = −real_sgn x` (SgnOdd), `real_sgn(inv x) = real_sgn x`
  (SgnPreservedByInv).

So `|x·y| = |x|·|y|`, `|−(x·y)| = |x|·|y|`, `real_sgn(−x) = −real_sgn x`, … close as
**reflexivity after normalization** — WITHOUT the cross-sign sign-of-product a brute
multi-atom case split would need (the contradictory `&0≤x ∧ &0≤y ∧ x·y<&0` branch the
linear branch-prover cannot refute). The fold only touches abs/sgn of a compound, so
a bare `abs(variable)` / `real_sgn(variable)` is untouched (the leaf split's domain) —
`&0 ≤ |x|`, `real_sgn x ≤ &1`, … still go to the split. All laws are unconditional (they
hold at the degenerate points, e.g. `abs(x/&0) = abs x / abs &0` since `inv &0 = &0`)
and bound by `InstallRealBundle`. NOT folded
(no single law): `abs(x+y)` — `|x+y| ≤ |x|+|y|` is the triangle *inequality*
(it closes via the case split), and `|x+y| = |x|+|y|` is correctly NOT a
theorem.

### The modulus of another carrier

A carrier's absolute value into ℝ — ℂ's `complex_abs` — is a real number, so
it stands in ℝ's rows as an atom. `modulus.go` reads three things about it from
the laws its chapter states (`ModulusLaws`, installed by `library/serve` from
`complex_abs`), under the policy bit `ArithPolicy.Modulus`:

- **its laws, as rewrites toward the leaves** (`modulusSimpStep`): each law is
  an unconditional equation `∀xs. m(p) = r` read left to right, matched first
  order at the head of the modulus's argument — `|z·w| = |z|·|w|`, `|z/w|`,
  `|inv z|`, `|zⁿ|`, `|−z|`, `|conj z|`, `|&x| = real_abs(x)`, `|i| = &1`. The
  install refuses a law whose right side applies the modulus to anything but
  the law's own variables, so every firing moves the modulus strictly inward.
  The leaf sits in the hypothesis pre-simp and in every decided target's leaf
  set, as `realAbsSgnSimp` does;
- **its sign** (`modulusProver`): the real decide leaf's prover is wrapped so
  that `&0 ≤ m(u)` joins the hypotheses of each atom's decision, for every
  modulus the hypotheses and the atom spell outside a binder, and is cut from
  the proof (`enrichAndCut`). A modulus whose sign the context states is
  skipped.

- **its zero test** (`modulus_zero.go`; `ModulusLaws.EqZero`,
  `PosIffNonzero`, read as facts and never as rewrites): a term and its
  modulus vanish together, carried across the two layers each way. For a
  modulus `m(s)` a real decision spells, the carrier's structure ring is
  asked about s (`ArithPolicy.modulusEvidence`): where it shows `s = zero`
  — a ring identity, `|c − c|`, or the context's equations — the fact is
  `m(s) = &0`, where it shows `s ≠ zero` the fact is `&0 < m(s)`, and
  either stands in place of the sign. For a modulus the hypotheses spell,
  the ring's decision holds `s ≠ zero` where ℝ's linear prover shows
  `&0 < m(s)` over the hypotheses and the moduli's signs, and `s = zero`
  where it shows `m(s) = &0` (`modulusCarrierFacts`, read by
  `structureLeaves` at an atom the hypotheses as written leave open).
  Each layer asks the other's evidence as that layer holds it without
  the test, so the two do not re-enter each other. The ring's answer for
  a modulus under a decision's hypotheses is kept for the arith step
  (`modulusZeroMemo`).

There is no case split: a modulus on ℂ is not piecewise linear. A sum or a
difference under it matches no law and is one unknown, as spelled, so the swap
`|z − w| = |w − z|` and the triangle inequality are cited laws. The laws'
capability is `arith:modulus`; a proof in their foundation runs without the
reading (`ModulusAllowsTarget`).

## The integer (`int`) type layer

`int` is the integer *type* — built as a subtype of `real`
(`int_le x y ⇔ real_of_int x ≤ real_of_int y`, and the whole ℤ order/ring
suite is the ℝ suite lifted through `real_of_int`).
omega does **not** follow that reduction: it treats `int` as its own `Domain`
(the seam built for exactly this) and replays with **int-native** order lemmas,
so the layer is self-contained — no `real_of_int` rewrite, no dependence on the
real bundle being installed. (Distinguish this from the integer-reasoning
*extension over `num`* in [`omega`](#omega--the-integer-layer): that one produces
`num` theorems using integrality; this one is the `int` type.)

The layer is a near-mechanical mirror of the real layer (`int*.go`), installed
the same way. Its parts — the positive-linear core, then sub/neg and
discreteness on top of it:

- `intDomain` (`domain.go`) — the int operator vocabulary + builders
  (`intPlusT`/`intStarT`/`intSubT`/`intNegT`/…) and the `&n = int_of_num(<bit-tree
  n>)` literal; the `sub`/`neg` matchers + builders feed the signed normalizer;
- `IntLemmaBundle` (`int_lemmas.go`) — the `RealLemmaBundle` field set (int's
  order/ring lemmas are the real ones lifted) PLUS the symmetric sub/neg + relation
  move-across fields, PLUS the **one int-only** field `Discrete` (ℝ has no
  discreteness to lift). `SetIntLemmaBundle` + nil-safe accessors, same
  graceful-degradation contract;
- the int leaves (`int_lemmas.go`) — ring AC / order duality / `*Add2` family /
  `*AddLeft` cancel / `*MulLeft` scaling (with the `&0 ≤ c` side condition) / `GreaterIffLess`/`GreaterEqIffLessEq`
  bridges / the sub/neg primitives (`SubDef`/`NegAdd`/`NegNeg`/`NegZero`/`MulRightNeg`) /
  the subtraction move-across family / `Discrete`, each one a
  macro instantiation of a bundle field;
- `intRing` + the `int_of_num` norm_num bridge (`int_lemmas.go`) —
  `intNormalizeProof` (the replay's transport step) and `IntRingProve`; numerals
  reuse the sound `num` evaluator through the `OfNum{Add,Mul,Lt,Le,Eq}`
  homomorphism, exactly as the real layer reuses it through its own;
- the linarith certificate replay (`int_linarith.go`) — `IntLinRefuteProof` /
  `IntLinProve`, the proof-producing twin of `real_linarith.go` (no `&0 ≤ x`
  rows, like ℝ), with the **ℤ-discreteness strict-row strengthening** in
  `intBuildAll` (every `<` row → `+ &1 ≤`, via `Discrete`);
- the deep-rewrite simp + decide leaf (`int.go`) —
  `IntArithDecideWithHyps` / `IsIntArithContent` / `IntArithEnabled`, with the
  move-across leaf in the rewrite stack so sub/neg goals reach the decider positive;
- the **signed normalizer + move-across** (`subneg.go`, domain-generic over
  `int`+`real` — see [Total subtraction and negation](#total-subtraction-and-negation-the-signed-normalizer)
  below): `signedNorm` (`⊢ t = P + (−N)`) and `moveAcrossCmp`
  (`⊢ (L ⋈ R) ⇔ positive`), shared by `Int/RealSignedNormalizeProof` and wired
  into both the decide leaf (goal side) and `hypConstraints` (hyp side).

Two genuine differences from `num` (shared with ℝ): int variables have no default
`xᵢ ≥ 0` bound, and scaling carries a `&0 ≤ c` side condition discharged on the
concrete coefficient.

**The agent surface (`ext/dsl`, `ext/format.go`).** `int` is a first-class
DSL domain: the operator table dispatches `+ − * < ≤ > ≥` to the int instance on
int-typed operands (`-` is total `int_sub`, distinct from num's monus), a unary
`−` prefix builds `int_neg`/`real_neg`, and `&n` is **type-directed** —
`int_of_num` when its context is int, `real_of_num` otherwise. The printer renders
the int operators as their overloaded infix symbols; int literals print as the
**explicit** `int_of_num(n)` (not `&n`, which would re-parse to real), keeping
round-trip unambiguous. `real_sub`/`real_neg` are handled symmetrically.

**The lift — `IntOfRealThm` (`int_lemmas.go`).** A proven theorem over ℝ + the homomorphism bridges →
its ℤ analogue, with no per-theorem proof search. It specializes each real
`∀`-var to `real_of_int(v:int)`, DEPTH-rewrites with the bridges reversed
(`real_of_int a ⋆ real_of_int b → real_of_int(a ⋆ b)`; `real_of_int a ⋈
real_of_int b → a ⋈ b`; `&n → real_of_int(int_of_num n)`), β-normalizes, and
re-generalizes over the int vars (conjunctions recurse). It reuses
`prop.UnifyEqRewrite` (the exported unification rewrite) on each bridge re-shaped
to `⊢ λvars. R = λvars. L` — hyp-free, so the output carries no hypotheses.
Soundness is the kernel's by construction (every step is a primitive inference);
the only check is `Conclusion().AlphaEquals(want)`, so **no replay is needed** — it
is an install-time derived cert, like `InstallRealBundle`'s `CurryIffConj` /
`fromGeneral` adapters. `serve.InstallIntBundle` calls this to populate the
`IntLemmaBundle` fields (the order/ring suite + the sub/neg + move-across
families) from the real bundle's theorems via the installed homomorphism bridges
(including `int_sub_th` / `int_neg_th` for the sub/neg lift). The one field with
no real source is `Discrete`, proved natively.

### Total subtraction and negation (the signed normalizer)

`int_sub`/`int_neg` (and the symmetric `real_sub`/`real_neg`) flow into the
positive-linear pipeline **without** making the shared natural-coefficient
`linForm`/`poly` core signed. The seam is a domain-generic `subnegVocab` over the `Domain`
(`subneg.go`), instantiated for `int` and `real`. Int subtraction is *total*
(unlike `num`'s truncated monus), so the reduction is unconditional.

- `signedNorm(t) → (P, N, ⊢ t = P + (−N))` peels all sub/neg from a term
  into two positive (subtraction-free) canonical sides. Holding the invariant in
  `P + (−N)` (add+neg) form rather than `P − N` lets the additive case reuse the
  EXISTING positive ring AC / `mergeProof` / `scaleProof`, so the recursion needs
  only five primitive leaves (`SubDef`/`NegAdd`/`NegNeg`/`NegZero`/`MulRightNeg`) — no new ring
  variant, no signed monomials, no 4-var rearrangement lemmas. A sub/neg-free
  subterm takes the fast path straight through the positive normalizer.
- `moveAcrossCmp(atom) → ⊢ (L ⋈ R) ⇔ positive` rewrites a comparison/equality whose
  sides carry sub/neg into the positive two-sided `(Pl+Nr) ⋈ (Pr+Nl)` the decider
  already eats: the left move-across → re-normalize the left side with the signed normalizer
  (so no separate rearrangement lemma) → the right move-across; `>`/`≥` bridge to `<`/`≤`
  first. It is wired into both the decide leaf (goal side, `int.go` / `real.go`)
  and `hypConstraints` (hyp side, `domain.go` — needed because `linOf` *atomizes* a
  raw `a − b` instead of rejecting it). The hyp path carries `{h} ⊢ positive`, so the
  refutation's hypotheses stay ⊆ the goal's (the `IsStronger` contract).

So `arith` closes `x − y ≤ 3`, `−x ≤ y`, `0 ≤ x − y`, `x + 2 = y − 5`, and
hyp-driven goals like `a − b ≤ c ⊢ a ≤ c + b`. The move-across
families are `IntOfRealThm` lifts of their ℝ originals. The agent writes these
through the DSL surface above; on output int terms render with infix operators and
explicit `int_of_num(n)` literals.

### ℤ discreteness

The int discharge (`intBuildAll`) strengthens every strict `<` row to the
integer-tight non-strict `a + &1 ≤ b` (konst+1), carrying `Discrete`
(`x + &1 ≤ y ⇔ x < y`). This is the `int`-type mirror of the `num` side's `sucLessEqIffLessThan`
(`nat_omega.go`), and it closes the off-by-one / consecutive-integer class
(`x < y ⊢ x + &1 ≤ y`) that pure ℚ-Farkas cannot. It is sound because every int row
sum is an integer (`Σ < 0 ⟺ Σ + 1 ≤ 0`), always-on, and complete-preserving. It is
**categorically not the gcd cut** — no division or remainder, no provenance DAG (the same
`sucLessEqIffLessThan`-vs-`roundedCut` separation the `num` side draws). `Discrete` is the
one int leaf with no real analogue to lift (ℝ is dense), so it is proved natively.

### `int_abs` — the int case split

`int_abs x = COND(&0 ≤ x, x, −x)` (AbsBySign) is piecewise-linear by the guard
`&0 ≤ x`, exactly the shape the case-split engine eliminates — so `int_abs` is the
`int`-type twin of the `num` `nat_max`/`nat_min` handler (`nat_sub.go`). `int_split.go`
mirrors that engine: `intAbsSplittable` recognizes `int_abs x` anywhere in
hyps∪goal, `intCondSplit` builds the excluded middle split on `&0 ≤ x`, each branch
pinning `int_abs x` to `x` (resp. `−x`) by collapsing the def's COND under that
branch's guard verdict (`intCondPin`, reusing `IntArithDecideWithHyps`). The `−x`
branch then flows through the signed normalizer into the positive-linear decider, so
goals like `&0 ≤ int_abs x`, `x ≤ int_abs x`, `−x ≤ int_abs x` close. The reusable
machinery (`splittableAtom`/`splitBranch`/`enrichAndCut`/`proveSplit`-shape/
`prop.ByCases`/`prop.ExcludedMiddle`) is shared with the num engine; only the
recognizer, the int comparison vocabulary (`intNegComparison`), and the COND
collapser are int-specific. It is wired into `intProveDecAtom` (`int.go`) as the
fallback after the linear prover, so the decide leaf reaches it. The `AbsBySign` bundle
field is `AbsBySign`, the operator's own definition.

### The rank-1 GCD-equality test

A single equality `Σcᵢxᵢ = k` with `gcd(cᵢ) ∤ k` is integer-unsatisfiable yet
ℚ-*satisfiable* (`2·x = &1` has the ℚ solution `x = 1/2`), so pure ℚ-Farkas cannot
refute it — the contradiction is in the coefficient divisibility. `int_linarith.go` closes
it **without any divisibility predicate**, using only the discreteness + linarith the
layer already has: with `M = V/g` (the reduced variable form, `g = gcd`) and
`q = ⌊k/g⌋`, the sign split `M ≤ q ∨ q < M` (excluded middle; the `q < M` arm becomes
`q + &1 ≤ M` by `Discrete`) makes each branch an honest ℚ-Farkas contradiction
against the original equality — the atoms of `M` are those of `V`, so the scaled
equality cancels the variables to a false numeric bound. `intGroundedGcdEq` builds
the two branch refutations through `intFarkasRefute` (the plain ℚ-Farkas path, NOT the
gcd-checking `IntLinRefuteProof`, so the test never re-fires on its own residual) and
recombines via `prop.ByCases`. It handles the **general** `Σcᵢxᵢ = k` (any two-sided
`int_add`/literal equality — `2·x = &1` and `2·x = 2·y + &1` alike): the signed
combined form is computed directly (`intCombinedForm`) and the split condition is
written sub-free as a positive two-sided `left ≤ right` (`intReducedLe`), so no
`int_sub` reaches `linOf`. (A side carrying top-level `int_sub`/`int_neg` is first
positivized by the signed-normalizer pre-pass `intPositivizeConstraints`
(int_linarith.go), so `2·x − 2·y = &1` reaches the test with its real coefficients
instead of one atomized `a−b` whose gcd collapses to 1; a *nonlinear* sub/neg —
`x·(a−b)` — the pre-pass declines, leaving it atomized.) Strictly rank-1 —
no division or remainder, no provenance DAG — below the gcd-*cut* / Cooper-QE frontier.

### The rank-1 gcd rounding cut

The inequality companion of the GCD-equality test (`int_linarith.go`). It closes the gap
ℚ-Farkas + discreteness leaves: a system of **non-strict** inequalities whose
ℚ-solution set is non-empty but contains no integer — `&4 ≤ 3·x ∧ 3·x ≤ &5`
(`x ∈ [4/3, 5/3]`, no integer). Discreteness tightens only *strict* rows and the
negated goal, so it can't reach this; the cut tightens `g·Σ ≤ b ⟹ Σ ≤ ⌊b/g⌋`.

It is the int twin of the num `roundedCut` (`LessEqRightDivEq` + `DivModUniq`) but needs
**no int division**: the tightened row is exactly a forward goal the int layer already
proves *via discreteness* (negating `Σ ≤ ⌊b/g⌋` gives a strict bound the discrete
strengthening closes against `g·Σ ≤ b`). So the cut is a **forward enrichment** —
`intRoundingCutRefute` tightens each non-strict constraint whose coefficient gcd > 1
genuinely rounds (`tightenLe`), derives the tightened constraint's proof through
`intFarkasRefute` (`intProveLe`, discreteness — NOT `IntLinRefuteProof`, so the cut
never re-enters itself), adds it, and re-refutes. Soundness rides on the per-cut proof:
a row is added only with a real `{orig} ⊢ Lt ≤ Rt` derivation, so a miscomputed cut is
simply dropped. Strictly rank-1 — no leaf of its own, no division or remainder, no
provenance DAG.

### The exact elimination of equations

The last pass of `IntLinRefuteProof` (`intEliminationRefute`) is the step the
`num` layer runs ahead of Fourier–Motzkin
([Equations are eliminated before Fourier–Motzkin](#equations-are-eliminated-before-fouriermotzkin)),
on the rows of `intBuildAll`: each row rounded by the gcd of its
coefficients, every equation with an atom of coefficient ±1 solved and
substituted, the substituted rows rounded, then ℚ-Farkas on what is left. It
closes `n = &2·q + &1 ∧ &1 < n ⊢ &3 ≤ n` and `n = &2·q ∧ n = &2·p + &1 ⊢ ⊥`,
where neither equation alone is gcd-unsat and no input row rounds. A
rounding is proved as the rank-1 cut's is, by discreteness (`intProveLe`), on
the sum of the rows the rounded row combines. The pass declines where no
equation has such an atom: the three passes before it have then said all
there is.

### Structural operator handlers

Beyond the linear core, the same families the `num` side carries are mirrored over
`int` — pure case-split / simp / substitution structure, no integer-completeness
frontier. They reuse the type-generic engine pieces (`splittableAtom`/`splitBranch`/
`enrichAndCut`/`prop.ByCases`/`prop.ExcludedMiddle`/`collectRawSubterms`); only the
atom-domain primitives are int-specific.

- **Operator case splits** (`int_split.go`). `int_abs x = COND(&0 ≤ x, x, −x)`,
  `int_max`/`int_min` (`COND(a ≤ b, …)`), and `int_sgn` (a nested `COND` — the inner
  `COND` is handled by the raw-`COND` kind in the recursion) are each piecewise by a
  comparison guard; `intCondSplit` splits on it and pins the operator to its branch
  value (the `−x` arm flows through the signed normalizer). A bare int-typed
  `COND(guard, x, y)` is the raw-`COND` kind. Closes `&0 ≤ |x|`, `a ≤ int_max a b`,
  `int_min a b ≤ a`, `−&1 ≤ int_sgn x ≤ &1`, … The int twin of the num
  `nat_max`/`nat_min`/`COND` handlers; the `*Def` bundle fields are the operators' own definitions.
- **Hypothesis splits** (`int_split.go`, `intHypSplittable`). A disjunctive hyp
  `p ∨ q`, an int `≠` (trichotomy via `LessThanTrichotomy`, the `a=b` disjunct killed under
  the hyp), or an int implication `p ⇒ q` (`¬p ∨ q`, the `¬p` arm bridged to the
  complementary comparison) — boolean/relational structure the linear core drops — is
  put to work by a split. So `x ≠ y, x ≤ y ⊢ x < y` and `(x ≤ &0 ⇒ &2 ≤ x) ⊢ &1 ≤ x`
  close.
- **Formula-level boolean split** (`int_split.go`, `intArithBoolLeaf`). A goal whose
  validity is propositional over several contingent int comparison atoms — the
  trichotomy `(x<y) ∨ (x=y) ∨ (y<x)`, antisymmetry-as-iff `(x≤y ∧ y≤x) ⇔ (x=y)`,
  `(x≤y ⇒ x≤z) ∨ (z<y)` — is closed by interleaved case analysis (collapse under each
  new atom-hypothesis first, via the decider minus this leaf, so the recursion
  terminates). Its branches run the **NoSignSplit** decider on both legs (the
  collapse through `intArithCollapseRewriteNoSignSplit`, the terminal decide through
  `intProveDecAtomNoSignSplit`): a branch is inside a case-split handler and takes
  the branch discipline `intProveDecAtomBranch` documents — never a case-split
  handler of its own. The reason is cost: the engine's hyp loop decides each
  hypothesis under the OTHERS, so a conjunctive hypothesis meets this leaf with
  an EMPTY context, where the full decider's `intImageSplit` (a 4-way sign split
  whose `x = ±&n` pins every `IntLinProve` re-derives through the signed
  normalizer) is a search that cannot succeed. Measured on the cancellation
  hypothesis `&0 < p ∧ p·a ≤ p·b` met with an empty context: the full
  decider in the branches makes a bool-leaf call cost about six times as
  much, under the placeholder bundle and under the production bundles alike
  (about four times for a compound factor `p·q`). The ℝ twin, which has no
  sign split to enter, pays under three times. A whole `by {arith:true}`
  cancellation row moves only on the compound factor, about three times; the
  plain rows cost the same either way. The int twin of `arithBoolLeaf`; wired last in `IntArithDecideWithHyps`.
- **`int_pow` literal-exponent unfold** (`int.go`). A literal num exponent `c`
  unfolds to a product chain `m · … · m` (`&1` for `c=0`): the strictly-shrinking
  `c ≤ 1` fold auto-fires in the simp; `ExpandIntPowRewrite` does the agent-controlled
  `c ≥ 2` expansion. The int twin of `nat_pow`. After expanding, the basic rewrites close the
  common cases — `int_pow x 2 = x·x` decides ⊤ (the `&1`-fold + reflexivity), even for a
  variable base. A genuinely nonlinear *equality* — reassociating/commuting a product, e.g.
  matching `x·(x·x)` against `(x·x)·x`, or `(x+y)² = x²+2xy+y²` — is closed by the full
  multivariate `IntRingProveFull` (`ring.go`; see [The full multivariate ring](#the-full-multivariate-ring)),
  wired into the `=` decide leaf. Nonlinear *inequalities* (true RCF) remain the frontier:
  the ring *declines* an unequal pair rather than reporting which side is larger.
- **Equality-hypothesis substitution** (`variable_subst.go`, shared with ℕ, ℝ
  and the structure rings). A hyp `v = e` defines the int variable `v`; the
  dedicated stack reads it as a deep-rewrite leaf `v → e` (`eqHypSubst`), so an
  opaque atom on `v` (`int_abs v`, `int_max v k`, `x·x`, …) is substituted and then
  folds. A **coefficient-equality**
  `c·x = k` (literal `c ≥ 2`, `c ∣ k`) is first SOLVED to the bare form `x = &(k/c)` —
  the SAT dual of the GCD-equality test, via discreteness (`c·x = k ⊢ x = &(k/c)`) —
  then substituted (`intCoeffEqSubst`), so `2·x = &4 ⊢ x·x = &4` closes. (`c ∤ k` is
  integer-unsat — the GCD-equality test's job; `c = 1` is the bare shape the
  variable-sided rule takes.)
- **Bounded enumeration** (`int.go`, `intProveBoundedEnum`). A goal NONLINEAR in a
  variable `x` that the hyps bound by a two-sided literal range `&a ≤ x ≤ &b`
  (`b − a ≤ enumMax`) is decided by enumerating `x ∈ {a … b}`: the value disjunction is
  PROVED from the two bounds by the int bool-split (ℤ has no `suc` peel and no default
  lower bound, the two ℤ-specific departures from the num enum), each value substituted
  and evaluated, recombined via `ByCasesRecursive`. Closes `&0 ≤ x ≤ &2 ⊢ x·x ≤ &4`.

### The full multivariate ring

The linear `IntRingProve` closes only linear `=` goals; a nonlinear *equality* like
`x·y = y·x`, `x·(y+z) = x·y + x·z`, or `(x+y)² = x²+2xy+y²` needs the full multivariate
normalizer. `ring.go` provides it for all three domains off the **domain-generic
`ringVocab` seam**: the num `RingProveFull` (used by the `nat_pow` and
`nat_div`/`nat_mod` distribution handlers) is a `ringVocab` method, and
`realRing`/`intRing` instantiate the same composition over their own `*` AC
leaves, giving **`RealRingProveFull` / `IntRingProveFull`**. The per-domain ingredients
(`ring.go` `buildMulSort`) are the monomial-factor AC sort and the `⊢ x·0 = 0` leaf
(derived from `commuteMUL` + `zeroMul`, since ℝ/ℤ have no `MulClauses`); everything else —
the model-then-reprove additive machinery (`mergeProof`/`scaleProof`/like-term merging) — is
shared. `normalizeFull` atomizes a genuinely nonlinear product into a monomial *regardless*
of the domain's `polyMul` hook, so a domain whose linear path declines a product
still closes nonlinear equalities here. Wired into the `=` decide leaf (`intProveDecAtom` /
`realProveDecAtom`), so `arith` reaches it end-to-end.

Subtraction/negation in **nonlinear** position — `(x−y)²`, `(a−b)(a+b)` — is handled by the
**signed multivariate ring** (below). What stays out of scope: `=` is ⊤-only, so a nonlinear
*inequality* is the genuine algorithmic frontier (true RCF); the **monotone-scaling / sign
fragment** of it (sign-known products) is handled separately below, but the general
`a≤b ⊢ a²≤b²` is not.

### The signed multivariate ring

A nonlinear equality with subtraction/negation **inside** a product — `(x−y)² = x²−2xy+y²`,
`(a−b)(a+b) = a²−b²` — needs signed polynomial arithmetic, which the positive ring (natural
coefficients) and the *linear* signed normalizer (top-level sub/neg only) both miss. `mulSigned`
(`subneg.go`) closes it by FOILing two signed forms WITHOUT signed coefficients, keeping the
`P + (−N)` (positive-`P`, positive-`N`) invariant the linear normalizer already uses:

  (Pₓ + −Nₓ)·(P_y + −N_y) = (Pₓ·P_y + Nₓ·N_y) + (−(Pₓ·N_y + Nₓ·P_y))

Each of the four positive·positive products folds to a canonical multivariate polynomial via the
**existing full ring** (`mulProofFull`); the two cross-sign products carry one negation pushed
out by `mulRightNeg`/`negLmul`/`negNeg` (the latter two derived); the result regroups via
`combineSignedAdd` (factored from the `+` case). The base case falls back to `normalizeFull` for a
sub-free nonlinear factor. Because this extends `signedNorm`, **`moveAcrossCmp` (wired into
the decide leaf) positivizes a nonlinear-with-sub equality**, and the positive
ring (`IntRingProveFull`) closes the result — no decide-leaf wiring of its own. So `arith` closes
`(x−y)·(x−y) = x·x + y·y − &2·(x·y)`, `(a−b)(a+b) = a·a − b·b`, `(−x)·(−x) = x·x`. (The `int_pow`
form `(x−y)^2` composes after the agent-driven `expand_exp` unfold.)

### Monotone scaling and sign-of-product

A nonlinear *inequality* whose validity follows from the **signs/order of its factors** —
not full RCF — is closed by `int.go`, applying the monotonicity lemmas with a
**symbolic** multiplier (the Farkas scaling fires only on a *literal* one). The linear core
atomizes `c·a`/`c·b` into unrelated atoms, so without this the goals don't reach the lemmas:

- **monotone scaling**: `a ≤ b ∧ &0 ≤ c ⊢ c·a ≤ c·b` (and the strict / right-factor
  variants) via the bundle's `LessEqMulLeft` / `LessThanMulLeft`.
  The `a·c`/`b·c` orientation reduces to the left one by commuting
  (`intCommuteMUL`), so **no right-factor leaf** is needed;
- **sign-of-product** (`intProveSignedProduct`): **all four sign combinations** of
  `&0 ⋈ x·y` and `x·y ⋈ &0`, non-strict via `LessEqMul` and strict via
  `MulPos`. The both-positive case is the lemma directly; the negated-factor
  combos reduce to it on `(−·)` operands (`negNegMul`/`negLmul`/`mulRightNeg` push
  the negation back out), and the nonpositive target flips `&0 ⋈ −(x·y)` to `x·y ⋈ &0` at the
  proof level via `NegNonneg`/`NegPositiveIffNegative` (linarith atomizes `−(x·y)`
  and `x·y` as independent atoms, so it cannot flip). Distinct from the `Image` square
  split (`&0 ≤ x·x`, no hyps), which still takes over when no factor-sign hyps are present;
- **two-sided product bound**: `&0≤a ∧ a≤b ∧ &0≤c ∧ c≤d ⊢ a·c ≤ b·d`,
  **derived** from two monotone scalings chained by `LessEqTrans` — no
  field of its own, since int does not atomize the product atoms for linarith to chain.

The sign/order side conditions discharge through the **linear** forward prover
(`intLinProveSigned` = `IntLinProve` + one move-across pass, so a negated goal like
`&0 ≤ −x` positivizes) — never the full decider, which could recurse. A bounded sub-RCF
fragment, shared in shape with ℝ/num (the lemmas lift). Out of scope: the **strict**
two-sided bound, and the genuine RCF `a ≤ b ⊢ a² ≤ b²` (no sign assumption on the factors).

### The `int_of_num` homomorphism collapse

`&n` (n a num *variable*) is opaque to linarith and the ring atomizes it, so neither sees
`&n·&n = &(n·n)`. `int.go`'s `intOfNumNormalize` collapses an int term whose leaves are
`&`-coerced nums (combined by `int_neg` / `int_mul` / same-sign `int_add`) to a **signed num
image** `±&(num expr)`, running the `OfNumAdd/OfNumMul` homomorphism as proof rewrites (over
arbitrary num args, not just literals) and tracking the sign through `MulRightNeg` /
`NegNeg`. The decide leaf `intProveOfNum`: an `=` goal closes when both sides collapse to
the same signed image (the of_num twin of `IntRingProveFull` — which can't see it, since it
atomizes `&n`); a `≤` / `<` goal whose sides are **nonnegative** images drops to the num
comparison via `OfNumLe/OfNumLt`, closed by num's default-nonneg bound — so `&0 ≤ &n·&n`
reduces to `0 ≤ n·n`. Sign-mixed addition declines (num has no subtraction — the signed
normalizer's linear job, not this).

### The Image sign split

Every int is ±a-nat (`Image`: `∀x. ∃n. x = −&n ∨ x = &n`), so a sign-dependent nonlinear
goal — `&0 ≤ x·x` (`SquareNonneg`) — is decided by splitting a bare int variable on its sign,
feeding `x = ±&n` to the collapse above: each branch `&0 ≤ (±&n)·(±&n)` → `&(n·n)` → the num
`0 ≤ n·n`. `int.go` instantiates `Image` at `x`, proves the two branches under a
**fresh** num var `n₀` (the eq-subst `x→±&n₀` is then valid — the ε-witness `εn.(x=…)` mentions
`x`, so it can't be substituted into the goal), recombines with `prop.ByCases`, and discharges
the existential with **`chooseElim`** (`prop_helpers.go`) — the ∃-elimination seam (`SelectExists` + fresh-var
`TermInst` + `DeriveTrans`, the ε-witness touching only the body hyp), shared with the
divisibility skolemize below.

### `int_abs` / `int_sgn` algebraic laws

Folds `int_abs` / `int_sgn` over an operator-compound argument toward the
leaves — the int twin of the ℝ-end `realAbsSgnSimp` (`real_ops.go`). Distinct
from the case split (`int_split.go`), which eliminates a piecewise `int_abs
x` / `int_sgn x` at a **bare leaf** by its `&0 ≤ x` (or `&0 < x`) guard; this
fold is pure equational rewriting on a compound argument.

The six laws are members of the library's `int_real_lift` and `int_embed`
chapters (the ℤ statements of the corresponding ℝ laws), bound directly
by `InstallIntLemmaBundle`. The fold is wired into `intArithSimpStep`, placed
FIRST so a compound abs/sgn folds before any other simp.

- `int_abs(x·y) = int_abs x · int_abs y`  (`AbsMul`)
- `int_abs(−x) = int_abs x`  (`AbsEven`)
- `int_abs(int_abs x) = int_abs x`  (`AbsIdempotent`)
- `int_abs(int_of_num n) = int_of_num n`  (`OfNumAbs`, `n:num`)
- `int_sgn(x·y) = int_sgn x · int_sgn y`  (`SgnMul`)
- `int_sgn(−x) = −(int_sgn x)`  (`SgnOdd`)

So `|x·y| = |x|·|y|`, `|−(x·y)| = |x|·|y|`, `sgn(−(x·y)) = −(sgn x · sgn y)`,
… all close as reflexivity after normalization. The compound-arg fold leaves
a bare `int_abs(variable)` / `int_sgn(variable)` to the case split.

### The image split's branch prover

`intImageSplit`'s branch sub-prover is not the full decider: `imageBranchImp`
uses `intArithDecideWithHypsRawBranch`, the branch decider variant that runs
every handler **except** `intImageSplit`, `intProveBoundedEnum`,
`intElimEqHyps`, and the `intArithBoolLeaf` bool split. A branch cannot
re-enter the case-split machinery, so the recursion is bounded
**structurally**, not by per-call-site guards. Each exclusion closes one way
back in: with the full decider in a branch the image split picks another
variable, splits, and re-enters (bounded by `pinnedByHyp`, but only per
variable, so several int variables compound into expensive walks); the bool
leaf re-fires the bool split with `done` reset to nil; and the Gaussian cut's
identity-keyed recursion guard is defeated by nested self-reentry, which grows
the hyp slice every level.

The pattern — every case-split handler takes a strictly weaker branch
sub-prover — is the one `intProveSplit` follows, passing `IntLinProve` for its
branches and, for a leaf under a hypothesis split, `intProveLeaf`: handlers
that prove without re-entering the decide chain.

Closes `sgn(x·y) = sgn(x)·sgn(y)`, `sgn(−(x·y)) = −(sgn x · sgn y)`,
`q∣m ⊢ div(m,q)·q = m` (with eq-symmetry hyp-echo), and the subtraction form
`q∣m ⊢ m − div(m,q)·q = &0`. In the last, `moveAcrossCmp`'s signed normal form
canonicalizes the residual product to the multivariate-sorted shape
`q · div(m,q)`, which alpha-misses the raw fact `div(m,q)·q = m` that
`intProveQuotientExact` injects. `intHypEchoEq` (`int.go`) bridges the two: its
alpha checks are the cheap fast path, and on an alpha miss it tries, for each
hyp equation `c = d`, `IntRingProveFull(a, c)` and `IntRingProveFull(b, d)`
(and the swapped pairing), bridging the goal `a = b` through the hyp via
`EqTrans`/`EqSym`. Sound (only ring-provable equalities bridge; a miscomputed
cert means `IntRingProveFull` returns nil) and cheap (the alpha-equal common
case is unchanged; the ring calls fire only on an alpha miss).

### Div/rem distribution, the full division identity, and the quantifier bridges

A cluster of bundle leaves: div/rem distribution simps, the agent-invoked
`DivisionAlgorithm` full identity helper, the `int_pow` ↔ `nat_pow` bridge, and the
non-negative-int ↔ num quantifier bridges. Five are stated over ℤ by the
library; `OfNumPow` is lifted from ℝ's at install
(`IntOfRealThm`). All are bound by `InstallIntLemmaBundle`.

- **`div(m + n·p, n) → div(m, n) + p`** (`nat_divmod.go` `intDivModAddMulFold`,
  `DivMulAdd`). Auto simp in `intDivModFold`: when the dividend has a
  rightmost summand `n·p` AND `n` is a literal nonzero (so `~(n=&0)`
  discharges), strip the summand. Mirror clause for `rem` via `RemMulAdd`.
  Strict size-shrink → DeepRewrite fixpoint converges. A symbolic n with
  `n ≠ &0` in hyps would need a separate enrichment-style handler, which is not
  built. Ring AC normalization typically puts the dividend into right-associated
  form before this simp visits it.
- **`~(n=&0) ⇒ (m = div(m,n)·n + rem(m,n) ∧ &0 ≤ rem(m,n) ∧ rem(m,n) < int_abs(n))`**
  (`int_lemmas.go` `intDivisionAlgorithm` / `IntDivisionAlgorithm` export, the `DivisionAlgorithm` field).
  The agent-invoked full Euclidean-division identity. **NOT** auto-wired in
  `intArithSimpStep` / `intProveDecAtom`: it would compound with the
  bool/int_abs splits into expensive search (see
  [Euclidean division](#euclidean-division--div--rem)).
  Available to the engine/strategy layer when a div/rem-heavy goal needs the
  whole identity in one shot.
- **`int_pow(&m, n) → &(nat_pow(m, n))`** (`int.go` `intPowSimp`'s OfNumPow clause,
  `OfNumPow` lifting ℝ's). The `pow` sibling of OfNumAdd /
  OfNumMul / OfNumDiv / OfNumRem. Strict size-shrink (`int_pow` → `int_of_num`
  + `nat_pow`). The wrapped `nat_pow(m, n)` is then the num simp step's
  (`expSimp`): a power of two literals folds to its numeral (`NormNatExp`),
  `c ≤ 1` and the bases 0 and 1 reduce, and any other shape stays opaque unless
  the agent expands it (`ExpandEXPRewrite`).
- **`(∀x:int. &0 ≤ x ⇒ P x) ⇔ (∀n:num. P (int_of_num n))`** and the existential
  dual (`int_lemmas.go` `IntForallNonneg` / `IntExistsNonneg` exports, `ForallNonneg`
  / `ExistsNonneg`). Higher-order quantifier bridges that route a
  non-negative int quantifier to num so num automation can take over. **NOT**
  auto-wired in omega — quantifier handling lives above omega's atom-level
  decider; the strategy layer calls these explicitly to transform a quantified
  goal before handing the body `P(&n)` back to `arith`.

### Div/rem ↔ divides bridges

Handlers that close the gap between the Euclidean div/rem subsystem and the
int_divides subsystem — a fact in one becomes useful in the other. All five
bundle fields are stated over ℤ (there is no ℝ source to lift) and bound by
`InstallIntLemmaBundle`.

- **`rem(m,n) = &0 ↔ int_divides(n, m)`** (`int.go` `intDividesIffRemZeroSimp`,
  `DividesIffRemZero`). Goal-side simp `rem(m,n) = &0 → int_divides(n, m)`: a
  remainder-zero goal becomes a divisibility goal (closed by `intDividesGoal`);
  a hyp `rem(m,n) = &0` (via the shared hyp pre-simp) becomes
  `int_divides(n, m)` and feeds `intDividesSkolem`. Skips `n = &0 / &1` — the
  divmod-simp's domain (`RemByZero / RemByOne` fold the rem to `m / &0` directly).
- **`int_divides(d, e) ∧ e ≠ &0 ⊢ |d| ≤ |e|`** (`int.go`
  `intProveDivisorBound`, `DivisorBoundedByDividend`). An enrichment that injects the
  size bound whenever a divisibility hyp pairs with a derivable `e ≠ &0`.
  Closes the bare contradictory `int_divides(&5, &3) ⊢ ⊥` class — the
  gcd-rank-1 test doesn't fire on `int_divides(lit, lit)` (each row's
  coefficient gcd = 1), but the injected `|&5| ≤ |&3|` reduces (after the
  int_abs split on literals) to `&5 ≤ &3`, refuted by linarith.
- **`int_divides(q, m) ⊢ div(m, q) · q = m`** (`int.go` `intProveQuotientExact`,
  `QuotientExactOfDivides`). The exact-division identity as an enrichment: under a
  divisibility hyp, linarith can substitute `div(m, q)` away. Reaches both the
  direct eq form and the **subtraction form** `m − div(m,q)·q = &0` (which
  moveAcrossCmp positivizes — the residual product survives in
  multivariate-sorted shape `q · div(m,q)`; the ring-bridged `intHypEchoEq`
  closes the canonical/raw alpha mismatch against the injected fact, see
  [The image split's branch prover](#the-image-splits-branch-prover)).
- **`div(&m, &n) = &(nat_div(m, n))` / `rem(&m, &n) = &(nat_mod(m, n))`** (`nat_divmod.go`
  `intDivModFold`'s OfNum fallback, `OfNumDiv` / `OfNumRem`). The
  div/rem siblings of the `OfNumAdd/OfNumMul` bridges — `intNormNatDiv` /
  `intNormNatMod` route a literal pair through num's `nat_div`/`nat_mod` evaluator,
  fallback after `intDivModUniqWitness` for symbolic-num operands that pass the
  `int_of_num` matcher but not `intLitVal`.

### Square, pow sign, abs ordering, and the n-ary triangle

Handlers beside the linear / monotone / `Image` core, each a
near-mechanical mirror of the corresponding ℝ handler in `real_ops.go`. Their
fields are theorems over ℝ lifted at install through `IntOfRealThm`
(`liftEntry` / `liftReal` in `serve.InstallIntLemmaBundle`), except
`AbsTriangle`, a member of the `int_real_lift` chapter.

- **Square nonneg (no hyp)** (`int.go` `intProveSquareNonneg`, `SquareNonneg`).
  `⊢ &0 ≤ x·x` with no sign hypothesis — the SINGLE-LEMMA alternative to the
  `Image` sign split above (which closes the same goal via a ±&n case split
  + of_num collapse). Wired BEFORE `intImageSplit` in `intProveDecAtom`, so a
  square-nonneg goal preempts the case-split cost.
- **`int_pow` sign** (`int.go` `intProvePowSign`, `PowNonneg` / `PowPos` /
  `PowTwoNonneg`). `&0 ≤ x ⊢ &0 ≤ x pow n`, `&0 < x ⊢ &0 < x pow n`, and the
  no-hyp `&0 ≤ x pow 2`. The int twin of `realProvePowSign`.
- **`int_abs` triangle inequality** (`int.go` `intProveAbsTriangle`,
  `AbsTriangle`). Binary base + n-ary closure via iterated triangle +
  `LessEqAdd2` + `LessEqTrans`, then a `IntLinProve` transit to the goal rhs. Closes
  `|t1 + (... + tn)| ≤ rhs` when each `|tᵢ|` has a derivable bound and linarith
  can sum them. The int twin of `realProveAbsTriangle`.
- **Pow²-abs interchange** (`int.go` `intPowLawSimp`, `intAbsLessEqIffPowTwoLessEqSimp`,
  `intNegEqZeroSimp`; `SquareOfAbs` / `AbsLessEqIffPowTwoLessEq` / `NegEqZero`).
  Three goal-side simp leaves in `intArithSimpStep`: `(int_abs x) pow 2 →
  int_pow x 2` strips abs from a square; `int_pow x 2 ≤ int_pow y 2 →
  int_abs x ≤ int_abs y` pushes a squared comparison to its canonical abs LHS
  form (so a hyp `|x| ≤ |y|` closes `x² ≤ y²` directly); `(−x = &0) ⇔ (x = &0)`
  is the neg twin of `NegNonneg`/`NegPositiveIffNegative` (zero-detection through neg, which
  linarith — atomizing `−x` and `x` independently — can't see).

### Integral domain — `MulEqZero`

ℤ has no zero divisors (`MulEqZero`: `x·y = &0 ⇔ x = &0 ∨ y = &0`, the `MulEqZero` field,
lifts from `MulEqZero`). A hypothesis `a·b = &0` with **distinct** factors is turned into
the splittable disjunction `a=&0 ∨ b=&0` (`int_split.go` `intHypSplittable`, reusing the
case-split engine), so `x·y=&0, x≠&0 ⊢ y=&0` and the bare `x·y=&0 ⊢ x=&0 ∨ y=&0` close. The
**square** case `x·x=&0` collapses to a single guard (`(p∨p)⇔p`) that `ByCases` cannot
recombine, so it is handled forward instead (`intProveMulEqZeroSquare`): derive the lone fact
`x=&0` and re-prove. **Strict square positivity** `x ≠ &0 ⊢ &0 < x·x` (`intProveStrictSquare`)
reuses the same `≠`-trichotomy split as the `≠`-hyp handler (`LessThanTrichotomy`) to give `x` a
definite sign per branch, then closes each with the strict sign-of-product above —
`ByCases` over the distinct guards `x<&0` / `&0<x`. (The units fact `x·x=&1 ⇒ x=±&1` is a
further Image specialization, not yet built.)

### Divisibility — `int_divides`

`int_divides d e ⇔ ∃z. e = d·z` (`DividesDef`). `int.go`: a **goal** `int_divides(d,e)`
closes by an ∃-witness (the syntactic quotient `d·t`, or `e/d` for literals); a **hyp**
`int_divides(d,e)` is skolemized to a linear equation `e = d·z₀` (`chooseElim`), feeding the
gcd-equality test — `int_divides(&2, &1)` is contradictory because `2z = 1` has gcd 2 ∤ 1. All
divisibility hyps are skolemized in **one pass with a flat discharge fold** (nesting renames the
inner ε-witness and breaks `DeriveTrans`).

The **parity** `2∣x ∧ 2∣(x+1) ⊢ ⊥` needs one more step: skolemizing gives `x = 2z₀` and
`x+1 = 2w₀`, but the gcd test runs *per-equation* (coefficient gcd 1 each) and misses the
combined `2w₀ − 2z₀ = 1`. The decide's eq-subst rewrites a variable in the **goal** using the
hyps, but never rewrites one hyp into another. Two handlers do, at two levels. The linear
refuter combines the two on the rows:
[the elimination of equations](#the-exact-elimination-of-equations) solves `x = 2z₀` for x,
substitutes it into the rows of `x+1 = 2w₀`, and rounds what is left (`2z₀ + 1 ≤ 2w₀` to
`z₀ + 1 ≤ w₀`, `2w₀ ≤ 2z₀ + 1` to `w₀ ≤ z₀`). And `int.go`'s `intElimEqHyps` substitutes at
the TERM level: an equality hyp `x = e` derives the substituted copy `H[x:=e]` of another
**equality** hyp (`prop.DeepRewrite` + the equality), adds it, and re-decides. The rows
cannot stand in for it where x sits inside a product of the other hypothesis:
`u = w ∧ x + m·u = y + m·w ⊢ x = y` and `R = &0 ∧ m·R = y₁² + … ⊢ y₁ = R` read m·u and m·R
as monomials of their own, which no row of `u = w` or `R = &0` meets
(rational_point_bound.FrobeniusTensorInjectivity, sum_of_squares.OddMultipleDescends).
(Restricted to equality hyps — rewriting `x` into a divisibility just relocates it into a
new `int_divides` that re-skolemizes.)
The bounded / literal-divisor fragment; a variable divisor is Cooper-territory.

### Euclidean division — `div` / `rem`

`div(m,n)` / `rem(m,n)` are int Euclidean division (`m = div(m,n)·n + rem(m,n)`
with `&0 ≤ rem(m,n) < int_abs(n)` for `n ≠ &0`). It is the int twin of
the num `nat_div`/`nat_mod` bounded-atom enrichment (`nat_divmod.go`), with one int twist: num's
*unconditional* `nat_mod(m,n) ≤ m` / `nat_div(m,n) ≤ m` are **false for a signed dividend**
(int `rem ≥ 0`, so `m < 0 ⇒ rem > m`; `rem(m,n) ≤ m` is no theorem, and
the quotient bound is `|div| ≤ |m|`). So the backbone is instead:

- **literal operands** — `intDivModUniqWitness` evaluates `div(&a,&b)` / `rem(&a,&b)`
  to their numeric value via **`DivModUnique`** at the computed `(q,r)`, discharging
  the premises `&a = &q·&b + &r ∧ &0 ≤ &r ∧ &r < int_abs(&b)` through the int decider
  (the `int_abs(&b)` upper bound via the int_abs split). A simp fold, so it collapses
  a div/rem redex anywhere. Closes `div(&7,&2) = &3`, `rem(&7,&2) = &1`. The `&0`/`&1`
  divisor folds (`DivByZero`/`RemByZero`/`DivByOne`/`RemByOne`) cover `n = &0` (where
  the evaluator declines) and a symbolic dividend over `&1`;
- **bounded-atom enrichment** (`intProveDivRem`) — for a symbolic dividend over a
  literal/positive divisor, inject the **unconditional** identity (`DivisionIdentity`)
  plus `&0 ≤ rem(m,n)` (`RemNonneg`) and `rem(m,n) < n` (`RemBelowDivisor`, when `&0 < n`
  discharges), then re-run linarith — for a literal divisor `div(m,n)·n` is linear in
  the `div` atom, so ℤ-discreteness pins what it can. Closes `&0 ≤ rem(m,&3)`,
  `rem(m,&3) < &3`, `m = div(m,&3)·&3 + rem(m,&3)`, and `&0 < n ⊢ rem(m,n) < n`;
- **the general `n ≠ &0` bound** — for a **negative / unknown-sign** divisor (where
  `RemBelowDivisor`'s `rem < n` is false), inject `&0 ≤ rem(m,n)` (`RemNonneg`) and
  `rem(m,n) < int_abs(n)` (the `RemUpperAbs` field) whenever `n ≠ &0`
  discharges — explicitly, or from `&0 < n` / `n < &0` (`intProveNeqZero`). The re-run
  also tries the int_abs case split, so the `int_abs(n)` bound composes to a sign-specific
  goal: closes `n ≠ &0 ⊢ rem(m,n) < int_abs(n)`, `n < &0 ⊢ &0 ≤ rem(m,n)`, and
  `n < &0 ⊢ rem(m,n) < −n` (int_abs(n) pinned to −n).

Not handled: the symbolic `n = &0` split off `RemUpperAbs`'s `(n=&0) ∨ …`
disjunction (for goals valid for *all* n, including n=0). As an always-on
handler it compounds with the bool/int_abs splits into an expensive search; it
needs a guarded or agent-invoked form.

### Soundness and completeness

`serve.InstallIntBundle` (called from `initEngine`) binds every
`IntLemmaBundle` field to a theorem of the library, and the binding tests
(`TestInstallIntLemmaBundleBinding*`) are the ground truth — fabricator-free,
so a bundle-nil field panics. omega's own algorithm tests exercise the kernel
composition against placeholder TestThms (the package-local fabricator a test
file's `init` installs), independent of the library. The layer is not
complete for ℤ: the gcd-cut / Cooper-QE frontier is open — see
[Future work](#future-work).

## The structure ring — the ring at a ring or field record fact

`structure_ring.go` instantiates the ring normalizer (`ringVocab`), the
signed normalizer (`subnegVocab`) and a `Domain` at a COMMUTATIVE-RING
STRUCTURE FACT instead of at a number type's constants — the fourth
arithmetic layer, and the one that is not a twin. The leaves read the
algebra chapters' carrier laws (`StructureRingLaws`, installed by
`serve.InstallStructureRingBundle` in their STATED form `∀R.
comm_ring_on(R) ⇒ ∀x y. x ∈ R.carrier ∧ … ⇒ body`) at the fact's
record, its operations and carrier the record's fields computed in the
instance normal form, discharging the structure hypothesis from the
fact: a resident `comm_ring_on(R)` or `field_on(F)`, or a whole-type
`comm_ring(R)` or `field(F)` read through `CommRingOnUniverse` /
`FieldOnUniverse` as the record restricted to `𝕌` (an abstract
chapter's ring, carried as a hypothesis of every leaf theorem — the
composition below the leaves carries hypotheses as it always did, and
IsStronger is what refuses a close whose fact the goal lacks;
`ring_hyp_leaves_test.go` pins this), or an installed instance theorem
(`StructureInstance`: ℂ's `complex_field.Field`, hyp-free). Every
membership guard is discharged: on `𝕌` by `InUniv`, on another carrier
from the context. The numerals are the additive powers of one,
`monoid_pow(add, zero, one, n)`,
folded by comm_monoid.PowAdd at the additive
monoid and comm_ring.AddPowMul; a literal spelled otherwise — the `zero`
and `one` components, a carrier's own `complex_of_real(&n)` — is read by
`asLiteral` and bridged to the canonical numeral by
`ringVocab.literalBridge` (`complex_field.AddPowOne`), so the canonical
form is internal. The power `monoid_pow(mul, one, x, n)` at a literal
exponent is the pow basis's chain; a field's `div(u, v)` is the quotient
basis's `mul(u, inv(v))`; the equality move-across laws are DERIVED from
group right cancellation, `SubAddNeg` and the identity laws rather than
read.

Dispatch: an equation at a carrier that is not num / real / int, whose
operators are the components of a fact available in the goal's
hypotheses or installed — or, between two atoms naming no operation,
any such fact at the carrier once the context holds an equation there
(`IsStructureRingContent`, `structureRingsForAtom`) — under
`ArithPolicy.Structure` (the capability `arith:structure`, roots = the
laws and the instances). Two leaves beside the twins': the move-across
(sub/neg into the positive two-sided form) and the equality decider —
a ring identity (`ringProveFull`), or an INTEGER linear combination of
the context's equations over the monomial basis (Gaussian elimination
over ℚ in `ratPoly`, declined unless every coefficient is an integer:
over a general ring nothing divides by a numeral; the replay is
`⊢ l + Y = r + Y'` by the ring, `⊢ Y' = Y` from the hypotheses by
congruence, and the additive group's right cancellation). The context's
equations are the hypotheses and the conjuncts of hypotheses at the
carrier (`contextEquations`, as `Domain.extractHypConstraints` reads
the number domains'); on a carrier set one over an atom without a
resident membership is not read, and `StructureRingMissingMemberships`
names that atom beside the goal's. At a FIELD, a factor and its
inverse cancel wherever they stand in a monomial, as over ℝ — every pair
a monomial holds, and a divisor that is a product factor by factor, the
inverse of a product being read as the product of the inverses
(`InvMul`, `field.InvMulOn`): once the
context's equations alone decline, the unit facts `R·(inv(t)·t) = R`
the sequent's inverse atoms ask for (`unit_facts.go`, the search ℝ
shares, which reads each cofactor it finds as one more monomial) join
them for one more combination, each proved from the
field's left inverse law (`MulLeftInverse`, `field.MulLeftInverseOn`)
on the context's evidence that t is not zero — a resident `t ≠ zero`,
or a resident disequality that `t = zero` contradicts by the
combination, or once zero is put for t, so that a product shown nonzero
is evidence for each factor (`structure_unit_facts.go`). A field may have a
characteristic, so at an abstract field no literal is nonzero without
such evidence. An instance that names an injective embedding of ℝ
(`StructureInstance.RealEmbedding`: ℂ's `complex_of_real`, by
`complex_field.OfRealInjective`) has characteristic zero: there
`embed(r) ≠ zero` follows from ℝ's own evidence `r ≠ &0`
(`realProveNeqZero`, the context included) through injectivity, under
`ArithPolicy.Real`, so ℂ's literal `complex_of_real(&2)` needs no
premise.

The decider answers ⊥ as well as ⊤ (`structure_refute.go`). What a
context denies at the carrier is its disequalities, and at a field
`one ≠ zero` (`OneNotZero`, `field.OneNotZeroOn`); an equation `l = r` is
refuted where the context's equations and `l = r` combine by integers to
`p = q` for a denied pair — `zero * w = one` at a field, `z + one = z`,
and with a zero side whatever the evidence above shows not zero. A
commutative ring that is no field denies nothing by itself: the zero
ring is one. At a field the evidence that a term is not zero also reads
the term's parts — a product by its factors, an inverse and a quotient
by their arguments, a negation by its argument — and the same law read
forward gives, from a context equation `x·y = zero` with x shown not
zero, the equation `y = zero` for the combination to read. A context
equation whose two sides share a factor shown not zero gives the
equation of what is left of them (`cancelledEquations`), a factor at a
time. All three are one cancellation (`cancelFrom`): the equation times
`inv(x)`, and the unit facts of x. A power reads the same way through
`PowEqZero` (`field.PowEqZeroOn`): it is not zero where its base is not,
and a context equation `xⁿ = zero` gives `x = zero`.

A
POLYNOMIAL coefficient is the author's: `ScaleEquation` is what a `Scaled(c, h)`
By premise adds — the congruence `{l = r} ⊢ c·l = c·r` under the
carrier's multiplication (num, real, int or a structure ring). Order is
not read: the Domain's comparison matchers never match.

## Code map

**File-naming convention: a `nat_`/`real_`/`int_` prefix = that domain's
instantiation; a bare name = the domain-generic machinery shared by all three
(behind the `Domain` / `ringVocab` / `subnegVocab` seams).** So to find a domain's
code, grep its prefix; to find the shared engines, look at the unprefixed files.

| area | files |
|---|---|
| **shared / generic** | |
| Domain seam + the three instances (`natDomain`/`realDomain`/`intDomain`) + matchers / term builders | `domain.go` |
| ring (model + replay; domain-generic over num/ℝ/ℤ via `ringVocab`, full multivariate + signed) | `ring.go` |
| linarith ℚ-Farkas FM core (`atomTable`/`row`/`LinRefute`) | `linarith.go` |
| the model's exact integers (`_Integer`, and `_Vector` for a row) | `integer.go` |
| the pow basis, the quotient basis and the inverse basis (a literal power, a symbolic quotient, the inverse of a product read as monomials) | `pow_basis.go`, `quotient_basis.go` |
| the ring normal form as a rewrite (`RingNormalizeRewrite`) | `ring_nf.go` |
| ground congruence: a compound hypothesis equation substituted into the term the decider reads | `congruence_subst.go` |
| the variable-sided rule (a hypothesis `v = e` read as a definition), and a target that denies a value decided by the same reading | `variable_subst.go`, `denied_value.go` |
| a zero-sided equation read in either orientation | `zero_sided.go` |
| the structure ring (the ring at a ring or field record fact), a factor beside its inverse at a field, the refutation of an equation the context denies, and at a field the cancellation of a common factor and a power's zero test | `structure_ring.go`, `structure_unit_facts.go`, `structure_refute.go` |
| a factor beside its inverse in a monomial: the cofactor search ℝ and the structure ring share | `unit_facts.go` |
| `ArithPolicy` and the bundles' foundation closures (the self-circularity gate) | `circularity.go` |
| signed normalizer + relation move-across (sub/neg, shared int+real via `subnegVocab`) | `subneg.go` |
| case-split engine (`caseSplit`/`enrichAndCut`/`splittableAtom`) + the unified `arith` decide driver (`ArithDecideWithHyps`) | `engine.go` |
| bundle leaf-macros (`eqLeaf`/`implyLeaf`/`macroEq`) + placeholder seam + `IntOfRealThm`-style derive helpers | `bundle.go` |
| kernel-rule helpers (`chooseElim` for ∃-elimination / ε-discharge; `freshVar` / `freshNumVar` for the freshness side condition; `disjSyllogism` for orientation-agnostic ∨-elim under a refuted disjunct) | `prop_helpers.go` |
| **num (`nat`)** | |
| decide leaf + simp step + `factorial` + eq-subst + disjunction + formula bool-split | `nat.go` |
| ring AC/identity leaves + `NatLemmaBundle` (struct + accessors) | `nat_lemmas.go` |
| norm_num (bit recursion `NormNat*` + comparison bit lemmas) | `nat_norm.go` |
| linarith discharge + scaling/add2 lemmas + forward provers (`LinProve`/`OmegaProve`) | `nat_linarith.go` |
| Presburger-over-num (gcd rounding cut, `notDivides`, the `dvd` layer) | `nat_omega.go` |
| exact elimination of equations ahead of Fourier–Motzkin, shared by `num` and `int` | `equation_elimination.go` |
| `nat_div`/`nat_mod` (simp + distribution + bounded-atom enrichment), and the int Euclidean `div`/`rem` handlers | `nat_divmod.go` |
| monus + `nat_max`/`nat_min`/`predecessor`/`nat_even`/`nat_odd`/`nat_dist` + the nat split recognizers | `nat_sub.go` |
| `nat_pow` literal-exponent unfold + bounded enumeration (`proveBoundedEnum`, `proveBoundedExists`) | `nat_exp.go` |
| a zero product's split, the positivity of a product of positive factors and of a power of a positive base, a zero power's base | `nat_products.go` |
| the scaling of a comparison by the factors its sides share, and their cancellation from a hypothesis, on ℕ | `nat_scaling.go` |
| the factors two products share, read up to order and grouping | `shared_factors.go` |
| **real (ℝ)** | |
| decide leaf (`realProveDecAtom`) + simp step + `RealArithDecideWithHyps` + bool-split leaf + engine glue (`RealArithEnabled`/`IsRealArithContent`) | `real.go` |
| ring leaves + `realRing` norm + `RealLemmaBundle` (struct + accessors) + scale/add2/subneg leaves | `real_lemmas.go` |
| linarith certificate replay (the `IsStronger` discharge) | `real_linarith.go` |
| operator handlers — case splits + monotone/sign-of-product/square + field (`real_div`/`real_inv`) + `real_pow` + abs/sgn algebraic laws + `real_of_num` collapse | `real_ops.go` |
| pairwise products, monomial sign rows, the cancellation from a hypothesis of a positive factor and, for an equation, of a factor that is not zero | `real_products.go`, `real_sign_rows.go`, `real_cancel.go` |
| field evidence: a quotient by a numeral anywhere in the sequent — added, or multiplied by a cofactor — nonzeroness of a term, a factor beside its inverse in a monomial | `real_quotient.go`, `real_nonzero.go`, `real_unit_facts.go` |
| **int (`int` type)** | |
| decide leaf + the full handler chain (`int_pow`/eq-subst/enum/`int_of_num` collapse/Image/`int_divides`/Euclidean `div`-`rem`/monotone/MulEqZero) | `int.go` |
| `IntLemmaBundle` + ring leaves + `intRing` norm + the `IntOfRealThm` lift | `int_lemmas.go` |
| linarith certificate replay + ℤ-discreteness + GCD-equality test + rounding cut + the elimination pass | `int_linarith.go` |
| operator case splits (`int_abs`/`int_max`/`int_min`/`int_sgn`/COND) + hyp splits (∨/≠/⇒/product-zero) + formula bool-split | `int_split.go` |
| pairwise products, monomial sign rows, positive-factor cancellation from a hypothesis (the ℝ files' twins) | `int_products.go`, `int_sign_rows.go`, `int_cancel.go` |
| **DSL agent surface (ℤ/ℝ ops)** | `ext/dsl/arith.go`, `ext/dsl/build.go`, `ext/dsl/ast.go`, `ext/dsl/parser.go`, `ext/format.go` |

## Testing

```sh
# from the repository root
go test ./prover/solver/omega/        # unit tests (TestThm-backed leaves)
go test ./library/serve/ -run TestInstallNatBundleBinding         # library binding: nat
go test ./library/serve/ -run TestInstallRealBundleBinding        # library binding: real
go test ./library/serve/ -run TestInstallIntLemmaBundleBinding    # library binding: int
go test ./engine/ -run Arith   # engine `arith` move surface
```

Unit tests exercise the algorithm and kernel composition against
`core.TestThm`-fabricated bundles (the fabricator is installed only from
a test file, via `SetPlaceholderFabricator` — the placeholder seam in `bundle.go`); the
`TestInstall{Nat,Real,Int}*Binding` suites in `library/serve` are the soundness ground truth — they run in a
fabricator-free package, so every leaf must bind its library theorem or
panic, the only place orientation/shape drift against the bound theorems surfaces.

## Future work

- **Integer completeness frontier.** The elimination of equations rounds the
  rows a substitution leaves, each a node the certificate names beside the
  input rows (`equation_elimination.go`). Three things past it are unbuilt: an
  equation with no atom of coefficient ±1 (`2·a = 3·b + 1`; the Omega test
  solves it through a fresh variable, an ∃-introduction the replay has no
  step for), a cut on a row Fourier–Motzkin derives between two inequalities
  (a further node per combination, in the engine's inner loop), and full
  Presburger, which needs Cooper QE with proof-producing per-step
  equivalences (`∃x.φ ⟺ ⋁…`). The "dark shadow" is *not* applicable to
  refutation (it is a sufficient condition for SAT). ℚ-Farkas, the rounding
  of a row, the elimination, monus and the hyp/COND splits cover the common
  corpus goals.
- **ℝ field-clearing depth.** The denominator-clearing path handles one
  outer division per atom; multi / nested denominators
  (`a/b + c/d`, `a/(b/c)`, …) need a generalization. Full
  division/inverse automation is demand-driven and unbuilt — the
  sub-RCF / field suite decides the sign-known fragment plus
  the positive-divisor clearing, which covers the common corpus goals.
- **`int` completeness frontier (ℤ-unique, demand-driven).** The
  rank-1 layer (gcd-equality test, gcd rounding cut, `Image` sign split,
  bounded / literal-divisor `int_divides`,
  sign-known nonlinear fragment, Euclidean `div`/`rem` for literal operands +
  positive- and unknown-sign divisors — see the int-layer body sections) covers
  the common goals, with the elimination of equations (shared with `num`)
  behind it. Open past them, as on `num`: an equation with no atom of
  coefficient ±1, a cut on a row Fourier–Motzkin derives, Cooper QE
  (proof-producing `∃x.φ ⟺ ⋁…`), plus general (variable-divisor)
  `int_divides` elimination.
  A smaller non-Cooper extension is also unbuilt: the symbolic `n=&0` split off
  `RemUpperAbs`'s disjunction (as an always-on handler it compounds
  into an expensive search; it needs a guarded/agent-invoked form). Expensive, no
  real analogue to lift.
- **Bounded existential search.** `nat_exp.go::proveBoundedExists` (the ∃-dual
  of bounded enumeration) is written and unit-tested but **wired to nothing** — it
  must NOT live in always-on `arith` (a bounded-∃ goal usually has a better
  structural proof, which enumeration would preempt and persist into the corpus).
  It awaits an explicit, agent-invoked `bounded_qe`-style move, sequenced after the
  structural attempts. (The ∀ direction needs no new code: `strip_quant ;
  assume(i<c) ; arith`.)
- **A more general `ring`** (optional): non-commutative semirings, and explicit
  powers in a monomial instead of repeated factors.
