# real_sgn_abs — ℝ's sign–absolute-value pair

Two functions enter ℝ by cases at the same layer: the absolute value
`|x| = COND(&0 ≤ x, x, -x)`, one guard on the nonstrict order, and the
sign `sgn(x) = COND(&0 < x, &1, COND(x < &0, -&1, &0))`, two nested
guards on the strict one. This chapter is where both case definitions
become algebra: every law here quotients the sign split away, so that
a consumer can reason about `|·|` and `sgn` by citing rather than by
reopening a COND. One consumer still does the opposite: ℤ's
construction unfolds both definitions directly, `int_construction` on
`real_abs` and again on `real_sgn`, where the laws here would serve.

The distance between two reals is defined here too — `real_dist(x, y)
= |x − y|`, written `dist(x, y)`, the word ℕ's and ℝⁿ's distances share
— since it is the magnitude of a difference and nothing more; the
chapters that read the line as a metric space (`real/real_topology`)
cite it, and its three axioms are the arithmetic closer's.

They are one chapter rather than two because they are mirror halves of
one decomposition. `|x|` is the magnitude and `sgn x` the direction,
and the polar family — `sgn x · x = |x|`, `x = sgn x · |x|`,
`x = y ⇔ |x| = |y| ∧ sgn x = sgn y` — is about the PAIR, with no
natural home when the halves are split. The downstream demand arrives
in pairs too: `real_sqrt` is DEFINED by naming both
(`sqrt x = εy. |x| = y² ∧ sgn x = sgn y`), and ℤ lifts its `int_sgn`
and `int_abs` theory by the same transport. Members carry an `Abs` or
`Sgn` prefix for the half their statement is about — a polar member
takes the prefix of its subject, and only one that is symmetric in the
two halves takes neither.

The theory unfolds in seven movements. The abs wing is movements 1–3,
movement 4 has the sign's own three laws, movement 5 has the law that
ties the halves together, movement 6 has the six division laws, and
movement 7 holds the two interval equivalences, a window that keeps
away from 0, and their summit, the triangle inequality, with its forms
at a difference and a size bounded by one plus its square.

**1. The two unconditional bounds**:

- **`AbsNonneg`** — `∀x:real. &0 ≤ real_abs(x)`. A size is never
  negative.
- **`AbsDominates`** — `∀x:real. x ≤ real_abs(x)`. Nothing exceeds its
  own size, and it reaches `AbsNonneg` rather than repeating its sign
  analysis — which is what makes the pair an opening rather than two
  transcripts.

**2. Symmetry, fixed points and the equations** —
which arguments the size leaves alone, which it flips, and which
single argument it sends to &0:

- **`AbsEven`** — `∀x:real. real_abs(-x) = real_abs(x)`. The size
  forgets the sign.
- **`AbsFixedIffNonneg`** — `∀x:real. real_abs(x) = x ⇔ &0 ≤ x`.
  Exactly when the case split was vacuous.
- **`AbsNegatedIffNonpos`** — `∀x:real. real_abs(x) = -x ⇔ x ≤ &0`, its
  dual: when the size is a reflection instead. Between them they cover
  the line, and they OVERLAP at &0, where a value is fixed and reflected
  at once — consistent only because `-&0 = &0`, and settling that is the
  member's whole content. It is kept because three members need the
  overlap settled and none of them is about it.
- **`AbsOfZero`** — `real_abs(&0) = &0`. That characterization at the
  one point where the definition's two branches agree.
- **`AbsIdempotent`** — `∀x:real. real_abs(real_abs(x)) = real_abs(x)`.
- **`AbsOfNum`** — `∀n:num. real_abs(&n) = &n`, and **`AbsOfOne`** at
  the unit.
- **`AbsVanishes`** — `∀x:real. real_abs(x) = &0 ⇔ x = &0`, and
  **`AbsPosIffNonzero`** — `∀x:real. &0 < real_abs(x) ⇔ x ≠ &0` — the
  same fact with the order put back in.

The last four are the characterizations read at particular values, so
the file's shape is two case analyses and six citations of them; each
member's own doc comment says which reading it is.

**3. The multiplicative law**:

- **`AbsMul`** — `∀x y:real. real_abs(x * y) = real_abs(x) * real_abs(y)`.
  Sizes multiply. The chapter's first argument about two arguments,
  and its case analysis is correspondingly two-dimensional.

**4. The sign function** — everything the definition's two
nested guards say about the sign on its own, before it is paired with
the size:

- **`SgnTrichotomy`** —
  `∀x:real. real_sgn(x) = -&1 ∨ real_sgn(x) = &0 ∨ real_sgn(x) = &1`.
  The sign takes three values and no others, which is what lets every
  later argument treat it as a three-valued quantity instead of as a
  pair of guards.
- **`SgnOfZero`** — `real_sgn(&0) = &0`. At this one argument both
  guards ask the same question, so failing it once sends both to the
  last branch together.
- **`SgnOdd`** — `∀x:real. real_sgn(-x) = -real_sgn(x)`. The mirror of
  `AbsEven`: between them the pair says what negation does to the polar
  decomposition, leaving the magnitude alone and reversing the
  direction.

The shape invites a trichotomy split and none of the three needs one,
each avoiding it differently: the range law reads off what the reduced
guards already offer, `SgnOfZero` decides both at once because at that
argument they ask the same comparison, and `SgnOdd` rewrites the guards
until the two sides of its equation test the same conditions.

**5. The polar decomposition** (shared with movement 6)
— where the two halves finally meet:

- **`SgnMulSelfIsAbs`** — `∀x:real. real_sgn(x) * x = real_abs(x)`.
  Direction times magnitude is magnitude. It is the chapter's first
  argument that has to relate the two functions rather than develop one
  of them, and correspondingly its first case analysis: the two sides
  are guarded by different tests, and nothing aligns them.

Its relatives arrive as demand pulls them: the decomposition
`x = sgn x · |x|` read the other way, and the uniqueness form
`x = y ⇔ |x| = |y| ∧ sgn x = sgn y`, which is the pair's separation
fact — two reals agree exactly when they agree in size and in
direction.

**6. The division wing** — what inversion and division
do to the pair. It shares a file with movement 5, and the reason is the
argument rather than the size of either: the two polar members are what
let every member here treat a sign as a value over its size instead of
as a pair of guards, so the laws below are calculations only because the
decomposition above was proved first. These are the laws the field
chapters leave to "their own chapters": the algebra of `inv`/`div`
lives in `real_field`/`real_order_field`, but what INV AND DIV DO TO
size and sign is this pair's business.

- **`AbsInv`** — `∀x:real. real_abs(real_inv(x)) = real_inv(real_abs(x))`.
  The size of an inverse is the inverse of the size, learned the way the
  field chapter learns every inverse: exhibit a product equal to `&1`
  and let uniqueness name the factor.
- **`AbsDiv`** — `∀x y:real. real_abs(x / y) = real_abs(x) / real_abs(y)`.
  Nothing of its own to prove — a quotient is a product with an inverse,
  and the two laws above carry one side onto the other.
- **`SgnPreservedByInv`** — `∀x:real. real_sgn(real_inv(x)) = real_sgn(x)`.
  A reciprocal points where the number it inverts points. Inversion
  changes neither of the sign's two questions, so the guards rewrite
  across and no case is ever decided — `SgnOdd`'s move again.
- **`SgnEqSelfDivAbs`** — `∀x:real. real_sgn(x) = x / real_abs(x)`.
  Dividing by the size is what taking the sign IS: the quotient throws
  the magnitude away and keeps the direction. Here the guards cannot be
  rewritten across — the size asks one nonstrict question and the sign
  two nested strict ones — so the three regions are decided instead, by
  the peel movement 5 opened.
- **`SgnMul`** — `∀x y:real. real_sgn(x * y) = real_sgn(x) * real_sgn(y)`,
  and **`SgnDiv`** at the quotient. These are what `SgnEqSelfDivAbs` is
  for: once every sign in the goal is restated as a value over its size,
  no guard is left to ask about and the whole statement is one
  rearrangement of a four-factor product. Both are calculations, and
  they close the movement the way `AbsDiv` closed its half — by
  rewriting rather than by deciding.

**7. Intervals** — a bound on a size, read as a
two-sided bound on the value:

- **`AbsBounds`** — `∀x k:real. real_abs(x) ≤ k ⇔ -k ≤ x ∧ x ≤ k`. A
  size bound IS the pair of bounds, in both directions. The size
  dominates the value and its reflection alike, which gives both ends
  at once; going back, the definition takes one of two values each
  already bounded, so the guard never has to be decided.
- **`AbsBetween`** — `∀x y d:real. real_abs(y - x) < d ⇔ x - d < y ∧ y < x + d ∧ &0 < d`.
  The same statement one order relation over and applied to a
  difference: y lies within d of x exactly when it lies in the open
  interval of radius d around x — the form every metric estimate is
  actually stated in.
- **`NonzeroNear`** — `∀a b:real. real_abs(a - b) < real_abs(a) ⇒ b ≠ &0`.
  A real closer to a than |a| is not 0: the window of radius |a| about
  a is (0, 2a) or (2a, 0), by the sign of a.

- **`AbsTriangle`** — `∀x y:real. real_abs(x + y) ≤ real_abs(x) + real_abs(y)`.
  The chapter's summit and the gateway to every metric estimate above:
  what lets a quantity be broken into pieces and bounded piece by
  piece. The proof is `AbsBounds` read in both of its directions — a
  size brackets its own value for nothing (the bound it asks for is
  reflexivity), two such brackets add end by end, and a bracket by
  `±(|x| + |y|)` IS the statement.
- **`AbsTriangleSub`** — `∀x y:real. |x - y| ≤ |x| + |y|`. The
  triangle inequality at x and −y, the reflection forgotten by `AbsEven`.
- **`AbsReverseTriangle`** — `∀x y:real. ||x| - |y|| ≤ |x - y|`. Sizes
  differ by at most the size of the difference: the triangle inequality
  at x = (x − y) + y and at y = (y − x) + x brackets |x| − |y|.
- **`AbsSubComm`** — `∀x y:real. |x - y| = |y - x|`. The distance reads
  the same both ways, `AbsEven` at a difference.
- **`AbsQuadraticBound`** — `∀x:real. |x| ≤ &1 + x * x`. The squares of
  x + 1 and x − 1 are nonnegative, so 1 + x² lies above x and −x.

Three kinds of customers pull on this chapter. ℤ inherits its entire
size-and-sign theory by transport — `int_abs` is DEFINED as
`int_of_real(real_abs(real_of_int x))` and `int_sgn` likewise, so
every law here becomes a ℤ law one `IntOfRealDerive` step later, and
`int_num/int_real_lift`'s abs members are those lifts. ℤ's
CONSTRUCTION reaches further back: the predicate ℤ is carved by is
stated with `|·|`, so `int_num/int_construction` cites these laws
directly rather than lifting them. And the developments above ℝ
consume the pair together — `real_sqrt`'s definition names both halves,
and the analysis layer takes the interval and triangle laws.

Laws that mention a still-later layer — `real_sqrt`, `real_sup`/`real_inf`,
`real_max`/`real_min` — belong to those layers' chapters, not here, the
same criterion the order chapters use. **Powers, too** — and they are
worth a sentence. By subject they look like ours: what a power does TO
a size or a sign is this pair's business, exactly as inversion and
division are, and on that reading `sgn(xⁿ)` and the two ℤ-exponent
laws belong here. But this chapter sits BELOW `real_pow` in the import
order and cannot reach up: `real_pow` depends on this chapter through
five packages, including the ℤ chapters that lift these very abs laws.
So the three power laws live in `real_pow`, next to the ℕ-exponent
`|xⁿ| = |x|ⁿ` — which is where the reader wants them anyway, since
every ℤ-exponent law in that chapter is written beside its ℕ original.

Framework mechanics (typed cites, recorded deps, the family pb, replay) are the
standard ones: see `library/chapter_constitution.md` and
`library/registry/`.
