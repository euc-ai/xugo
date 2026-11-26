# int_real_lift — ℤ inherits its algebra from ℝ

int is carved out of ℝ (`int_construction`) and every operation is
defined by transport along real_of_int, so ℤ's ring, order,
absolute-value and sign laws are not re-proved — they are the images of
their ℝ twins under the embedding, one transport step each.

This family is that chapter. Its members are the lifted laws the corpus
cites — a one-step lift has no argument to record, so a member here is
its statement — and the laws that complete a GROUP those sit in. A
group is a set of statements this chapter states together and a reader
reads together: a slot pair (left / right), a relation pair (≤ / <), a
sign pair, the corners of a composition square, the laws that make a
relation an order, or the values a constant takes where the chapter
otherwise only says what it does. A member that completes a group
names its group in its doc comment. Three of the four corners of
translation-invariance — `LessEqAddRight`, `LessEqAddLeft` and
`LessThanAddLeft` — would look like a claim about which combinations
survive a translation; there is no such claim, and reading past the
gap costs more than stating the fourth.

What is NATIVE to ℤ — the division algorithm, divisibility, the ℕ↔ℤ
boundary — lives in the sibling families (`int_div_rem`, `int_divides`,
`int_embed`), and how the type is built out of ℝ belongs to
`int_construction` below them.

Discreteness (`x < y ⇔ x + &1 ≤ y`) is the one native thing that is
NOT here — it found its home in `int_embed.Discrete`,
proved from the image analysis rather than lifted, there being
nothing in ℝ to lift it from.
There is no `int_order`: ℤ's order is almost entirely inherited, so the
order laws are this chapter's, and the handful that are not turn out to
be division facts wearing an order relation.

`IntRingDef` packs the integer operations and carrier `𝕌` into
`int_ring: ring_ops(int)`. `AddGroup` states
`abelian_group(additive_group(int_ring))` and `CommRing` states
`comm_ring(int_ring)`, the structures on the whole type; `CommRingOn`
states `comm_ring_on(int_ring)`, the same ring on its carrier `𝕌`,
where a chapter reads the laws of a ring on a set, and
`IntegerRingCarrierUniversal` puts every integer in that carrier.

ℤ as an instance of the abstract structures — the lifted ring laws
assembled, one case per axiom, into `AddMonoid`, `MulMonoid`,
`AddGroup` and `CommRing`, which `CommRingOn` reads on the carrier,
and the four fold facts they yield:
`MonoidalAdd`, `NeutralAdd`, `MonoidalMul`, `NeutralMul`. The
embedding itself is an instance too: `RealOfIntHom` says `real_of_int`
is a homomorphism of additive groups ℤ → ℝ — the two additive groups,
each read as a group, and the additive bridge, one case each.

Members, by what they are about — the ring:

- **`AddLeftIdentity`** — `∀x:int. &0 + x = x`
- **`MulLeftZero`** — `∀x:int. &0·x = &0`
- **`MulRightZero`** — `∀x:int. x·&0 = &0`. Stated on both sides rather
  than once plus commutativity: the sites that want it are zero-divisor
  branches whose whole argument is one line, and reaching it through the
  other one would put a commutation premise in every one of them.
- **`MulAssoc`** — `∀x y z:int. x·(y·z) = (x·y)·z`
- **`LeftDistrib`** — `∀x y z:int. x·(y + z) = x·y + x·z`
- **`MulSym`** — `∀x y:int. x·y = y·x`
- **`AddRightIdentity`** — `∀x:int. x + &0 = x`
- **`SubRightZero`** — `∀x:int. x − &0 = x`. Read against `SubLeftZero`
  (`&0 − x = −x`, its neighbour in the ring section), which is NOT an identity:
  subtraction has a right unit and no left one, and the pair says so.
- **`SubRefl`** — `∀x:int. x − x = &0`
- **`SubEqZero`** — `∀x y:int. x − y = &0 ⇔ x = y`. The difference is
  the whole of the equality: a congruence chapter and a uniqueness
  argument both end by reading a vanishing gap back as an equation.
- **`SubTriangle`** — `∀a b c:int. (a − b) + (b − c) = a − c`. Two
  consecutive differences telescope, which is how an argument that moves
  one factor at a time adds its steps up.
- **`SubAddPairwise`** — `∀a b c d:int. (a − c) + (b − d) = (a + b) − (c + d)`
- **`SubLeftDistrib`** — `∀x y z:int. x·(y − z) = x·y − x·z`
- **`SubRightDistrib`** — `∀x y z:int. (x − y)·z = x·z − y·z`
- **`EqSubRightAdd`** — `∀x y z:int. x − y = z ⇔ x = z + y`. Solving a
  difference, which is how a decomposition gets rearranged.
- **`MulRightCancel`** — `∀x y z:int. y·x = z·x ⇔ x = &0 ∨ y = z`.
  `MulLeftCancel`'s mirror: the factor cancels off the right as it does
  off the left, its own vanishing the one alternative in both.

negation, in the ring:

- **`NegZero`** — `-&0 = &0`
- **`NegNeg`** — `∀x:int. -(-x) = x`
- **`MulLeftNeg`** — `∀x y:int. (-x)·y = -(x·y)`
- **`NegAdd`** — `∀x y:int. -(x + y) = -x + -y`. Negation distributes
  over a sum, which with `NegNeg` is what lets a sign be pushed through
  an expression rather than carried alongside it.

the order:

- **`LessEqRefl`** — `∀x:int. x ≤ x`
- **`LessEqTrans`** — `∀x y z:int. x ≤ y ∧ y ≤ z ⇒ x ≤ z`
- **`LessEqAntisym`** — `∀x y:int. x = y ⇔ x ≤ y ∧ y ≤ x`
- **`LessEqTotal`** — `∀x y:int. x ≤ y ∨ y ≤ x`. Of any two integers one
  is at or below the other — with reflexivity, transitivity and
  antisymmetry, the last of the four laws that make ≤ a TOTAL order.
- **`LessEqOfEq`** — `∀x y:int. x = y ⇒ x ≤ y`. An equation is a weak inequality.
- **`NotLessThan`** — `∀x y:int. ¬(x < y) ⇔ y ≤ x`. The strict order IS
  the negation of the reversed weak one, which is why so many proofs
  reach for this rather than for a second order fact.
- **`LessThanTrichotomy`** — `∀x y:int. x = y ∨ x < y ∨ y < x`. Every pair is decided one of three ways.
- **`LessThanIrrefl`** — `∀x:int. ¬(x < x)`. `LessThanTrichotomy` offers
  three cases; this is what keeps the first from overlapping the other
  two, and it is what a proof by contradiction closes on once it has
  driven a quantity below its own value.
- **`LessEqSplit`** — `∀x y:int. x ≤ y ⇔ x < y ∨ x = y`. `LessThanSplit`
  read from the other side: the same content in the second of the two
  shapes an argument wants it in — that one to sharpen a bound, this one
  to case-split one already in hand.
- **`LessEqLessThanTrans`** — `∀x y z:int. x ≤ y ∧ y < z ⇒ x < z`
- **`LessThanLessEqTrans`** — `∀x y z:int. x < y ∧ y ≤ z ⇒ x < z`
- **`LessThanTrans`** — `∀x y z:int. x < y ∧ y < z ⇒ x < z`. The square's
  last corner: with the three above it, every way of composing a ≤ with a
  < has a law, so a chain never weakens a link just to knit it.
- **`LessThanAddRight`** — `∀x y z:int. x + z < y + z ⇔ x < y`.
  `LessEqAddRight`'s strict reading.
- **`LessEqAddLeftImp`** — `∀x y z:int. y ≤ z ⇒ x + y ≤ x + z`.
  `LessThanAddLeftImp`'s non-strict companion: the direction a chain uses
  when it is translating a bound it holds rather than recovering one.
- **`LessThanMulRight`** — `∀x y z:int. x < y ∧ &0 < z ⇒ x·z < y·z`.
  `LessThanMulLeft`'s mirror, stated on both sides for the reason
  `MulRightZero` is: reaching one through the other would put a
  commutation premise in every scaling step.
- **`LessEqMulRightEq`** — `∀x y z:int. &0 < z ⇒ (x·z ≤ y·z ⇔ x ≤ y)`.
  `LessThanMulRightEq`'s non-strict twin. The ⇔ is what makes it a
  cancellation law as well as a scaling one.
- **`SubPos`** — `∀x y:int. &0 < x − y ⇔ y < x`. `SubNonneg`'s strict
  twin: a difference is positive exactly when taken in the increasing
  direction.

how negation meets the order:

- **`NegNonneg`** — `∀x:int. x ≤ &0 ⇔ &0 ≤ -x`. Negation exchanges ℤ's
  two halves.
- **`NegNonpos`** — `∀x:int. &0 ≤ x ⇔ -x ≤ &0`. `NegNonneg` read the
  other way round; the pair is what carries a bound across a sign change
  in whichever direction an argument happens to hold it.
- **`NegPositiveIffNegative`** — `∀x:int. &0 < -x ⇔ x < &0`. A negation is positive exactly when the number is negative.
- **`NegNegativeIffPositive`** — `∀x:int. -x < &0 ⇔ &0 < x`. The strict
  companion of `NegNonpos`, and `NegPositiveIffNegative`'s mirror.
- **`LessEqNeg2`** — `∀x y:int. -x ≤ -y ⇔ y ≤ x`. It reverses them.
- **`LessThanNeg2`** — `∀x y:int. -x < -y ⇔ y < x`. And it reverses the
  strict order too.
- **`LessThanNegTotal`** — `∀x:int. x = &0 ∨ &0 < x ∨ &0 < -x`.
  Trichotomy through negation: an integer is zero, positive, or positive
  after a sign change.
- **`LessEqNegTotal`** — `∀x:int. &0 ≤ x ∨ &0 ≤ -x`. Every integer has a
  nonnegative side — the same statement with the zero case absorbed into
  both alternatives.

the unit, where ℤ's order meets its numerals:

- **`ZeroLessEqOne`** — `&0 ≤ &1`
- **`ZeroLessThanOne`** — `&0 < &1`

and absolute value:

- **`AbsNonneg`** — `∀x:int. &0 ≤ |x|`
- **`AbsDominates`** — `∀x:int. x ≤ |x|`. The other unconditional lower
  bound, and the one that closes arguments by contradiction: a quantity
  forced to be strictly larger than its own size has nowhere to be.
- **`AbsMul`** — `∀x y:int. |x·y| = |x|·|y|`
- **`AbsTriangle`** — `∀x y:int. |x + y| ≤ |x| + |y|`. Subadditivity, the
  estimate every bound on a sum goes through.
- **`AbsIdempotent`** — `∀x:int. ||x|| = |x|`. A size has no sign left
  to forget.
- **`AbsPosIffNonzero`** — `∀x:int. x ≠ &0 ⇔ &0 < |x|`
- **`AbsBounds`** — `∀x k:int. |x| ≤ k ⇔ -k ≤ x ∧ x ≤ k`. The exchange
  between a size bound and a two-sided bracket, which is how an estimate
  is consumed: an argument holding `|x| ≤ k` wants the two inequalities
  apart, and one that has bracketed x wants the size back.
- **`AbsBetween`** — `∀x y d:int. |y - x| < d ⇔ x - d < y ∧ y < x + d ∧ &0 < d`.
  The same exchange on a DIFFERENCE, which is the form a proximity
  argument states it in.
- **`AbsOfOne`** — `|&1| = &1`. The unit is its own size, `AbsOfZero`'s
  companion at the other numeral the chapter states things at.

and, with it, the sign:

- **`SgnOfZero`** — `int_sgn(&0) = &0`
- **`SgnOdd`** — `∀x:int. int_sgn(-x) = -int_sgn(x)`. Negation reverses
  the direction.
- **`SgnMul`** — `∀x y:int. int_sgn(x·y) = int_sgn(x)·int_sgn(y)`. The
  direction of a product is the product of the directions, the sign's
  counterpart of `AbsMul`.
- **`SgnMulSelfIsAbs`** — `∀x:int. int_sgn(x)·x = |x|`. An integer
  splits as direction times magnitude, `x = int_sgn(x)·|x|`; this is
  that decomposition solved for the magnitude, so the direction cancels
  itself rather than having to be case-split away.
- **`SgnTrichotomy`** —
  `∀x:int. int_sgn(x) = -&1 ∨ int_sgn(x) = &0 ∨ int_sgn(x) = &1`.
  A direction is one of exactly three things. The four members above say
  what the sign DOES and none of them says what it IS; without this one
  `int_sgn(x)` stays an opaque factor and `SgnMulSelfIsAbs`'s split into
  direction times magnitude cannot be consumed.

The mixed transitivities, `LessEqLessThanTrans` and
`LessThanLessEqTrans`, differ only in which hypothesis is strict; the
names spell both relations out in the order the hypotheses use them.

The integer power's defining clauses, proved by the same one-step
transport this chapter uses for everything, are `int_num/int_pow`'s
`PowClauses`: ℤ's power operation has its own chapter, and the lift
lives with it.

`MulAssoc` and `LeftDistrib` are the pair that carries Bézout's
combination step — `e·(p·x) + e·(q·y) = e·(p·x + q·y)` — for both gcd
chapters, which is the whole reason they are here rather than absent.
