# comm_ring — a commutative ring with one

A ring is one `R:ring_ops(A)` record holding `add`, `zero`, `neg`,
`mul`, `one`, `sub` and `carrier`. The predicate `comm_ring_on(R)`
states the ring axioms on `R.carrier`. The whole-type predicate
`comm_ring(R)` states the original unguarded axioms on every element of
A, using the same operation fields. Its meaning does not depend on
`R.carrier`.

The additive group is `additive_group(R)`. Multiplication and its
identity give the commutative monoid. Under a record binder the fields
carry arithmetic notation: `x + y` is `R.add(x, y)`, `x - y` is
`R.sub(x, y)`, `x * y` is `R.mul(x, y)` and `-x` is `R.neg(x)`.
Distinguished elements are `R.zero` and `R.one`.

The bridge `CommRingOnUniverse` identifies `comm_ring(R)` with
`comm_ring_on(restrict_ring(R, 𝕌))`. Each carrier law keeps its guarded
`On` interface, and its bare whole-type view discharges those guards
through `CommRingAtUniverse`; the alternating-sign laws are carrier laws
only. A subring is `subring(R, S)`, read as a
ring of its own through `restrict_ring(R, S)`; quotients and
localizations supply their own records. Below, c denotes
`R.carrier`.

The predicate `characteristic_zero(R)` says that no positive natural
multiple of `R.one` under addition is `R.zero`; it is stated directly in
the ring operations.

## The structures and their axioms

Every law of the ring is proved once, for a commutative ring on a SET —
`comm_ring_on(R)`, an abelian group on `R.carrier`
under the addition, a commutative monoid on `R.carrier` under the multiplication,
distributivity and the subtraction law for the members of `R.carrier` — and
stated beside it for the whole type, where it reads unguarded: the
whole-type ring is the ring on `𝕌`, and its law is the view of the
set's. The three projections are axioms or laws of each form, and the
closure laws say which terms a proof forms lie in `R.carrier`. The fold laws
stay on the whole type, where the fold lives. A quotient ring and a
localization are rings on sets and nothing else, and they read every
law here at their classes.

| member | statement |
|---|---|
| `CommRing` | `comm_ring(R)` ⇔ the additive group, the multiplicative monoid, `R.mul(x, R.add(y, z)) = R.add(R.mul(x, y), R.mul(x, z))` and `R.sub(x, y) = R.add(x, R.neg(y))` |
| `CommRingOn` | `comm_ring_on(R)` ⇔ the abelian group on `R.carrier`, the multiplicative monoid on `R.carrier`, distributivity and the subtraction law for members of `R.carrier` |
| `CommRingOnUniverse` | `comm_ring(R) ⇔ comm_ring_on(restrict_ring(R, 𝕌))` |
| `CharacteristicZeroDef` | `characteristic_zero(R)` ⇔ every positive natural additive power of `R.one` is nonzero |
| `AddGroup` | `abelian_group(additive_group(R))` |
| `AddGroupOn` | `abelian_group_on(additive_group(R))` |
| `AddMonoid` | `comm_monoid(R.add, R.zero)` |
| `AddMonoidOn` | `comm_monoid_on(R.carrier, R.add, R.zero)` |
| `MulMonoid` | `comm_monoid(R.mul, R.one)` |
| `MulMonoidOn` | `comm_monoid_on(R.carrier, R.mul, R.one)` |
| `ZeroIn`, `OneIn` | `R.zero ∈ R.carrier`, `R.one ∈ R.carrier` |
| `AddIn`, `MulIn`, `SubIn` | `x ∈ R.carrier ∧ y ∈ R.carrier ⇒ x + y ∈ R.carrier`, the product and the difference likewise |
| `NegIn` | `x ∈ R.carrier ⇒ -x ∈ R.carrier` |
| `ClosedSubsetRingOn` | `T ⊆ R.carrier` holding `R.zero` and `R.one` and closed under `+`, `-x` and `*` ⇒ `comm_ring_on(restrict_ring(R, T))` |

| whole type | on a set | statement |
|---|---|---|
| `LeftDistrib` | `LeftDistribOn` | `x * (y + z) = x * y + x * z` |
| `SubAddNeg` | `SubAddNegOn` | `x - y = x + -y` |

## Subrings

`subring(R, S)` says that `S` lies in `R.carrier`, holds `R.zero` and
`R.one`, and is closed under the sum, the negation and the product. It
asks nothing of `R`, as `subgroup` and `subfield` ask nothing of theirs.
Under a ring on `R.carrier` it is exactly a subset on which the ring's
operations make a ring of their own, `restrict_ring(R, S)`: every axiom
on `S` is an instance of the ring's on `R.carrier`.

| member | statement |
|---|---|
| `SubringDef` | `subring(R, S) ⇔ S ⊆ R.carrier ∧ R.zero ∈ S ∧ R.one ∈ S ∧` closure under `R.add`, `R.neg` and `R.mul` |
| `SubringSubset`, `SubringZero`, `SubringOne` | a subring lies in the carrier and holds zero and one |
| `SubringAdd`, `SubringNeg`, `SubringMul` | it holds sums, negations and products of its members |
| `SubringRestrict` | `subring(R, S) ∧ S ⊆ T ⇒ subring(restrict_ring(R, T), S)` |
| `SubringRingOn` | `subring(R, S) ⇔ S ⊆ R.carrier ∧ comm_ring_on(restrict_ring(R, S))` |
| `CarrierSubring` | `subring(R, R.carrier)` |

## What the two operations say to each other

| whole type | on a set | statement |
|---|---|---|
| `RightDistrib` | `RightDistribOn` | `(x + y) * z = x * z + y * z` |
| `MulLeftZero` | `MulLeftZeroOn` | `R.zero * x = R.zero` |
| `MulRightZero` | `MulRightZeroOn` | `x * R.zero = R.zero` |
| `MulLeftNeg` | `MulLeftNegOn` | `-x * y = -(x * y)` |
| `MulRightNeg` | `MulRightNegOn` | `x * -y = -(x * y)` |
| `MulNegNeg` | `MulNegNegOn` | `-x * -y = x * y` |
| `NegOneMul` | `NegOneMulOn` | `-R.one * x = -x` |

## Powers of a negation

The ring's power is its multiplicative monoid's (`comm_monoid.MonoidPowDef`),
spelled `monoid_pow(R.mul, R.one, x, n)` with the ring's components. An even
power forgets the sign — both sides are the `n`-th power of one square,
and `(−x)·(−x) = x·x` — and an odd power keeps it.

| member | statement |
|---|---|
| `NegPowEven` | `monoid_pow(R.mul, R.one, -x, 2 * n) = monoid_pow(R.mul, R.one, x, 2 * n)` |
| `NegPowOdd` | `monoid_pow(R.mul, R.one, -x, 2 * n + 1) = -monoid_pow(R.mul, R.one, x, 2 * n + 1)` |

## The alternating signs

The alternating signs one, −one, one, … are `alternating_sign(i)`
(`AlternatingSignDef`: one at 0, each sign the negation of the one
before), written under the ring with its one and negation implicit; a
double complex's total boundary carries them on its vertical part.
They lie in the carrier, follow the exponent law, square to one, and
cancel in adjacent pairs.

| member | statement |
|---|---|
| `AlternatingSignDef` | `alternating_sign(one, neg, i)`: one at 0, negated at each step |
| `AlternatingSignIn` | every sign lies in `R.carrier` |
| `AlternatingSignAdd` | `alternating_sign(p + j) = alternating_sign(p) * alternating_sign(j)` |
| `AlternatingSignSquare` | `alternating_sign(n) * alternating_sign(n) = R.one` |
| `AlternatingSignSuc` | `alternating_sign(n + 1) + alternating_sign(n) = R.zero` |

## The ring's numerals

The additive power of one, `monoid_pow(R.add, R.zero, R.one, n)` — n copies of
one summed — is the ring's numeral n: with
`comm_monoid.PowAdd` at the additive monoid it adds, and here it
multiplies, so the additive powers of one are a copy of ℕ inside every
commutative ring. The arithmetic closer's structure ring folds its
coefficients with these two laws.

| whole type | on a set | statement |
|---|---|---|
| `AddPowMul` | `AddPowMulOn` | `monoid_pow(R.add, R.zero, R.one, m * n) = monoid_pow(R.add, R.zero, R.one, m) * monoid_pow(R.add, R.zero, R.one, n)` |

## The two fold laws a ring carries

Each operation is a commutative monoid, so each folds: Σ and Π over any
ring are the fold mechanism read at these laws.

| member | statement |
|---|---|
| `MonoidalAdd` | `monoidal_op(R.add)` |
| `NeutralAdd` | `neutral_elem(R.add) = R.zero` |
| `MonoidalMul` | `monoidal_op(R.mul)` |
| `NeutralMul` | `neutral_elem(R.mul) = R.one` |
