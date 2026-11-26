# real_ring — ℝ as a commutative ring

The tower hands us ℝ with eighteen axioms. Four of them describe
addition (`AddSym`, `AddAssoc`, `AddLeftId`, `AddLeftInv`), four
describe multiplication (`MulSym`, `MulAssoc`, `MulLeftId`,
`MulLeftInverse`), one links them (`LeftDistrib`), and the rest govern
the order and the ℕ-embedding. This chapter is what follows from the
first nine — the algebra of `+`, `·`, `-` and unary `-` with the order
set aside.

The development is short because commutativity does most of the work,
and it runs in five movements: the additive group, multiplication,
negation, subtraction, and the integral-domain laws.

## ℝ as an instance of the abstract structures

`RealRingDef` packs the real operations and carrier `𝕌` into
`real_ring: ring_ops(real)`. `AddGroup` states
`abelian_group_on(additive_group(real_ring))`, including closure on
that carrier. `CommRing` states `comm_ring(real_ring)`, and
`CommRingOn` states `comm_ring_on(real_ring)`, the instance at which
the laws of a ring on a set are read. ℝ as an integral domain is
`real_formal_series.RealIntegralDomain`, in the lowest chapter of ℝ
that reads integral domains: the chapters this one carries do not.
`AddPowOne` states that n ones summed is the real numeral:
`monoid_pow(real_add, &0, &1, n) = &n`.

`AddMonoid` and `MulMonoid` state the commutative monoids of real
addition and multiplication. Their fold readings are `MonoidalAdd`,
`NeutralAdd`, `MonoidalMul` and `NeutralMul`, used by Σ and Π over ℝ.

## 1. The additive group, completed on the right

The axioms are stated on the left: `&0 + x = x` and `-x + x = &0`.
Commutativity mirrors both (`AddRightId`, `AddRightInv`), and with
associativity in hand the group cancels: `x + y = x + z ⇔ y = z`
(`AddLeftCancel`), which is proved by adding `-x` on the left and is
the single most-used fact in the chapter. Its right-handed twin and
the `y = &0` specialization follow, and `NegLeftUnique` — `x + y = &0
⇔ x = -y` — says the inverse is the *only* thing that annihilates.
`AddAC` packages commutativity, associativity and the derived
left-commutativity `x + (y + z) = y + (x + z)` for use as a rewrite
set.

## 2. Zero, one, and the other distributive law

`MulRightZero` is the first fact that genuinely needs distributivity:
`x·&0 = x·&0 + x·&0` by `&0 + &0 = &0` and `LeftDistrib`, so
cancellation forces `x·&0 = &0`. `MulLeftZero` reads the corresponding law at `CommRing`.
Commutativity gives `MulRightId` and `RightDistrib`; the latter
commutes the product, distributes on the left, and commutes each summand back.

## 3. Negation

With the group laws available, negation becomes computational.
`NegNeg` and `NegAdd` are cancellation arguments, and `NegZero` says
zero is its own negative. `MulRightNeg` — `x·(-y) = -(x·y)` — is the
bridge between the additive and multiplicative structures, proved by
showing `x·(-y) + x·y = &0`. `MulLeftNeg` reads the corresponding law at `CommRing`. Together
the two laws give `MulNegNeg` — two signs in one product cancel —
and `NegMinusOne`, which identifies negation with multiplication by `-&1`.

Two more laws move a minus sign across an equation rather than compute
with one. `NegEq` — `-x = y ⇔ x = -y` — is the involution read once at
each variable, and `NegEqZero` — `-x = &0 ⇔ x = &0` — is the special
case at zero. The second belongs here only by subject matter: its
argument never mentions negation at all, and runs entirely on the
additive group's cancellation (`AddLeftCancelZero` at `y := -x` is
already the biconditional it needs). Later chapters reach for both
whenever an equation has to be rearranged.

## 4. Subtraction

`x - y` is defined as `x + -y`, so this movement is bookkeeping over
the previous two: unfold the definition, apply a group law, fold back.
The laws divide into the identities (`SubRightZero`, `SubLeftZero`,
`SubRefl`), the add/subtract adjunctions (`SubAddRight`, `SubAddLeft`,
`EqSubRightAdd` — the one law that lets an equation be rearranged;
its mirror `x = y - z ⇔ x + z = y` is the same theorem under a renaming of
the binders and keys with it), the negation interactions (`SubRightNeg`, `SubLeftNeg`, `NegSub`,
`SubNegNeg`), the regrouping laws (`SubTriangle`, `SubAddPairwise`,
`SubSelfAdd`), and distribution over subtraction on both sides.
`SubEqZero` — `x - y = &0 ⇔ x = y` — is the one that later chapters
reach for most: it is how an equality becomes something to compute
with.

## 5. The integral domain

`MulEqZero` is the chapter's only argument that reaches back for a
multiplicative inverse: if `x·y = &0` and `x ≠ &0`, multiplying by
`inv x` gives `y = &0`. It buys multiplicative cancellation
(`MulLeftCancel`, `MulRightCancel`) — `x·y = x·z ⇔ x = &0 ∨ y = z`,
which is `SubLeftDistrib` plus `MulEqZero` plus `SubEqZero` — and with
that the ring layer is closed.

## Mechanics this chapter leans on

- **`real_sub` is unfolded.** `DefExpandStep(v.Minus)` opens movement 4;
  the subtraction laws are group laws in disguise, and spelling that is
  what keeps them one-liners. Where the unfold goes is decided by the
  shape of the goal, and once a difference is opened it is never
  reconstructed — nothing here folds back; the code is the model.
- **Ring laws can be read at `CommRing`.** `MulLeftZero` and
  `MulLeftNeg` use the general laws at the real instance. Longer
  equational arguments use `CalcEq` to display their intermediate values.
- **A cite is bare when the goal already spells its instance.** Most
  cites here carry no witnesses, and that is the chapter default rather
  than a series of local accidents: a `CalcEq` leg names the very term
  the law produces, and a cite consumed as a goal rewrite has no
  hypothesis slot to ground. Witnesses appear where the cite installs a
  fact the goal does not already name — `Cite(real_construction.AddSym, x, &0)` in
  the two-step mirrors, and `At(dep, w…)` for the same thing in a `By`
  premise list, which is how a ground instance is spelled when it is a
  premise rather than a step.
- **Embedded literals are built, not parsed.** `v.Lit(0)` / `v.Lit(1)`
  (vocab.go) construct `&0` and `&1` through the same `real_of_num` ∘
  bit0/bit1 tower the statement text parses to, so a witness list and
  its statement stay spelled alike.
- **AC rearrangement, two faces, one statement of the pair.** `real_construction.AddAC` /
  `real_construction.MulAC` (tower/real_construction) build a deriver from the axioms' associativity and
  symmetry. When the rearrangement is a premise inside a larger
  argument: `By(real_construction.AddAC(ctx).Eq(lhs, rhs))`. When the rearrangement IS the
  goal — as in both AC packs — `ACRegroupWith(real_construction.AddAC(ctx))`, which reads
  the two sums off the goal so the equation is written once, in the
  statement.
- **Nothing here closes by omega**: omega's
  real bundle is built out of exactly these laws, so using it to prove
  them would leave the chapter saying nothing.
