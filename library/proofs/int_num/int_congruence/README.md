# int_congruence — congruence mod n on ℤ

Two integers are congruent modulo `n` when `n` divides their difference.
That is the definition, and it is almost useless as one: divisibility is
an existence statement, and an existence statement is a bad thing to
have at the bottom of a theory whose whole purpose is to let you compute.

So the chapter opens by trading the definition for two characterizations.
It unfolds it once more after that, at the single place where a theorem
stated about `∣` has to be reached.

- **`x ≡ y (mod n) ⇔ ∃d. x - y = n·d`** — the existence made explicit.
  This is the form every construction uses: to prove a congruence you
  exhibit the multiple.
- **`x ≡ y (mod n) ⇔ int_rem(x,n) = int_rem(y,n)`** — the existence eliminated.
  This is the form every computation uses: congruence is a decidable
  equality between two normal forms, supplied by the division algorithm
  next door.

Almost everything else is one of these two read at a particular place.
The reduction laws say a remainder may replace its dividend on either
side of the relation. The compatibility laws say the relation survives
`+`, `-` and `·` — that congruence is a ring congruence — and from
those it follows that a remainder may be taken EARLY: before an
operation rather than after,
which is what makes modular arithmetic computable. The power law is
that last reading iterated, and is the one member whose proof passes
through no congruence at all. The closing group then names the
representative: one exists in `⟦0, |n|⟭` at any nonzero modulus, and at
a POSITIVE modulus it is the only one there — which is what makes "the
residue" a thing you can name.

## The residue classes as cosets

The multiples of `n` are a subgroup of the additive group of ℤ — `0` is
`n · 0`, `n · a + n · b` is `n · (a + b)`, `-(n · a)` is `n · (-a)` —
and a normal one, since a conjugate `(g + x) + -g` is `x` itself when
addition commutes. So the residue classes mod `n`, the cosets of that
subgroup, are the carrier of a quotient group (`algebra/group/quotient_group`),
and ℤ/nℤ is the general construction at ℤ: `quotient_group.QuotientGroup`
applies at ℤ's additive group and `MultiplesNormal`; this chapter states
nothing more of it. The residue class of `x` IS the coset `x + nℤ`
(`ResidueClassIsCoset`): a point lies in the class exactly when its
difference from `x` is a multiple of `n`, and in the coset exactly when
`-x` plus it is one, the two multiples being each other's negation. The
three members live in `residue_classes.go`, beside the chapter's one
other file.

| member | statement |
|---|---|
| `MultiplesSubgroup` | `subgroup(int_add, &0, int_neg, {x \| n ∣ x})` |
| `MultiplesNormal` | `normal_subgroup(int_add, &0, int_neg, {x \| n ∣ x})` |
| `ResidueClassIsCoset` | `equivalence_class(λy z. y ≡ z (mod n), x) = left_coset(int_add, x, {y \| n ∣ y})` |

## Where the chapter sits

Congruence's definitional floor is ℤ, and it is met here — the relation
is `int_cong`, defined from `int_divides`, and the `x ≡ y (mod n)` surface
lowers to it whenever the operands are integers.

ℕ has its own congruence, defined natively as equality of remainders
(`nat_num/nat_congruence`), and the embedding carries it to this chapter's
relation: `OfNumCongruent`, `x ≡ y (mod n) ⇔ &x ≡ &y (mod &n)`. It sits
here rather than at the boundary for the reason the remainder's
transport sits in `int_div_rem` — the ℤ side of the clause is this
chapter's own characterization.

Everything this chapter stands on is below it. `int_div_rem` supplies
the division algorithm and the remainder normal form the second
characterization is stated in; `int_real_lift` supplies ℤ's inherited
ring algebra, which is what the compatibility proofs are written in.
Further down, `int_divides` owns `∣` — the relation congruence is
DEFINED from. Exactly one proof here reaches past that definition to a
theorem ABOUT `∣`: `EqOfSmallDifference` needs the bound saying a
divisor is no larger than what it divides, and that is the chapter's
only contact with divisibility theory.

## Members

Seven parts of `int_congruence.go`, and an eighth in `residue_classes.go`
(the section above).

**Congruence is an equivalence.**

| | |
|---|---|
| `CongruenceEquivalence` | `∀m. equivalence(λx y. x ≡ y (mod m))` |

Read through its definition a congruence says that x − y is a multiple
of m, and each property of an equivalence asks for one more multiple,
exhibited outright: 0, the given one negated, the two given ones added.
The member is an instance of `relations/equivalence`'s structure, so the
residue classes mod m are that chapter's classes and its laws apply to
them.

**What a congruence is.**

| | |
|---|---|
| `CongruentIffMultiple` | `∀x y n. x ≡ y (mod n) ⇔ ∃d. x - y = n·d` |
| `CongruentIffSameRem` | `∀x y n. x ≡ y (mod n) ⇔ int_rem(x,n) = int_rem(y,n)` |

The two trades described above. The second doubles as a symmetry: read
either way a congruence is one equality of remainders, and equality is
symmetric — which is how the remainder laws below reverse a congruence:
the equality they compute with is already symmetric, and none of them
cites the equivalence.

**ℕ's congruence, read in ℤ.**

| | |
|---|---|
| `OfNumCongruent` | `∀x y n:num. x ≡ y (mod n) ⇔ &x ≡ &y (mod &n)` |

The ℕ relation is an equality of remainders by definition, the ℤ one by
`CongruentIffSameRem`; the remainder's transport (`int_div_rem.OfNumRem`)
puts the two equations on one side of `&`, and injectivity reads the ℤ
equation back as the ℕ one.

**What may be replaced inside one.**

| | |
|---|---|
| `RemCongruent` | `∀m n. int_rem(m,n) ≡ m (mod n)` |
| `RemLeft` | `∀x y n. int_rem(x,n) ≡ y (mod n) ⇔ x ≡ y (mod n)` |
| `RemRight` | `∀x y n. x ≡ int_rem(y,n) (mod n) ⇔ x ≡ y (mod n)` |

One permission stated three times: a congruence does not distinguish an
argument from its remainder, so either side may be reduced first.

**What congruences may be combined by.**

| | |
|---|---|
| `AddCongruent` | `∀x y u v n. x ≡ y ⇒ u ≡ v ⇒ x + u ≡ y + v (mod n)` |
| `SubCongruent` | the same for `-` |
| `MulCongruent` | the same for `·` |
| `ProductCongruent` | `∀n f g s. finite(s) ∧ (∀x ∈ s. f(x) ≡ g(x) (mod n)) ⇒ Π_{x∈s} f(x) ≡ Π_{x∈s} g(x) (mod n)` |

They differ in length for a reason worth knowing. Regrouping a
difference of SUMS reaches the wanted multiple without naming either
given one, so `AddCongruent` names neither. A difference of DIFFERENCES
and a difference of PRODUCTS both have to be assembled, so
`SubCongruent` and `MulCongruent` name both of theirs.
The product law iterates: a relation ℤ's multiplication respects is
inherited by the fold (`monoidal.Related`), which is `ProductCongruent`.

**A remainder may be taken early.**

| | |
|---|---|
| `RemOfSum` | `∀x y n. int_rem(x+y, n) = int_rem(int_rem(x,n) + int_rem(y,n), n)` |
| `RemOfProduct` | the same for `·` |
| `RemOfDifference` | the same for `-` |
| `RemOfPower` | `∀k:num. ∀x n. int_rem(x^k, n) = int_rem(int_rem(x,n)^k, n)` |

Each operand may be replaced by its remainder BEFORE the operation
rather than after, so no intermediate ever grows past the modulus. The
first three run the same two steps: each operand's congruence to its own
remainder (`RemCongruent`), fed to the corresponding compatibility law,
read back as an equation through `CongruentIffSameRem`. The power law is
the product law applied once per factor, and is the only member whose
proof states no congruence at all.

**The residue.**

| | |
|---|---|
| `ResidueInRange` | `∀a n. n ≠ &0 ⇒ ∃x. &0 ≤ x < \|n\| ∧ x ≡ a (mod n)` |
| `NaturalRepresentative` | `∀x n. (n = &0 ⇒ &0 ≤ x) ⇒ ∃k:num. &k ≡ x (mod n)` |
| `EqOfSmallDifference` | `∀x y n. \|x - y\| < n ∧ x ≡ y (mod n) ⇒ x = y` |
| `EqOfCongruentSigns` | `∀p:num. ∀u v. nat_prime(p) ∧ p ≠ 2 ∧ -&1 ≤ u ≤ &1 ∧ -&1 ≤ v ≤ &1 ∧ u ≡ v (mod &p) ⇒ u = v` |
| `RemCharacterization` | `∀m n p. int_rem(m,n) = p ⇔ ((n = &0 ∧ m = p) ∨ (&0 ≤ p < \|n\|)) ∧ m ≡ p (mod n)` |

Existence, then the same in ℕ, then uniqueness, then the statement that
pins WHICH representative it is: the remainder. The first two exhibit a
witness and both times it is the remainder — the second reads it back
across the embedding, so its witness is `num_of_int(int_rem(x,n))`. The last
two say nothing else can be it.

## Reading the statements

`x ≡ y (mod n)` is the surface for `int_cong(x, y, n)` — a three-place
relation in the order the mixfix reads, the same shape as ℕ's
`nat_cong(x, y, n)`. The mixfix dispatches on operand type, so the same
three characters mean ℕ's native `nat_cong` at naturals and this
chapter's relation at integers;
`&x ≡ &y (mod &n)` is always the ℤ one, since a coercion cannot be a
natural. The longhand application form appears nowhere in this corpus.
