# nat_congruence — congruence, defined in ℕ

`x ≡ y (mod n)` when x and y leave the same remainder:

    nat_cong = λx y n. nat_mod(x, n) = nat_mod(y, n)

That is the whole chapter's premise, and it is a choice rather than a
transcription. The definition ℕ's congruence arrived with takes the long
way round — it embeds all three arguments into ℤ and asks there whether
n divides the difference — which puts the ℤ construction, and its
subtraction, underneath every ℕ fact about remainders. Nothing in that
theory needs the integers; only its definition did. So this chapter
defines the relation where it belongs and lets the theory stand on ℕ
alone.

On ℕ the honest definition is the computational one. Congruence is not
"n divides x − y" here — ℕ has no subtraction to speak of — it is the
statement that division by n leaves the same thing behind, which is what
one actually checks.

The constant is defined here (`definitions.go`), through the define
door: the equation is read in the chapter's vocabulary, the kernel
mints the constant, and the definition entry is what a proof cites to
unfold it — in this package or any other, the same constant with the
same defining theorem behind it.

## Reducing an argument, and the residue

- **`ModLeft`** — `∀x y n:num. x ≡ y (mod n) ⇔ nat_mod(x, n) ≡ y (mod n)`.
- **`ModRight`** — `∀x y n:num. x ≡ y (mod n) ⇔ x ≡ nat_mod(y, n) (mod n)`.
  Reducing either argument by the modulus leaves the congruence
  unchanged.
- **`ResidueCongruent`** — `∀x n:num. nat_mod(x, n) ≡ x (mod n)`. A number
  is congruent to its own residue: the joint where a law that answers
  with a remainder meets a claim stated as a congruence. The words
  chapters are its consumers.

## Congruence respects the arithmetic

Congruence mod n is an equivalence (`CongruenceEquivalence`), and
addition and multiplication respect it (`AddCongruent`,
`MulCongruent`): replacing a summand or a factor by a congruent one
leaves the result's class unchanged. Over ℕ each is a statement about
remainders: the equivalence is equality's own three properties, and a
sum's or a product's remainder depends only on the remainders of its
parts, which one residue law each says. Powers follow by induction on
the exponent (`PowCongruent`).

## Congruence and divisibility

Over ℤ a congruence is divisibility of a difference. ℕ has no difference
to speak of, so the bridge is stated where ℕ can state it:
`OffsetIffDivides` says x and x + d are congruent exactly when n divides
d. Read with the distance between two numbers — ℕ's own |x − y|,
`nat_monus`'s `dist` — it becomes symmetric: `DistIffDivides` says two
numbers are congruent exactly when n divides the distance between them,
and the laws after it are facts about that distance. A common summand
cancels because moving both numbers by x leaves their distance alone
(`AddCancel`); a factor coprime to the modulus cancels because it
multiplies the distance, and a modulus coprime to it sheds it
(`MulCancel`, through `nat_gcd.CoprimeCancel`).

## The Chinese remainder theorem

`chinese.go`. Modulo coprime a and b, a congruence is exactly a
congruence modulo both (`Chinese`): two coprime divisors of the distance
divide it together (`nat_gcd.CoprimeProductDivides`). That is the
theorem's uniqueness — two solutions of the same pair of congruences
agree modulo a·b. `ChineseRemainder` is its existence: any pair of
residues is attained. The proof writes down no solution; it counts. The
numbers u + a·i for i below b are all congruent to u modulo a, and no
two of them share a remainder modulo b — cancel u and then a, coprime to
b, and two numbers below b with one remainder are equal. So their b
remainders are all the remainders below b (`num_segment`'s pigeonhole,
`BelowStrictInjectiveOnto`), and one of them is v's. When b is 0 the
coprimality makes a equal to 1, and v itself is a solution.

## An inverse modulo n

A number coprime to n > 0 has an inverse mod n below n
(`InverseExists`). Multiplying by it is one-to-one on the residues below
n, since a coprime factor cancels (`MulCancel`), so by the pigeonhole
principle on those residues it is onto, and some residue goes to 1.

## Products modulo n

`products.go`. Numbers adding pairwise to p have congruent products
mod p (`ProductOfComplements`), so when m + 2k + 1 = p the factorial
(p − 1)! is m! · (2k)! mod p (`FactorialSplitMod`). These are the
residue computations behind the corollary of Wilson's theorem for
p ≡ 1 (mod 4), in `algebra/group/units_mod`.

## Members

| member | statement |
|---|---|
| `ModLeft` | `x ≡ y (mod n) ⇔ nat_mod(x, n) ≡ y (mod n)` |
| `ModRight` | `x ≡ y (mod n) ⇔ x ≡ nat_mod(y, n) (mod n)` |
| `ResidueCongruent` | `nat_mod(x, n) ≡ x (mod n)` |
| `CongruenceEquivalence` | `∀n. equivalence(λx y. x ≡ y (mod n))` |
| `AddCongruent` | `x ≡ y (mod n) ⇒ u ≡ v (mod n) ⇒ x + u ≡ y + v (mod n)` |
| `MulCongruent` | `x ≡ y (mod n) ⇒ u ≡ v (mod n) ⇒ x * u ≡ y * v (mod n)` |
| `PowCongruent` | `x ≡ y (mod n) ⇒ x ^ k ≡ y ^ k (mod n)` |
| `OffsetIffDivides` | `x ≡ x + d (mod n) ⇔ n ∣ d` |
| `DistIffDivides` | `x ≡ y (mod n) ⇔ n ∣ dist((x, y))` |
| `AddCancel` | `x + y ≡ x + z (mod n) ⇔ y ≡ z (mod n)` |
| `MulCancel` | `nat_coprime(c, n) ⇒ (c * x ≡ c * y (mod n) ⇔ x ≡ y (mod n))` |
| `Chinese` | `nat_coprime(a, b) ⇒ (x ≡ y (mod a * b) ⇔ x ≡ y (mod a) ∧ x ≡ y (mod b))` |
| `ChineseRemainder` | `nat_coprime(a, b) ⇒ ∃x. x ≡ u (mod a) ∧ x ≡ v (mod b)` |
| `InverseExists` | `0 < n ⇒ nat_coprime(a, n) ⇒ ∃b. b < n ∧ a * b ≡ 1 (mod n)` |
| `ProductOfComplements` | `a + c = p ⇒ b + d = p ⇒ a * b ≡ c * d (mod p)` |
| `FactorialSplitMod` | `m + 2 * k + 1 = p ⇒ factorial(p - 1) ≡ factorial(m) * factorial(2 * k) (mod p)` |

## What is NOT a member

"Congruence mod n is equality of remainders" has no entry here. Read
over `nat_cong` it is the defining equation, and a chapter does not
register its own definition as a theorem — a consumer that wants the
remainders unfolds. Under a congruence defined in ℤ the computational
reading is a theorem to be earned; here it is where one starts.

That is also why `ModLeft` and `ModRight` are two lines each. Unfolded,
each says only that reducing twice by the same modulus is reducing
once, which is `nat_div_mod.ModModRefl`.

The crossing to ℤ — `x ≡ y (mod n) ⇔ &x ≡ &y (mod &n)` — is not here
either: `&` occurs in the statement, so it belongs beside ℤ's own
congruence, as `int_num/int_congruence.OfNumCongruent`.

## Reading the proofs

Corpus-wide conventions — ground-cite witnesses, the `↦` marker, comment
policy, statement style — are in [proofs/README.md](../../README.md)
and are not restated here.

One chapter-specific thing. The mixfix `x ≡ y (mod n)` denotes THIS
chapter's constant at three `num` operands, and ℤ's congruence at three
`int` operands.
