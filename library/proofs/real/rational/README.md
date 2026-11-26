# rational — ℚ as a subset of ℝ

A real is rational when it is a quotient of two integers. That one
sentence is the chapter's definition, and it is a predicate on reals,
not a type: the corpus builds ℝ from ℕ and carves ℤ out of it by
`integer`, and ℚ is carved out the same way by `rational`. A rational
is a real with a property; its arithmetic is ℝ's; a theorem about
rationals is a theorem about reals with `rational` among its
hypotheses. Nothing here has a numerator or a denominator of its own.

The chapter has three movements.

**1. The rationals are a subfield containing the integers.** Every
integer is rational (its quotient by 1), so every natural is; and the
rationals are closed under negation, addition, multiplication and
inversion — each closure exhibits the quotient the textbook writes,
`-m/n`, $\frac{m_1 n_2 + m_2 n_1}{n_1 n_2}$, $\frac{m_1 m_2}{n_1 n_2}$ and `n/m`. The sum and
the product read the integrality of their parts off the closure of
`integer` under the ring operations; the inverse keeps the old parts,
swapped, once zero — its own inverse — is set aside. Subtraction and
division follow as one line each.

**2. The rationals are dense.** Between any two reals lies a
rational, and every real is within any positive distance of one. The
tool is an integer part: every real x has an integer m with
m ≤ x < m + 1. For a nonnegative x that integer is a natural — the
least natural strictly above x, less one — and the well-ordering of ℕ
finds it, the Archimedean property having shown there is a natural
above x at all. An arbitrary x is shifted into the nonnegative half by
a natural and shifted back, with no case on its sign. Density then
reads off the Archimedean property once more: a step 1/n smaller than
y − x cannot cross from x to y without landing between them, and the
multiple of 1/n it lands on is the integer part of x·n, plus one.

**3. A prime has no rational square root.** The argument descends in
ℕ, and the descent is `nat_num/nat_prime`'s: if a² = p·b² with p prime,
Euclid's lemma puts p into a, and cancelling p leaves b² = p·c² — the
same equation with a smaller pair — so the only solution is a = b = 0.
A rational whose square is p would
give, through the absolute values of its numerator and denominator, a
nontrivial solution; so no rational squares to a prime, no prime has a
rational square root, and √2 is the first instance. The chapter closes
by turning that back into a density statement: between any two reals
lies an irrational, a rational shifted by √2.

## Members

The definition (definitions.go):

| entry | statement |
|---|---|
| `RationalDef` | `rational(x) ⇔ ∃m n. integer(m) ∧ integer(n) ∧ n ≠ &0 ∧ x = m / n` |

The subfield (closure.go):

| entry | statement | argument |
|---|---|---|
| `IntegerRational` | `integer(x) ⇒ rational(x)` | x is x / &1 |
| `OfNumRational` | `rational(&n)` | a natural is an integer |
| `RationalNeg` | `rational(x) ⇒ rational(-x)` | -(m/n) = (-m)/n, the sign passing into the numerator |
| `RationalAdd` | `rational(x) ∧ rational(y) ⇒ rational(x + y)` | $\frac{m_1 n_2 + m_2 n_1}{n_1 n_2}$, the identity by clearing denominators and dividing back |
| `RationalSub` | `rational(x) ∧ rational(y) ⇒ rational(x - y)` | x − y is x + −y |
| `RationalMul` | `rational(x) ∧ rational(y) ⇒ rational(x * y)` | $\frac{m_1 m_2}{n_1 n_2}$, n₁n₂ inverted factor by factor |
| `RationalInv` | `rational(x) ⇒ rational(real_inv(x))` | zero inverts to zero; otherwise m ≠ 0 and the inverse of m/n is n/m |
| `RationalDiv` | `rational(x) ∧ rational(y) ⇒ rational(x / y)` | x / y is x · y⁻¹ |

Density (density.go):

| entry | statement | argument |
|---|---|---|
| `NonnegIntegerPart` | `&0 ≤ x ⇒ ∃m:num. &m ≤ x ∧ x < &m + &1` | the least natural strictly above x, less one |
| `IntegerPart` | `∃m. integer(m) ∧ m ≤ x ∧ x < m + &1` | shift x by a natural N above −x, take the natural integer part k there; k − N is x's |
| `NearestInteger` | `∃m. integer(m) ∧ \|x - m\| ≤ &1 / &2` | the integer part n of x, or n + 1 when x is more than a half above n |
| `RationalBetween` | `x < y ⇒ ∃r. rational(r) ∧ x < r ∧ r < y` | a step 1/n shorter than y − x (Archimedean); $r = \frac{m+1}{n}$ with m the integer part of x·n |
| `RationalApproximation` | `&0 < e ⇒ ∃r. rational(r) ∧ real_abs(r - x) < e` | a rational between x and x + e |

Irrationality (irrational.go):

| entry | statement | argument |
|---|---|---|
| `PrimeNotRationalSquare` | `nat_prime(p) ∧ rational(x) ⇒ real_pow(x, 2) ≠ &p` | x = m/n cleared to m·m = p·(n·n); the naturals \|m\|, \|n\| solve a² = p·b² (`nat_prime.SquareEqPrimeTimesSquare`), so n = 0 |
| `SqrtPrimeIrrational` | `nat_prime(p) ⇒ ¬rational(real_sqrt(&p))` | (√p)² = p; at p = 2, with `nat_prime.PrimeTwo`, √2 is irrational |
| `IrrationalBetween` | `x < y ⇒ ∃z. ¬rational(z) ∧ x < z ∧ z < y` | a rational r between x − √2 and y − √2; r + √2 is irrational, since √2 = (r + √2) − r |

## Mechanics

- **Statements** are text, every name resolved through its mint:
  `rational` here, `integer` in `int_num/int_construction`, `real_sqrt` in
  `real/real_sqrt`, `nat_prime` in `nat_num/nat_prime`. The chapter has
  no vocabulary rows of its own.
- **Cites** are typed references to entry vars, all of them.
- **The CNF cache** is one shared `rational.cnf.pb` for the family;
  `family.go` carries the record and GC recipes.
