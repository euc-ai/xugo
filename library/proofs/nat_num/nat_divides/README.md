# nat_divides — divisibility, defined in ℕ

`d ∣ n` when n is a multiple of d:

    nat_divides = λd n. ∃x. n = d · x

That is the whole chapter's premise, and it is a choice rather than a
transcription. The definition ℕ's divisibility theory arrived with takes
the long way round — it embeds both arguments into ℤ and asks the
question there — which puts the ℤ construction underneath every ℕ fact
about multiples, coprimality and primality. Nothing in that theory needs
the integers; only its definition did. So this chapter defines the
predicate where it belongs and lets the theory stand on ℕ alone.

The constant is defined here (`definitions.go`), through the define
door: the equation is read in the chapter's vocabulary, the kernel
mints the constant, and the definition entry is what a proof cites to
unfold it — in this package or any other, the same constant with the
same defining theorem behind it.

## Members

| member | statement |
|---|---|
| `DividesMod` | `∀m n:num. m ∣ n ⇔ nat_mod(n, m) = 0` |
| `DividesOne` | `∀n:num. n ∣ 1 ⇔ n = 1` |
| `DividesLessEq` | `∀m n:num. m ∣ n ⇒ m ≤ n ∨ n = 0` |
| `ZeroDivides` | `∀n:num. 0 ∣ n ⇒ n = 0` |
| `DividesLessEqStrong` | `∀m n:num. m ∣ n ⇒ 1 ≤ m ∧ m ≤ n ∨ n = 0` |
| `DividesRefl` | `∀n:num. n ∣ n` |
| `DividesZero` | `∀d:num. d ∣ 0` |
| `OneDivides` | `∀n:num. 1 ∣ n` |
| `DividesOwnMultiple` | `∀d c:num. d ∣ c * d ∧ d ∣ d * c` |
| `PowDividesPow` | `∀p m n:num. m ≤ n ⇒ p ^ m ∣ p ^ n` |
| `DividesTrans` | `∀a b c:num. a ∣ b ∧ b ∣ c ⇒ a ∣ c` |
| `DividesAntisym` | `∀m n:num. m ∣ n ∧ n ∣ m ⇔ m = n` |
| `DividesAddCancel` | `∀d a b:num. d ∣ a ⇒ (d ∣ a + b ⇔ d ∣ b)` |
| `DivAdd` | `∀d a b:num. d ∣ a ∨ d ∣ b ⇒ nat_div(a + b, d) = nat_div(a, d) + nat_div(b, d)` |
| `MultDiv` | `p ∣ m ⇒ nat_div(m * n, p) = nat_div(m, p) * n`, and the same on the other factor |
| `DivSucIndicator` | `∀n d:num. d ≠ 0 ⇒ div(n + 1, d) = div(n, d) + COND(d ∣ n + 1, 1, 0)` — the quotient of n + 1 grows by one exactly when d divides n + 1 |
| `DivisorQuotient` | `∀d n:num. 0 < n ∧ d ∣ n ⇒ 0 < d ∧ d * div(n, d) = n ∧ 0 < div(n, d)` |
| `DividesFactor` | `∀d n:num. d ∣ n ⇔ ∃x:num. n = d * x` — the relation as its own definition |
| `DividesMul` | `∀m n k:num. m ∣ n ⇒ m ∣ n * k` |
| `MulDividesLCancel` | `∀c m n:num. c ≠ 0 ∧ c * m ∣ c * n ⇒ m ∣ n` |
| `MulDividesMulLeft` | `∀c m n:num. m ∣ n ⇒ c * m ∣ c * n` |
| `MultiplesBelowCount` | `∀p m:num. 0 < p ⇒ has_size({a:num \| a < p * m ∧ p ∣ a}, m)` — the multiples of p below p·m (`multiples.go`) |
| `DivisorsFinite` | `∀n:num. 0 < n ⇒ finite({d:num \| d ∣ n})` — a positive number has finitely many divisors (`multiples.go`) |
| `DividesFactorial` | `∀d m:num. 1 ≤ d ∧ d ≤ m ⇒ d ∣ factorial(m)` — every number from 1 to m divides m! (`factorial.go`) |

The chapter's own members reach the multiple behind `d ∣ n` by
unfolding the definition. `DividesFactor` is that definition read as a
theorem, for the chapters that argue with divisibility without owning
it, and the two laws after it are proved through it.

## Reading the proofs

Corpus-wide conventions — ground-cite witnesses, the `↦` marker, comment
policy, statement style — are in [proofs/README.md](../../README.md)
and are not restated here.

`∣` is this chapter's constant, so the statements above read as they
would on paper.
