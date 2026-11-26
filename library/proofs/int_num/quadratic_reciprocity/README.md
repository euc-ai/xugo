# quadratic_reciprocity — the law of quadratic reciprocity and the Jacobi symbol

For distinct odd primes p and q, $\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}$. The
proof computes in an algebraically closed field of characteristic q holding
a p-th root of unity ζ ≠ 1: the Gauss sum $g = \sum_{a<p} \left(\frac{a}{p}\right) \zeta^a$ has
$g^2 = \left(\frac{-1}{p}\right) p$, and the q-th power map, a ring homomorphism, sends g to
$\left(\frac{q}{p}\right) g$. Computed through g², $g^q = (g^2)^{\frac{q-1}{2}} \cdot g$ is $\left(\frac{\left(\frac{-1}{p}\right) p}{q}\right) \cdot g$
by Euler's criterion mod q; g is not 0, so the two values of $g^q$ give
$\left(\frac{q}{p}\right) = \left(\frac{\left(\frac{-1}{p}\right) p}{q}\right)$. The Jacobi symbol $\left(\frac{a}{n}\right)$
multiplies the Legendre symbols over the prime factorization of n; it is
multiplicative in both arguments, and reciprocity and its supplements
extend to it through the factorization.

## Members

| Member | Statement |
|---|---|
| `JacobiSymbolDef` | `jacobi_symbol`: int → num → int |

## The law of quadratic reciprocity

The Gauss-sum computation gives $\left(\frac{q}{p}\right) = \left(\frac{p^\ast}{q}\right)$, where $p^\ast = \left(\frac{-1}{p}\right) p$. The
law is then sign bookkeeping: $\left(\frac{p^\ast}{q}\right) = \left(\frac{\left(\frac{-1}{p}\right)}{q}\right)\left(\frac{p}{q}\right)$, the first factor is
$(-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}$ because the symbol of a power is the power of the
symbol, and $\left(\frac{p}{q}\right)^2 = 1$.

| Member | Statement |
|---|---|
| `PrimeNotDividesPStar` | For an odd prime p and a prime q ≠ p, q does not divide $p^\ast = \left(\frac{-1}{p}\right) \cdot p$ |
| `QuadraticCharacterOfPStar` | For distinct odd primes p and q, $\left(\frac{q}{p}\right) = \left(\frac{p^\ast}{q}\right)$, where $p^\ast = \left(\frac{-1}{p}\right) \cdot p$ |
| `QuadraticReciprocity` | For distinct odd primes p and q, $\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}$ |

## The Jacobi symbol

The Jacobi symbol may be taken over any set of primes that holds the prime
divisors of n: a prime of the larger set occurs in n to the power 0 and
contributes 1. Over no primes this gives $\left(\frac{a}{1}\right) = 1$; over {p} it gives the
Legendre symbol; over the primes of m · n, where the multiplicities add,
it gives multiplicativity in the lower argument.

| Member | Statement |
|---|---|
| `JacobiOverPrimes` | $\left(\frac{a}{n}\right)$ is the same product taken over any set of primes holding the prime divisors of n |
| `JacobiAtOne` | $\left(\frac{a}{1}\right) = 1$ |
| `JacobiOne` | $\left(\frac{1}{n}\right) = 1$ |
| `JacobiPrime` | At a prime p, $\left(\frac{a}{p}\right)$ is the Legendre symbol |
| `JacobiMulRight` | $\left(\frac{a}{m \cdot n}\right) = \left(\frac{a}{m}\right) \cdot \left(\frac{a}{n}\right)$ for nonzero m and n |
| `JacobiMulLeft` | For odd n, $\left(\frac{a \cdot b}{n}\right) = \left(\frac{a}{n}\right) \cdot \left(\frac{b}{n}\right)$ |

For odd n the symbol is multiplicative in a as well, with no change of
index set: every prime of n is odd, and the Legendre symbol at an odd
prime is multiplicative.

## The supplements

The first supplement carries from the Legendre symbol to every odd n by
strong induction: split off a prime factor p of n = p · m. Then
$\left(\frac{-1}{n}\right) = \left(\frac{-1}{p}\right)\left(\frac{-1}{m}\right)$, and the two signs multiply, because on odd numbers
$(-1)^{\frac{n-1}{2}}$ is multiplicative. The second supplement travels the
same way once the Legendre symbol's law is read as a sign: $\left(\frac{2}{p}\right) = 1$
exactly when p ≡ ±1 (mod 8), which is exactly when $\frac{p^2-1}{8}$ is even; and
on odd numbers $(-1)^{\frac{n^2-1}{8}}$ is multiplicative, because an odd square
is one more than a multiple of 8.

| Member | Statement |
|---|---|
| `HalfOddSignMul` | On odd numbers the sign $(-1)^{\frac{n-1}{2}}$ is multiplicative |
| `JacobiMinusOne` | For odd n, $\left(\frac{-1}{n}\right) = (-1)^{\frac{n-1}{2}}$ |
| `EighthSignMul` | On odd numbers the sign $(-1)^{\frac{n^2-1}{8}}$ is multiplicative |
| `JacobiTwo` | For odd n, $\left(\frac{2}{n}\right) = (-1)^{\frac{n^2-1}{8}}$ |

## Reciprocity for the Jacobi symbol

The law carries to Jacobi symbols by two strong inductions, each splitting
off one odd prime factor. First an odd m meets an odd prime p not dividing
it: each prime factor q of m meets p in quadratic reciprocity. Then m meets
any odd n prime to it: each prime factor p of n meets m in the first law.
Both symbols, and the sign $(-1)^{\frac{m-1}{2} \cdot \frac{n-1}{2}}$, are multiplicative in
each odd argument.

| Member | Statement |
|---|---|
| `HalfOddSignPowMul` | On odd numbers the sign $(-1)^{\frac{n-1}{2} \cdot k}$ is multiplicative in n |
| `JacobiReciprocityPrime` | For an odd prime p not dividing an odd m, $\left(\frac{m}{p}\right)\left(\frac{p}{m}\right) = (-1)^{\frac{m-1}{2} \cdot \frac{p-1}{2}}$ |
| `JacobiReciprocity` | For odd m and n prime to each other, $\left(\frac{m}{n}\right)\left(\frac{n}{m}\right) = (-1)^{\frac{m-1}{2} \cdot \frac{n-1}{2}}$ |
