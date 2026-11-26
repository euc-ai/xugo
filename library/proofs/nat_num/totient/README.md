# totient — Euler's totient, the count of residues coprime to n, and Gauss's divisor sum

φ(n) counts the residues below n that are coprime to n. Sorting the
residues below n by their gcd with n gives Gauss's identity: the φ(d) over
the divisors d of n add up to n. The divisors of a product of two coprime
numbers are the products of their divisors, each arising once. The values
at a prime and at a prime power are counted directly.

## Members

| Member | Statement |
|---|---|
| `TotientDef` | `totient`: num → num |

## Gauss's divisor sum

Sorting the residues a below n by the divisor d with gcd(a, n) · d = n
puts e · b, for b below d coprime to d (n = d · e), into the class of d,
since gcd(e · b, e · d) = e · gcd(b, d); the class of d therefore has φ(d)
members, and counting the classes gives $\sum_{d \mid n} \varphi(d) = n$.

For coprime m and n the divisors of m · n are the products of a divisor of
m and a divisor of n, each arising from exactly one pair: a divisor of m · n
splits between the factors whatever m and n are
(`nat_gcd.DivisorProductFactors`), and coprime cancellation recovers each
coordinate from an equality of products. So the sum of a multiplicative
real function over the divisors of m · n is the product of its sums over
the divisors of m and over those of n.

| Member | Statement |
|---|---|
| `TotientHasSize` | φ(n) is the size of the set it counts |
| `GcdClassCount` | For a divisor d of n > 0, the residues below n whose gcd with n is n/d number φ(d) |
| `DivisorSum` | Gauss's identity: the totients of the divisors of n > 0 add up to n |
| `DivisorsOfCoprimeProduct` | For coprime m and n, (d, e) ↦ d · e maps the pairs of a divisor of m and a divisor of n one-to-one onto the divisors of m · n |
| `DivisorSumMultiplicative` | For coprime m, n > 0 and a real f with f(a · b) = f(a) · f(b) at coprime a and b, the sum of f over the divisors of m · n is the product of its sums over the divisors of m and of n |

## The values of φ

At a prime power a residue fails to be coprime exactly when p divides it
(`nat_prime.CoprimePrimePowerIff`), and the multiples of p below
$p^k = p \cdot p^{k-1}$ are the $p^{k-1}$ numbers p · b
(`nat_divides.MultiplesBelowCount`); taking them out of the p ^ k residues gives
$\varphi(p^k) = p^k - p^{k-1}$, and φ(p) = p − 1 is its case k = 1.

| Member | Statement |
|---|---|
| `TotientPrimePower` | $\varphi(p^k) = p^k - p^{k-1}$ for a prime p and k > 0 |
| `TotientPrime` | φ(p) = p − 1 for a prime p |
| `TotientPositive` | φ(n) is positive for n > 0 |
