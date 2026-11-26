# nat_multiplicity — the exponent of a prime in a natural number, and Legendre's formula for a factorial

The multiplicity of p in n is the exponent e with p ^ e dividing n and
$p^{e+1}$ not; for 2 ≤ p and n ≠ 0 there is exactly one. For a prime it
adds over products, and Legendre's formula counts it in n! as the sum of
the quotients n div p ^ i.

## Members

| Member | Statement |
|---|---|
| `NatMultiplicityDef` | `nat_multiplicity`: num → num → num |

## The exponent of a prime

For 2 ≤ p and n ≠ 0 the exponents e with p ^ e dividing n include 0 and
are bounded by n, so there is a largest one, and the exponent the choice
defining the multiplicity picks is one past which p no longer divides;
read as an order statement on exponents, p ^ e divides n exactly when e
is at most the multiplicity, so the choice is that largest exponent. The
multiplicity leaves a cofactor that p does not divide; for a prime the
cofactors of m and n multiply to one that p still does not divide, by
Euclid's lemma, so the multiplicities add. Counted the other way, the multiplicity is the
number of exponents i from 1 to n with p ^ i dividing n.

| Member | Statement |
|---|---|
| `MultiplicitySpec` | For 2 ≤ p and n ≠ 0, p to the multiplicity divides n and the next power does not |
| `DividesIff` | For 2 ≤ p and n ≠ 0, p ^ e divides n exactly when e is at most the multiplicity |
| `MultiplicityUnique` | For 2 ≤ p and n ≠ 0, an exponent e with p ^ e dividing n and $p^{e+1}$ not is the multiplicity |
| `MultiplicityOfNonDivisor` | A number that does not divide n occurs in n to the power 0 |
| `MultiplicitySelf` | A number p ≥ 2 occurs in itself exactly once |
| `MultiplicityCofactor` | For 2 ≤ p and n ≠ 0, n is p to its multiplicity times a cofactor p does not divide |
| `MultiplicityMul` | For a prime, the multiplicity of a product of nonzero numbers is the sum of the multiplicities |
| `MultiplicityAsCount` | For 2 ≤ p and n ≠ 0, the multiplicity counts the i in 1 .. n with p ^ i dividing n |
| `PrimeFactorizationProduct` | A nonzero n whose prime divisors are at most N is the product, over the primes up to N, of each prime to its multiplicity (`factorization.go`) |
| `ProductOfPrimesDivides` | A product of finitely many primes each dividing N divides N (`factorization.go`) |

## Legendre's formula

Passing from n! to (n + 1)! adds the multiplicity of p in n + 1, which
counts the powers of p dividing n + 1; those are exactly the quotients
div(n, p ^ i) that grow by one at n + 1. By induction, the multiplicity of
p in n! is the sum of the quotients div(n, p ^ i) over i from 1 to n.

| Member | Statement |
|---|---|
| `Legendre` | For a prime p, the multiplicity of p in n! is $\sum_{i \in 1 .. n} \operatorname{div}(n, p^i)$ |
