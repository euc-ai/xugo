# real_pow — ℝ's powers

Iterating the product. The chapter's constant is
**`real_pow : real → num → real`**, the ℕ-indexed power, minted by
primitive recursion on the exponent: the empty product is `&1`, each
successor one more factor of the base.

The theory needs only ℝ's field and order, and ℤ's construction
consumes it — powers of integers are integers. `int_num/int_pow` — ℤ's
own power chapter — lifts this chapter's recursion equations and its
embedding law into ℤ.

Three chapters beside this one build on it, each a family of its own.
[real_zpow](../real_zpow/README.md) is the power at an integer exponent:
every law there is a law here read through the sign of the exponent, and
ℤ enters there: this chapter reads none of it.
[real_sqrt](../real_sqrt/README.md) is the square root: its definition names
`real_pow(y, 2)` beside `sgn` and `|·|`, and its existence comes once from
completeness. [real_rpow](../real_rpow/README.md) is the power at a real
exponent, `exp(a · log x)` for x > 0, so it stands above exp and log, which
are built from this chapter's natural powers. The dependency is one-way: each
imports this package, and this package imports none of them.

## The movements

1. **Recursion** — where the power comes from: the
   `Pow` mint and its two clause projections — the successor clause
   also read at `n + 1`, the way an indexed statement writes the next
   exponent (`PowAddOne`), and the same recursion read as the monoid
   power of ℝ's product (`MonoidPow`) — then the evaluations
   that pin one slot of the power and read the answer off those
   clauses. The base at 1 and at 0 (`OnePow`, `ZeroPow`), the exponent
   at 1 and at 2 (`PowOne`, `PowTwo`), and the law that the embedding
   ℕ ↪ ℝ carries ℕ's power to this one (`OfNumPow`). `OnePow`, `PowOne`
   and `PowTwo` are the generic power's laws (`comm_monoid`) read at
   ℝ's product through `MonoidPow`; `ZeroPow` and `OfNumPow` induct on
   the exponent. No law in this movement relates two exponents to one
   another — that is the movement below.
2. **Algebra** — the homomorphism laws: what the power
   does to the operations its two slots are built from. Exponent
   addition and iterated powers on the ℕ side (`PowAdd`, `PowPow`),
   base distribution, inverses and quotients on the ℝ side
   (`MulPowDistrib`, `InvPow`, `DivPow`). `PowAdd`, `PowPow` and
   `MulPowDistrib` are the generic power's laws read at ℝ's product
   (`comm_monoid.PowAdd`, `PowPow`, `MulPow`), proved once for every
   commutative monoid; `InvPow` is an induction in which both sides
   descend their own recursion in lockstep. `DivPow` says what the others
   are for: a quotient is a product with an inverse, so opening it leaves
   two laws already proved and nothing to induct on.
3. **The factorization** — one identity standing apart from the
   homomorphism laws: $x^n - y^n = (x-y) \cdot \sum_{i<n} x^i \cdot y^{n-1-i}$
   (`DifferenceOfPowers`). It relates no operation to the power; it is
   a telescope — each scaled term is a forward difference of
   $x^i \cdot y^{n-i}$, and the sums chapter evaluates the telescope at the
   two ends. The binomial theorem, `BinomialExpansion` (its own file,
   `binomial.go`), reaches into Σ as well:
   `(x + y)ⁿ = Σ_{k∈0..n} &binomial(n, k)·xᵏ·yⁿ⁻ᵏ`.
   Its proof is `nat_num/binomial`'s `Expansion` read in ℝ; each
   coefficient is a natural number carried in by `&`, and the embedding
   adds, so Pascal's rule holds of the carried coefficients too.
4. **Order** — positivity and monotonicity. Nonnegativity
   and positivity are preserved by the power (`PowNonneg`, `PowPos`),
   the power is monotone in its base (`PowMonoBase`, and strictly once
   the exponent is nonzero, `PowMonoBaseStrict`) and in its exponent
   for bases at least one (`PowMonoExp`). For bases in `⟦0, 1⟧` the
   exponent order reverses (`PowMonoExpBelowOne`), and a square is never
   negative (`PowTwoNonneg`). The sign laws, the base-monotonicity laws,
   and Bernoulli's inequality iterate a product one factor at a time.
   Bernoulli says that a power of `1 + x` never falls below its linear
   part `1 + n·x` once `x ≥ −1` (`Bernoulli`), and on ⟦0, ∞⟭ the power
   tⁿ⁺¹ lies above its tangent line at any point (`PowAboveTangentLine`). The other order laws are
   consequences, including the square's order fact: one square
   is at most another exactly when the size of its base is at most the
   other's (`AbsLessEqIffPowTwoLessEq`). `OneLessEqPow` is the hinge — base-monotonicity
   read at the two bases `&1` and `x` is what makes monotonicity in the
   EXPONENT need no induction of its own.
5. **Absolute value and sign** — `AbsPow` commutes
   `|·|` with the power at every exponent, and `SgnPow`, its twin at the
   sign, does the same for `real_sgn`, proved in lockstep; `SquareOfAbs` says the square
   in particular cannot tell `|x|` from `x`. The second is not a
   corollary of the first: it is a statement about the sign rather than
   about iteration, and a dependency constraint keeps the short route
   between them closed, so it goes through the ring's negation laws
   instead.

Public member map:

| member | statement |
|---|---|
| `Pow` | x⁰ = &1 ∧ x^suc n = x · xⁿ |
| `PowAddOne` | $x^{n+1} = x \cdot x^n$ — the successor clause at `n + 1` |
| `MonoidPow` | `real_pow(x, n) = monoid_pow(real_mul, &1, x, n)` — the generic power of ℝ's product, by the same recursion |
| `OnePow` | 1ⁿ = 1 |
| `ZeroPow` | 0ⁿ = COND(n = 0, &1, &0) |
| `PowOne` | x¹ = x |
| `PowTwo` | x² = x · x |
| `OfNumPow` | (&m)ⁿ = &(nat_pow(m, n)) — stated power-first, like every entry above; ℤ's twin spells the mirror |
| `PowAdd` | $x^{m+n} = x^m \cdot x^n$ |
| `PowPow` | $(x^m)^n = x^{m \cdot n}$ |
| `MulPowDistrib` | (x·y)ⁿ = xⁿ · yⁿ |
| `InvPow` | (x⁻¹)ⁿ = (xⁿ)⁻¹ |
| `DivPow` | (x/y)ⁿ = xⁿ / yⁿ |
| `PowNonneg` | &0 ≤ x ⇒ &0 ≤ xⁿ |
| `PowPos` | &0 < x ⇒ &0 < xⁿ |
| `PowMonoBase` | &0 ≤ x ∧ x ≤ y ⇒ xⁿ ≤ yⁿ |
| `PowMonoBaseStrict` | n ≠ 0 ∧ &0 ≤ x ∧ x < y ⇒ xⁿ < yⁿ |
| `Bernoulli` | −&1 ≤ x ⇒ &1 + &n·x ≤ (&1 + x)ⁿ |
| `PowAboveTangentLine` | &0 ≤ u ∧ &0 ≤ v ⇒ uⁿ⁺¹ + &(n + 1)·uⁿ·(v − u) ≤ vⁿ⁺¹ |
| `OneLessEqPow` | &1 ≤ x ⇒ &1 ≤ xⁿ |
| `PowMonoExp` | &1 ≤ x ∧ m ≤ n ⇒ xᵐ ≤ xⁿ |
| `PowMonoExpBelowOne` | &0 ≤ r ∧ r ≤ &1 ∧ m ≤ n ⇒ rⁿ ≤ rᵐ |
| `PowTwoNonneg` | &0 ≤ x² — our name; the ring's `SquareNonneg` already holds the other spelling of "square" |
| `AbsPow` | \|xⁿ\| = \|x\|ⁿ |
| `SquareOfAbs` | x² = \|x\|² |
| `SgnPow` | sgn(xⁿ) = (sgn x)ⁿ |
| `AbsLessEqIffPowTwoLessEq` | \|x\| ≤ \|y\| ⇔ x² ≤ y² — the chapter spells the square PowTwo and a ⇔ takes the corpus's Iff form |
| `DifferenceOfPowers` | $x^n - y^n = (x-y) \cdot \sum_{i<n} x^i \cdot y^{n-1-i}$ |
| `BinomialExpansion` | (x + y)ⁿ = Σ_{k∈0..n} &binomial(n, k)·xᵏ·yⁿ⁻ᵏ |

Every algebra member is stated compound-power-first, like the
evaluations above them: the subject is the power of the compound thing,
and the right-hand side is what it splits into — with one exception, `DifferenceOfPowers`, whose subject is a difference of two powers and which is stated the way the factorization is read, difference first.

## Naming

Fixed-slot members read like `nat_num/nat_arith`'s exponentiation file,
whose conventions this chapter deliberately mirrors: a special BASE
puts the noun first (`OnePow`, `ZeroPow` — 1ⁿ, 0ⁿ), a special EXPONENT
puts `Pow` first (`PowOne`, `PowTwo` — x¹, x²).

Framework mechanics (family manifest, shared CNF cache, replay) are
the standard family shape — see `family.go` and
`library/registry`.
