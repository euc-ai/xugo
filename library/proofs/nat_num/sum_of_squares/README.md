# sum_of_squares — which primes are sums of two squares, and Lagrange's theorem that every number is a sum of four

A prime is a sum of two squares exactly when it is 2 or ≡ 1 (mod 4): mod a
prime p ≡ 1 (mod 4) the number −1 is a square, so p divides some m² + 1,
and a prime dividing m² + 1 is a sum of two squares because ℤ[i] is a
principal ideal domain (complex/gaussian_integer). Every natural number is
a sum of four squares, by Euler's four-square identity and Lagrange's
descent.

## Two squares

A square is 0 or 1 mod 4 according to the parity of its root, so an odd
prime a² + b², whose roots have opposite parities, is ≡ 1 (mod 4).
Conversely a prime p ≡ 1 (mod 4) divides some m² + 1, and so is a sum of
two squares.

| Member | Statement |
|---|---|
| `FermatTwoSquares` | Fermat's theorem: a prime is a sum of two squares exactly when it is 2 or ≡ 1 (mod 4) |

## Four squares

Every prime divides some x² + y² + 1, by counting residues of squares. The
least multiple of p that is a sum of four squares is p itself, since an
even multiple halves and an odd one descends through Euler's identity.
Every number then follows from its prime factors, because sums of four
squares are closed under products.

| Member | Statement |
|---|---|
| `FourSquareIdentity` | Euler's four-square identity over ℤ |
| `FourIntegerSquaresNatural` | A natural number that is a sum of four integer squares is a sum of four natural squares |
| `SumFourSquaresMul` | A product of two sums of four squares is a sum of four squares |
| `PrimeDividesTwoSquaresPlusOne` | Every prime divides some x² + y² + 1 with x, y ≤ p/2 |
| `HalfOfFourSquares` | Half of an even sum of four squares is a sum of four squares |
| `EvenMultipleHalves` | An even multiple m · p that is a sum of four squares gives a smaller one |
| `OddMultipleDescends` | An odd multiple m · p, m not dividing p, that is a sum of four squares gives a smaller one |
| `PrimeFourSquares` | Every prime is a sum of four squares |
| `LagrangeFourSquares` | Lagrange's theorem: every natural number is a sum of four squares |
