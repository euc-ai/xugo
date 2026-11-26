# int_pow — ℤ's power operation

Raising an integer to a natural exponent. The operation is inherited,
not constructed: `int_pow` is defined by transport along
`real_of_int`, exactly as ℤ's ring operations are, so everything this
chapter states is an image of ℝ's power theory read through the
embedding.

The members carry the whole story:

| member | what it says |
|---|---|
| `PowBridge` | a power of an integer represents that power of its representative — the closure argument (powers of integers are integers) that makes the transported definition well-formed |
| `PowClauses` | the recursion equations: the empty product is `&1`, and each further factor is one more multiplication by the base |
| `OfNumPow` | `&` commutes with iterating a product: a power computed in ℕ and embedded agrees with the ℤ power of the embedded base |
| `PowTwoNonzero` | `int_pow(&2, n) ≠ &0` — the first consequence read back across OfNumPow: ℕ's power-of-two nonzeroness carried to ℤ by the embedding's injectivity |
| `PowAdd` | a power splits over a sum of exponents, $x^{m+n} = x^m \cdot x^n$ |
| `PowPow` | a power of a power is the power at the product of the exponents, $(x^m)^n = x^{m \cdot n}$ |
| `OnePow` | every power of 1 is 1 |
| `MulPow` | a power of a product is the product of the powers, `(x·y)^n = x^n · y^n` |
| `NegOnePowParity` | `(−1)^n` is 1 at even n and −1 at odd n |
| `NegOnePowValues` | every power of −1 is 1 or −1 |

`PowBridge` is the first member with an argument of its own — an
induction on the exponent, settling each case against one of ℝ's two
defining equations plus a closure law of `int_construction`. `PowClauses`
is the image of ℝ's recursion and `OfNumPow` the image of ℝ's own
embedding law, single transport steps, as are the exponent laws `PowAdd`,
`PowPow` and `OnePow`. `NegOnePowParity` follows by induction through
`PowClauses`; `NegOnePowValues` reads its two possible values directly.

## Why this is not part of int_construction

ℤ's construction — the type, its ring, its order — is power-free: no
bridge, closure law, or discreteness fact below needs a power. The
power is a DERIVED operation introduced on top of the finished
construction, and this chapter is where it lives: above
`int_construction` (whose closure laws `PowBridge` imports), and above
the ℝ power theory its members are read from. Consumers downstream
— parity's powers of two, congruence's power-of-a-remainder law — reach
ℤ's power here without dragging it into the construction they also
stand on.
