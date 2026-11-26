# real_polynomial — the polynomial functions on ℝ

A real function is polynomial when some finite list of coefficients
sums to it: `polynomial_function p` says there are `m` and `c` with
`p x = Σ_{i∈0..m} cᵢ·xⁱ` for every `x`. The definition is an
existential over Σ, so the chapter is written in the interval calculus
of `iterate/real/real_sum` throughout — unfold to a sum over `0 .. m`, work
there, and package the result back up.

The first movement is closure. The constants and the identity are
polynomial; the class survives addition, scaling on either side,
negation, subtraction, multiplication, finite sums of polynomials,
powers, and composition. The linear laws are constructions on
coefficient lists — adding two polynomials pads both lists with zeros
to the sum of the two degrees and adds them coefficientwise — and the
arithmetic that verifies a construction is Σ's linearity. Products,
powers and sums are inductions instead, and the product's list is
never written down: a coefficient sum one degree higher is its
constant term plus `x` times a shorter sum (the peel), and induction
on the degree carries a product through that reading.

Closing the movement is the structural induction principle — a
property that holds of the constants and the identity and is preserved
by sums and products holds of every polynomial. It says the generators
above are all there is, and it is how the later members avoid
re-entering the coefficient representation: composition is proved by
induction over the outer polynomial, not by composing two sums.

The second movement is roots. A nonzero polynomial has finitely many
roots, and the bound is its degree. The route runs through the
factorization `xⁿ − yⁿ = (x − y)·Σ` — carried through the sum, so that
`p x − p y` factors through `x − y` — which yields the degree bound by
induction, and the finiteness statements follow: a coefficient sum has
finitely many roots exactly when its list is not identically zero, and
a polynomial meets any value finitely often exactly when it is not
constantly that value.

## Members

| entry | statement |
|---|---|
| `Const` | `λx. c` is polynomial |
| `Id` | `λx. x` is polynomial |
| `Identity` | `identity_map` is polynomial |
| `Add` | closure under `p + q` |
| `ScalarLeft` | closure under `c · p` |
| `ScalarRight` | closure under `p · c` |
| `Neg` | `λx. −p x` is polynomial ⇔ `p` is |
| `Sub` | closure under `p − q` |
| `Horner` | the peel: $\sum_{i \le m+1} c(i) \cdot x^i = c(0) + x \cdot \sum_{i \le m} c(i+1) \cdot x^i$ |
| `TimesX` | the shift: $x \cdot \sum_{i \le m} c(i) \cdot x^i$ is polynomial |
| `Mul` | closure under `p · q` |
| `Pow` | closure under `pⁿ` |
| `Sum` | closure under finite sums $\sum_{i \in s} p_i$ |
| `Induction` | the induction principle: constants, the identity, `+`, `·` generate |
| `Compose` | closure under composition `p ∘ q` |
| `DifferenceFactors` | `Σa(i)xⁱ − Σa(i)yⁱ = (x − y)·Σ`, the cofactor a coefficient sum of degree `n − 1` |
| `RootBound` | a coefficient sum with some coefficient not `&0` has at most its degree many roots |
| `FiniteRootsIffNonzero` | the root set is finite ⇔ some coefficient is not `&0` |
| `FiniteLevelSets` | a polynomial meets a value finitely often ⇔ it is not constantly that value |

The chapter is written in two files: `closure.go` carries the class
and what it is closed under, `roots.go` the factorization and the
root count.
