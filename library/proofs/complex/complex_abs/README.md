# complex_abs — the modulus

The modulus of `z` is its length as a point of the plane:
`complex_abs(z) = real_sqrt(re(z) * re(z) + im(z) * im(z))`. Most laws
here open the root and finish with a law of the real square root —
uniqueness (a nonnegative number squaring to the radicand is the root),
its sign, or its lower bound. `AbsSquare`, the square of the modulus as
the sum of the squares of the parts, carries the laws whose route is
squaring: the zero test, the product and the triangle.

## The modulus and its square

| member | statement |
|---|---|
| `SumSquaresNonneg` | `&0 ≤ re(z) * re(z) + im(z) * im(z)` |
| `AbsSquare` | `complex_abs(z) * complex_abs(z) = re(z) * re(z) + im(z) * im(z)` |
| `AbsNonneg` | `&0 ≤ complex_abs(z)` |
| `AbsEqZero` | `complex_abs(z) = &0 ⇔ z = complex_of_real(&0)` |
| `AbsPosIffNonzero` | `&0 < complex_abs(z) ⇔ z ≠ complex_of_real(&0)` |
| `AbsOfReal` | `complex_abs(complex_of_real(x)) = real_abs(x)` |
| `AbsOfNonnegReal` | `&0 ≤ x ⇒ complex_abs(complex_of_real(x)) = x` |
| `AbsOfRealSub` | `complex_abs(complex_of_real(x) - complex_of_real(y)) = real_abs(x - y)` |
| `AbsI` | `complex_abs(complex_i) = &1` |
| `AbsNeg` | `complex_abs(-z) = complex_abs(z)` |
| `AbsConj` | `complex_abs(conj(z)) = complex_abs(z)` |

Only zero has modulus zero, because a sum of two squares vanishes only
when both parts do (`real_order_ring.SumSquaresEqZero`). On the reals
the modulus is the absolute value: `|x|` is the nonnegative number that
squares to `x · x`, so it is the root; a nonnegative real is its own
modulus, and two reals are as far apart in ℂ as in ℝ (`AbsOfRealSub`).
Negation and conjugation change signs of parts, which their squares do
not see.

## The modulus is multiplicative

| member | statement |
|---|---|
| `AbsMul` | `complex_abs(z * w) = complex_abs(z) * complex_abs(w)` |
| `AbsInv` | `complex_abs(complex_inv(z)) = real_inv(complex_abs(z))` |
| `AbsDiv` | `complex_abs(w / v) = complex_abs(w) / complex_abs(v)` |
| `AbsPow` | `complex_abs(z ^ n) = real_pow(complex_abs(z), n)` |
| `AbsRootOfUnity` | `z ^ n = complex_of_real(&1) ∧ n ≠ 0 ⇒ complex_abs(z) = &1` |

The radicand of `z · w` is the product of the two radicands — the
two-squares identity `(ac − bd)² + (ad + bc)² = (a² + b²)(c² + d²)` —
and `|z|·|w|`, nonnegative and squaring to it, is its root by
uniqueness of the root.

The inverse follows from the product: the modulus is a map from ℂ to
ℝ that respects zero, one and products — not sums, which `field.MapInv`
does not ask for — so it carries inverses to inverses, and with the
product, quotients to quotients. So does the
power: a map keeping one and products carries powers to powers
(`comm_monoid.MapPow`), and ℝ's power is its product's
(`real_pow.MonoidPow`). `z ^ n` is ℂ's power, the monoid power of its
product, which this chapter binds. A root of unity has modulus 1.

## The triangle inequality

| member | statement |
|---|---|
| `ReLessEqAbs` | `real_abs(re(z)) ≤ complex_abs(z)` |
| `ImLessEqAbs` | `real_abs(im(z)) ≤ complex_abs(z)` |
| `PartsNonexpanding` | `real_abs(re(z) - re(w)) ≤ complex_abs(z - w) ∧ real_abs(im(z) - im(w)) ≤ complex_abs(z - w)` |
| `AbsLeParts` | `complex_abs(z) ≤ real_abs(re(z)) + real_abs(im(z))` |
| `AbsTriangle` | `complex_abs(z + w) ≤ complex_abs(z) + complex_abs(w)` |
| `AbsSubTriangle` | `complex_abs(x - u) ≤ complex_abs(x - y) + complex_abs(y - u)` |
| `AbsSubComm` | `complex_abs(z - w) = complex_abs(w - z)` |
| `AbsTriangleReverse` | `real_abs(complex_abs(z) - complex_abs(w)) ≤ complex_abs(z - w)` |
| `AbsSumTriangle` | `finite(s) ⇒ complex_abs(module_sum(complex_add, &0, s, F)) ≤ sum(s, λi. complex_abs(F(i)))` |
| `AbsSumDominated` | `finite(s) ∧ (∀x. x ∈ s ⇒ complex_abs(F(x)) ≤ g(x)) ⇒ complex_abs(module_sum(complex_add, &0, s, F)) ≤ sum(s, g)` |

Each part is at most the modulus: its square is one of the two
nonnegative squares the modulus is the root of. The triangle inequality
is the textbook one. The square of `|z + w|` differs from
`(|z| + |w|)²` only in the cross term — twice `re(z · conj(w))` against
twice `|z| · |w|` — and a real part never exceeds the modulus, which for
`z · conj(w)` is `|z| · |w|` (`AbsMul`, `AbsConj`); the squares compare,
and the moduli being nonnegative, so do the moduli. Between three
points it reads at `x − u = (x − y) + (y − u)`: the distance from `x`
to `u` is at most the way round through `y` (`AbsSubTriangle`), and it is
the distance from `u` to `x`, `x − u` being `−(u − x)` (`AbsSubComm`).
The reverse inequality reads the triangle at `z = (z − w) + w` and at
`w = −(z − w) + z`, the two identities coming from ℂ's additive group,
read at its instance. A finite sum takes the inequality one term at a
time, by induction on the index set, and what dominates the moduli of
the terms then bounds the modulus of the sum, as `real_sum.Triangle`
and `real_sum.Dominated` do on the line.
