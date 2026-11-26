# complex_field — the complex numbers, a field

A complex number is a pair of reals. `complex(x, y)` is the number with
real part `x` and imaginary part `y`, read back by `re(z)` and `im(z)`
(the words `complex_re` and `complex_im` declare). The type is a record
— a datatype with that one constructor, its two arguments declared as
its parts — so everything about the pair comes with it: every complex
number is `complex(x, y)` for some reals, two pairs are equal exactly
when their entries are (`ComplexInjective`), each part reads back its
entry (`ComplexReDef`, `ComplexImDef`), and a number is its parts
(`ComplexEq`).

The operations are spelled on the parts, and each is written with the
symbol its field reads: `z + w` and `-z` part by part, `z - w` as
`z + -w`, `z * w` as `complex(re(z)·re(w) − im(z)·im(w),
re(z)·im(w) + im(z)·re(w))`, `complex_inv(z)` as the conjugate's parts
over `re(z)² + im(z)²`, and `z / w` as `z * complex_inv(w)`. The inverse
is total, as ℝ's is: at zero every quotient by the zero sum is zero.
A real `x` is `complex_of_real(x) = complex(x, &0)`, `complex_i` is
`complex(&0, &1)`, and `conj(z)` negates the imaginary part.

## A number is its parts

| member | statement |
|---|---|
| `ComplexEq` | `z = w ⇔ re(z) = re(w) ∧ im(z) = im(w)` |

`ComplexEq` is the chapter's working move. Every equation between
complex numbers is, through it, two equations between reals: rewrite
the equation into its parts, compute each part from the definitions,
and what is left is arithmetic of ℝ. `Parts` is that reading as one
rule set — `ComplexEq` and the two projections — so a law reads
`Simp(Parts, Fwd(ComplexMulDef)), ByArith()`, naming only the
operations it computes. The equational axioms of the instances below,
and every law of the last two sections but the two about the inverse,
are that move alone.

## The parts of the operations

| member | statement |
|---|---|
| `PartsAdd` | `re(z + w) = re(z) + re(w) ∧ im(z + w) = im(z) + im(w)` |
| `PartsNeg` | `re(-z) = -re(z) ∧ im(-z) = -im(z)` |
| `PartsSub` | `re(z - w) = re(z) - re(w) ∧ im(z - w) = im(z) - im(w)` |
| `PartsMul` | `re(z * w) = re(z) * re(w) - im(z) * im(w) ∧ im(z * w) = re(z) * im(w) + im(z) * re(w)` |
| `PartsInv` | `re(complex_inv(z)) = re(z) / (re(z) * re(z) + im(z) * im(z)) ∧ im(complex_inv(z)) = -im(z) / (re(z) * re(z) + im(z) * im(z))` |
| `PartsConj` | `re(conj(z)) = re(z) ∧ im(conj(z)) = -im(z)` |
| `PartsOfReal` | `re(complex_of_real(x)) = x ∧ im(complex_of_real(x)) = &0` |
| `PartsI` | `re(complex_i) = &0 ∧ im(complex_i) = &1` |

Each law is its operation's definition read under `re` and under `im`.
The engine computes a part only at `complex(a, b)`: `re(z * w)` stands
as spelled in a statement, in a claim and in an instance of a law alike.
A proof that wants its parts cites the law, as a premise
(`PartsMul.At(z, w)`) or as a rewrite (`Simp(Fwd(PartsMul))`), and the
rewrite touches a product only where it stands under `re` or `im`.
`Simp(Parts, Fwd(ComplexMulDef))` stays the move for an equation
between complex numbers, where every product is to be opened. A
quotient has no law of its own: it is a product with an inverse.

## ℂ is a field

`ComplexRingDef` and `ComplexFieldOpsDef` pack the operations and
carrier `𝕌` into `complex_ring: ring_ops(complex)` and
`complex_field_ops: field_ops(complex)`. The field's ring projection is
`complex_ring`.

The structures are built in the order they nest, one case per axiom:
each equational axiom is the move above, a sub-structure or a
definition is cited, and `one ≠ zero` is the move above under a
negation. `Field` is ℂ's instance of the abstract field, and `FieldOn`
states the same of `complex_field_ops` through `field_on`.

| member | statement |
|---|---|
| `AddGroup` | `abelian_group(additive_group(complex_ring))` |
| `MulMonoid` | `comm_monoid(complex_mul, complex_of_real(&1))` |
| `CommRing` | `comm_ring(complex_ring)` |
| `CommRingOn` | `comm_ring_on(complex_ring)` |
| `Field` | `field(complex_field_ops)` |
| `FieldOn` | `field_on(complex_field_ops)` |
| `ComplexIntegralDomain` | `integral_domain_on(complex_ring)` |
| `ComplexCharacteristicZero` | `characteristic_zero(complex_ring)` |

Only the left inverse is an argument rather than a computation. A
nonzero `z` has parts that are not both zero, so the sum `D` of their
squares is not zero (`real_order_ring.SumSquaresEqZero`); then the real
part of `complex_inv(z) * z` is `D` over itself and the imaginary part
cancels.

The algebra of ℂ is not restated here. Every law of the ring and of the
field is read at these instances where it is used:
`comm_ring.MulLeftZeroOn.Read(CommRing)` is `complex_of_real(&0) * z =
complex_of_real(&0)`, `field.InvInvOn.Read(Field)` is
`complex_inv(complex_inv(z)) = z`, and `field.MulEqZeroOn.Read(Field)`
says ℂ has no zero divisors. The chapters stated over a field apply to
ℂ as they do to ℝ: `basis.DimVec.Read(Field)` is `vec_dim(complex_add,
complex_of_real(&0), complex_mul, {u:(num → complex) |
vec⟨n⟩(complex_of_real(&0), u)}) = n` — ℂⁿ has dimension n — with no
line of proof written for ℂ.

## The reals, and i

| member | statement |
|---|---|
| `ISquared` | `complex_i * complex_i = -complex_of_real(&1)` |
| `INonzero` | `complex_i ≠ complex_of_real(&0)` |
| `InvI` | `complex_inv(complex_i) = -complex_i` |
| `StandardForm` | `complex(x, y) = complex_of_real(x) + complex_i * complex_of_real(y)` |
| `OfRealInjective` | `complex_of_real(x) = complex_of_real(y) ⇔ x = y` |
| `OfRealAdd` | `complex_of_real(x + y) = complex_of_real(x) + complex_of_real(y)` |
| `OfRealNeg` | `complex_of_real(-x) = -complex_of_real(x)` |
| `OfRealSub` | `complex_of_real(x - y) = complex_of_real(x) - complex_of_real(y)` |
| `OfRealMul` | `complex_of_real(x * y) = complex_of_real(x) * complex_of_real(y)` |
| `OfRealRingHomomorphism` | `ring_homomorphism(real_ring, complex_ring, complex_of_real)` |
| `OfRealInv` | `complex_of_real(real_inv(x)) = complex_inv(complex_of_real(x))` |
| `OfRealDiv` | `complex_of_real(x / y) = complex_of_real(x) / complex_of_real(y)` |
| `OfRealPow` | `complex_of_real(real_pow(x, n)) = monoid_pow(complex_mul, complex_of_real(&1), complex_of_real(x), n)` |
| `OfRealSum` | `finite(s) ⇒ complex_of_real(Σ_{i∈s} f(i)) = Σ_{i∈s} complex_of_real(f(i))` |
| `OfRealCond` | `complex_of_real(COND(c, x, y)) = COND(c, complex_of_real(x), complex_of_real(y))` |
| `AddPowOne` | `monoid_pow(complex_add, complex_of_real(&0), complex_of_real(&1), n) = complex_of_real(&n)` |

The embedding of ℝ preserves the operations, so ℝ sits inside ℂ as a
subfield; it also passes through finite sums and through a conditional.
The inverse, the quotient and the power are the laws not
computed from the parts: the embedding respects zero, one and products,
a map between fields that does carries inverses to inverses
(`field.MapInv`), a quotient is a product with an inverse, and a map
that keeps one and products carries powers to powers
(`comm_monoid.MapPow`, at ℝ's power read as its product's,
`real_pow.MonoidPow`). `OfRealPow` spells ℂ's power with its components
— `monoid_pow(complex_mul, complex_of_real(&1), …)`, not `z ^ n` —
because a chapter cannot bind the monoid instance it registers itself.
`AddPowOne` is the embedding of ℕ: n copies of one summed is the real
numeral n seen in ℂ — the bridge by which the arithmetic closer's
structure ring reads ℂ's literals (`complex_of_real(&2)`) as the ring's
numerals, so a ring identity over ℂ closes by a bare `ByArith()`.

## Conjugation

| member | statement |
|---|---|
| `ConjConj` | `conj(conj(z)) = z` |
| `ConjAdd` | `conj(z + w) = conj(z) + conj(w)` |
| `ConjMul` | `conj(z * w) = conj(z) * conj(w)` |
| `ConjOfReal` | `conj(complex_of_real(x)) = complex_of_real(x)` |
| `ConjI` | `conj(complex_i) = -complex_i` |
| `MulConj` | `z * conj(z) = complex_of_real(re(z) * re(z) + im(z) * im(z))` |
| `SquareSumMul` | `re(z * w)² + im(z * w)² = (re(z)² + im(z)²) · (re(w)² + im(w)²)`: the square sum of the parts is multiplicative |
| `ConjInv` | `conj(complex_inv(z)) = complex_inv(conj(z))` |

Conjugation is an automorphism of the field that fixes the reals and
sends `i` to `−i`; it commutes with the inverse by `field.MapInv`, as
the embedding does.

## Finite products

| member | statement |
|---|---|
| `ComplexProductDef` | `complex_product`: set(A) → (A → complex) → complex |
| `ComplexProductModuleSum` | `finite(s) ⇒ module_sum(complex_mul, complex_of_real(&1), s, f) = product(s, f)` |

`complex_product` is the fold at complex multiplication, written
`product(s, f)` and `Π_{i<n} f(i)` at a complex body, as the products over
ℕ, ℤ and ℝ are. The law beside it reads the module chapter's fold at ℂ's
multiplicative monoid as that product.
