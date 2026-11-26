# ring_ideal — ideals of a commutative ring on a set, their products, prime and maximal ideals, and units

An ideal of the ring on `c` is a subset of `c` holding zero, closed under
the addition and absorbing the multiplication by every element of `c`:
`ring_ideal(R, I)`, where `R : ring_ops(A)` carries its operations and `c = R.carrier`.
Closure under the negation is a law, not a condition, since `-x` is
`-one * x`. A prime ideal is a proper ideal holding a factor of each
product it holds; a maximal ideal is a proper ideal with no proper ideal
strictly above it. The ideal a set generates is the intersection of the
ideals holding it, which is defined without a finite sum; that its
members are combinations, one generator at a time, is a theorem
(`SpanInsert`), and so is that a member uses finitely many generators
(`SpanFinite`). The radical of an ideal is not minted: what the prime
spectrum needs of it is `PrimeAvoidingPowers`, a prime missing a given
element above an ideal holding none of its powers. Zorn's lemma enters
once, in `ExistsMaximalAvoiding`; a maximal ideal above a proper ideal and
a prime missing the powers of `f` both start from it, at `{one}` and at
the powers of `f`, and that the second is prime is its own argument.

## The definitions and their conditions

| member | statement |
|---|---|
| `RingIdealDef` | `ring_ideal(R, I)` ⇔ `I ⊆ c`, `zero ∈ I`, closed under `+`, absorbing `*` by `c` |
| `PrimeIdealDef` | `prime_ideal(R, p)` ⇔ an ideal, `one ∉ p`, `x * y ∈ p ⇒ x ∈ p ∨ y ∈ p` on `c` |
| `MaximalIdealDef` | `maximal_ideal(R, m)` ⇔ an ideal, `one ∉ m`, every ideal above is `m` or holds `one` |
| `IdealCoverDef` | `ideal_cover(R, J, H)` ⇔ `J` and `H` ideals, `J ⊆ H`, `J ≠ H`, every ideal between them is `J` or `H` |
| `IdealSpanDef` | `ideal_span(R, S)` = the intersection of the ideals holding `S` |
| `IdealMulDef` | `ideal_mul(R, I, J)` = the ideal the products `x * y`, `x ∈ I`, `y ∈ J`, generate |
| `IdealPowDef` | `ideal_pow(R, I, n)` = the `n`-th power of `I` under `ideal_mul`, with unit `c` |
| `RingUnitDef` | `ring_unit(R, x)` ⇔ `x ∈ c` with an inverse in `c` |
| `IdealSubset`, `IdealZero`, `IdealAdd`, `IdealMul` | the four conditions of an ideal |
| `PrimeIdealIdeal`, `PrimeIdealProper`, `PrimeIdealPrime` | the three conditions of a prime ideal |
| `PrimeIdealPow` | a prime ideal holding a power of `f` holds `f` |
| `PrimeIdealMulSubset` | a prime ideal holding the product `ideal_mul(R, I, J)` of two ideals holds `I` or `J` |
| `MaximalIdealIdeal`, `MaximalIdealProper`, `MaximalIdealMaximal` | the three conditions of a maximal ideal |
| `MaximalIdealCover` | `maximal_ideal(R, m) ⇒ ideal_cover(R, m, R.carrier)`: the carrier covers a maximal ideal |
| `MaximalIdealNotWhole` | `subring(R, S) ∧ maximal_ideal(restrict_ring(R, S), m) ⇒ m ≠ S`: a maximal ideal of a subring is not all of it |

## Every ideal, and the two ideals every ring has

| member | statement |
|---|---|
| `IdealNeg` | `ring_ideal(R, I) ∧ x ∈ I ⇒ -x ∈ I` |
| `IdealSub` | `ring_ideal(R, I) ∧ x ∈ I ∧ y ∈ I ⇒ x + -y ∈ I`: an ideal holds the difference of two members |
| `CarrierIdeal` | `ring_ideal(R, R.carrier)` |
| `ZeroIdeal` | `ring_ideal(R, {zero})` |
| `IdealOneIff` | `ring_ideal(R, I) ⇒ (one ∈ I ⇔ I = c)` |
| `OneUnit` | `ring_unit(R, one)` |
| `RingUnitPow` | `ring_unit(R, x) ⇒ ring_unit(R, xⁿ)`: a power of a unit is a unit |
| `RingUnitMul` | `ring_unit(R, x) ∧ ring_unit(R, y) ⇒ ring_unit(R, x * y)`: a product of units is a unit |
| `UnitPlusSquareZeroIsUnit` | `u * w = R.one ∧ j * j = R.zero ⇒ ring_unit(R, u + j)`, with inverse `w − w² j`: a unit plus a member of square zero is a unit |
| `UnitNotInProperIdeal` | a proper ideal holds no unit |
| `ChainUnionIdeal` | the union of a non-empty chain of ideals is an ideal |
| `IdealContraction` | `subring(R, S) ∧ S ⊆ T ∧ ring_ideal(restrict_ring(R, T), J) ⇒ ring_ideal(restrict_ring(R, S), S ∩ J)`: an ideal of T meets a subring inside T in an ideal |

## The ideal a set generates

Ideal generation is a closure operator on `{S | S ⊆ R.carrier}`. The least-ideal
property supplies its laws through `relations/order.ClosureFromLeast`,
the same construction used by submodule span and topological closure.

| member | statement |
|---|---|
| `SpanIdeal` | `S ⊆ c ⇒ ring_ideal(R, ideal_span(R, S))` |
| `SpanContains` | `S ⊆ ideal_span(R, S)` |
| `SpanLeast` | `ring_ideal(R, J) ∧ S ⊆ J ⇒ ideal_span(R, S) ⊆ J` |
| `SpanOfIdeal` | `ring_ideal(R, I) ⇒ ideal_span(R, I) = I` |
| `SpanMono` | `S ⊆ T ⇒ ideal_span(R, S) ⊆ ideal_span(R, T)` |
| `SpanInsertAbove` | `S ⊆ c ∧ h ∈ c ⇒` `J = ideal_span(R, insert(h, S))` is an ideal, `S ⊆ J`, `h ∈ J`, and `h ∉ S ⇒ J ≠ S` |
| `SpanInsert` | `S ⊆ c ∧ h ∈ c ⇒ ideal_span(R, insert(h, S)) = {b * h + t \| b ∈ c, t ∈ ideal_span(R, S)}` |
| `SpanInsertIdeal` | `ring_ideal(R, I) ∧ h ∈ c ⇒ ideal_span(R, insert(h, I)) = {b * h + t \| b ∈ c, t ∈ I}` |
| `SpanPairWhole` | `g₁, g₂, c₁, c₂ ∈ c ∧ c₁ * g₁ + c₂ * g₂ = R.one ⇒ ideal_span(R, {g₁, g₂}) = c` |
| `SpanUnionIdeals` | the ideal generated by two ideals consists of their element sums |
| `PrincipalIdealMultiples` | `p ∈ c ⇒ ideal_span(R, {p}) = {r * p \| r ∈ c}` |
| `SpanFinite` | a member of `ideal_span(R, S)` lies in the span of a finite part of `S` |
| `SpanClosureOperator` | `ideal_span(R, ·)` is a closure operator on the subsets of `R.carrier` |

## The product of two ideals

The product `ideal_mul(R, I, J)` is the span of the products `x * y`, so its
calculus needs no finite sums. It holds those products and lies in every ideal
that holds them; it grows with its factors; over a ring it is an ideal when its
factors lie in the carrier, inside
`I ∩ J` when `I` and `J` are ideals. It commutes, it associates by fixing one
factor at a time through the colon ideal `(I : z)`, and the carrier is its
unit: the ideals of any commutative ring are a commutative monoid under the
product.

| member | statement |
|---|---|
| `IdealMulHolds` | `x ∈ I ∧ y ∈ J ⇒ x * y ∈ ideal_mul(R, I, J)` |
| `IdealMulLeast` | `ring_ideal(R, K) ∧ (∀x y. x ∈ I ∧ y ∈ J ⇒ x * y ∈ K) ⇒ ideal_mul(R, I, J) ⊆ K` |
| `IdealMulMono` | `I ⊆ M ∧ J ⊆ N ⇒ ideal_mul(R, I, J) ⊆ ideal_mul(R, M, N)` |
| `IdealMulIdeal` | `I ⊆ c ∧ J ⊆ c ⇒ ring_ideal(R, ideal_mul(R, I, J))` |
| `IdealMulSubsetInter` | `ring_ideal(R, I) ∧ ring_ideal(R, J) ⇒ ideal_mul(R, I, J) ⊆ I ∩ J` |
| `IdealMulComm` | `I ⊆ c ∧ J ⊆ c ⇒ ideal_mul(R, I, J) = ideal_mul(R, J, I)` |
| `ColonIdeal` | `ring_ideal(R, I) ∧ z ∈ c ⇒ ring_ideal(R, {w \| w ∈ c ∧ w * z ∈ I})`, the colon ideal `(I : z)` |
| `IdealMulAssoc` | `I, J, K ⊆ c ⇒ ideal_mul(R, ideal_mul(R, I, J), K) = ideal_mul(R, I, ideal_mul(R, J, K))` |
| `IdealMulOne` | `ring_ideal(R, I) ⇒ ideal_mul(R, c, I) = I` |
| `IdealsCommMonoid` | the ideals form a commutative monoid under `ideal_mul(R, ·, ·)` with unit `c` |
| `IdealPowZero`, `IdealPowSuc` | `ideal_pow(R, I, 0) = c`; `ideal_pow(R, I, suc(n)) = ideal_mul(R, I, ideal_pow(R, I, n))` |
| `IdealPowIdeal` | `ring_ideal(R, I) ⇒ ring_ideal(R, ideal_pow(R, I, n))` |
| `IdealPowAdd` | `ring_ideal(R, I) ⇒ ideal_pow(R, I, m + n) = ideal_mul(R, ideal_pow(R, I, m), ideal_pow(R, I, n))` |

## Prime and maximal ideals

| member | statement |
|---|---|
| `MaximalIsPrime` | `maximal_ideal(R, m) ⇒ prime_ideal(R, m)` |
| `ExistsMaximalAvoiding` | an ideal missing `S` lies in an ideal maximal among the ideals missing `S` |
| `ExistsMaximalAbove` | a proper ideal lies in a maximal ideal |
| `PrimeAvoidingPowers` | an ideal holding no power of `f` lies in a prime ideal missing `f` |
| `MaximalComplement` | `maximal_ideal(R, m) ∧ a ∈ c ∧ a ∉ m ⇒ ideal_span(R, insert(a, m)) = c` |
| `MaximalUnitModulo` | `maximal_ideal(R, m) ∧ a ∈ c ∧ a ∉ m ⇒ ∃v ∈ c. v * a - one ∈ m` |
| `MaximalPowerUnitModulo` | an element outside a maximal ideal has an inverse modulo every natural power of that ideal |
