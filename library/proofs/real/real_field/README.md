# real_field — ℝ as a field

`real_ring` develops ℝ's algebra as far as the ring laws reach. The
tower gives `real_inv` two further facts and nothing else: it is a
TOTAL function — `real_construction.InvZero` fixes `inv &0 = &0`, so there is no
partiality to carry around — and it inverts on the left,
`x ≠ &0 ⇒ inv x · x = &1`. Those two facts, the ring, ℕ's `1 ≠ 0` and
division (defined below) are the axioms of the abstract field
(algebra/field/field), and this chapter is where ℝ becomes an instance
of it.

## Division

`RealDivDef` — `x / y = x * real_inv(y)`. The definition says nothing
about the divisor being nonzero: the inverse of zero is a value like
any other, and a law that needs the divisor nonzero says so in its own
hypothesis.

## ℝ as a field

`RealFieldOpsDef` packs the real operations, inverse, division and
carrier `𝕌` into `real_field_ops: field_ops(real)`. `RealFieldRing`
states its ring as an equation, `field_ring(real_field_ops) =
real_ring`: both records pack the same operations. `Field` states
`field(real_field_ops)`: its ring is `real_ring` by that equation, and
the remaining cases are the inverse axioms, division and the
distinctness of zero and one inherited from ℕ.

## The laws of the inverse and of division

They are the field chapter's, proved once over the structure, and a
consumer reads each at this instance where it uses it:
`field.InvMulOn.Read(real_field.Field)` is `real_inv(x * y) =
real_inv(x) * real_inv(y)`, `field.DivRightMulOn.Read(real_field.Field)`
is `y ≠ &0 ⇒ x / y * y = x`. ℂ reads the same laws at its own instance
(`complex_field.Field`). The ℝ arithmetic closer is served these
readings too.
