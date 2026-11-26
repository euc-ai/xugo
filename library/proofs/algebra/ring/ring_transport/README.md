# ring_transport — a commutative ring carried along an injection onto its image

A ring record `R : ring_ops(A)` and a map `ι : A → B` give a ring record
on `B`. Each operation pulls its arguments back to `R`'s carrier through
the chosen preimage `inverse_on(R.carrier, ι, u)` of the sets chapter,
operates in `R`, and pushes the result forward; the zero and the one are
pushed forward. `transport_ring(ι, R)` packs the six operations with the
carrier `image(ι, R.carrier)` as one record, so a statement reads the
transported operations as its fields, `transport_ring(ι, R).add` and so
on. The point is a ring whose members live in a type of one's choosing:
the free algebra hosts its polynomials in a type through an injection and
takes its operations from here.

Off the image the chosen preimage is an unspecified point, and nothing is
said of the operations there. On the image, along a map injective on the
carrier, the preimage of `ι(x)` is `x` itself, so a transported operation
at values of points is the value of the operation at them
(`TransportBinaryOpAtImage`, `TransportUnaryOpAtImage`). Every law of
`R` then transfers: `ι` keeps the six operations on the image
of `c`, and the image of a commutative ring along such a map is one
(`ring_homomorphism.ImageCommRingOn`). The laws are stated for a subring
`c ⊆ R.carrier`, read through the preimage chosen in the whole carrier:
the image of `c` is a commutative ring under the transported operations,
and `ι` is an isomorphism onto it. At `c = R.carrier` this is the
transported ring itself; a smaller `c` is the free algebra on a set of
variables inside the free algebra on every variable. Injectivity on the
whole carrier, not on `c` alone, is what the laws need, since the
preimage is chosen there. A subring is a subset of a record's carrier,
and the hypotheses read it as the record restricted to it:
`comm_ring_on(restrict_ring(R, c))`.

## The definitions

| member | statement |
|---|---|
| `TransportBinaryOpDef` | `transport_binary_op(ι, c, op, u, v) = ι(op(inverse_on(c, ι, u), inverse_on(c, ι, v)))` |
| `transportUnaryOpDef` | `transport_unary_op(ι, c, op, u) = ι(op(inverse_on(c, ι, u)))` |
| `TransportRingDef` | `transport_ring(ι, R)` = the transported sum, negation, product and difference on `R.carrier`, the zero `ι(R.zero)`, the one `ι(R.one)`, and the carrier `image(ι, R.carrier)` |
| `TransportBinaryOpAtImage` | `ι` injective on `c`, `x, y ∈ c` ⇒ `transport_binary_op(ι, c, op, ι(x), ι(y)) = ι(op(x, y))` |
| `TransportUnaryOpAtImage` | `ι` injective on `c`, `x ∈ c` ⇒ `transport_unary_op(ι, c, op, ι(x)) = ι(op(x))` |

## The transported ring

| member | statement |
|---|---|
| `TransportCommRingOn` | `ι` injective on `R.carrier`, `c ⊆ R.carrier` a commutative ring under `R`'s operations ⇒ `image(ι, c)` is a commutative ring under those of `transport_ring(ι, R)` |
| `TransportRingIsomorphism` | under the same hypotheses `ι` is a ring isomorphism from `c` onto `image(ι, c)` |

## The transported field

A field record goes along the same way: `transport_field(ι, F)` adds the
transported inverse and division to the ring operations, so its ring
projection is `transport_ring(ι, field_ring(F))`, and along a map
injective on the carrier it is a field. The algebraic closure brings a
field into its host type this way, and a quotient field back into its
coefficients' type (algebra/field/algebraic_closure).

| member | statement |
|---|---|
| `TransportFieldDef` | `transport_field(ι, F)` = the transported ring operations, inverse and division on `F.carrier`, with the carrier `image(ι, F.carrier)` |
| `TransportFieldOn` | `ι` injective on `F.carrier`, `F` a field ⇒ `field_on(transport_field(ι, F))` |
| `TransportFieldHomomorphism` | `ι` injective on `F.carrier`, `F` a field ⇒ `ι` is a ring homomorphism from `field_ring(F)` to `field_ring(transport_field(ι, F))` |

