# number_field — fields of characteristic zero, finite over their rational images

A number field is finite over the rational image in its carrier. The definition does not assume an integral basis. Its two scalar rings are stated once, for every later chapter to start from: characteristic zero makes the rational image a subfield and the integer image a principal ideal domain inside it, and the field is a module over each; finite-dimensional field arithmetic over them provides the trace, lattice and integer-ring constructions. A statement over a number field L names the two scalar rings «ℤ» = `restrict_ring(field_ring(L), integer_image(field_ring(L)))` and «ℚ» = `restrict_ring(field_ring(L), rational_image(L))`; the images themselves, as sets, are written out.

## Members

| Member | Statement |
|---|---|
| `NumberFieldDef` | `number_field`: field_ops(A) → bool |
| `NumberFieldScalars` | A number field has characteristic zero; its rational image is a subfield, its integer image is a principal ideal domain inside the rational image, and the field is a module over each |
