# characteristic_zero — integer and rational images in characteristic zero

The native integers map into a commutative ring by repeated addition of one. In characteristic zero, the map is injective and restriction to native integer scalars preserves submodules, spans, bases and finite generation. In a field of characteristic zero, the rational image is the fraction field of the integer image.

The ring predicate `characteristic_zero` is defined by `comm_ring.CharacteristicZeroDef`: no positive natural multiple of one vanishes.

## The definitions

| Member | Statement |
|---|---|
| `IntegerMapDef` | `integer_map`: ring_ops(A) → int → A |
| `IntegerImageDef` | `integer_image`: ring_ops(A) → set(A) |
| `rationalMapDef` | `rational_map`: field_ops(A) → real → A |
| `RationalImageDef` | `rational_image`: field_ops(A) → set(A) |
| `RationalValueDef` | Inverse to the rational embedding only on its image; no assertion about arbitrary host elements |
| `IntegerValueDef` | `integer_value`: ring_ops(A) → A → int |

## The integer map and the integer image

| Member | Statement |
|---|---|
| `IntegerMapOfNum`, `IntegerMapNegOfNum` | Nonnegative and negative integers map to the corresponding signed additive powers of one. |
| `IntegerMapInCarrier` | Every integer maps into the ring's carrier. |
| `IntegerMapHom` | The integer map preserves the ring operations and is the unique additive map taking one to one. |
| `IntegerImageCommRing` | The integer image is a commutative subring. |
| `IntegerMapIntoImage` | The integer map is a ring homomorphism from the integer ring into the integer image. |
| `IntegerMapHomomorphism` | The integer map is a ring homomorphism from the integers into any commutative ring. |
| `IntegerMapSum` | The integer map carries an integer sum over a finite set to the ring's sum of the images. |
| `IntegerMapPow` | The integers' map into a ring takes a ^ n to the n-th power of the image of a. |
| `IntegerValueRightInverse` | On the integer image, the integer map undoes `integer_value`. |
| `IntegerMapPositiveNonzero` | In characteristic zero, a positive natural number maps to a nonzero element. |
| `IntegerMapInjective` | In characteristic zero, distinct integers have distinct images. |
| `IntegerValueLeftInverse` | In characteristic zero, `integer_value` undoes the integer map. |
| `IntegerRingRegularModule` | The integer ring is a module over itself. |

That every native integer lies in the carrier of the integer ring is stated beside the definition of `int_ring`, as `int_real_lift.IntegerRingCarrierUniversal`, and that every additive subgroup of the integers has a unique nonnegative generator is the division algorithm's first consequence, `int_div_rem.IntegerSubgroupPrincipal`. `IntegerRingRegularModule` is stated here because it reads the module chapter, which `int_real_lift` does not import. The principal ideal domain instance is `int_lattice.IntegerRingPrincipalIdealDomain`.

## The rational map and the rational image

| Member | Statement |
|---|---|
| `RationalIntegerFraction` | Every rational is a native integer divided by a positive natural. |
| `RationalMapFraction` | The rational map sends an integer fraction with positive natural denominator to the corresponding fraction in the field. |
| `RationalEmbedding` | The rational map embeds the rationals as a subfield, agrees with the integer map, and has an inverse on its image. |
| `RationalValueRational` | In characteristic zero, `rational_value` takes a point of the rational image to a rational number. |
| `RationalValueAddMul` | In characteristic zero, `rational_value` keeps sums and products of points of the rational image. |
| `RationalValueZeroOneNegOne` | In characteristic zero, `rational_value` takes the field's zero, one and minus one to 0, 1 and -1. |
| `RationalCommonDenominator` | A finite set of rationals has a common positive integer denominator. |
| `FiniteRationalDenominator` | In a field of characteristic zero, one positive integer scales every element of a finite set of rational elements into the integer image. |
| `IntegerWeightedSumBound` | An integer weighted sum is bounded by the uniform coefficient bound times the sum of absolute weights |

## Integer scalars and separability

The integer scalar consequences are stated in `principal_ideal_domain`:
`IntegerScalarRestriction` preserves submodules, spans, bases and finite
generation along the integer map; `IntegerRationalImagesStructure` identifies
the integer image as a principal ideal domain with the rational image as its
fraction field; and `IntegerRationalImageModules` gives the ambient field its
modules over both images.

`separable_polynomial.CharZeroIrreducibleSeparable` states that irreducible
polynomials over characteristic-zero subfields are separable.
