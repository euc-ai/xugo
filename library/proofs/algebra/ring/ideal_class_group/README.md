# ideal_class_group — invertible fractional ideals modulo principal scaling

Invertible fractional ideals form an abelian group before any factorization hypothesis is imposed. Principal fractional ideals form its subgroup, class equality is scalar rescaling, and a fraction-field denominator gives integral representatives.

## Members

| Member | Statement |
|---|---|
| `InvertibleIdealsDef` | `invertible_ideals(R, S) = {I \| invertible_fractional(R, S, I)}`: the invertible fractional ideals of S |
| `PrincipalFractionalIdealsDef` | `principal_fractional_ideals(R, S) = {image(R.mul(a), S) \| a ∈ R.carrier ∧ a ≠ R.zero}`: the principal fractional ideals aS of the nonzero a |
| `IdealClassDef` | `ideal_class(R, S, I) = left_coset(fractional_mul(R, S), I, principal_fractional_ideals(R, S))`: the class I·P of I |
| `IdealClassesDef` | `ideal_classes(R, S) = left_cosets(fractional_mul(R, S), invertible_ideals(R, S), principal_fractional_ideals(R, S))`: the invertible ideals modulo the principal ones |
| `InvertibleIdealsAbelianGroup` | invertible fractional ideals form an abelian group under fractional multiplication |
| `PrincipalIdealsSubgroup` | `a ↦ a · S` is a homomorphism from the nonzero scalars of L to the invertible fractional ideals, and its image, the principal fractional ideals, is a subgroup |
| `IdealClassEqIffScale` | invertible ideals have equal classes exactly when they differ by a nonzero scalar multiple |
| `InvertibleIdealClassGroupAbelian` | invertible ideal classes form an abelian group under coset multiplication |
| `IdealClassMul` | the class of a product of invertible ideals is the product of their classes |
| `IntegralClassRepresentative` | when L is the field of fractions of S, every ideal class has a nonzero integral invertible representative |
