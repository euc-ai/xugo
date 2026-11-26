# discriminant — trace Gram determinants and integer-lattice indices

The discriminant is a signed integer determinant. Change of integral basis multiplies it by the square of the change-of-basis determinant; absolute values enter the lattice-index and different-norm formulas, not the definition itself.

## Members

| Member | Statement |
|---|---|
| `DiscriminantDef` | `basis_discriminant`: field_ops(A) → num → (num → A) → A |
| `IntegerFieldDiscriminantDef` | The choice is specified by the basis-independence theorem; no independence or existence is built into number-field data |
| `DiscriminantBasisChange` | Bilinearity gives Gram(f)=Uᵀ Gram(e) U — card |
| `DiscriminantNonzero` | A vector annihilated by the Gram matrix pairs to zero with a rational basis and hence with the entire field — card |
| `IntegralBasisDiscriminantIndependent` | Traces of products of integers give integral Gram entries — card |
| `DiscriminantIndexSquare` | Compare the sublattice basis with an integral basis of the integer ring — card |
| `GaussMonicFactor` | Clear integer denominators and separate contents of the two factors — card |
| `IntegralMinimalPolynomialCoefficients` | An integral monic relation is divisible by the rational minimal polynomial with a monic rational quotient; apply GaussMonicFactor — card |
