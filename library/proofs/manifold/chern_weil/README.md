# chern_weil — projection connections and finite Chern–Todd forms

A connection on im P is P d plus a smooth projected matrix of one-forms. Its curvature is $F=P(dP\wedge dP)P+P(d\Gamma)P+\Gamma\wedge\Gamma$. Complex forms are pairs of real forms; matrix products use finite sums and the exterior product. The normalized curvature is $\Omega=-F/(2\pi i)$, and the real degree-$2k$ Chern-character component is $\operatorname{Re}\operatorname{tr}(\Omega^k)/k!$. The names `chern_form` and `chern_class` refer to these Chern-character components, not the elementary Chern classes.

Todd coefficients are defined by the formal identity $\operatorname{Td}(x)(1-e^{-x})/x=1$. Their formal logarithm determines a finite recurrence for each homogeneous Todd form. Only degrees at most the manifold dimension contribute; no analytic convergence is used. Theorems are cards, including independence of connections.

## Members

| Member | Statement or role |
|---|---|
| `realPartDef` | Definition of `complex_form_real` |
| `imaginaryPartDef` | Definition of `complex_form_imag` |
| `complexFormDef` | Definition of `complex_form_on` |
| `ComplexWedgeDef` | Definition of `complex_form_wedge` |
| `ComplexDerivativeDef` | Definition of `complex_form_derivative` |
| `MatrixFunctionDef` | Definition of `chern_matrix_function` |
| `matrixProductDef` | Definition of `chern_matrix_product` |
| `ConnectionDef` | Definition of `projection_connection` |
| `curvatureDef` | Definition of `projection_curvature` |
| `curvaturePowerDef` | Definition of `chern_curvature_power` |
| `ChernFormDef` | Definition of `chern_form` |
| `ChernClassDef` | Definition of `chern_class` |
| `ToddCoefficientsDef` | Definition of `todd_coefficient` |
| `toddLogarithmDef` | Definition of `todd_log_coefficient` |
| `ToddFormDef` | Definition of `todd_form` |
| `ToddClassDef` | Definition of `todd_class` |
| `ToddRecurrence` | The selected Todd form sequence satisfies its finite recurrence — card |
| `GrassmannConnection` | The Grassmann connection is the zero projected perturbation — card |
| `CurvatureForm` | The displayed connection curvature is a complex matrix of two-forms — card |
| `ChernClosed` | Each Chern-character component is a closed form of its specified degree — card |
| `ChernConnectionIndependent` | The Chern-character component is independent of the projected connection — card |
| `ToddClosed` | Each Todd component is a closed form of its specified degree — card |
| `ToddConnectionIndependent` | The Todd class is independent of the projected connection — card |
| `ToddSeries` | The Todd coefficient and logarithm choices satisfy their defining formal identities — card |
| `ChernIsomorphism` | Isomorphic smooth bundles have equal Chern-character components — card |
| `ChernDirectSum` | Chern-character components are additive under direct sum — card |
| `ToddDirectSum` | Todd classes are multiplicative under direct sum — card |
| `ChernNaturality` | Chern-character components commute with smooth pullback — card |
| `ToddNaturality` | Todd classes commute with smooth pullback — card |
| `ToddIsomorphism` | Isomorphic smooth bundles have equal Todd classes — card |
| `ToddTrivial` | The trivial projection has the unit as its Todd class — card |
| `ChernTensor` | The Chern character is multiplicative under tensor product in cohomology — card |
| `MatrixProductForm` | A product of matrices of complex p- and q-forms is a matrix of complex (p+q)-forms — card |
