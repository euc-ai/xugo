# polynomial_system_descent — polynomial systems and prime ideals of forms carried along algebraically closed embeddings

A system of r equations and s inequations in n variables has a solution over F exactly when its image under an embedding of algebraically closed fields has one over G. Solution descent is proved by elementarity in the embedding mode, through `algebraically_closed_field_transfer.EmbeddingElementary`; `SolutionDescent`'s comment says how the two systems become one formula. The same step carries primality: an algebraically closed field is infinite (finite_field.ClosedFieldInfinite), so the ideal finitely many forms generate is prime exactly when degree-bounded pointwise conditions hold (homogeneous_polynomial.FormIdealPrimeCriterion), and those conditions cross along the embedding, so the ideal is prime over F exactly when the ideal of the carried forms is prime over G.

| Member | Statement |
|---|---|
| `PolynomialSystemDef` | A tuple satisfying a finite list of equations and a finite list of inequations. |
| `SolutionDescent` | Finite polynomial systems with inequations descend along algebraically closed embeddings. |
| `FormIdealPrimeDescent` | Along an embedding of algebraically closed fields, the ideal finitely many forms generate is prime exactly when the ideal of their carried forms is. |
