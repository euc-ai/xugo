# bott_operator — the normal Bott operator on Hermite sequences and Schwartz forms

Hermite multi-indices and exterior masks form the fixed sequence host. Wedge with a coordinate and contraction determine the exterior signs; annihilation and creation shift the Hermite index with the weights √(2α) and √(2α+2). The graph norm has weight 1+2|α|+2p.

The physical operator is d+d*+x♭∧+ιₓ on Schwartz forms. The Hermite functions are real/hermite_function's; the Schwartz class is an algebra closed under the coordinates and the partial derivatives, it holds the Hermite functions, a Schwartz function with no Hermite coefficient is zero, and rapidly decreasing coefficients are the coefficients of a Schwartz function. Hermite synthesis and Parseval connect the physical operator to the sequence model. Its even-to-odd realization has one Gaussian kernel vector and no cokernel. Orthogonal changes of frame act on the exterior factor by the exterior power of the matrix (algebra/exterior_basis), an orthogonal matrix again, and on the full operator, both Hilbert norms and the graph domain, and fix that Gaussian vector.

## Members

| Member | Statement or role |
|---|---|
| `indicesDef` | Definition of `bott_indices` |
| `energyDef` | Definition of `bott_energy` |
| `shiftDef` | Definition of `bott_multi_shift` |
| `signDef` | Definition of `bott_exterior_sign` |
| `sequenceOperatorDef` | Definition of `bott_sequence_operator` |
| `moduleDef` | Definition of `bott_sequence_module` |
| `innerDef` | Definition of `bott_sequence_inner` |
| `groundDef` | Definition of `bott_ground_sequence` |
| `schwartzDef` | Definition of `bott_schwartz` |
| `schwartzFormDef` | Definition of `bott_schwartz_form` |
| `hermiteTransformDef` | Definition of `bott_hermite_transform` |
| `physicalDef` | Definition of `bott_physical_operator` |
| `rapidDef` | Definition of `bott_rapid_sequence` |
| `SequenceSquare` | The squared sequence Bott operator is the oscillator energy multiplier — card |
| `SequenceHilbert` | The parity sequence spaces and graph domain are Hilbert spaces — card |
| `GraphBounded` | The Bott shift is bounded from its graph domain to the target Hilbert space — card |
| `GaussianKernel` | The even Bott kernel is the Gaussian ground-state line — card |
| `NoOddCokernel` | The odd obstruction space vanishes — card |
| `BottFredholmIndex` | The even-to-odd Bott operator is Fredholm with index one — card |
| `HermiteCorrespondence` | Hermite coefficients identify Schwartz forms with rapidly decreasing sequences — card |
| `HermiteParseval` | The Hermite transform preserves the L2 inner product — card |
| `HermiteIntertwining` | The Hermite transform intertwines the physical and sequence Bott operators — card |
| `GaussianPoincare` | The Gaussian ground state has the stated oscillator spectral gap — card |
| `orthogonalDef` | Definition of `bott_orthogonal_matrix` |
| `rotationDef` | Definition of `bott_rotate_form` |
| `rotationOperatorDef` | Definition of `bott_rotation_operator` |
| `ExteriorOrthogonal` | The exterior power of an orthogonal matrix is orthogonal on the 2ⁿ masks — card |
| `OrthogonalCovariance` | The physical Bott operator commutes with orthogonal coordinate and exterior actions — card |
| `RotationIntertwining` | An orthogonal frame change acts by a bounded operator on Hermite sequences that intertwines the Hermite transform with the rotation of Schwartz forms — card |
| `OrthogonalDomain` | Orthogonal actions preserve the graph domain — card |
| `OrthogonalOperatorCommutes` | The descended Hilbert action commutes with the Bott operator — card |
| `GroundFrameIndependent` | Orthogonal changes of frame fix the Gaussian ground-state vector — card |

## The Schwartz class and the Hermite expansion (schwartz.go)

| Member | Statement or role |
|---|---|
| `SchwartzRapid` | A Schwartz function is continuous and decreases rapidly — card |
| `SchwartzAlgebra` | Sums, complex multiples and products of Schwartz functions are Schwartz — card |
| `SchwartzDerivativeCoordinate` | A coordinate times a Schwartz function, and its partial derivative along a coordinate below n, are Schwartz — card |
| `HermiteSchwartz` | The Hermite functions, zero off ℝⁿ, are Schwartz — card |
| `HermiteComplete` | A Schwartz function with every Hermite coefficient zero is zero — card |
| `HermiteSynthesis` | Rapidly decreasing coefficients are the Hermite coefficients of a Schwartz function — card |
