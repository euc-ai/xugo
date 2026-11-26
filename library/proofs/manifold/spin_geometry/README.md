# spin_geometry — Spin lifts, spinor bundles and the lifted metric connection

A Spin atlas is a finite open cover with oriented real orthonormal tangent frames and smooth Clifford-valued lifts of their orthogonal transitions satisfying the cocycle identity. The metric is induced by the displayed Euclidean embedding. A spinor realization is a finite smooth projection with unitary local frames whose transitions are the explicit Spin representation.

Its connection is fixed by the local matrix one-form $-\frac14\sum_{a,b}\omega_{ab}c(e_a)c(e_b)$, where $\omega_{ab}=\langle F_a,dF_b\rangle$. This is the lift of the Levi–Civita connection, not an arbitrary Clifford-compatible connection. Exterior parity supplies the two graded projections. All existence and descent assertions remain cards.

## Members

| Member | Statement or role |
|---|---|
| `SpinAtlasDef` | Definition of `spin_atlas` |
| `spinorRealizationDef` | Definition of `spinor_realization` |
| `ParityDef` | Definition of `spinor_parity` |
| `localSpinConnectionDef` | Definition of `spin_local_connection` |
| `SpinConnectionDef` | Definition of `spinor_connection` |
| `FrameVectorDef` | Definition of `spin_frame_vector` |
| `SpinorBundleExists` | A compact Spin atlas admits a finite projection spinor realization — card |
| `GradedSpinorBundles` | The parity projections form smooth spinor bundles and split the total spinor bundle — card |
| `SpinConnectionExists` | The lifted metric connection exists in the projection realization — card |
| `FrameVector` | The selected tangent frame vectors invert the embedded orthonormal frame — card |
