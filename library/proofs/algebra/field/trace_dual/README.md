# trace_dual — trace pairings, lattice duals and codifferents

The trace dual is the functional dual at the field trace (algebra/field/functional_dual): stability and localization are that chapter's theorems at this instance. The same trace_dual constant is used for arbitrary test lattices and value modules. Nondegeneracy enters duality and basis statements, while linearity suffices for localization. A common basis produces a bounded codifferent before ideal arithmetic proves its invertibility; a monogenic formula requires an actual monogenic integral basis.

`free_lattice.go` proves the free-lattice theorem in sections: the trace-dual basis, the trace dual of an S-span, and the two coefficient readings that make each S-span the trace dual of the other's generators. `codifferent.go` treats codifferents using additional hypotheses on ideals.

## Members

| Member | Statement |
|---|---|
| `TraceDualIsFunctionalDual` | The trace dual is the functional dual at the field trace; both definitions unfold to one set |
| `TraceDualSubmodule` | The trace dual of an S-submodule of K against a subring B is a B-submodule of L: the functional dual of the K-linear trace |
| `TraceDualMonotone` | A smaller test set imposes fewer conditions, and a larger target permits more trace values — card |
| `TraceDualHomIso` | For a finite set E that is an S-basis of B and a K-basis of L, with nondegenerate trace pairing, and an S-submodule N of K: z ↦ (b ↦ tr(zb)), zero off B, is a B-module isomorphism from the trace dual of B into N onto the coextension of scalars of N from S to B — card |
| `TraceDualValueInvertible` | For an invertible fractional ideal N of S in K, the trace dual of B with values in N is the product of N with the trace dual of B with values in S — card |
| `TraceDualTestIdealInvertible` | For an invertible fractional ideal I of B and an S-submodule N of K, the trace dual of I with values in N is I⁻¹ times the trace dual of B with values in N — card |
| `TraceDualFreeLattice` | A finite K-basis with nondegenerate trace pairing has a trace-dual K-basis, which is an S-basis of the trace dual of the S-span; taking the trace dual twice recovers the original S-span |
| `MonogenicCodifferent` | When L = K(y) with y separable and its minimal polynomial μ has coefficients in S, the trace dual of S[y] with values in S is μ′(y)⁻¹·S[y], and its fractional inverse over S[y] is μ′(y)·S[y] — card |
| `TraceDualLocalizes` | Inverting s commutes with the trace dual: each span is a saturation at s, N saturates alike in K and in L, and the functional dual commutes with saturation |
| `CodifferentBoundedFractionalIdeal` | For a finite set E that is an S-basis of B and a K-basis of L, with nondegenerate trace pairing, K the fractions of S and L the fractions of B: the trace dual of B with values in S is a bounded fractional ideal of B, contains B, and has a finite S-basis — card |
| `CodifferentInvertible` | Under those hypotheses, if every nonzero ideal of B is invertible, the trace dual of B with values in S is invertible and its inverse is a nonzero ideal of B — card |
| `TraceDualDef` | The elements pairing into a specified value module under the field trace. |
