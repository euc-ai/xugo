# intervention — interventions on structural causal models and the regime family

An intervention do(X = x) replaces the mechanism of each node of X by
the constant x(i) and deletes the edges into X; the noise and the
background stay (`DoDef`). The intervened model is a model of the same
record type, so every theorem about models applies to it, and the
interventional distribution is its distribution.

Rules that compare two interventional distributions need them in one
probability space. The regime family of a model and an intervention
do(Z = z) tosses a fair coin beside the background sample and solves
the model on one face and the intervened model on the other
(`RegimeSolveDef`); conditioned on the coin it has the two
distributions, and on the intervened face its Z-coordinates are z. The
regime is not a node of the model and takes no state; it appears only
in the graph, as the root `none` that `dag_add_root` adds above Z.

| Member | Statement |
|---|---|
| `DoDef` | `scm_do(M, X, x)`: the mechanisms on X replaced by the constants x(i), the edges into X deleted |
| `RegimeSolveDef` | `regime_solve(M, Z, z, p) = COND(snd(p), scm_solve(scm_do(M, Z, z), fst(p)), scm_solve(M, fst(p)))` |
| `DoLegal` | an intervention with values in the states keeps a model legal and its noise independent — card |
| `DoCompose` | `scm_do(scm_do(M, X, x), Z, z) = scm_do(M, X ∪ Z, override_on(Z, z, x))` — card |
| `DoEmpty` | `scm_do(M, ∅, x) = M` — card |
| `DoCoordinate` | an intervened node takes its assigned value — card |
| `DoNonDescendant` | a node descending from no point of X keeps its value at every sample — card |
| `InterventionConsistency` | where the solution already takes the values x on X, the intervened solution is the same — card |
| `InterventionConsistencyMeasure` | P(E ∩ {V_X = x}) ≤ P_x(E) for a measurable E, finite X and measurable singletons — card |
| `DoSolveJointMeasurable` | the intervened solution is jointly measurable in the sample and the intervened values — card |
| `RegimeFaces` | on the face F = ⊤ the regime variables have half the intervened distribution, on F = ⊥ half M's — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
