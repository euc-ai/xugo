# kernel_do_calculus — the three rules in kernel form and the back-door adjustment for continuous variables

On continuous values the point formulas of `causal/do_calculus` are
true and empty: every point has probability zero. What carries the
content there is the conditional distribution of the outcome given the
conditioning variables, a kernel, and a kernel is fixed only almost
everywhere. The chapter names the laws of node groups (`ScmMarginalDef`,
`ScmJointLawDef`) and a version of the conditional distribution of V_Y
given V_W (`ScmCondKernelDef`, a disintegration of their joint law),
and states the three rules as relations between versions.

Rule 1 compares conditional distributions of one interventional law, so
any version serves. Rules 2 and 3 compare two interventional laws, and a
version of one is free on the null sets of the other's conditioning
variable, which may carry the other's mass. So each is stated twice:
there is a common version (`KernelDoExchange`, `KernelDoDelete`), and
under absolute continuity of the second law's conditioning variable
with respect to the first's, every version is one
(`KernelDoExchangeVersion`, `KernelDoDeleteVersion`). Rule 3 reads the
two-point regime of `causal/intervention`. Rule 2 needs the
interventional values to vary with the observed ones, which two points
cannot give, and a two-point regime on a null point carries no
information: the randomized regime draws the intervened values z from a
law ρ beside the background sample and the coin, and solves the model
intervened at z on one face (`randomRegimeSolveDef`). With ρ the law of
V_Z the two faces have the same law on Z and are not singular; its root,
carrying (z, coin), is a regime node above Z, and the graph lemma of the
two-point regime reads it unchanged.

The back-door adjustment for continuous variables follows from the
kernel form of Rule 2: for almost every x, P_x(V_Y ∈ a) = ∫ K((x, z), a)
P^Z(dz), under an overlap condition saying that the product of the laws
of X and Z is absolutely continuous with respect to their joint law. The
formula holds for almost every x only, and it and the discrete
`BackdoorAdjustment`, which holds at every x under its support
condition, imply neither the other.

The conditional distributions need standard Borel state spaces where a
version is constructed or compared; other nodes are unrestricted.

| Member | Statement |
|---|---|
| `ScmMarginalDef` | `scm_marginal(M, K)`: the law of V_K on the configurations of K |
| `ScmJointLawDef` | `scm_joint_law(M, W, Y)`: the law of (V_W, V_Y) |
| `ScmCondKernelDef` | `scm_cond_kernel(M, W, Y, K)`: K disintegrates the law of (V_W, V_Y), a conditional distribution of V_Y given V_W |
| `randomRegimeSolveDef` | `random_regime_solve(M, Z, ((u, z), r))`: the solution of M intervened at z if r, of M otherwise |
| `RandomRegimeFaces` | the face F = ⊤ has the ρ-mixture of the interventional distributions, F = ⊥ that of M beside ρ — card |
| `RandomRegimeStructuralFamily` | the randomized regime is a structural family on the graph with a root above Z — card |
| `RandomRegimeExchangeIndependence` | separation with Z's out-edges deleted gives V'_Y ⊥ root \| V'_{Z ∪ W} — card |
| `KernelDoObserve` | Rule 1: a conditional distribution of V_Y given V_W is one given V_{Z ∪ W} — card |
| `KernelDoExchange` | Rule 2: a common version, given V_{Z ∪ W} under P_x and, at almost every z, given V_W under P_{x,z} — card |
| `KernelDoExchangeVersion` | Rule 2 under absolute continuity: every version under P_x is one — card |
| `KernelDoDelete` | Rule 3: a common version given V_W under P_x and P_{x,z} — card |
| `KernelDoDeleteVersion` | Rule 3 under absolute continuity: every version under P_x is one under P_{x,z} — card |
| `BackdoorAdjustmentKernel` | under the back-door criterion and overlap, P_x(V_Y ∈ a) = ∫ K((x, z), a) P^Z(dz) for almost every x — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
