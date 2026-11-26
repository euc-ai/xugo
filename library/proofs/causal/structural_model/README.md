# structural_model — structural causal models on general measurable carriers

A structural causal model is one record, `scm_model(A, B, I)`:
samples of type A, states in the host type B, nodes of type I. It packs
a background probability space; a finite DAG on the nodes; for each node
a state carrier and σ-algebra, with a fixed value off the nodes; for
each node a noise σ-algebra on the samples; and for each node a
mechanism, which maps a configuration of the node's parents and a
sample to a state (`ScmData`). The structural equation of a node reads
its parents through the restriction of the configuration to them
(`EquationsDef`), so locality is written into the equation and is not a
condition to verify. A model is legal when its graph is a DAG, its
background a probability space and each mechanism measurable for the
product of its parents' product σ-algebra with its noise (`ScmOn`).
Every node carries its own noise, a common cause is a node, and which
nodes are observed is not model data: it is a parameter of
identifiability.

The solution is chosen from the equations (`SolveDef`); that the
equations have exactly one solution, that it is measurable and that its
distribution — the background probability pushed forward along it
(`DistributionDef`) — is a probability are the chapter's theorems.
Solution and distribution are defined for any joint background law; the
class of models whose graph carries their semantics adds that the noise
σ-algebras are independent (`NoiseIndependentDef`). Such models exist:
one built on finitely many fair coins, each node owning a block of them
and reading the sample through it alone, is legal and has independent
noise (`CoinModelLegal`).

| Member | Statement |
|---|---|
| `ScmData` | the record `mk_scm(sample, events, prob, nodes, edges, states, state_sigma, default, noise, mech)` |
| `ScmOn` | `scm_on(M)`: DAG, probability space, state σ-algebras, noise sub-σ-algebras, measurable mechanisms |
| `NoiseIndependentDef` | `scm_noise_independent(M) ⇔ independent_sigma_family(M.sample, M.events, M.prob, M.nodes, M.noise)` |
| `EquationsDef` | `scm_equations(M, u, v)`: v(i) = M.mech(i, override_on(dag_parents(M.edges, i), v, M.default), u) on the nodes, M.default off them |
| `SolveDef` | `scm_solve(M, u) = εv. scm_equations(M, u, v)` |
| `DistributionDef` | `scm_distribution(M) = pushforward_measure(M.sample, M.prob, scm_solve(M))` |
| `SigmaDef` | `scm_sigma(M, K) = coordinate_sigma(M.sample, scm_solve(M), M.state_sigma, K)` |
| `ScmSolution` | on a DAG the structural equations have exactly one solution at every sample — card |
| `ScmSolutionStates` | at a background sample the solution of a legal model lies in the configurations — card |
| `ScmSolutionMeasurable` | the solution of a legal model is measurable into the configurations' product σ-algebra — card |
| `ScmDistributionProbability` | the distribution of a legal model is a probability on the configurations — card |
| `CoinModelLegal` | a model on finitely many fair coins — uniform law, finite discrete carriers, each node's noise and mechanism reading its own block of coins — is legal with independent noise — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
