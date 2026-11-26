# id_derivation — the lines of the ID algorithm as derivations

The identification algorithm ID of Shpitser and Pearl runs in the
engine; this chapter holds what each of its lines proves, stated for
every graph as a lemma about `do_derivable`, so that a run on a
concrete graph is assembled from these lemmas and checked by the
kernel. The lines read the latent projection of the full DAG onto the
observed nodes — its ancestors and its districts — while the
derivation rules read separations in the full DAG.

ID's recursion enters two kinds of subproblem, and a derivation of each
transfers back. The second line restricts to the ancestors of Y, latent
ones included: a derivation in the restriction to a parent-closed set is
one in the graph (`DerivableAncestralTransfer`). The fourth and seventh
lines remove a set D of observed nodes, keeping the latent ones: a
derivation in G[V ∖ D] is one in G with D added to every atom's
intervention group (`DerivableInterveneTransfer`, with the operation
`do_expr_intervene`). Removing D, not deleting its in-edges, is what the
subproblem's graph must do: a node of D left with its out-edges would act
as a common cause the subproblem does not observe.

A district S of the whole projection is identified by Tian's formula
Q[S] = P_{O ∖ S}(S) = Π_{v_i ∈ S} P(v_i | v_π^{(i−1)}) along a
topological list of the observed nodes (`DistrictDerivable`, the product
`do_chain`), every conditional of Q[S] is then observational
(`DistrictAtomDerivable`), and the joint law is the product of the Q[S]
over the districts (`DistrictFactorization`, the list product
`do_prod`). The six line lemmas follow, with IDC's two for a conditional
query, and the inductive theorem that without a hedge every effect
derives to an observational expression. That theorem's semantic
reading — identification, and the converse, completeness — is
`causal/hedge_criterion`; this chapter reads only the syntax and the
graph chapters.

| Member | Statement |
|---|---|
| `TopologicalListDef` | `dag_topological_list(E, O, l)`: l lists O once each, no node an ancestor of one before it |
| `interveneDef` | `do_expr_intervene(D, e)`: D added to the intervention group of every atom of e |
| `prodDef` | `do_prod(l)`: the product of a list of expressions, 1 for the empty list |
| `chainDef` | `do_chain(S, l)`: along l latest first, the product over v ∈ S of P(v \| the nodes after v in l) |
| `TopologicalListExists` | the observed nodes of a DAG have a topological list — card |
| `DerivableAncestralTransfer` | a derivation in the restriction to a parent-closed set is one in the graph — card |
| `DerivableInterveneTransfer` | a derivation in G[V ∖ D] is one in G with D intervened in every atom — card |
| `DistrictDerivable` | for a district S of the projection, P_{O ∖ S}(S) derives to the chain of S — card |
| `DistrictFactorization` | the joint law derives to the product of Q[S] over the districts — card |
| `DistrictAtomDerivable` | every conditional of Q[S] derives to a quotient of sums of the chain — card |
| `IdLineOne` | line 1: `do_prob(Y, ∅, ∅)` derives to Σ_{O ∖ Y} P(O) — card |
| `IdLineAncestors` | line 2: a derivation on the ancestors of Y gives one for the query — card |
| `IdLineIntervene` | line 3: intervening on the non-ancestors of Y adds nothing — card |
| `IdLineDistricts` | line 4: P_x(y) derives to Σ_{O ∖ (X ∪ Y)} Π_S over the districts of O ∖ X — card |
| `IdLineDistrict` | line 6: when O ∖ X is a district of the whole projection, P_x(y) derives to Σ of its chain — card |
| `IdLineSubDistrict` | line 7: a derivation in the subgraph of a district S ⊇ O ∖ X gives one with O ∖ S intervened — card |
| `IdcLineExchange` | IDC line 1: an observed z with no back door to Y becomes an intervention — card |
| `IdcLineCondition` | IDC line 2: P_x(y \| w) derives to e / Σ_Y e for e a derivation of P_x(y, w) — card |
| `NoHedgeDerivable` | without a hedge for X and Y, the effect derives to an observational expression — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
