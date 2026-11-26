# hedge_criterion — identifiability exactly when there is no hedge, and completeness of the do-calculus

On the positive class of `causal/identifiability`, the effect of X on Y
is identifiable at every value exactly when the latent projection of the
graph contains no hedge for the effect of X on Y (`HedgeCriterion`,
Shpitser and Pearl). The hedge is for X itself. Shpitser and Pearl's
corollary ranges over subsets X′ ⊆ X, and in the direction from a hedge
to non-identifiability that fails: with l latent, l → a, l → c and
a → c → y, the effect of {a, c} on y is P(y | c), though {a, c} hold a
hedge for the effect of a alone. A hedge for a part of Y is one for Y,
its roots being ancestors of Y. One direction is syntax and
soundness: without a hedge the lines of ID build a derivation to an
observational expression (`causal/id_derivation`), and a derived effect
is identifiable (`causal/do_semantics`). The other is a construction:
a hedge carries two positive models that agree on every observation and
differ under the intervention (`HedgeNotIdentifiable`). Together they
make the derivation relation complete for effects
(`DoDerivationComplete`), and IDC reduces a conditional effect to which
no exchange of observation for intervention applies to its joint effect
(`IdcReduction`).

Completeness needs room for the construction, and the hypotheses say how
much: an infinite sample type, to hold any finite number of independent
coins; an infinite state type, so that a latent node can carry several
bits; and observed carriers with at least two points. Identifiability is
relative to the sample type fixed by the statement, a formula of the
logic not quantifying over types; the soundness direction holds for any.

The construction goes in three steps. A network of dyadic conditional
probabilities on a finite DAG is the law of a model with independent
noise on fair coins, and its interventional laws are the truncated
factorization (`DyadicNetworkRealized`). A specification on the latent
projection, in which an observed node reads its parents in the
projection and fair bits shared by the nodes below a common latent
ancestor, is the observed law of such a network, the latent nodes
carrying what passes through them (`ProjectionKernelsRealized`); with
each observed carrier split into one point and the rest it is a sign
program, the mean of each node's sign given the classes of its parents
and the bits it reads (`latent_sign_program`), with the law of the
classes it induces (`latent_sign_law`, `SpinProgramRealized`). A hedge
then carries two sign programs with the same class law whose marginals
on Y differ under the intervention (`HedgeSpinProgramsExist`). Both are
forest programs (`c_forest_sign_mean`), well formed and bounded by 1/2
(`ForestSignProgram`), on the data the hedge gives (`HedgeForestData`),
and the class law of a forest program has a closed form, from which the two claims are read
(`ClassMarginalsParity`). The forest mean reads at a vertex only the
labels on the edges at it, the law over a set
of labels is the law over the labels the program reads, and the terms of
one track multiply, by the telescope, to the coefficients and the signed
factors of the roots and of the track. In each,
a node of its forest multiplies the fair signs of its bidirected edges,
and these average to zero unless every node of the forest takes part: observed, the two
programs carry one correlation among the roots; with a node of X held,
the larger forest loses it and the smaller keeps it. Routes carry the
correlation from the roots to Y; a bidirected edge
holds one fair bit for each set of vertices where a route re-enters
the larger forest. The three identities stand on a telescope along a
step map (`StepSignTelescope`) and on general laws of sums over the
subsets of a set and of products of binomials (`iterate/real/real_sum`,
`iterate/real/real_product`).

| Member | Statement |
|---|---|
| `HedgeNotIdentifiable` | a hedge for X and Y gives a value where the effect of X on Y is not identifiable — card |
| `HedgeCriterion` | the effect is identifiable at every legal value exactly when there is no hedge for X and Y — card |
| `DoDerivationComplete` | an identifiable effect derives to an observational expression — card |
| `signProgramDef` | `latent_sign_program(E, O, Λ, N, g)`: g gives the mean of each observed node's sign, local in the projection parents' classes and in the labels attached to the node, dyadic, each label's readers sharing a latent ancestor |
| `signLawDef` | `latent_sign_law(O, Λ, g, X, z)`: the probability of the class set z off X with X held, the average over the fair bits of the product of the factors (1 ± g)/2 |
| `forestSignMeanDef` | `c_forest_sign_mean(W, κ, α, F, R, U, Ed, τ)`: the sign program of a forest F with roots R — the route term W, and on F the sum over the tracks A ⊆ U of the edge spins, the signs stepping to the vertex, and W, κ or 1 |
| `DyadicNetworkRealized` | a network of dyadic conditional probabilities on a finite DAG is the law of a legal model with independent noise, its interventional laws the truncated factorization — card |
| `ProjectionKernelsRealized` | a dyadic specification on the latent projection, with fair bits shared below a common latent ancestor, is the observed law of a model on the graph under every intervention on observed nodes — card |
| `SpinProgramRealized` | a sign program on the projection is realized on finite carriers with a second point, over weights that do not depend on the program — card |
| `HedgeSpinProgramsExist` | a hedge carries two sign programs with equal class laws whose marginals on Y differ with X held |
| `ForestSignProgram` | a forest mean with local, dyadic, bounded data is a sign program bounded by 1/2 — card |
| `HedgeForestData` | a hedge of the projection gives F ⊆ O, connected bidirected edges inside F and inside F′, a step inside F from each vertex off F′, and routes from F′ to Y off X — card |
| `ClassMarginalsParity` | two functions on the class sets with the same marginals on Y have the same sum against the parity of T ⊆ Y — card |
| `StepSignTelescope` | along a step map the product over v of z(v) and the signs stepping to v is the product of z over the roots and the vertices left out — card |
| `IdcReduction` | with no exchange applicable, a conditional effect is identifiable exactly when its joint effect is — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.

## The files

`definitions.go` holds the vocabulary the construction is stated in:
the sign programs on a latent projection, their class laws and the
forest's sign mean. `edge_spins.go` is fair spins on the edges of a
connected graph: the edge set read as a connected graph, the exchange of
the vertex and edge products, the spin average, and its expansion over
one track and over several. `route_parity.go` is the parity sum of a
family of routes along a step map. `forest_program.go` is the class law
of a forest program in closed form, with what it stands on: the forest
mean's locality, the law over the labels a program reads and the
product along one track. `hedge_programs.go` is
the two sign programs of a hedge, with a product of signs being a sign.
`cards.go` holds the statements laid ahead of their proofs: the
criterion and the completeness of the derivation relation, the
realization of networks and programs, the step-sign telescope, the
forest program's well-formedness, the forest data of a hedge and the
parity of the class marginals. `family.go` is the manifest and the
chapter's table of names.
