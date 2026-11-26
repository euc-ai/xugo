# identifiability — identifiability over a model class

A query is identifiable over a class of models when two models of the
class with the same observational distribution give it the same value
(`IdentifiableDef`). The observed nodes O enter here and only here; the
observational distribution is compared through the masses of the
observed configurations, which determine it when the observed state
carriers are finite. The class is fixed by its graph, its observed
nodes and their state carriers, independent noise and a support
condition on the observational distribution; latent state carriers are
free, so two models of the class may have different latent spaces, and
different mechanisms, noise and background laws. The first class is
the positive one: finite observed carriers with all subsets measurable,
and every observed configuration of positive probability
(`PositiveScmDef`); positivity passes to interventional distributions
through consistency, so every interventional conditional probability on
observed nodes has a positive denominator there.

The sample type is fixed: a formula of the logic cannot quantify over
types, so identifiability is relative to one background type. A query
read as a functional of the observational distribution is identifiable,
which is how the adjustment formulas give identification results. The
bow graph U → X, U → Y, X → Y with U latent carries two models that
agree on every observation and differ under do(X = 0): the effect is
not identifiable there, though the observational law is strictly
positive.

| Member | Statement |
|---|---|
| `PositiveScmDef` | `positive_scm(V, E, O, D, M)`: legal with independent noise on the graph (V, E); finite observed carriers D(i) with all subsets measurable; every observed configuration of positive mass |
| `IdentifiableDef` | `scm_identifiable(C, O, Q)`: models of C with equal masses on the observed configurations give Q the same value |
| `BowNodeData` | the vertices `bow_u`, `bow_x`, `bow_y` of the bow graph |
| `BowModelDef` | `bow_model(c)`: X copies U, Y is its noise where X = U and c elsewhere, on two fair coins |
| `FdNodeData` | the vertices `fd_u`, `fd_x`, `fd_z`, `fd_y` of the front-door graph |
| `IdentifiedByFunctional` | a query that is a functional of the observed masses on the class is identifiable — card |
| `PositiveInterventional` | in the positive class every interventional probability of an observed configuration is positive — card |
| `ObservedMarginal` | the probability of a partial observed configuration is the sum of its completions' masses — card |
| `BackdoorIdentifiable` | under the back-door criterion the effect of X on Y is identifiable on the positive class — card |
| `FrontdoorIdentifiable` | under the front-door criterion the effect of X on Y is identifiable on the positive class — card |
| `FrontdoorExample` | the graph U → X, U → Y, X → Z → Y meets the front-door criterion — card |
| `FrontdoorExampleIdentifiable` | on the front-door graph with U latent the effect of X on Y is identifiable on the positive class — card |
| `BowNotIdentifiable` | the two bow models agree on every observation and give P(Y = ⊤ \| do(X = ⊥)) = 1/4 and 3/4: not identifiable — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
