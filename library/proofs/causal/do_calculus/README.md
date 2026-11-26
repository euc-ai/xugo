# do_calculus — the three rules of the do-calculus

The three rules are first statements of conditional independence,
stated for a model with independent noise and pairwise disjoint node
groups Y, Z and W, without a further intervention group. Rule 1
(observation) reads the global Markov property of the model. Rule 2
(exchange of intervention and observation) and Rule 3 (deletion of an
intervention) are conditional independences on the regime family of
do(Z = z), whose graph conditions two graph lemmas of
`relations/graph/d_separation` turn into separation from the regime
root. Pearl's form with an intervention group X is the same three rules
read on the intervened model, its graph and the condition X ∪ W.

From each independence a point formula follows, cross-multiplied so
that it holds without support conditions: a null factor makes both
sides zero. Only the conditioning coordinates are read at a point, and
they need measurable singletons there; the outcome is any event of the
Y-coordinates, so a continuous outcome is covered, and no state space
need be finite or countable. The ratio forms follow under positive
denominators.

| Member | Statement |
|---|---|
| `RegimeExchangeIndependence` | separation of Y from Z given W with Z's out-edges deleted gives V'_Y ⊥ F \| V'_{Z ∪ W} on the regime family — card |
| `RegimeDeleteIndependence` | separation of Y from Z given W with the in-edges of Z ∖ An(W) deleted gives V'_Y ⊥ F \| V'_W — card |
| `DoObserve` | Rule 1: P_x(E, F, w) P_x(w) = P_x(E, w) P_x(F, w), E an event of Y's coordinates and F of Z's — card |
| `DoExchange` | Rule 2: P_{x,z}(E, w) P_x(z, w) = P_x(E, z, w) P_{x,z}(w) — card |
| `DoDelete` | Rule 3: P_{x,z}(E, w) P_x(w) = P_x(E, w) P_{x,z}(w), Z needing only legal values — card |
| `DoObserveRatio` | P_x(E \| z, w) = P_x(E \| w) where P_x(z, w) > 0 — card |
| `DoExchangeRatio` | P_{x,z}(E \| w) = P_x(E \| z, w) where both denominators are positive — card |
| `DoDeleteRatio` | P_{x,z}(E \| w) = P_x(E \| w) where both denominators are positive — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
