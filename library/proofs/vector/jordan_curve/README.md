# jordan_curve — the Jordan curve theorem in the plane, by Maehara's route through Brouwer's fixed point theorem

A simple closed curve in the plane is a subset of ℝ² homeomorphic to the
unit circle, as subspaces; an arc is one homeomorphic to the unit
interval. Both are stated through `homeomorphic` and no constant is
minted.

Maehara's proof reads Brouwer's theorem twice. First, two paths across a
rectangle, one from its left side to its right side and one from its
bottom to its top, meet: if they did not, the normalized difference of
their points would be a continuous map of the square into its own
boundary with no fixed point, the four end conditions forbidding one on
each side. Second, the complement of an arc has no bounded component: a
retraction of a large disc onto the arc, Tietze's extension of the
identity of the arc, would otherwise give a retraction of the disc onto
its boundary circle. With the complement of a large disc path-connected,
the complement of an arc is path-connected.

The Jordan curve theorem follows: the complement of the curve is the
union of two disjoint nonempty open path-connected sets, one of them
bounded, each with the curve for its frontier. The rectangle spanned by
two points of the curve at the greatest horizontal distance finds a
point of a bounded component; the arcs the curve splits into, whose
complements are connected, leave room for one bounded component only and
make every point of the curve a frontier point of both.

## The theorem (jordan_curve.go)

| member | statement |
|---|---|
| `RectangleCrossing` | paths f and g in the rectangle `⟦a, b⟧ × ⟦c, d⟧` of the plane with `f(&0)(0) = a`, `f(&1)(0) = b`, `g(&0)(1) = c`, `g(&1)(1) = d` meet: `∃s t. s, t ∈ ⟦0, 1⟧ ∧ f(s) = g(t)` — card |
| `ArcComplementPathConnected` | `s ⊆ {x \| vec⟨2⟩(x)} ∧ homeomorphic(«I», subtopology(euclidean_topology(2), s)) ⇒ path_connected_in(euclidean_topology(2), {x \| vec⟨2⟩(x)} ∖ s)` — card |
| `JordanCurve` | for `c ⊆ {x \| vec⟨2⟩(x)}` with `homeomorphic(euclidean_sphere_topology(1), subtopology(euclidean_topology(2), c))`: there are disjoint nonempty open path-connected u and v with `u ∪ v = {x \| vec⟨2⟩(x)} ∖ c`, u bounded, and `frontier(euclidean_topology(2), u) = c = frontier(euclidean_topology(2), v)` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
