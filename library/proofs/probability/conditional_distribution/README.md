# conditional_distribution — disintegration of a probability on pairs and conditional distributions

A probability π on the product σ-algebra of W × V disintegrates along
its first coordinate through a kernel K when every measurable rectangle
b × a has the mass of K(·, a) integrated over b against the first
marginal of π (`IsDisintegrationDef`). For random variables Z and Y the
law of (Z, Y) is such a π, and K is a version of the conditional
distribution of Y given Z: the relation is stated once, on the joint
law, and every statement about random variables reads it there.

Two facts need the target to be standard Borel and are stated only
where they are used: a disintegration exists, and two of them agree as
measures at almost every point of the first marginal. Equivalently K
disintegrates π exactly when π is the join of its first marginal with
K. Conditional independence is one kernel serving two conditions: Y is
independent of X given Z exactly when the conditional distribution of Y
given Z, read as a kernel in (z, x) that ignores x, is one given (Z, X).

| Member | Statement |
|---|---|
| `IsDisintegrationDef` | `is_disintegration(W, U, V, T, π, K)`: π a probability on pairs, K a probability kernel, `π(b × a)` the integral of K(·, a) over b against π's first marginal |
| `DisintegrationExists` | a probability on pairs with a standard Borel second factor has a disintegration — card |
| `DisintegrationUnique` | two disintegrations agree as measures at almost every point, for a standard Borel target — card |
| `DisintegrationJoint` | K disintegrates π exactly when π is the join of its first marginal with K — card |
| `CondIndepDisintegration` | Y ⊥ X \| Z exactly when the conditional distribution of Y given Z serves as one given (Z, X) — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
