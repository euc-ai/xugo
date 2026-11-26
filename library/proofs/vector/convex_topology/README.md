# convex_topology — convex sets of ℝⁿ as spaces: contractible, retracts of ℝⁿ by the nearest point, and Brouwer's fixed point theorem on compact convex sets and the ball

A coordinatewise open box of ℝⁿ is convex, the empty box among them. A
nonempty convex set of ℝⁿ contracts to any of its points along
straight lines. A nonempty closed set holds a point nearest to any
vector, the distance attaining its least value on a compact piece of the
set; in a convex set the nearest point y to x is characterized by every
point z of the set making an angle of at least a right angle with x at
y, ⟪x − y, z − y⟫ ≤ 0, and from that inequality at two vectors, nearest
points lie no farther apart than the vectors do. So the nearest point is
unique and continuous in the vector, and a nonempty closed convex set is
a retract of ℝⁿ.

Brouwer's theorem on the cube is euclidean_topology's, through Kuhn's
lemma. A box ⟦a, b⟧ⁿ is the cube under an affine homeomorphism, or a
point, and the fixed point property is topological; a nonempty compact
convex set lies in a box, and is a retract of it by the nearest point,
and the property passes to a retract (topology/continuous). So every
nonempty compact convex set of ℝⁿ has the fixed point property, the
closed unit ball among them.

No constant is minted: the nearest point is stated by its property, and
the retraction is `continuous`'s `retract_of`.

## Contraction and the nearest point (nearest_point.go)

| member | statement |
|---|---|
| `OpenBoxConvex` | `convex(euclidean_open_box⟨n⟩(a, b))` — card |
| `ConvexContractible` | `convex(k) ∧ k ≠ ∅ ∧ k ⊆ {u \| vec⟨n⟩(u)} ⇒ contractible_space(subtopology(euclidean_topology(n), k))` |
| `NearestPointExists` | `closed_in(euclidean_topology(n), k) ∧ k ≠ ∅ ∧ vec⟨n⟩(x) ⇒ ∃y. y ∈ k ∧ ∀z. z ∈ k ⇒ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, z)` |
| `NearestPointVariational` | for k convex and y ∈ k: `(∀z. z ∈ k ⇒ dist⟨n⟩(x, y) ≤ dist⟨n⟩(x, z)) ⇔ ∀z. z ∈ k ⇒ ⟪x - y, z - y⟫_n ≤ &0` |
| `NearestPointNonexpansive` | for k convex in ℝⁿ, y nearest in k to x and y' to x': `dist⟨n⟩(y, y') ≤ dist⟨n⟩(x, x')` — card |
| `ClosedConvexRetract` | `closed_in(euclidean_topology(n), k) ∧ convex(k) ∧ k ≠ ∅ ⇒ retract_of(euclidean_topology(n), k)` — card |

## Brouwer's fixed point theorem (fixed_point.go)

| member | statement |
|---|---|
| `BallConvex` | `convex(euclidean_ball(n))` — card |
| `BoxFixedPoint` | `a ≤ b ⇒ fixed_point_property(subtopology(euclidean_topology(n), {u \| vec⟨n⟩(u) ∧ ∀i. i < n ⇒ a ≤ u(i) ∧ u(i) ≤ b}))` — card |
| `CompactConvexFixedPoint` | `compact_in(euclidean_topology(n), k) ∧ convex(k) ∧ k ≠ ∅ ⇒ fixed_point_property(subtopology(euclidean_topology(n), k))` — card |
| `BallFixedPoint` | `fixed_point_property(subtopology(euclidean_topology(n), euclidean_ball(n)))` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
