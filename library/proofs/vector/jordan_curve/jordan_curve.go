// jordan_curve.go — the Jordan curve theorem, by Maehara's route through
// Brouwer's theorem: two paths crossing a rectangle, one from left to
// right and one from bottom to top, meet; the complement of an arc in the
// plane is path-connected; and the complement of a simple closed curve is
// two open path-connected sets, one of them bounded, each with the curve
// for its frontier.

package jordan_curve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/convex_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// RectangleCrossing — a path across a rectangle from its left side to its
// right side meets a path across it from its bottom to its top.
var RectangleCrossing = rectangleCrossingThm{family.Add(registry.ProofEntry{
	Name: "RectangleCrossing",
	Key:  "prop_49e0d0d521ef728c",
	Reading: "a > b or c > d makes the hypotheses unsatisfiable, at t = 0. At a " +
		"= b it is the intermediate value theorem for g's second coordinate. f(s) = " +
		"g(t) is an equality of whole sequences, path_in putting both values in ℝ².",
	Deps: []registry.EntryLike{
		convex_topology.BoxFixedPoint,
		convex_topology.CompactConvexFixedPoint,
		euclidean_topology.ContinuousIffCoordinates,
	},
	Build: family.Card(Statement{
		Binders: "∀a b c d:real. ∀f g:(real → num → real).",
		Hypotheses: []string{
			"path_in(euclidean_topology(2), f)",
			"path_in(euclidean_topology(2), g)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ a ≤ f(t)(0) ∧ f(t)(0) ≤ b ∧ c ≤ f(t)(1) ∧ f(t)(1) ≤ d",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ a ≤ g(t)(0) ∧ g(t)(0) ≤ b ∧ c ≤ g(t)(1) ∧ g(t)(1) ≤ d",
			"f(&0)(0) = a",
			"f(&1)(0) = b",
			"g(&0)(1) = c",
			"g(&1)(1) = d",
		},
		Conclusion: "∃s t:real. &0 ≤ s ∧ s ≤ &1 ∧ &0 ≤ t ∧ t ≤ &1 ∧ f(s) = g(t)",
	},
		"Maehara's lemma. If the paths never meet, N(s, t) = max(|f(s)₀ − g(t)₀|, |f(s)₁ − g(t)₁|) "+
			"is positive on the square, and F(s, t) = ((g(t)₀ − f(s)₀) / N(s, t), (f(s)₁ − g(t)₁) / "+
			"N(s, t)) carries the square ⟦−1, 1⟧² continuously into its own boundary; rescaled to the "+
			"square, it has a fixed point (CompactConvexFixedPoint), which lies on the boundary, and "+
			"checking the four sides with the four end conditions gives a sign that contradicts it"),
})}

// ArcComplementPathConnected — the complement of an arc in the plane is
// path-connected.
var ArcComplementPathConnected = arcComplementPathConnectedThm{family.Add(registry.ProofEntry{
	Name: "ArcComplementPathConnected",
	Key:  "prop_4e612da14892e23c",
	Reading: "The homeomorphism with ⟦0, 1⟧ is load-bearing: a circle " +
		"separates the plane (JordanCurve). s ⊆ ℝ² makes the subspace's points s.",
	Deps: []registry.EntryLike{
		convex_topology.CompactConvexFixedPoint,
		real_valued.Tietze,
		euclidean_topology.HeineBorel,
	},
	Build: family.Card(Statement{
		Binders: "∀s:set(num → real).",
		Hypotheses: []string{
			"s ⊆ {x:(num → real) | vec⟨2⟩(x)}",
			"homeomorphic(«I», subtopology(euclidean_topology(2), s))",
		},
		Conclusion: "path_connected_in(euclidean_topology(2), {x:(num → real) | vec⟨2⟩(x)} ∖ s)",
	},
		"the arc is compact, so the complement of a large disc D around it is path-connected and "+
			"every unbounded component of the complement contains it: there is one. There is no "+
			"bounded component U: with ρ a retraction of D onto the arc (Tietze, the arc being a copy "+
			"of ⟦0, 1⟧), the map that is ρ on U and the identity elsewhere is continuous, the "+
			"frontier of U lying in the arc, and misses a point z of U; followed by the projection "+
			"from z onto the boundary circle it retracts D onto that circle, and minus a retraction "+
			"of the disc onto its circle has no fixed point, against Brouwer (CompactConvexFixedPoint)"),
})}

// JordanCurve — the Jordan curve theorem: the complement of a simple closed
// curve in the plane is the union of two disjoint nonempty open
// path-connected sets, one of them bounded, each having the curve for its
// frontier.
var JordanCurve = jordanCurveThm{family.Add(registry.ProofEntry{
	Name: "JordanCurve",
	Key:  "prop_e679a39cb530727e",
	Reading: "c ⊆ ℝ² makes the subspace's points c; the homeomorphism with S¹ is " +
		"load-bearing. u is the inner region, which meets the boundedness clause; u " +
		"and v being open, each frontier is its closure less itself, which is c.",
	Deps: []registry.EntryLike{
		RectangleCrossing,
		ArcComplementPathConnected,
		topological_space.FrontierDef,
		euclidean_topology.HeineBorel,
	},
	Build: family.Card(Statement{
		Binders: "∀c:set(num → real).",
		Hypotheses: []string{
			"c ⊆ {x:(num → real) | vec⟨2⟩(x)}",
			"homeomorphic(euclidean_sphere_topology(1), subtopology(euclidean_topology(2), c))",
		},
		Conclusion: "∃u v:set(num → real). " +
			"    u ∈ euclidean_topology(2) ∧ " +
			"    v ∈ euclidean_topology(2) ∧ " +
			"    u ≠ ∅ ∧ " +
			"    v ≠ ∅ ∧ " +
			"    u ∩ v = ∅ ∧ " +
			"    u ∪ v = {x:(num → real) | vec⟨2⟩(x)} ∖ c ∧ " +
			"    path_connected_in(euclidean_topology(2), u) ∧ " +
			"    path_connected_in(euclidean_topology(2), v) ∧ " +
			"    (∃r:real. ∀x:(num → real). x ∈ u ⇒ ‖x‖_2 ≤ r) ∧ " +
			"    frontier(euclidean_topology(2), u) = c ∧ " +
			"    frontier(euclidean_topology(2), v) = c",
	},
		"Maehara's proof. The curve is compact, so one component of its complement is unbounded. Take "+
			"two points of the curve at the greatest horizontal distance and the rectangle they span; the "+
			"curve splits into two arcs joining them, and the vertical through the middle meets them; a "+
			"path from the top side to the bottom side crossing one arc only would cross the other by "+
			"RectangleCrossing, which finds a point of a bounded component. Every component has the curve "+
			"for its frontier, since a curve less an open arc is an arc, whose complement is path-connected "+
			"(ArcComplementPathConnected), and that also leaves room for one bounded component only"),
})}
