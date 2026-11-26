// definitions.go — the open sets of ℝⁿ, the metric topology of the
// n-vectors under the distance; the unit cube; the unit sphere, as a set
// and as a space; and the closed unit ball.

package euclidean_topology

import (
	"github.com/euc-ai/xugo/library/registry"
)

// EuclideanTopologyDef — `euclidean_topology(n)`: the open sets of ℝⁿ,
// the metric topology of the n-vectors under the distance. It is the
// family of open sets itself, so "u is open" is `u ∈
// euclidean_topology(n)`, as it is on the line.
var EuclideanTopologyDef = euclideanTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanTopologyDef",
	Key:   "prop_46667987ea9057a2",
	Const: "euclidean_topology",
	Type:  "num → set(set(num → real))",
	Equations: []string{
		"∀n:num. euclidean_topology(n) = metric_topology({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩)",
	},
	// The mints of the metric topology, the comprehension, the n-vectors
	// and the distance.
})}

// UnitCubeDef — `unit_cube(n)`: the n-vectors whose coordinates lie in
// ⟦0, 1⟧.
var UnitCubeDef = unitCubeDefThm{family.Define(registry.DefEntry{
	Name:  "UnitCubeDef",
	Key:   "prop_8ddb69cfd9eb3085",
	Const: "unit_cube",
	Type:  "num → set(num → real)",
	Equations: []string{
		"∀n:num. unit_cube(n) = {u:(num → real) | vec⟨n⟩(u) ∧ ∀i:num. i < n ⇒ &0 ≤ u(i) ∧ u(i) ≤ &1}",
	},
})}

// EuclideanSphereDef — `euclidean_sphere(n)`: the unit sphere Sⁿ, the
// (n + 1)-vectors of norm 1. The index is the sphere's dimension, one
// below that of the space it sits in: S¹ is the circle in ℝ², S⁰ the two
// points ±1 of the line.
var EuclideanSphereDef = euclideanSphereDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanSphereDef",
	Key:   "prop_a04d4c258a9ae5c7",
	Const: "euclidean_sphere",
	Type:  "num → set(num → real)",
	Equations: []string{
		"∀n:num. euclidean_sphere(n) = {u:(num → real) | vec⟨n + 1⟩(u) ∧ vec_norm⟨n + 1⟩(u) = &1}",
	},
})}

// EuclideanSphereTopologyDef — `euclidean_sphere_topology(n)`: the unit
// sphere Sⁿ as a space, the subspace of ℝⁿ⁺¹ on euclidean_sphere(n).
var EuclideanSphereTopologyDef = euclideanSphereTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanSphereTopologyDef",
	Key:   "prop_63ff9438d4fdbb43",
	Const: "euclidean_sphere_topology",
	Type:  "num → set(set(num → real))",
	Equations: []string{
		"∀n:num. " +
			"    euclidean_sphere_topology(n) = subtopology(euclidean_topology(n + 1), euclidean_sphere(n))",
	},
	Deps: []registry.EntryLike{EuclideanTopologyDef, EuclideanSphereDef},
})}

// EuclideanBallDef — `euclidean_ball(n)`: the closed unit ball Dⁿ, the
// n-vectors of norm at most 1. Its boundary in ℝⁿ is the sphere of one
// dimension less, so D^(n + 1) is bounded by euclidean_sphere(n).
var EuclideanBallDef = euclideanBallDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanBallDef",
	Key:   "prop_e607db8d329aaaa4",
	Const: "euclidean_ball",
	Type:  "num → set(num → real)",
	Equations: []string{
		"∀n:num. euclidean_ball(n) = {u:(num → real) | vec⟨n⟩(u) ∧ vec_norm⟨n⟩(u) ≤ &1}",
	},
})}
