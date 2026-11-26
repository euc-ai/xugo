// fixed_point.go — Brouwer's fixed point theorem beyond the cube: on a
// box, carried from the cube by an affine homeomorphism; on a nonempty
// compact convex set, a retract of a box holding it; and on the closed
// unit ball, which is convex.

package convex_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/convex"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// BallConvex — the closed unit ball is convex.
var BallConvex = ballConvexThm{family.Add(registry.ProofEntry{
	Name:    "BallConvex",
	Key:     "prop_161bd2d8c39709f2",
	Reading: "Unconditional; at n = 0 the ball is {0}.",
	Deps: []registry.EntryLike{
		euclidean_topology.EuclideanBallDef,
		convex.ConvexDef,
		euclidean.NormTriangle,
		euclidean.NormSmul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num.",
		Conclusion: "convex(euclidean_ball(n))",
	},
		"‖c • x + d • y‖ ≤ c‖x‖ + d‖y‖ ≤ c + d = 1 for nonnegative weights "+
			"(NormTriangle, NormSmul), and an average of n-vectors is an n-vector"),
})}

// BoxFixedPoint — Brouwer's theorem on a box ⟦a, b⟧ⁿ.
var BoxFixedPoint = boxFixedPointThm{family.Add(registry.ProofEntry{
	Name: "BoxFixedPoint",
	Key:  "prop_21ebb5f9803787e5",
	Reading: "a ≤ b makes the box nonempty: with a > b and n ≥ 1 it is empty and the property fails, " +
		"there being no point to fix. At n = 0 the box is {0} for any a, b, and at a = b it is one point.",
	Deps: []registry.EntryLike{
		euclidean_topology.BrouwerCube,
		continuous.HomeomorphicFixedPoint,
		continuous.FixedPointPropertyDef,
		euclidean_topology.ContinuousIffCoordinates,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
		},
		Conclusion: "fixed_point_property(subtopology(euclidean_topology(n), " +
			"        {u:(num → real) | vec⟨n⟩(u) ∧ ∀i:num. i < n ⇒ a ≤ u(i) ∧ u(i) ≤ b}))",
	},
		"the cube has the property, BrouwerCube read as fixed_point_property; for a < b "+
			"the affine map λx. λi. COND(i < n, (x(i) − a)/(b − a), 0), with inverse λy. λi. "+
			"COND(i < n, a + (b − a) · y(i), 0) — the padding past n left at 0 — is a "+
			"homeomorphism of the box onto the cube (ContinuousIffCoordinates), and "+
			"HomeomorphicFixedPoint carries the property back; for a = b the box is one point"),
})}

// CompactConvexFixedPoint — Brouwer's theorem: a nonempty compact convex
// set of ℝⁿ has the fixed point property.
var CompactConvexFixedPoint = compactConvexFixedPointThm{family.Add(registry.ProofEntry{
	Name: "CompactConvexFixedPoint",
	Key:  "prop_573808c02b9f7e25",
	Reading: "Each hypothesis is load-bearing: the empty space lacks " +
		"the property, a rotation of the circle (not convex) has no fixed " +
		"point, and neither has a translation of ℝⁿ (not compact) for n ≥ 1.",
	Deps: []registry.EntryLike{
		BoxFixedPoint,
		ClosedConvexRetract,
		continuous.RetractFixedPoint,
		euclidean_topology.CompactIffClosedBounded,
		euclidean.ComponentLeNorm,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀k:set(num → real).",
		Hypotheses: []string{
			"compact_in(euclidean_topology(n), k)",
			"convex(k)",
			"k ≠ ∅",
		},
		Conclusion: "fixed_point_property(subtopology(euclidean_topology(n), k))",
	},
		"k is closed and bounded (CompactIffClosedBounded), so it lies in a box ⟦−B, "+
			"B⟧ⁿ (ComponentLeNorm); the retraction of ℝⁿ onto k (ClosedConvexRetract) "+
			"restricts to a retraction of the box onto k, and the property passes from "+
			"the box (BoxFixedPoint) to the retract (RetractFixedPoint)"),
})}

// BallFixedPoint — Brouwer's theorem on the closed unit ball.
var BallFixedPoint = ballFixedPointThm{family.Add(registry.ProofEntry{
	Name:    "BallFixedPoint",
	Key:     "prop_a940b61ff499b8c4",
	Reading: "Unconditional: the ball holds the zero vector at every n, and at n = 0 it is {0}.",
	Deps:    []registry.EntryLike{CompactConvexFixedPoint, BallConvex, euclidean_topology.BallCompact},
	Build: family.Card(Statement{
		Binders:    "∀n:num.",
		Conclusion: "fixed_point_property(subtopology(euclidean_topology(n), euclidean_ball(n)))",
	},
		"the ball is compact (BallCompact), convex (BallConvex) "+
			"and holds the zero vector; CompactConvexFixedPoint"),
})}
