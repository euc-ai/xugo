// disc.go — what π₁(S¹) ≅ ℤ says about the disc and the sphere: the
// circle is not a retract of the disc it bounds; a map of the circle to
// itself that commutes with x ↦ −x is not homotopic to a constant; and so
// a continuous map of the 2-sphere to the plane sends some pair of
// antipodal points to one point (Borsuk–Ulam).

package circle

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/covering_space"
	"github.com/euc-ai/xugo/library/proofs/topology/fundamental_group"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/proofs/vector/convex_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// NoRetractionDisc — the circle is not a retract of the closed disc.
var NoRetractionDisc = noRetractionDiscThm{family.Add(registry.ProofEntry{
	Name: "NoRetractionDisc",
	Key:  "prop_d48ea7cd34b84152",
	Reading: "The circle lies in the disc, so retract_of's first conjunct holds; what " +
		"fails is the retraction, which would make the loop winding once null-homotopic in S¹.",
	Deps: []registry.EntryLike{
		CircleFundamentalGroup,
		CircleLoopsDistinct,
		continuous.RetractOfDef,
		convex_topology.ConvexContractible,
		convex_topology.BallConvex,
		fundamental_group.ContractibleSimplyConnected,
		fundamental_group.FundamentalMapCompose,
		fundamental_group.FundamentalMapIdentity,
		euclidean_topology.SphereSubsetBall,
	},
	Build: family.Card(Statement{
		Conclusion: "¬retract_of(«D²», euclidean_sphere(1))",
	},
		"a retraction r of the disc onto the circle, after the inclusion of the circle in the "+
			"disc, is the identity of the circle, so the identity of π₁(S¹) factors through π₁ of the "+
			"disc (FundamentalMapCompose, FundamentalMapIdentity); the disc is convex, so contractible "+
			"and simply connected (BallConvex, ConvexContractible, ContractibleSimplyConnected), and "+
			"the loop winding once would be homotopic to the constant loop, against CircleLoopsDistinct"),
})}

// OddMapNotNullHomotopic — a map of the circle to itself that sends
// antipodal points to antipodal points is not homotopic to a constant
// map.
var OddMapNotNullHomotopic = oddMapNotNullHomotopicThm{family.Add(registry.ProofEntry{
	Name: "OddMapNotNullHomotopic",
	Key:  "prop_7384e6fb226e5081",
	Reading: "Oddness is load-bearing: a constant map is null-homotopic and not odd. A constant " +
		"c off the circle makes homotopic_rel false at once, the homotopy's end lying in the circle.",
	Deps: []registry.EntryLike{
		CircleCovering,
		CircleLoopsDistinct,
		covering_space.PathLifting,
		fundamental_group.FundamentalMapFreeHomotopy,
		fundamental_group.FundamentalMapClass,
	},
	Build: family.Card(Statement{
		Binders: "∀g:((num → real) → num → real).",
		Hypotheses: []string{
			"continuous_map(euclidean_sphere_topology(1), euclidean_sphere_topology(1), g)",
			"∀x:(num → real). x ∈ euclidean_sphere(1) ⇒ g(-x) = -g(x)",
		},
		Conclusion: "¬∃c:(num → real). " +
			"    homotopic_rel(euclidean_sphere_topology(1), " +
			"        euclidean_sphere_topology(1), " +
			"        ∅, " +
			"        g, " +
			"        λx:(num → real). c)",
	},
		"lift the loop g ∘ «circle» to a path h of the line (PathLifting); «circle»(t + 1/2) "+
			"= −«circle»(t), so oddness makes h(t + 1/2) − h(t) an integer plus 1/2 at every t of "+
			"⟦0, 1/2⟧, the same q + 1/2 throughout by continuity; so h(1) − h(0) = 2q + 1, and "+
			"the loop g ∘ «circle» is homotopic to the standard loop winding 2q + 1 times, an odd "+
			"number and not zero. A map homotopic to a constant sends that loop to a class "+
			"conjugate to the constant class (FundamentalMapFreeHomotopy), the identity, and the "+
			"loop winding 2q + 1 times is not homotopic to the constant loop (CircleLoopsDistinct)"),
})}

// BorsukUlamPlane — the Borsuk–Ulam theorem in dimension two: a continuous
// map of the 2-sphere to the plane agrees at some pair of antipodal points.
var BorsukUlamPlane = borsukUlamPlaneThm{family.Add(registry.ProofEntry{
	Name: "BorsukUlamPlane",
	Key:  "prop_b31c33fcbe2f3d63",
	Reading: "f lands in the padded 2-vectors, so f(−x) = f(x) is equality in ℝ²; " +
		"continuity on the whole 2-sphere is what is used. A constant f is met by every x.",
	Deps: []registry.EntryLike{
		OddMapNotNullHomotopic,
		convex_topology.BallConvex,
		homotopy.HomotopicRelDef,
		euclidean_topology.NormContinuous,
		euclidean_topology.ContinuousIffCoordinates,
	},
	Build: family.Card(Statement{
		Binders: "∀f:((num → real) → num → real).",
		Hypotheses: []string{
			"continuous_map(euclidean_sphere_topology(2), euclidean_topology(2), f)",
		},
		Conclusion: "∃x:(num → real). x ∈ euclidean_sphere(2) ∧ f(-x) = f(x)",
	},
		"if f(x) ≠ f(−x) everywhere, g(x) = (f(x) − f(−x)) / ‖f(x) − f(−x)‖ is a continuous "+
			"map of the 2-sphere to the circle with g(−x) = −g(x). On the equator, the circle "+
			"S¹ inside S², g is odd; it extends over the disc by the upper hemisphere, G(y) = "+
			"g(y₀, y₁, √(1 − y₀² − y₁²)), so H((x, t)) = G((1 − t) • x) is a homotopy of g on "+
			"the circle to the constant at G(0), against OddMapNotNullHomotopic"),
})}
