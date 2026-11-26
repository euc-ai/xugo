// fundamental_group.go — the fundamental group of the circle. The circle
// map t ↦ (cos 2πt, sin 2πt) is a covering of the circle by the line, so a
// loop lifts to a path of the line whose two ends differ by an integer,
// and homotopic loops lift to paths with the same ends: every loop at
// «circle»(s) is homotopic to exactly one of the standard loops
// t ↦ «circle»(s + k t), k an integer, and joining two standard loops adds
// their integers. So π₁(S¹) ≅ ℤ.

package circle

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/covering_space"
	"github.com/euc-ai/xugo/library/proofs/topology/fundamental_group"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/proofs/vector/standard_quotient_spaces"
	"github.com/euc-ai/xugo/library/registry"
)

// CircleCovering — the circle map is a covering of the circle by the
// line.
var CircleCovering = circleCoveringThm{family.Add(registry.ProofEntry{
	Name: "CircleCovering",
	Key:  "prop_8ca39c5524a8ebd7",
	Reading: "Each point «circle»(s) lies in the circle less «circle»(s + 1/2), " +
		"whose sheets are the open intervals ⟨s + k − 1/2, s + k + 1/2⟩ of length 1.",
	Deps: []registry.EntryLike{
		covering_space.CoveringMapDef,
		covering_space.EvenlyCoveredDef,
		standard_quotient_spaces.CircleMapContinuous,
		standard_quotient_spaces.CircleMapFibres,
		continuous.CompactHausdorffEmbedding,
	},
	Build: family.Card(Statement{
		Conclusion: "covering_map(real_topology, euclidean_sphere_topology(1), «circle»)",
	},
		"the circle less the point «circle»(s + 1/2) is evenly covered: its preimage is the union of "+
			"the disjoint open intervals ⟨s + k − 1/2, s + k + 1/2⟩, k an integer (CircleMapFibres), and "+
			"the circle map is a homeomorphism of each onto it, being continuous (CircleMapContinuous), one "+
			"to one there, and an embedding on every compact interval inside (CompactHausdorffEmbedding)"),
})}

// CircleLoopStandard — every loop of the circle at «circle»(s) is
// homotopic to a standard loop t ↦ «circle»(s + k t).
var CircleLoopStandard = circleLoopStandardThm{family.Add(registry.ProofEntry{
	Name:    "CircleLoopStandard",
	Key:     "prop_1826ad5cf9ce2438",
	Reading: "Holds at every real s; k is h(1) − s for h the lift of the loop from s.",
	Deps: []registry.EntryLike{
		CircleCovering,
		covering_space.PathLifting,
		covering_space.PathHomotopyLifting,
		standard_quotient_spaces.CircleMapFibres,
		homotopy.HomotopicRelComposeLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀s:real. ∀g:(real → num → real).",
		Hypotheses: []string{
			"g ∈ loops_at(euclidean_sphere_topology(1), «circle»(s))",
		},
		Conclusion: "∃k:int. " +
			"    path_homotopic(euclidean_sphere_topology(1), g, λt:real. «circle»(s + real_of_int(k) * t))",
	},
		"lift g from s (PathLifting); the lift h ends at a point over «circle»(s), so h(1) "+
			"= s + k for an integer k (CircleMapFibres); in the line h is homotopic to t ↦ s + "+
			"k t with the ends held, by the straight line between them, and the circle map "+
			"carries that homotopy to one of g with the standard loop (HomotopicRelComposeLeft)"),
})}

// CircleLoopsDistinct — standard loops with different integers are not
// homotopic.
var CircleLoopsDistinct = circleLoopsDistinctThm{family.Add(registry.ProofEntry{
	Name: "CircleLoopsDistinct",
	Key:  "prop_badcc9687c7ce1d1",
	Reading: "The lifts from s end at s + j and s + k, and homotopic " +
		"lifts share their ends. k = 0 is the constant loop at «circle»(s).",
	Deps: []registry.EntryLike{
		CircleCovering,
		covering_space.PathHomotopyLifting,
		homotopy.PathHomotopicEnds,
	},
	Build: family.Card(Statement{
		Binders: "∀s:real. ∀j k:int.",
		Hypotheses: []string{
			"path_homotopic(euclidean_sphere_topology(1), " +
				"    λt:real. «circle»(s + real_of_int(j) * t), " +
				"    λt:real. «circle»(s + real_of_int(k) * t))",
		},
		Conclusion: "j = k",
	},
		"the two loops lift from s to t ↦ s + j t and t ↦ s + k t; homotopic loops have homotopic lifts "+
			"from one point (PathHomotopyLifting), which end at one point (PathHomotopicEnds): s + j = s + k"),
})}

// CircleLoopsJoin — joining two standard loops adds their integers.
var CircleLoopsJoin = circleLoopsJoinThm{family.Add(registry.ProofEntry{
	Name: "CircleLoopsJoin",
	Key:  "prop_d2979595cfcee90a",
	Reading: "Unconditional; that j is an integer is what reads " +
		"the second half of the join as the line path from s + j.",
	Deps: []registry.EntryLike{
		standard_quotient_spaces.CircleMapFibres,
		standard_quotient_spaces.CircleMapContinuous,
		homotopy.HomotopicRelComposeLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀s:real. ∀j k:int.",
		Conclusion: "path_homotopic(euclidean_sphere_topology(1), " +
			"    path_join(λt:real. «circle»(s + real_of_int(j) * t), " +
			"        λt:real. «circle»(s + real_of_int(k) * t)), " +
			"    λt:real. «circle»(s + (real_of_int(j) + real_of_int(k)) * t))",
	},
		"the join is the circle map after the path of the line that runs from s to s + j "+
			"at double speed and then from s + j to s + j + k, the circle map not seeing the "+
			"integer j added to the second half (CircleMapFibres); in the line that path is "+
			"homotopic with its ends held to t ↦ s + (j + k) t by the straight line between "+
			"them, and the circle map carries the homotopy over (HomotopicRelComposeLeft)"),
})}

// CircleFundamentalGroup — π₁(S¹) ≅ ℤ: the integer k goes to the class of
// the loop that winds k times around the circle.
var CircleFundamentalGroup = circleFundamentalGroupThm{family.Add(registry.ProofEntry{
	Name: "CircleFundamentalGroup",
	Key:  "prop_4de93e8c83a8bfbf",
	Reading: "Unconditional in s: the standard loops are loops at «circle»(s) because " +
		"«circle»(s + k) = «circle»(s) for an integer k; the carrier of additive_group(int_ring) " +
		"is 𝕌, so onto is CircleLoopStandard and one to one CircleLoopsDistinct.",
	Deps: []registry.EntryLike{
		CircleLoopStandard,
		CircleLoopsDistinct,
		CircleLoopsJoin,
		fundamental_group.FundamentalGroupOn,
		fundamental_group.FundamentalGroupMember,
		fundamental_group.PathClassJoinClass,
		fundamental_group.PathClassEq,
		group_homomorphism.GroupIsomorphismDef,
		int_real_lift.AddGroup,
	},
	Build: family.Card(Statement{
		Binders: "∀s:real.",
		Conclusion: "group_isomorphism(additive_group(int_ring), " +
			"    fundamental_group(euclidean_sphere_topology(1), «circle»(s)), " +
			"    λk:int. path_class(euclidean_sphere_topology(1), λt:real. «circle»(s + real_of_int(k) * t)))",
	},
		"the standard loops are loops at «circle»(s), so the map lands in the group "+
			"(FundamentalGroupMember); it carries sums to products (CircleLoopsJoin, PathClassJoinClass), "+
			"is one to one (CircleLoopsDistinct, PathClassEq) and onto (CircleLoopStandard)"),
})}
