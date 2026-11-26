// van_kampen.go — the fundamental group of a union of two open sets,
// Seifert–van Kampen: the classes of loops in the two sets generate it,
// and two homomorphisms out of the groups of the two sets that agree on
// the group of the intersection extend to one out of the group of the
// union. A union of two simply connected open sets with a path-connected
// intersection is simply connected.

package fundamental_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/path_connected"
	"github.com/euc-ai/xugo/library/registry"
)

// VanKampenGenerated — two homomorphisms out of the fundamental group of a
// union of two open sets with a path-connected intersection agree if they
// agree on the classes of the loops in each set.
var VanKampenGenerated = vanKampenGeneratedThm{family.Add(registry.ProofEntry{
	Name: "VanKampenGenerated",
	Key:  "prop_c12c197850d215c3",
	Reading: "u, v ∈ T make the preimages an open cover of ⟦0, 1⟧ for " +
		"a Lebesgue number; u ∩ v path-connected joins x to each cut " +
		"point inside u ∩ v. u and v themselves need not be path-connected.",
	Deps: []registry.EntryLike{
		FundamentalMapClass,
		FundamentalGroupMember,
		PathClassJoinClass,
		complete_metric.LebesgueNumber,
		path_connected.PathConnectedInDef,
		group_homomorphism.GroupHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀u v:set(A). " +
			"∀x:A. " +
			"∀G:group_ops(E). " +
			"∀φ ψ:(set(real → A) → E). " +
			"∀D:set(real → A).",
		Hypotheses: []string{
			"is_topology(T)",
			"u ∈ T",
			"v ∈ T",
			"⋃T ⊆ u ∪ v",
			"path_connected_in(T, u ∩ v)",
			"x ∈ u ∩ v",
			"group_homomorphism(fundamental_group(T, x), G, φ)",
			"group_homomorphism(fundamental_group(T, x), G, ψ)",
			"∀C:set(real → A). " +
				"    C ∈ fundamental_group(subtopology(T, u), x).carrier ⇒ " +
				"    φ(fundamental_map(T, λy:A. y, C)) = ψ(fundamental_map(T, λy:A. y, C))",
			"∀C:set(real → A). " +
				"    C ∈ fundamental_group(subtopology(T, v), x).carrier ⇒ " +
				"    φ(fundamental_map(T, λy:A. y, C)) = ψ(fundamental_map(T, λy:A. y, C))",
			"D ∈ fundamental_group(T, x).carrier",
		},
		Conclusion: "φ(D) = ψ(D)",
	},
		"a loop at x is cut, by a Lebesgue number of the cover of ⟦0, 1⟧ by the preimages of u and v "+
			"(LebesgueNumber), into finitely many paths each inside u or inside v; merging neighbours inside "+
			"one set, each cut point lies in u ∩ v, and a path inside u ∩ v from x to it (path_connected_in) "+
			"turns each piece into a loop at x inside u or inside v. The class of the loop is the product of "+
			"the classes of those loops (PathClassJoinClass, FundamentalMapClass), on which φ and ψ agree"),
})}

// VanKampenExtension — two homomorphisms out of the fundamental groups of
// two path-connected open sets that agree on the fundamental group of their
// path-connected intersection extend to a homomorphism out of the
// fundamental group of the union.
var VanKampenExtension = vanKampenExtensionThm{family.Add(registry.ProofEntry{
	Name: "VanKampenExtension",
	Key:  "prop_2d514ffb73314c66",
	Reading: "u, v and u ∩ v path-connected join every grid point of a homotopy " +
		"to x inside each of the sets that holds it: that is the well-definedness " +
		"of χ, and it covers every triple intersection of a cover by two sets.",
	Deps: []registry.EntryLike{
		VanKampenGenerated,
		FundamentalMapHom,
		FundamentalMapClass,
		FundamentalGroupMember,
		complete_metric.LebesgueNumber,
		group_homomorphism.GroupHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀u v:set(A). ∀x:A. ∀G:group_ops(E). ∀φ ψ:(set(real → A) → E).",
		Hypotheses: []string{
			"is_topology(T)",
			"u ∈ T",
			"v ∈ T",
			"⋃T ⊆ u ∪ v",
			"path_connected_in(T, u)",
			"path_connected_in(T, v)",
			"path_connected_in(T, u ∩ v)",
			"x ∈ u ∩ v",
			"group_homomorphism(fundamental_group(subtopology(T, u), x), G, φ)",
			"group_homomorphism(fundamental_group(subtopology(T, v), x), G, ψ)",
			"∀C:set(real → A). " +
				"    C ∈ fundamental_group(subtopology(T, u ∩ v), x).carrier ⇒ " +
				"    φ(fundamental_map(subtopology(T, u), λy:A. y, C)) = " +
				"    ψ(fundamental_map(subtopology(T, v), λy:A. y, C))",
		},
		Conclusion: "∃χ:(set(real → A) → E). " +
			"    group_homomorphism(fundamental_group(T, x), G, χ) ∧ " +
			"    (∀C:set(real → A). " +
			"        C ∈ fundamental_group(subtopology(T, u), x).carrier ⇒ " +
			"        χ(fundamental_map(T, λy:A. y, C)) = φ(C)) ∧ " +
			"    (∀C:set(real → A). " +
			"        C ∈ fundamental_group(subtopology(T, v), x).carrier ⇒ " +
			"        χ(fundamental_map(T, λy:A. y, C)) = ψ(C))",
	},
		"χ sends the class of a loop cut into loops inside u or v (as in VanKampenGenerated) to the "+
			"product of their values under φ or ψ. That the value does not depend on the cut, nor on the "+
			"loop within its class, is the heart of the theorem: a homotopy of loops is cut by a Lebesgue "+
			"number of the unit square into small squares each inside u or v, each grid point joined to x by "+
			"a path inside every one of u, v, u ∩ v that holds it — the reason the three sets are "+
			"path-connected — and the product read along the bottom edge is carried to the product along the "+
			"top one square at a time, each step a relation in the group of u or v or an agreement over u ∩ v"),
})}

// SimplyConnectedUnion — a union of two simply connected open sets with a
// nonempty path-connected intersection is simply connected.
var SimplyConnectedUnion = simplyConnectedUnionThm{family.Add(registry.ProofEntry{
	Name: "SimplyConnectedUnion",
	Key:  "prop_d507f809d55c0cc1",
	Reading: "u ∩ v ≠ ∅ is load-bearing: two disjoint nonempty simply connected open sets make a " +
		"space that is not path-connected. A base point outside u ∩ v is first moved into it along a path.",
	Deps: []registry.EntryLike{
		SimplyConnectedSpaceDef,
		path_connected.PathConnectedUnion,
		complete_metric.LebesgueNumber,
		PathClassJoinClass,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀u v:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"u ∈ T",
			"v ∈ T",
			"⋃T ⊆ u ∪ v",
			"simply_connected_space(subtopology(T, u))",
			"simply_connected_space(subtopology(T, v))",
			"path_connected_in(T, u ∩ v)",
			"u ∩ v ≠ ∅",
		},
		Conclusion: "simply_connected_space(T)",
	},
		"the space is path-connected, a union of two path-connected sets sharing a point "+
			"(PathConnectedUnion); a loop at x is cut as in VanKampenGenerated into loops "+
			"inside u or v at a point of u ∩ v, each homotopic in its set to the constant loop, "+
			"so the loop is too. A base point outside u ∩ v is first moved into it along a path"),
})}
