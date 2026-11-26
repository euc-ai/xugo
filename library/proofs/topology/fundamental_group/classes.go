// classes.go — the classes of paths: two paths have one class exactly
// when they are homotopic, joining and reversing classes is joining and
// reversing their paths, the classes of the loops at a point of the
// space form a group, and a path between two points carries the group at
// one to the group at the other.

package fundamental_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/registry"
)

// PathClassEq — two paths have one class exactly when they are
// homotopic.
var PathClassEq = pathClassEqThm{family.Add(registry.ProofEntry{
	Name: "PathClassEq",
	Key:  "prop_7cd4280b8d93a56e",
	Reading: "The backward direction reads neither path hypothesis; the forward one needs one: a map " +
		"that is not a path has the empty class, so two such maps share a class without being homotopic.",
	Deps: []registry.EntryLike{
		PathClassDef,
		homotopy.PathHomotopicEquivalence,
		homotopy.PathHomotopicPaths,
		equivalence.EquivalenceOn,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g h:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
			"path_in(T, h)",
		},
		Conclusion: "path_class(T, g) = path_class(T, h) ⇔ path_homotopic(T, g, h)",
	},
		"path homotopy is an equivalence on the paths (PathHomotopicEquivalence), "+
			"and every path homotopic to a path is a path (PathHomotopicPaths): g "+
			"lies in its own class, and two classes sharing a member are one"),
})}

// PathClassJoinClass — the join of the classes of two paths meeting end to
// start is the class of their join.
var PathClassJoinClass = pathClassJoinClassThm{family.Add(registry.ProofEntry{
	Name: "PathClassJoinClass",
	Key:  "prop_78ebed53178f6abc",
	Reading: "g(1) = h(0) is what PathJoinHomotopic reads to compare the join of any " +
		"representatives with the join of g and h. No axiom on T: the pasting is on the square.",
	Deps: []registry.EntryLike{
		PathClassDef,
		PathClassJoinDef,
		homotopy.PathJoinHomotopic,
		homotopy.PathHomotopicEnds,
		homotopy.PathHomotopicEquivalence,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g h:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
			"path_in(T, h)",
			"g(&1) = h(&0)",
		},
		Conclusion: "path_class_join(T, path_class(T, g), path_class(T, h)) = " +
			"path_class(T, path_join(g, h))",
	},
		"a path homotopic to the join of g' ≃ g and h' ≃ h is homotopic to the join of g and h: g' "+
			"ends where g does and h' begins where h does (PathHomotopicEnds), so the two joins are "+
			"homotopic (PathJoinHomotopic); conversely g and h themselves are members of their classes"),
})}

// PathClassReverseClass — the reverse of the class of a path is the class
// of its reverse.
var PathClassReverseClass = pathClassReverseClassThm{family.Add(registry.ProofEntry{
	Name:    "PathClassReverseClass",
	Key:     "prop_5c22175204a45d35",
	Reading: "path_in(T, g) puts g in its own class, the witness for one inclusion.",
	Deps: []registry.EntryLike{
		PathClassDef,
		PathClassReverseDef,
		homotopy.PathReverseHomotopic,
		homotopy.PathHomotopicEquivalence,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "path_class_reverse(T, path_class(T, g)) = path_class(T, path_reverse(g))",
	},
		"the reverse of a path homotopic to g is homotopic to the reverse "+
			"of g (PathReverseHomotopic), and g is a member of its class"),
})}

// FundamentalGroupMember — the members of the fundamental group at x are
// the classes of the loops at x.
var FundamentalGroupMember = fundamentalGroupMemberThm{family.Add(registry.ProofEntry{
	Name: "FundamentalGroupMember",
	Key:  "prop_1e4a777541d91856",
	Reading: "No hypothesis: a path homotopic to a loop at x is a loop " +
		"at x, so the class taken among the loops is the whole class. At x " +
		"outside the space there are no loops and both sides are false.",
	Deps: []registry.EntryLike{
		FundamentalGroupDef,
		PathClassDef,
		LoopsAtDef,
		equivalence.QuotientOnDef,
		equivalence.EquivalenceClassDef,
		homotopy.PathHomotopicEnds,
		homotopy.PathHomotopicPaths,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀x:A. ∀C:set(real → A).",
		Conclusion: "C ∈ fundamental_group(T, x).carrier ⇔ " +
			"∃g:(real → A). g ∈ loops_at(T, x) ∧ C = path_class(T, g)",
	},
		"the carrier is the quotient of the loops at x by path homotopy; the class of a loop "+
			"relative to the loops is its whole class, since a path homotopic to a loop at x is "+
			"a path (PathHomotopicPaths) with the same ends (PathHomotopicEnds), a loop at x"),
})}

// FundamentalGroupOn — at a point of the space, the classes of loops form a
// group under joining.
var FundamentalGroupOn = fundamentalGroupOnThm{family.Add(registry.ProofEntry{
	Name: "FundamentalGroupOn",
	Key:  "prop_8d3bf882c9eb4df3",
	Reading: "x ∈ ⋃T is load-bearing: it makes the constant loop a path, so the unit lies in " +
		"the carrier; outside the space the carrier is empty and group_on fails. No axiom on T.",
	Deps: []registry.EntryLike{
		FundamentalGroupMember,
		PathClassJoinClass,
		PathClassReverseClass,
		PathClassEq,
		group.GroupOn,
		homotopy.PathJoinAssoc,
		homotopy.PathJoinConstantLeft,
		homotopy.PathJoinReverseLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "group_on(fundamental_group(T, x))",
	},
		"each axiom read on classes of loops (FundamentalGroupMember): the product and the inverse "+
			"of classes of loops are classes of loops (PathClassJoinClass, PathClassReverseClass), the "+
			"constant loop at x is a loop, and associativity, the left identity and the left inverse "+
			"are PathJoinAssoc, PathJoinConstantLeft and PathJoinReverseLeft through PathClassEq"),
})}

// BasepointChange — a path from x to y carries the fundamental group at x
// isomorphically onto the fundamental group at y, by conjugation.
var BasepointChange = basepointChangeThm{family.Add(registry.ProofEntry{
	Name:    "BasepointChange",
	Key:     "prop_616e5c0b4c93f9e3",
	Reading: "path_in(T, g) puts both ends in the space, so both records are groups. No axiom on T.",
	Deps: []registry.EntryLike{
		FundamentalGroupOn,
		FundamentalGroupMember,
		PathClassJoinClass,
		PathClassReverseClass,
		PathClassEq,
		group_homomorphism.GroupIsomorphismDef,
		homotopy.PathJoinAssoc,
		homotopy.PathJoinReverseLeft,
		homotopy.PathJoinReverseRight,
		homotopy.PathJoinConstantLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g:(real → A).",
		Hypotheses: []string{
			"path_in(T, g)",
		},
		Conclusion: "group_isomorphism(fundamental_group(T, g(&0)), " +
			"    fundamental_group(T, g(&1)), " +
			"    λC:set(real → A). " +
			"        path_class_join(T, " +
			"            path_class_join(T, path_class(T, path_reverse(g)), C), " +
			"            path_class(T, g)))",
	},
		"on the class of a loop c at g(0) the map is the class of the loop ḡ · c · g at g(1) "+
			"(PathClassJoinClass, PathClassReverseClass); it is a homomorphism because g · ḡ is "+
			"homotopic to the constant loop, and the conjugation by ḡ is its inverse, by the groupoid "+
			"laws (PathJoinAssoc, PathJoinReverseLeft, PathJoinReverseRight, PathJoinConstantLeft)"),
})}
