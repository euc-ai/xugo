// maps.go — the map of classes a continuous map induces: the class of a
// path goes to the class of its image, a homomorphism of fundamental
// groups, functorial, unchanged by a homotopy that holds the base point
// and conjugated by the track of the base point under one that moves it;
// so a homotopy equivalence induces an isomorphism, and a contractible
// space is simply connected.

package fundamental_group

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/homotopy"
	"github.com/euc-ai/xugo/library/registry"
)

// FundamentalMapClass — a continuous map carries the class of a path to
// the class of its image.
var FundamentalMapClass = fundamentalMapClassThm{family.Add(registry.ProofEntry{
	Name: "FundamentalMapClass",
	Key:  "prop_45cd58165ea12b99",
	Reading: "Continuity of f carries a homotopy of g to g' to one of f ∘ g to " +
		"f ∘ g' (HomotopicRelComposeLeft); path_in(T, g) puts g in its own class.",
	Deps: []registry.EntryLike{
		FundamentalMapDef,
		PathClassDef,
		homotopy.HomotopicRelComposeLeft,
		homotopy.PathHomotopicEquivalence,
		continuous.Compose,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀g:(real → A).",
		Hypotheses: []string{
			"continuous_map(T, S, f)",
			"path_in(T, g)",
		},
		Conclusion: "fundamental_map(S, f, path_class(T, g)) = path_class(S, f ∘ g)",
	},
		"f after a homotopy of paths is a homotopy of their images (HomotopicRelComposeLeft), so "+
			"f ∘ g' is homotopic to f ∘ g for every g' in the class of g, and g is in its own class"),
})}

// FundamentalMapHom — a continuous map induces a homomorphism of
// fundamental groups.
var FundamentalMapHom = fundamentalMapHomThm{family.Add(registry.ProofEntry{
	Name: "FundamentalMapHom",
	Key:  "prop_a9c1fca3bf7c02b2",
	Reading: "x ∈ ⋃T makes both records groups, f(x) being a point of S by " +
		"continuity. f after a join is the join of the images exactly, as functions.",
	Deps: []registry.EntryLike{
		FundamentalMapClass,
		FundamentalGroupOn,
		FundamentalGroupMember,
		PathClassJoinClass,
		group_homomorphism.GroupHomomorphism,
		continuous.MapsInto,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀x:A.",
		Hypotheses: []string{
			"continuous_map(T, S, f)",
			"x ∈ ⋃T",
		},
		Conclusion: "group_homomorphism(fundamental_group(T, x), " +
			"    fundamental_group(S, f(x)), " +
			"    fundamental_map(S, f))",
	},
		"both are groups (FundamentalGroupOn, f(x) being a point of S by MapsInto); the image of the "+
			"class of a loop at x is the class of a loop at f(x) (FundamentalMapClass), and f after a join "+
			"is the join of the two images, pointwise, so PathClassJoinClass on both sides gives the product"),
})}

// FundamentalMapIdentity — the identity induces the identity.
var FundamentalMapIdentity = fundamentalMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "FundamentalMapIdentity",
	Key:  "prop_b0b0d70fa9684a1b",
	Reading: "The carrier hypothesis is load-bearing: for a set that is not " +
		"a class, such as {g}, the identity's map gives the whole class of g.",
	Deps: []registry.EntryLike{FundamentalMapClass, FundamentalGroupMember, continuous.Identity},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀x:A. ∀C:set(real → A).",
		Hypotheses: []string{
			"C ∈ fundamental_group(T, x).carrier",
		},
		Conclusion: "fundamental_map(T, λy:A. y, C) = C",
	},
		"C is the class of a loop g (FundamentalGroupMember), "+
			"and the identity after g is g (FundamentalMapClass)"),
})}

// FundamentalMapCompose — the map a composite induces is the composite of
// the induced maps.
var FundamentalMapCompose = fundamentalMapComposeThm{family.Add(registry.ProofEntry{
	Name: "FundamentalMapCompose",
	Key:  "prop_939425840c3f1f60",
	Reading: "D in the carrier makes D the class of a path, so FundamentalMapClass " +
		"applies three times; both maps continuous is what it reads.",
	Deps: []registry.EntryLike{FundamentalMapClass, FundamentalGroupMember, continuous.Compose},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀U:set(set(C)). " +
			"∀f:(A → B). " +
			"∀h:(B → C). " +
			"∀x:A. " +
			"∀D:set(real → A).",
		Hypotheses: []string{
			"continuous_map(T, S, f)",
			"continuous_map(S, U, h)",
			"D ∈ fundamental_group(T, x).carrier",
		},
		Conclusion: "fundamental_map(U, h ∘ f, D) = fundamental_map(U, h, fundamental_map(S, f, D))",
	},
		"D is the class of a loop g (FundamentalGroupMember); both sides "+
			"are the class of h ∘ f ∘ g, by FundamentalMapClass three times"),
})}

// FundamentalMapHomotopic — maps homotopic with the base point held induce
// one map of the fundamental group.
var FundamentalMapHomotopic = fundamentalMapHomotopicThm{family.Add(registry.ProofEntry{
	Name: "FundamentalMapHomotopic",
	Key:  "prop_511cbfd1f8a914bd",
	Reading: "The held set {x} makes the track of x constant, and it is both tracks " +
		"of a loop at x; D in the carrier puts x in the space. Neither f nor h need be " +
		"continuous: on a family that is not a topology the ends of a homotopy need not be.",
	Deps: []registry.EntryLike{
		FundamentalMapDef,
		FundamentalGroupMember,
		homotopy.HomotopyAlongPath,
		homotopy.PathJoinConstantLeft,
		homotopy.PathJoinConstantRight,
		homotopy.PathJoinHomotopic,
		continuous.Eq,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f h:(A → B). ∀x:A. ∀D:set(real → A).",
		Hypotheses: []string{
			"homotopic_rel(T, S, {x}, f, h)",
			"D ∈ fundamental_group(T, x).carrier",
		},
		Conclusion: "fundamental_map(S, f, D) = fundamental_map(S, h, D)",
	},
		"argue member by member, f and h not being continuous on a T that is not a topology: "+
			"every member g' of D is a loop at x (FundamentalGroupMember), and the homotopy "+
			"swept along g' (HomotopyAlongPath) has for its two tracks the constant path at "+
			"f(x), x being held, so h ∘ g' is homotopic to f ∘ g' between two constant paths, "+
			"and so to f ∘ g' (PathJoinConstantLeft, PathJoinConstantRight, PathJoinHomotopic); "+
			"f ∘ g' and h ∘ g' are paths, the homotopy after t ↦ (g'(t), 0) and t ↦ (g'(t), 1) "+
			"on the interval (continuous.Eq). The two sets of FundamentalMapDef then agree"),
})}

// FundamentalMapFreeHomotopy — under a homotopy that moves the base point,
// the map the end induces is the map the start induces conjugated by the
// track of the base point.
var FundamentalMapFreeHomotopy = fundamentalMapFreeHomotopyThm{family.Add(registry.ProofEntry{
	Name: "FundamentalMapFreeHomotopy",
	Key:  "prop_7e9b16ddf1eddf22",
	Reading: "D in the carrier makes D the class of a loop at x, so the two " +
		"tracks along it are the one track of x. Neither f nor h need be continuous.",
	Deps: []registry.EntryLike{
		FundamentalMapDef,
		FundamentalGroupMember,
		PathClassJoinClass,
		PathClassReverseClass,
		PathClassEq,
		homotopy.HomotopyAlongPath,
		homotopy.PathJoinHomotopic,
		continuous.Eq,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀S:set(set(B)). " +
			"∀H:(prod(A, real) → B). " +
			"∀f h:(A → B). " +
			"∀x:A. " +
			"∀D:set(real → A).",
		Hypotheses: []string{
			"continuous_map(product_topology(T, «I»), S, H)",
			"∀y:A. y ∈ ⋃T ⇒ H((y, &0)) = f(y) ∧ H((y, &1)) = h(y)",
			"D ∈ fundamental_group(T, x).carrier",
		},
		Conclusion: "fundamental_map(S, h, D) = " +
			"path_class_join(S, " +
			"    path_class_join(S, " +
			"        path_class(S, path_reverse(λs:real. H((x, s)))), " +
			"        fundamental_map(S, f, D)), " +
			"    path_class(S, λs:real. H((x, s))))",
	},
		"argue member by member, f and h not being continuous on a T that is not a topology: D is "+
			"the class of a loop g at x (FundamentalGroupMember), and for each g' homotopic to g the "+
			"composites f ∘ g' and h ∘ g' are paths, the homotopy after t ↦ (g'(t), 0) and t ↦ (g'(t), "+
			"1) on the interval (continuous.Eq), homotopic to f ∘ g and h ∘ g through the homotopy of "+
			"g' to g read through H at times 0 and 1. HomotopyAlongPath makes h ∘ g homotopic to the "+
			"track of x run backwards, f ∘ g, and the track of x, g's two ends being x, and the class "+
			"of that join is the class join (PathClassJoinClass, PathClassReverseClass)"),
})}

// HomotopyEquivalenceFundamentalGroup — a homotopy equivalence induces an
// isomorphism of fundamental groups.
var HomotopyEquivalenceFundamentalGroup = homotopyEquivalenceFundamentalGroupThm{family.Add(registry.ProofEntry{
	Name: "HomotopyEquivalenceFundamentalGroup",
	Key:  "prop_d87d5ac8bf57b065",
	Reading: "Both homotopies are read: g ∘ f ≃ id makes f's map " +
		"injective and g's map at f(x) onto, f ∘ g ≃ id makes g's map at f(x) " +
		"injective; together f's map is onto. x ∈ ⋃T makes the records groups.",
	Deps: []registry.EntryLike{
		homotopy.HomotopyEquivalenceDef,
		FundamentalMapHom,
		FundamentalMapCompose,
		FundamentalMapIdentity,
		FundamentalMapFreeHomotopy,
		BasepointChange,
		group_homomorphism.GroupIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). ∀g:(B → A). ∀x:A.",
		Hypotheses: []string{
			"homotopy_equivalence(T, S, f, g)",
			"x ∈ ⋃T",
		},
		Conclusion: "group_isomorphism(fundamental_group(T, x), " +
			"    fundamental_group(S, f(x)), " +
			"    fundamental_map(S, f))",
	},
		"g ∘ f is homotopic to the identity, so the map it induces at x, g's after f's "+
			"(FundamentalMapCompose), is the identity's conjugated by the track of x "+
			"(FundamentalMapFreeHomotopy, FundamentalMapIdentity), a bijection (BasepointChange): "+
			"f's is injective and g's at f(x) is onto. Likewise f ∘ g homotopic to the identity "+
			"makes f's at g(f(x)) after g's at f(x) a bijection, so g's at f(x) is injective; g's "+
			"is then a bijection, and f's, g's inverse after a bijection, is one too"),
})}

// ContractibleSimplyConnected — a contractible space is simply connected.
var ContractibleSimplyConnected = contractibleSimplyConnectedThm{family.Add(registry.ProofEntry{
	Name: "ContractibleSimplyConnected",
	Key:  "prop_64dd95df29c4b143",
	Reading: "The point c and the tracks λs. H((y, s)) give path-connectedness. The empty space " +
		"is not contractible, so that case does not arise; the conclusion would hold there anyway.",
	Deps: []registry.EntryLike{
		homotopy.ContractibleSpaceDef,
		SimplyConnectedSpaceDef,
		homotopy.HomotopyAlongPath,
		homotopy.PathJoinAssoc,
		homotopy.PathJoinReverseRight,
		homotopy.PathJoinConstantLeft,
		homotopy.PathJoinConstantRight,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"contractible_space(T)",
		},
		Conclusion: "simply_connected_space(T)",
	},
		"for H the contraction to c, each point x is joined to c by its track τ = λs. "+
			"H((x, s)), so the space is path-connected. For a loop g at x, HomotopyAlongPath "+
			"makes the constant loop at c homotopic to τ̄ · g · τ; conjugating back by τ with "+
			"the groupoid laws (PathJoinAssoc, PathJoinReverseRight, PathJoinConstantLeft, "+
			"PathJoinConstantRight) makes g homotopic to τ · τ̄, so to the constant loop at x"),
})}

// SimplyConnectedPathsHomotopic — in a simply connected space two paths
// with the same ends are homotopic.
var SimplyConnectedPathsHomotopic = simplyConnectedPathsHomotopicThm{family.Add(registry.ProofEntry{
	Name: "SimplyConnectedPathsHomotopic",
	Key:  "prop_4188abd826077b19",
	Reading: "Simple connectivity is read only at the loop g · h̄ at g(0); both end equations " +
		"are load-bearing, one making g · h̄ a loop, the other letting the constant law absorb it.",
	Deps: []registry.EntryLike{
		SimplyConnectedSpaceDef,
		homotopy.PathJoinAssoc,
		homotopy.PathJoinReverseLeft,
		homotopy.PathJoinConstantRight,
		homotopy.PathJoinHomotopic,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀g h:(real → A).",
		Hypotheses: []string{
			"simply_connected_space(T)",
			"path_in(T, g)",
			"path_in(T, h)",
			"g(&0) = h(&0)",
			"g(&1) = h(&1)",
		},
		Conclusion: "path_homotopic(T, g, h)",
	},
		"g · h̄ is a loop at g(0), homotopic to the constant loop; so g ≃ g · (h̄ "+
			"· h) ≃ (g · h̄) · h ≃ h by the groupoid laws (PathJoinConstantRight, "+
			"PathJoinReverseLeft, PathJoinAssoc, PathJoinHomotopic)"),
})}
