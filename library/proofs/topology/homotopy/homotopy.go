// homotopy.go — homotopy relative to a set: an equivalence on the
// continuous maps, kept by composition on either side; and the square a
// homotopy sweeps along a path, which reads the image of the path at the
// far end as the image at the near end conjugated by the two tracks of
// its ends.

package homotopy

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/path_connected"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// HomotopicRelRefl — a continuous map is homotopic to itself, relative to
// any set.
var HomotopicRelRefl = homotopicRelReflThm{family.Add(registry.ProofEntry{
	Name: "HomotopicRelRefl",
	Key:  "prop_354742f027929cd7",
	Reading: "No axiom on either space: f after the first projection is continuous on any product. a " +
		"is read only at its points in the space, so any a serves, ∅ or a set outside the space included.",
	Deps: []registry.EntryLike{HomotopicRelDef, product_topology.FstContinuous, continuous.Compose},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀a:set(A). ∀f:(A → B).",
		Hypotheses: []string{
			"continuous_map(T, S, f)",
		},
		Conclusion: "homotopic_rel(T, S, a, f, f)",
	},
		"the homotopy λp. f(fst(p)) never moves: f after the first "+
			"projection, continuous on the product (FstContinuous, Compose)"),
})}

// HomotopicRelSym — a homotopy run backwards.
var HomotopicRelSym = homotopicRelSymThm{family.Add(registry.ProofEntry{
	Name: "HomotopicRelSym",
	Key:  "prop_f9dd68396b3733bc",
	Reading: "No axiom on either space. At a point of a in the space " +
		"g(x) = H((x, 1)) = f(x), so the reversed homotopy holds g(x) there.",
	Deps: []registry.EntryLike{
		HomotopicRelDef,
		product_topology.ProductMapContinuous,
		continuous.Compose,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀a:set(A). ∀f g:(A → B).",
		Hypotheses: []string{
			"homotopic_rel(T, S, a, f, g)",
		},
		Conclusion: "homotopic_rel(T, S, a, g, f)",
	},
		"H((x, 1 − t)), H after the product of the identity and t ↦ 1 − t "+
			"(ProductMapContinuous); at a point of a in the space H is f(x) at every time, "+
			"and g(x) = H((x, 1)) = f(x) there, so the reversed homotopy holds it at g(x)"),
})}

// HomotopicRelTrans — two homotopies run one after the other.
var HomotopicRelTrans = homotopicRelTransThm{family.Add(registry.ProofEntry{
	Name: "HomotopicRelTrans",
	Key:  "prop_be472908ff04b24e",
	Reading: "is_topology(T) is load-bearing: it makes T × «I» a topology for " +
		"ClosedPasting and the two halves ⋃T × ⟦0, 1/2⟧ and ⋃T × ⟦1/2, 1⟧ closed " +
		"in it. S needs nothing; on a, g = f, so the second half holds f too.",
	Deps: []registry.EntryLike{
		HomotopicRelDef,
		continuous.ClosedPasting,
		product_topology.ProductTopology,
		product_topology.ClosedRectangle,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀a:set(A). ∀f g h:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"homotopic_rel(T, S, a, f, g)",
			"homotopic_rel(T, S, a, g, h)",
		},
		Conclusion: "homotopic_rel(T, S, a, f, h)",
	},
		"the first homotopy at double speed on ⟦0, 1/2⟧ and the second on ⟦1/2, "+
			"1⟧, agreeing at time 1/2 where both are g; the two halves T × ⟦0, 1/2⟧ "+
			"and T × ⟦1/2, 1⟧ are closed in the product (ClosedRectangle), which is "+
			"a topology because T is (ProductTopology), and ClosedPasting joins them"),
})}

// HomotopicRelComposeLeft — a homotopy followed by a continuous map.
var HomotopicRelComposeLeft = homotopicRelComposeLeftThm{family.Add(registry.ProofEntry{
	Name:    "HomotopicRelComposeLeft",
	Key:     "prop_d3bef4f7917529cb",
	Reading: "No axiom on any of the three spaces: k after H is the homotopy, holding k(f(x)) on a.",
	Deps:    []registry.EntryLike{HomotopicRelDef, continuous.Compose},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀U:set(set(C)). ∀a:set(A). ∀f g:(A → B). ∀k:(B → C).",
		Hypotheses: []string{
			"homotopic_rel(T, S, a, f, g)",
			"continuous_map(S, U, k)",
		},
		Conclusion: "homotopic_rel(T, U, a, k ∘ f, k ∘ g)",
	},
		"k ∘ H is the homotopy (Compose)"),
})}

// HomotopyAlongPath — a homotopy swept along a path: the image of the path
// at the end of the homotopy is path-homotopic to the track of its start
// run backwards, the image at the beginning, and the track of its end.
var HomotopyAlongPath = homotopyAlongPathThm{family.Add(registry.ProofEntry{
	Name: "HomotopyAlongPath",
	Key:  "prop_e5336e1fe16ee89e",
	Reading: "No axiom on T or S; path_in(T, g) makes ⋃T nonempty. The " +
		"square «I» × «I» is a topology, which is what PairedContinuousIff " +
		"asks. Both sides run from H((g(0), 1)) to H((g(1), 1)).",
	Deps: []registry.EntryLike{
		PathHomotopicDef,
		HomotopicRelComposeLeft,
		product_topology.PairedContinuousIff,
		path_connected.PathJoin,
		path_connected.PathReverse,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀H:(prod(A, real) → B). ∀g:(real → A).",
		Hypotheses: []string{
			"continuous_map(product_topology(T, «I»), S, H)",
			"path_in(T, g)",
		},
		Conclusion: "path_homotopic(S, " +
			"    λt:real. H((g(t), &1)), " +
			"    path_join(path_join(path_reverse(λs:real. H((g(&0), s))), λt:real. H((g(t), &0))), " +
			"        λs:real. H((g(&1), s))))",
	},
		"Q((t, s)) = H((g(t), s)) is a continuous map of the unit square «I» × «I» "+
			"(PairedContinuousIff). In the square, the top edge and the path down the left "+
			"side, along the bottom and up the right side are two paths with the same ends, "+
			"path-homotopic by the straight line between them, the square being convex; Q "+
			"carries that homotopy into S (HomotopicRelComposeLeft), and Q after the edge paths "+
			"is the two sides of the statement, joining and reversing commuting with Q pointwise"),
})}
