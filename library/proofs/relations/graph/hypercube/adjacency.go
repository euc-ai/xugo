package hypercube

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/simple_graph"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// CubeAdjacentDef joins two cube vertices by a flip in one coordinate of S.
var CubeAdjacentDef = cubeAdjacentDefThm{family.Define(registry.DefEntry{
	Name:  "CubeAdjacentDef",
	Key:   "prop_aee1f4fe65d4fb68",
	Const: "cube_adjacent",
	Type:  "set(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀S X Y:set(A). cube_adjacent(S, X, Y) ⇔ ∃i:A. i ∈ S ∧ Y = set_toggle(i, X)",
	},
})}

// SimpleGraph says that cube adjacency over S is a simple graph on every
// family H of vertices: symmetric, and without loops. A flip is its own
// inverse, and it changes membership of the coordinate flipped.
var SimpleGraph = simpleGraphThm{family.Add(registry.ProofEntry{
	Name: "SimpleGraph",
	Key:  "prop_aa27d62050e94607",
	Build: family.Instance(simple_graph.SimpleGraphOn,
		"∀S:set(A). ∀H:set(set(A)). simple_graph_on(H, cube_adjacent(S))",
		Case(
			"flipping the same coordinate returns to the first vertex",
			Unfold(equivalence.SymmetricOnDef),
			Unfold(CubeAdjacentDef),
			By(set_basic.ToggleInvolution)),
		Case(
			"a flip changes membership of its coordinate",
			Unfold(CubeAdjacentDef),
			By(Normalized, set_basic.InToggle))),
})}
