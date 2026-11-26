// definitions.go — the chapter's definitional layer: the datatype
// btree(A) with its two constructors, and the three operations the
// chapter's theory is about.

package tree

import (
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// BtreeData — a binary tree is either a leaf, carrying nothing, or a
// node carrying a label between two subtrees. The datatype door mints
// the type and its constructors and derives the four principles a
// datatype comes with: induction, the recursion schema, injectivity of
// node and the distinctness of the constructors. The induction tactic
// reads the first under the library name btree_induction, and the define
// door's equation compiler reads the second under btree_recursion —
// every operation below is one definition against it.
//
// The label sits BETWEEN the subtrees rather than in front of them, so
// a node's three arguments stand in the order the tree draws them, and
// `btree_flatten` is then the identity on that order.
var BtreeData = family.DefineData(registry.DataEntry{
	Name:   "Btree",
	Type:   "btree",
	Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "btree_leaf"},
		{Name: "btree_node", Args: []string{"btree(A)", "A", "btree(A)"}},
	},
	// The four principles' registered names — the words the vars below
	// carry, so a session cites what this file spells.
	Principles: registry.DataPrinciples{
		Induction: "Induction",
		Recursion: "Recursion",
		Injective: "NodeInjective",
		Distinct:  "LeafNotNode",
	},
	// The universe's rows the derivations read: its recursion theorem
	// and its countable-family constructor (the schema), its node
	// constructor's injectivity (read for node's injectivity and for
	// leaf ≠ node), and 0 ≠ suc (the two tags differ).
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		peano.SucNotZero,
	},
})

// The four principles under chapter names — the names the door
// registers (Principles above), so `tree.LeafNotNode` is one name in Go
// and in a session.
var (
	// Induction — a property holding at leaf and preserved by node
	// holds of every tree: P(btree_leaf), (∀l a r. P(l) ∧ P(r) ⇒
	// P(btree_node(l, a, r))) ⊢ P(t).
	Induction = inductionThm{BtreeData.Induct}
	// Recursion — a function on trees is determined by its value at
	// leaf and its step at node, the step reading the values at both
	// subtrees.
	Recursion = recursionThm{BtreeData.Recursion}
	// NodeInjective — btree_node(l, a, r) = btree_node(l', a', r') exactly when the
	// three components agree.
	NodeInjective = nodeInjectiveThm{BtreeData.Inj}
	// LeafNotNode — btree_leaf ≠ btree_node(l, a, r).
	LeafNotNode = leafNotNodeThm{BtreeData.Distinct}
)

// BtreeSizeDef — how many labels a tree carries: none at a leaf, and one
// more than the two subtrees carry at a node.
var BtreeSizeDef = btreeSizeDefThm{family.Define(registry.DefEntry{
	Name:  "BtreeSizeDef",
	Key:   "prop_a27ce3899aa321f",
	Const: "btree_size",
	Type:  "btree(A) → num",
	Equations: []string{
		"btree_size(btree_leaf) = 0",
		"∀l:btree(A). ∀a:A. ∀r:btree(A). " +
			"    btree_size(btree_node(l, a, r)) = suc(btree_size(l) + btree_size(r))",
	},
})}

// BtreeMirrorDef — the tree reflected: a leaf is its own mirror, and a
// node's mirror swaps its subtrees, each mirrored in turn.
var BtreeMirrorDef = btreeMirrorDefThm{family.Define(registry.DefEntry{
	Name:  "BtreeMirrorDef",
	Key:   "prop_fe4a095fccf65455",
	Const: "btree_mirror",
	Type:  "btree(A) → btree(A)",
	Equations: []string{
		"btree_mirror(btree_leaf) = btree_leaf",
		"∀l:btree(A). ∀a:A. ∀r:btree(A). " +
			"    btree_mirror(btree_node(l, a, r)) = btree_node(btree_mirror(r), a, btree_mirror(l))",
	},
})}

// BtreeFlattenDef — the labels in the order the tree draws them: nothing at
// a leaf, and at a node the left subtree's labels, then the node's own,
// then the right subtree's. This is the bridge to `datatypes/list`, and
// the reason the label sits between the subtrees in node's arguments.
var BtreeFlattenDef = btreeFlattenDefThm{family.Define(registry.DefEntry{
	Name:  "BtreeFlattenDef",
	Key:   "prop_b7623fdf17aeca3c",
	Const: "btree_flatten",
	Type:  "btree(A) → list(A)",
	Equations: []string{
		"btree_flatten(btree_leaf) = nil",
		"∀l:btree(A). ∀a:A. ∀r:btree(A). " +
			"    btree_flatten(btree_node(l, a, r)) = list_append(btree_flatten(l), cons(a, btree_flatten(r)))",
	},
})}
