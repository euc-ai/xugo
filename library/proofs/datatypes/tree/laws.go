// laws.go — the chapter's theory: what the three operations do to each
// other.
//
// Two subjects, and they meet. Reflection is the one that changes
// nothing that can be counted — not the tree, when done twice, and not
// the number of labels, ever. Flattening is the one that leaves the
// chapter, carrying a tree into `datatypes/list`, and the two laws
// about it are where that crossing is paid for: the count survives the
// reading, and a reflected tree reads out backwards.
//
// Every proof is an induction over the two constructors. A step grants
// a hypothesis PER SUBTREE — that is what a two-successor datatype
// costs and what it buys — and in the first three the two arrive
// ambient, so a rewrite ladder reaches its close without ever naming
// them; the fourth takes both in hand, as the branch hands them over.

package tree

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
)

// MirrorMirror — mirroring twice restores the tree, because the swap is
// undone at every node. By induction on t: a leaf is its own mirror, and
// at btree_node(l, a, r) the mirror clause hangs btree_mirror(r) on the left and
// btree_mirror(l) on the right, so mirroring again returns the two subtrees to
// their own sides, each carrying a second mirror. The two hypotheses the
// step grants — one per subtree — fold those away.
var MirrorMirror = mirrorMirrorThm{family.Add(registry.ProofEntry{
	Name: "MirrorMirror",
	Key:  "prop_2aca5391c6a39281",
	Build: family.Theorem("∀t:btree(A). btree_mirror(btree_mirror(t)) = t",
		func(a *Argument) {
			a.Induct("t")
			a.Base(
				"at leaf: a leaf is its own mirror, so both sides read btree_leaf",
				Simp(Fwd(BtreeMirrorDef)),
				TrivialNormalized())
			a.Step(
				"at btree_node(l, a, r): the second mirror undoes the "+
					"swap, and the hypotheses fold each twice-mirrored subtree",
				Simp(Fwd(BtreeMirrorDef)),
				Basic())
		}),
})}

// SizeMirror — a tree and its mirror image carry the same number of
// labels. By induction on t: a leaf is its own mirror. At btree_node(l, a, r)
// mirroring puts the mirrored subtrees on opposite sides, so the size
// clause reads the node as one more than they carry between them, and
// the two hypotheses the step grants — one per subtree — replace each
// mirrored subtree's count by the subtree's own. The sum left standing
// is the node's own summed the other way round: the swap is why
// commutativity of addition appears, and it is the whole arithmetic
// content of the theorem.
var SizeMirror = sizeMirrorThm{family.Add(registry.ProofEntry{
	Name: "SizeMirror",
	Key:  "prop_38f2b0e3aa572ef9",
	Build: family.Theorem("∀t:btree(A). btree_size(btree_mirror(t)) = btree_size(t)",
		func(a *Argument) {
			a.Induct("t")
			a.Base(
				"at leaf: a leaf is its own mirror, so both sides read btree_size(btree_leaf)",
				Simp(Fwd(BtreeMirrorDef)),
				Refl())
			a.Step(
				"at btree_node(l, a, r): the hypotheses fold the mirrored subtrees "+
					"away, and commutativity of addition turns the sum back around",
				Simp(Fwd(BtreeMirrorDef), Fwd(BtreeSizeDef), Fwd(nat_arith.AddSym)),
				Basic())
		}),
})}

// LengthFlatten — the tree's size is exactly the length of its
// flattening: reading a tree out into a list is a faithful count, and
// that is where the chapter's own recursion and the list theory's are
// made to agree.
//
// By induction on t. A leaf flattens to the empty list, whose length is
// the leaf's own size, 0. At btree_node(l, a, r) the flattening is the left
// subtree's labels, then the node's own, then the right subtree's, so
// its length is list_length(btree_flatten(l)) + suc(list_length(btree_flatten(r))); AddSuc
// lifts that lone successor — the node's own label — out of the sum,
// leaving one more than the two subtrees contribute on either side,
// which is what the two hypotheses say.
var LengthFlatten = lengthFlattenThm{family.Add(registry.ProofEntry{
	Name: "LengthFlatten",
	Key:  "prop_cf3cda75e1bc4e33",
	Build: family.Theorem("∀t:btree(A). list_length(btree_flatten(t)) = btree_size(t)",
		func(a *Argument) {
			a.Induct("t")
			a.Base(
				"at leaf: nothing is read out, and the empty list has length 0 — the leaf's size",
				Simp(Fwd(BtreeFlattenDef), Fwd(list.ListLengthDef), Fwd(BtreeSizeDef)),
				Refl())
			a.Step(
				"at btree_node(l, a, r): LengthAppend splits the concatenation's "+
					"length, and AddSuc lifts the node's own label out of the sum",
				Simp(
					Fwd(BtreeFlattenDef),
					Fwd(BtreeSizeDef),
					Fwd(list.LengthAppend),
					Fwd(list.ListLengthDef),
					Fwd(nat_arith.AddSuc)),
				Basic())
		}),
})}

// FlattenMirror — reading a mirrored tree out is reading the tree out
// backwards: the swap the mirror performs at every node and the
// reversal of a list are the same operation, seen on the two sides of
// `btree_flatten`.
//
// By induction on t. A leaf flattens to the empty list, which is its
// own reversal. At btree_node(l, a, r) the mirror hangs the right subtree on
// the left, so the mirrored flattening leads with the right subtree's
// labels — exactly where reversing the concatenation puts them. The
// step that carries the weight is on the reversal's side: list_reverse sends
// the node's own label to the far end of a singleton, and only once
// associativity is read right to left does that singleton come to stand
// in front of the reversed left subtree, where list_append's own clauses
// absorb it and the label crosses back to the head. The two hypotheses
// then fold each mirrored subtree into its reversal.
var FlattenMirror = flattenMirrorThm{family.Add(registry.ProofEntry{
	Name: "FlattenMirror",
	Key:  "prop_cfc8d285e03f0baf",
	Build: family.Theorem("∀t:btree(A). "+
		"    btree_flatten(btree_mirror(t)) = list_reverse(btree_flatten(t))",
		func(a *Argument) {
			a.Induct("t")
			a.Base(
				"at leaf: nothing is read out either way, and the empty list is its own reversal",
				Simp(Fwd(BtreeMirrorDef), Fwd(BtreeFlattenDef), Fwd(list.ListReverseDef)),
				Refl())
			a.Step(
				"at btree_node(l, a, r): the mirror leads with the right "+
					"subtree, which is where reversing the concatenation puts it",
				// The only proof in the chapter that takes its two
				// hypotheses in hand: the ladder below leaves the
				// reversal's side needing them in a definite order, the
				// right subtree's first.
				func(b *Argument, leftSubtree, rightSubtree Fact) {
					b.Show(
						"re-bracketing lets list_append absorb the singleton, and "+
							"the hypotheses fold each mirrored subtree into its reversal",
						Simp(
							Fwd(BtreeMirrorDef),
							Fwd(BtreeFlattenDef),
							Fwd(list.ReverseAppend),
							Fwd(list.ListReverseDef),
							Rev(list.AppendAssoc),
							Fwd(list.ListAppendDef)),
						rightSubtree.Rw(),
						leftSubtree.Rw(),
						Basic())
				})
		}),
})}
