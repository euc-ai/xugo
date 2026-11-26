// vocab.go — the chapter's statement vocabulary.
//
// The chapter's alphabet is its own definitions (definitions.go),
// declared here by name with each type read off its mint: the two
// constructors `btree_leaf` and `btree_node`, and the operations `btree_size`, `btree_mirror`
// and `btree_flatten`. The LIST vocabulary a flattened tree is stated in —
// `nil`, `cons`, `list_append`, `list_length`, `list_reverse` — is declared here as
// HANDLES the bodies build with; `datatypes/list` owns the mints and
// this chapter only reads them. A statement would parse without any of
// these rows (a stated name resolves through the mint) — a row buys a
// pinned instance or a handle, nothing else (chapter_constitution.md
// §Structure, "What a row buys").

package tree

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var vocab = registry.NewVocabSpec(nil).
	OpsName("treeOps").
	Term("btree_leaf").    // btree(A)
	Term("btree_node").    // btree(A) → A → btree(A) → btree(A)
	Term("btree_size").    // btree(A) → num
	Term("btree_mirror").  // btree(A) → btree(A)
	Term("btree_flatten"). // btree(A) → list(A)
	Term("nil").           // the list side, minted by datatypes/list
	Term("cons").
	Term("list_append").
	Term("list_length").
	Term("list_reverse")

// Btree is `btree(A)` as a phantom of the typed term surface — the
// type-level twin of the chapter's carrier, declared beside its
// vocabulary per the phantom vocabulary's decentralization rule
// (ext/holtype_phantom.go). A signature over the chapter reads
// `Typed[Btree[A]]` exactly as its statement reads `t:btree(A)`; the
// typed-wrapper generator (gen_family) spells the type through it.
type Btree[Elem ext.TypePhantom] struct{}

func (Btree[Elem]) Reify() ext.HolType {
	return MakeType("btree", ext.HolTypeOf[Elem]())
}
