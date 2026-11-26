// vocab.go — the statement vocabulary the chapter's members are
// written in. The chapter's constants are defined in definitions.go.

package carrier

import (
	"github.com/euc-ai/xugo/core"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// The element type letter and the carrier shape every statement is
// written over.
var (
	elemType    = MakeVarType("A")
	carrierType = MakeFun(NumType, elemType)
)

// constMeta fetches an already-registered constant's canonical meta —
// the one every other proof reads, never a look-alike.
func constMeta(name string) core.ConstTermMeta {
	meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(name))
	if !ok || meta.IsZero() {
		panic(
			"carrier: const " + name + " is not registered — the chapter's definitional layer has not been loaded")
	}
	return meta
}

// vocab is the chapter alphabet as data: the minted constants a landed
// member states, each declared polymorphically — the element letter A
// is the chapter's own, so no row pins an instance. junk, which the
// members state, is declared by name.
var vocab = registry.NewVocabSpec(nil).
	Term("junk").
	Term("tuple").
	Term("tuple_cat").
	Term("tuple_take").
	Term("tuple_drop")
