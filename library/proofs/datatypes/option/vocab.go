// vocab.go — the chapter's statement vocabulary.
//
// The chapter's alphabet is the type's two constructors, both
// polymorphic in the element type: `none`, the absent value, and
// `some`, which wraps a present one — the chapter's own definition
// (definitions.go), declared here by name, each type read off its
// mint. Everything else a statement here mentions is bound by the
// statement itself (the predicate an induction is run on, the values
// a recursion is specified by), so no domain table applies. The
// constructors are declared at the abstract letter; each occurrence in
// a statement instantiates independently, the binder annotations
// anchoring every letter.

package option

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var vocab = registry.NewVocabSpec(nil).
	OpsName("optionOps").
	Term("none"). // option(A)
	Term("some")  // A → option(A)

// Option is `option(A)` as a phantom of the typed term surface — the
// type-level twin of the chapter's carrier, declared beside its
// vocabulary per the phantom vocabulary's decentralization rule
// (ext/holtype_phantom.go). A signature over the chapter reads
// `Typed[Option[A]]` exactly as its statement reads `x:option(A)`; the
// typed-wrapper generator (gen_family) spells the type through it.
type Option[Elem ext.TypePhantom] struct{}

func (Option[Elem]) Reify() ext.HolType { return MakeType("option", ext.HolTypeOf[Elem]()) }
