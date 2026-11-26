// vocab.go — the chapter's vocabulary: `permutation(A)` as a phantom
// of the typed term surface. The chapter declares no VocabSpec rows,
// so the carrier's phantom is the whole file.

package symmetric_group

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// Permutation is `permutation(A)` as a phantom of the typed term
// surface — the type-level twin of the chapter's carrier, declared
// beside it per the phantom vocabulary's decentralization rule
// (ext/holtype_phantom.go). A signature over the chapter reads
// `Typed[Permutation[A]]` exactly as its statement reads
// `p:permutation(A)`; the typed-wrapper generator (gen_family) spells
// the type through it.
type Permutation[Elem ext.TypePhantom] struct{}

func (Permutation[Elem]) Reify() ext.HolType {
	return MakeType(
		"permutation", ext.HolTypeOf[Elem]())
}
