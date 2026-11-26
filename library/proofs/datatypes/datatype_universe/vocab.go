// vocab.go — the chapter's vocabulary: `recspace(A)` as a phantom of
// the typed term surface. The chapter declares no VocabSpec rows, so
// the carrier's phantom is the whole file.

package datatype_universe

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
)

// Recspace is `recspace(A)` as a phantom of the typed term surface —
// the type-level twin of the chapter's carrier, declared beside it per
// the phantom vocabulary's decentralization rule
// (ext/holtype_phantom.go). A signature over the chapter reads
// `Typed[Recspace[A]]` exactly as its statement reads `r:recspace(A)`;
// the typed-wrapper generator (gen_typed_thms) spells the type through
// it.
type Recspace[Elem ext.TypePhantom] struct{}

func (Recspace[Elem]) Reify() ext.HolType { return MakeType("recspace", ext.HolTypeOf[Elem]()) }
