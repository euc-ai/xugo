// vocab.go — the chapter's vocabulary: `complex` as a phantom of the
// typed term surface. The chapter declares no VocabSpec rows, so the
// carrier's phantom is the whole file.

package complex_field

import "github.com/euc-ai/xugo/ext"

// Complex is `complex` as a phantom of the typed term surface — the
// type-level twin of the chapter's carrier, declared beside it per the
// phantom vocabulary's decentralization rule (ext/holtype_phantom.go).
// A signature over the chapter reads `Typed[Complex]` exactly as its
// statement reads `z:complex`; the typed-wrapper generator (gen_family)
// spells the type through it.
type Complex struct{}

func (Complex) Reify() ext.HolType { return ext.MakeType("complex") }
