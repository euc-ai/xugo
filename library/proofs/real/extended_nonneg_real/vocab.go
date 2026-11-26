// vocab.go — the chapter's vocabulary: `extended_nonneg_real` as a
// phantom of the typed term surface. The chapter declares no VocabSpec
// rows, so the carrier's phantom is the whole file.

package extended_nonneg_real

import "github.com/euc-ai/xugo/ext"

// ExtendedNonnegReal is `extended_nonneg_real` as a phantom of the typed
// term surface — the type-level twin of the chapter's carrier, declared
// beside its mint. A signature over the chapter reads
// `Typed[ExtendedNonnegReal]` exactly as its statement reads
// `x:extended_nonneg_real`.
type ExtendedNonnegReal struct{}

func (ExtendedNonnegReal) Reify() ext.HolType { return ext.MakeType("extended_nonneg_real") }
