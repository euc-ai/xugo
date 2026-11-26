// vocab.go — the chapter's statement vocabulary: the transitive and the
// reflexive–transitive closure this chapter mints, and the one property
// from `relations/equivalence` its statements read.

package closure

import (
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name, each typed
// by its mint.
var vocab = registry.NewVocabSpec(nil).
	OpsName("closureOps").
	// (A → A → bool) → A → A → bool
	Term("transitive_closure").As("TransitiveClosure").
	// (A → A → bool) → A → A → bool
	Term("reflexive_transitive_closure").
	// (A → A → bool) → bool — relations/equivalence's.
	Term("transitive")
