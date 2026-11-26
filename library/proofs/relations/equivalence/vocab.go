// vocab.go — the chapter's statement vocabulary: the properties a
// binary relation can have, the class of a point, the equivalence on a
// set with its restriction, quotient and lift, a partition of the type
// and the relation it induces — all defined here. A statement
// mentions nothing else that is not bound by the statement itself or
// minted by the set chapters.

package equivalence

import (
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name, each typed
// by its mint.
var vocab = registry.NewVocabSpec(nil).
	OpsName("equivalenceOps").
	Term("reflexive").         // (A → A → bool) → bool
	Term("symmetric").         // (A → A → bool) → bool
	Term("symmetric_on").      // set(A) → (A → A → bool) → bool
	Term("transitive").        // (A → A → bool) → bool
	Term("equivalence").       // (A → A → bool) → bool
	Term("equivalence_class"). // (A → A → bool) → A → set(A)
	Term("equivalence_on").    // (A → A → bool) → set(A) → bool
	Term("relation_on").       // set(A) → (A → A → bool) → A → A → bool
	Term("quotient_on").       // set(A) → (A → A → bool) → set(set(A))
	Term("respects_on").       // set(A) → (A → A → bool) → (A → B) → bool
	Term("induced_map").       // (A → B) → set(A) → B
	Term("set_partition").     // set(set(A)) → bool
	Term("same_block")         // set(set(A)) → A → A → bool
