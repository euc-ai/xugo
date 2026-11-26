// vocab.go — the chapter's statement vocabulary.
//
// The chapter spells three minted predicates — its own `comm_ring` and
// the two it is built from, `abelian_group` and `comm_monoid` — which
// resolve without declaration once minted, and the fold mechanism's
// two names, `monoidal_op` and `neutral_elem`, which the members deriving the
// ring's two fold instances state. Both rows spell their type at the
// chapter's letter, declaration-only.

package comm_ring

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name. The
// chapter has no domain table; each row spells its type as a phantom.
var vocab = registry.NewVocabSpec(nil).
	Spelled("monoidal_op", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.Bool]]).
	Spelled("neutral_elem", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.A]])
