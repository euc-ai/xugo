// vocab.go — the chapter's statement vocabulary.
//
// The chapter's own constant, `comm_monoid`, is minted by its
// definition member and resolves in every statement text from then
// on. What the vocabulary declares is the fold mechanism's reading of
// the same object — `monoidal_op(op)` and its Hilbert-choice identity
// `neutral_elem(op)` — which the bridge members state in both directions.
// Both rows spell their type at the type variable A, declaration-only:
// no body builds with them.

package comm_monoid

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name. The
// chapter has no domain table; each row spells its type as a phantom.
var vocab = registry.NewVocabSpec(nil).
	Spelled("monoidal_op", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.Bool]]).
	Spelled("neutral_elem", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.A]])
