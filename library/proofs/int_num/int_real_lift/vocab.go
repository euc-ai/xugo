// vocab.go — the chapter's statement vocabulary.
//
// ℤ's operations, which no default DSL scope knows: the text-DSL
// supplies ℕ's `+ * ≤ <` and the numerals on its own, but a statement
// about int_add must name `int_add`. Declaring the alphabet is what
// makes a text-form statement PARSE, and it is identical in every
// member, so the family installs it into each member's ParseScope
// (family.go's WithVocabSpec) rather than each proof re-typing a
// `ctx.Const` preamble. The types come from the ℤ domain's one
// NAME → type table (int_num/internal/intvocab); the rows below state
// WHICH names this chapter's statements spell. No member builds a term
// programmatically — the chapter states and lifts — so the build
// surface rendered from these rows (zz_vocab_gen.go) waits unused.
//
// `&` in a statement text is the type-directed coercion ℕ → ℤ: the DSL
// builds `int_of_num` for it once the surrounding term is int-typed,
// which is why `&0 + x = x` parses with x:int.

package int_real_lift

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(intvocab.Table()).
	Term("int_of_num"). // ℕ ↪ ℤ; spelled `&` in statement texts
	Term("int_add").
	Term("int_mul").
	Term("int_sub").
	Term("int_abs").
	Term("int_sgn").
	Term("int_le").
	Term("int_lt").
	Term("int_neg").
	// The fold mechanism's two names, which the chapter's fold facts
	// state: `monoidal_op(op)` and its choice-named identity `neutral_elem(op)`,
	// at the carrier-free letter — declaration-only, no body builds with
	// them.
	Spelled("monoidal_op", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.Bool]]).
	Spelled("neutral_elem", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.A]])
