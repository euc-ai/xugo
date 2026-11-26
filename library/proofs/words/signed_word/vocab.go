// vocab.go — the statement vocabulary the chapter's members are
// written in. The chapter's constants are defined in definitions.go.

package signed_word

import (
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data: the alphabet the chapter's
// statement and proof texts are written in — the two minted readings,
// the val-face operations the ring and complement rows relate them to,
// the bits face the top-bit rows read, and the ℤ heads the reading
// lands in. Every row reads its type off the constant's mint. ℤ's
// OPERATORS need no row — the DSL dispatches `+ - * < ≤` and the
// congruence `≡ (mod ·)` on operand type through fixed const metas —
// and `int_of_num` is what lets `&` steer to ℤ in an ordinary text.
// This chapter's statement texts spell the coercion out everywhere
// instead: a bare `&` needs an int-typed neighbour, never steers under
// a COND, and silently lands in ℝ when both sides of a comparison are
// coercions — the spelled form has no such modes.
//
// The vocabulary is the chapter's CERTIFIED statement set — every name
// some gate-certified frozen statement uses, declared when the
// statements were frozen; nothing enters on speculation beyond them.
var vocab = registry.NewVocabSpec(nil).
	Defined("int_of_word").
	Defined("word_of_int").
	Defined("word_add"). // machine_word's mints, read through their metas
	Defined("word_mul").
	Defined("word_sub").
	Defined("word_neg").
	Defined("word_not").
	Defined("word_bit").
	Term("nat_pow"). // ℕ's
	Term("nat_mod").
	Defined("bit_value").
	Term("int_of_num"). // ℤ's
	Term("num_of_int").
	Term("int_pow").
	Term("int_rem")
