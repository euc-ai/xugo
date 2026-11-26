// vocab.go — the chapter's statement vocabulary.
//
// Two alphabets, because this chapter's subject IS the boundary between
// them: ℕ's operations (which the text-DSL's default scope supplies on
// its own — `+ * nat_div nat_mod ≤ <` and the numerals) and the ℤ side, which
// has no default and must be declared. `&` in a statement text is the
// type-directed coercion ℕ → ℤ: the DSL builds `int_of_num` for it once
// the surrounding term is int-typed.
//
// Declaring the alphabet is what makes a text-form statement PARSE, and
// it is identical in every member, so the family installs the rows into
// each member's ParseScope (family.go's WithVocabSpec) rather than each
// proof re-typing a `ctx.Const` preamble. The term-BUILDING half is the
// surface rendered from the same rows (zz_vocab_gen.go), which a body
// calls only when it constructs witness terms.
//
// What is deliberately NOT declared: ℕ's own `+ * nat_div nat_mod ≤ <` and the
// numerals, which the text-DSL's default nat scope already supplies (a
// scope declaration would only shadow them with a second spelling of
// the same constant).

package int_embed

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name. The first
// five rows keep the established build surface: the embedding pair, the
// size, and the two ring operations a body constructs witness terms
// with.
var vocab = registry.NewVocabSpec(intvocab.Table()).
	OpsName("embedOps").
	Term("int_of_num"). // ℕ ↪ ℤ; spelled `&` in statement texts
	Term("num_of_int"). // the partial inverse, total on the nonnegatives
	Term("int_abs").
	Term("int_add").As("IntPlus").
	Term("int_mul").As("IntTimes").

	// Names this chapter's STATEMENTS carry. Three are operations whose
	// transport laws the chapter states and nothing here computes with —
	// the total difference ℕ's truncated one becomes and the two order
	// selectors. `int_neg`, `int_div` and `int_rem` are declared for the same
	// reason: claim texts name them, and
	// nothing builds them through a wrapper.
	//
	// `int_le` and `int_lt` are the exception on this list — proof
	// bodies DO build them, each re-typing
	// the relation locally. That is the drift the domain table exists to
	// prevent, and pointing those bodies at the IntLe/IntLt handles the
	// rows now render is the fix; it is recorded as an [arch-issue]
	// rather than done here because it touches every ordered claim in
	// the chapter.
	// `int_ge` and `int_gt` appear in exactly one statement — the
	// flipped-vocabulary reading of discreteness (int_embed.go's
	// DiscreteFlipped) — and nowhere else in the chapter.
	Term("int_le").
	Term("int_lt").
	Term("int_neg").
	Term("int_div").
	Term("int_rem").
	Term("int_sub").
	Term("int_max").
	Term("int_min").
	Term("int_ge").
	Term("int_gt")

// Embed is &n, the image of a natural in ℤ.
func (v *embedOps) Embed(n Term) *TermWrapper { return v.IntOfNum.Apply(n) }

// OfInt is num_of_int(x) — the natural x names, meaningful once x ≥ 0.
func (v *embedOps) OfInt(x Term) Term { return v.NumOfInt.Apply(x) }

// Abs is |x| on ℤ.
func (v *embedOps) Abs(x Term) Term { return v.IntAbs.Apply(x) }

// IntMul is x · y on ℤ.
func (v *embedOps) IntMul(x, y Term) Term { return v.IntTimes.Apply(x, y) }
