// vocab.go — the chapter's statement vocabulary.
//
// Every real_archimedean statement is written in the same alphabet: the
// two order relations, the ℕ→ℝ embedding that every headline names, the
// operations the statements apply to embedded literals, and the numeral
// tower `&0` / `&1` expand through (the NumeralsBundle row). The TYPES
// live in the ℝ domain's realvocab table; the rows below state WHICH
// names this chapter's statements spell — the family installs them into
// each member's ParseScope (family.go's WithVocabSpec), and the build
// surface members take with `v := ops(a.Ctx())` is rendered from the
// same rows (zz_vocab_gen.go).
//
// What the declaration buys is NOT parsing. The text-DSL already parses
// ℝ's infix surface — `+ - * / ≤ <` and the literal `&n` — but its metas
// for those constants are def-less, so a name has to be declared here
// before `Unfold` has a definition to expand and before a body can build
// a term at the right type. That is the same reason every ℝ chapter
// carries one of these files.
//
// The list grows with the chapter, one member at a time: a constant is
// named when a member states or builds it and never in advance — the
// Alphabet contract's own rule.

package real_archimedean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name.
//
// Three of them are what bodies BUILD with. `real_of_num` is the
// chapter's characteristic one — every headline says something about
// `&n` — and `real_sub` spells the shifted bound `M - &1` the
// completeness argument works with. `real_inv` joins them because the
// last member reasons about reciprocals of terms it has just named:
// building `real_inv(&n₀)` from the Skolem VALUE beats re-spelling the
// Skolem's own name in text, which is the corpus rule that claims over
// named quantities are constructed rather than spelled.
//
// `real_le` and `real_lt` are what the notation resolves to, and
// `real_mul` is spelled by the Archimedean headline and built by no
// body. Two names this chapter's statements DO use are absent from the
// list on purpose, because the DSL resolves each without a declaration:
// `+` and `/` parse scope-lessly to `real_add` and `real_div`.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("realOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_le").As("Le").
	Term("real_lt").As("Lt").
	Term("real_mul").As("Times").
	Term("real_of_num").As("OfNum").
	Term("real_sub").As("Sub").
	Term("real_inv").As("Inv")

// Invert is the reciprocal real_inv(x).
func (v *realOps) Invert(x Term) Term { return v.Inv.Apply(x) }

// Sub1 is x - &1, the shifted bound the completeness argument works
// with: it is what a least upper bound cannot also be an upper bound of.
func (v *realOps) Sub1(x Term) Term { return v.Sub.Apply(x, v.Lit(1)) }
