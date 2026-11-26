// vocab.go — the chapter's statement vocabulary.
//
// Every real_order_field statement is written in the same alphabet: the
// order and its strict part, the operations its headlines name, the
// ℕ→ℝ embedding, and the numeral tower the embedded literals `&0` and
// `&1` expand through (the NumeralsBundle row). The TYPES live in the ℝ
// domain's realvocab table; the rows below state WHICH names this
// chapter's statements spell — the family installs them into each
// member's ParseScope (family.go's WithVocabSpec), and the build
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
// The list grew with the chapter, one tier at a time, because a
// constant is named when a member states or builds it and never in
// advance — the Alphabet contract's own rule. What is below is where
// that ended.

package real_order_field

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name.
//
// The bodies BUILD with four of them, and the chapter ended there:
// `real_inv` (some of the witnesses are inverses), `real_div` (others
// are quotients), `real_add`, which the density witness needs to spell
// its denominator, and `real_of_num`, which Lit reaches through.
// `real_le` and `real_lt` are what the notation resolves to and what
// `Unfold` names, and `real_mul` is spelled by statements but built by
// none.
//
// `real_neg` and `real_sub` are absent: no headline in the chapter's
// plan and no cited dep statement mentions either. The sign work this
// chapter does runs through cancellation and the inverse, not through
// negation.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("realOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_le").As("Le").
	Term("real_lt").As("Lt").
	Term("real_mul").As("Times").
	Term("real_inv").As("Inv").
	Term("real_div").As("Div").
	Term("real_add").As("Plus").
	Term("real_of_num").As("OfNum")

// Term-building shorthands, so a witness list reads as algebra rather
// than as applications.

// Invert is inv a.
func (v *realOps) Invert(a Term) Term { return v.Inv.Apply(a) }

// Quot is a / b.
func (v *realOps) Quot(a, b Term) Term { return v.Div.Apply(a, b) }

// Add is a + b.
func (v *realOps) Add(a, b Term) Term { return v.Plus.Apply(a, b) }
