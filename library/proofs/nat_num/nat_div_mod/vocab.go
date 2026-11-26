// vocab.go — the chapter's statement vocabulary.
//
// Every nat_div_mod statement is written in the same alphabet: the two
// division operators, the ℕ operations a quotient-remainder equation is
// written in, and the order relations the remainder bound needs. The
// TYPES live in the ℕ domain's natvocab table; the rows below state
// WHICH names this chapter's statements spell — the family installs
// them into each member's ParseScope (family.go's WithVocabSpec), and
// the build surface members take with `v := ops(a.Ctx())` is rendered
// from the same rows (zz_vocab_gen.go).

package nat_div_mod

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("divmodOps").
	Term("suc").As("SucOp"). // the Suc shorthand below builds suc(a)
	Term("_0").As("Zero").
	Term("+").As("Plus").
	Term("*").As("Times").
	Term("-").As("Minus").
	Term("nat_div").
	Term("nat_mod").
	Term("<=").As("Le").
	Term("<").As("Lt")

// Term-building shorthands, so a witness list reads as arithmetic
// rather than as applications.

// Add is a + b.
func (v *divmodOps) Add(a, b Term) *TermWrapper { return v.Plus.Apply(a, b) }

// Mul is a · b.
func (v *divmodOps) Mul(a, b Term) *TermWrapper { return v.Times.Apply(a, b) }

// Sub is a − b, truncated at zero as everywhere on ℕ.
func (v *divmodOps) Sub(a, b Term) Term { return v.Minus.Apply(a, b) }

// Suc is suc(a).
func (v *divmodOps) Suc(a Term) Term { return v.SucOp.Apply(a) }

// LessEq is the order atom a ≤ b.
func (v *divmodOps) LessEq(a, b Term) Term { return v.Le.Apply(a, b) }

// LessThan is the order atom a < b.
func (v *divmodOps) LessThan(a, b Term) Term { return v.Lt.Apply(a, b) }

// Div is nat_div(a, b), the quotient.
func (v *divmodOps) Div(a, b Term) *TermWrapper { return v.NatDiv.Apply(a, b) }

// Mod is nat_mod(a, b), the remainder.
func (v *divmodOps) Mod(a, b Term) *TermWrapper { return v.NatMod.Apply(a, b) }
