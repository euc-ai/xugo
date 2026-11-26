// vocab.go — the chapter's statement vocabulary.
//
// Every nat_arith statement is written in the same alphabet: the recursive
// operations `+`, `*`, `nat_pow`, `factorial` and the numeral tower. The order
// relations are deliberately NOT here — nat_arith sits below nat_order,
// and the order-entangled chapters (nat_order's bounds tier,
// nat_monus, nat_div_mod) own their own alphabets. The TYPES live in
// the ℕ domain's natvocab table; the rows below state WHICH names this
// chapter's statements spell — the family installs them into each
// member's ParseScope (family.go's WithVocabSpec), and the build
// surface members take with `v := ops(a.Ctx())` is rendered from the
// same rows (zz_vocab_gen.go).

package nat_arith

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("numOps").
	Term("suc").As("SucOp"). // the Suc shorthand below builds suc(a)
	Term("_0").As("Zero").
	Term("+").As("Plus").
	Term("*").As("Times").
	Term("nat_pow").
	Term("bit1").As("Bit1Op").
	// Headlines state both — `factorial(0) = 1 ∧ …`, `bit0(n) = n + n` —
	// but no body builds with either.
	Term("factorial").
	Term("bit0")

// Term-building shorthands, so a witness list reads as arithmetic
// rather than as applications.

// Add is a + b.
func (v *numOps) Add(a, b Term) *TermWrapper { return v.Plus.Apply(a, b) }

// Mul is a · b.
func (v *numOps) Mul(a, b Term) Term { return v.Times.Apply(a, b) }

// Suc is suc(a).
func (v *numOps) Suc(a Term) Term { return v.SucOp.Apply(a) }
