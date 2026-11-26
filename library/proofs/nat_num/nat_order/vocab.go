// vocab.go — the chapter's statement vocabulary.
//
// Every nat_order statement is written in the same alphabet: the two
// order relations, the ℕ operations they are stated over, and the
// numeral tower. The TYPES live in the ℕ domain's natvocab table; the
// rows below state WHICH names this chapter's statements spell — the
// family installs them into each member's ParseScope
// (family.go's WithVocabSpec), and the build surface members take with
// `v := ops(a.Ctx())` is rendered from the same rows (zz_vocab_gen.go).
// OrderCalc, ℕ's ≤-chain kit, is built on the same alphabet's Le.

package nat_order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("orderOps").
	Term("suc").As("SucOp"). // the Suc shorthand below builds suc(a)
	Term("_0").As("Zero").
	Term("+").As("Plus").
	Term("*").As("Times").
	Term("<=").As("Le").
	Term("<").As("Lt").
	Term("bit1").As("Bit1Op")

// Term-building shorthands, so a witness list reads as arithmetic
// rather than as applications.

// Add is a + b.
func (v *orderOps) Add(a, b Term) *TermWrapper { return v.Plus.Apply(a, b) }

// Mul is a · b.
func (v *orderOps) Mul(a, b Term) Term { return v.Times.Apply(a, b) }

// Suc is suc(a).
func (v *orderOps) Suc(a Term) *TermWrapper { return v.SucOp.Apply(a) }

// LessEq is the order atom a ≤ b.
func (v *orderOps) LessEq(a, b Term) Term { return v.Le.Apply(a, b) }

// LessThan is the strict order atom a < b.
func (v *orderOps) LessThan(a, b Term) Term { return v.Lt.Apply(a, b) }

// OrderCalc is ℕ's instance of the ≤-chain kit (proof.CalcOrder): a
// chain a ≤ t₁ ≤ … ≤ b of legs, each with its own justification, whose
// transitivity steps are LessEqTrans, read by the consuming member as
// its own dependency. It is held here because ℕ's order is this
// chapter's subject; real_order_ring.OrderCalc is ℝ's, and says what
// the kit does with `=` links (Eq stays nil: ℕ's equality is the
// kernel's, and a chain mixing `=` with `≤` is CalcLeibniz).
func OrderCalc(ctx *Script) proof.CalcOrder {
	le := vocab.Handle(ctx, "Le")
	return proof.CalcOrder{
		Le:      func(x, y Term) Prop { return MakeProp(le.Apply(x, y)) },
		LeTrans: LessEqTrans,
	}
}
