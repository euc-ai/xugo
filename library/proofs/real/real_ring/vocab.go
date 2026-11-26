// vocab.go — the chapter's statement vocabulary.
//
// Every real_ring statement is written in the same alphabet: ℝ's four
// operations, the ℕ→ℝ embedding, and the numeral tower the embedded
// literals `&0` / `&1` expand through (the NumeralsBundle row). The
// TYPES live in the ℝ domain's realvocab table; the rows below state
// WHICH names this chapter's statements spell — the family installs
// them into each member's ParseScope (family.go's WithVocabSpec), and
// the build surface members take with `v := ops(a.Ctx())` is rendered
// from the same rows (zz_vocab_gen.go).
//
// real_inv earns its place even though no ring statement mentions it:
// the integral-domain argument at the top of the chapter runs through
// ℝ's multiplicative-inverse axiom, and a body that names that fact
// parses its statement here.

package real_ring

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/internal/realvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name. The
// CoerceDomain row makes an unanchored `&` ℝ by declaration, not by
// global default.
var vocab = registry.NewVocabSpec(realvocab.Table()).
	OpsName("realOps").
	CoerceDomain(RealDomain).
	Embed(realvocab.NumeralsBundle).
	Term("real_add").As("Plus").
	Term("real_mul").As("Times").
	Term("real_sub").As("Minus"). // binary real_sub
	Term("real_neg").As("Neg").
	Term("real_of_num").As("OfNum"). // what Lit applies
	Term("real_inv").As("Inv").      // built by MulEqZero only
	// The fold mechanism's two names, which the chapter's fold facts
	// state: `monoidal_op(op)` and its choice-named identity `neutral_elem(op)`,
	// at the carrier-free letter — declaration-only, no body builds with
	// them.
	Spelled("monoidal_op", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.Bool]]).
	Spelled("neutral_elem", ext.HolTypeOf[ext.Fun[ext.Op[ext.A], ext.A]])

// Term-building shorthands, so a witness list reads as algebra rather
// than as applications.

// Add is a + b.
func (v *realOps) Add(a, b Term) *TermWrapper { return v.Plus.Apply(a, b) }

// Mul is a · b.
func (v *realOps) Mul(a, b Term) *TermWrapper { return v.Times.Apply(a, b) }

// Negate is -a.
func (v *realOps) Negate(a Term) Term { return v.Neg.Apply(a) }
