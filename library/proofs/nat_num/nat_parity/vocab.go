// vocab.go — the chapter's statement vocabulary.
//
// It holds what the LANDED statements are written in and grows with
// them: the two predicates the chapter is about, the successor and zero
// the recursion defining them runs on, the exponentiation and
// multiplication the homomorphism laws state, and the `nat_mod` the residue
// laws relate parity to. `nat_div` and `<` come with `nat_mod` rather than with
// a statement — no headline names either, but the residue proofs split
// a number into a quotient times the divisor plus a remainder, and then
// bound that remainder, so their bodies build both.
//
// `+` and `*` parse without being declared — the text parser supplies
// ℕ's arithmetic. `*` has a row anyway because a body that BUILDS a
// product needs a handle on it, which is what the generated surface
// provides: `ops` returns the vocabulary as programmable terms, so an
// induction step can hand its witness the term it already holds instead
// of re-spelling it as a string.
//
// nat_even and nat_odd are IMPORTED constants: the chapter re-derives their
// defining equations (nat_parity.go) but does not mint the names, so
// declaring them hands back the same metas every other consumer reads.
// Both are at `num → bool` — unrelated to the higher-arity ∃-bound nat_even
// and nat_odd the mints in nat_parity.go quantify over.
//
// The TYPES live in the ℕ domain's natvocab table; the rows below state
// WHICH names this chapter's statements spell — the family installs
// them into each member's ParseScope (family.go's WithVocabSpec), and
// the build surface members take with `v := ops(a.Ctx())` is rendered
// from the same rows (zz_vocab_gen.go).

package nat_parity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/internal/natvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(natvocab.Table()).
	OpsName("parityOps").
	Term("*").As("Times").
	Term("nat_pow").
	Term("suc").As("SucOp"). // the Suc shorthand below builds suc(a)
	Term("nat_even").        // the shape lemma's induction splits on it
	Term("nat_div").
	Term("nat_mod").
	Term("<").As("Lt").
	Term("nat_odd"). // stated by every odd headline; no body applies it
	Term("_0").As("Zero")

// Mul is a · b.
func (v *parityOps) Mul(a, b Term) Term { return v.Times.Apply(a, b) }

// Exp is aᵇ.
func (v *parityOps) Exp(a, b Term) Term { return v.NatPow.Apply(a, b) }

// Suc is suc(a).
func (v *parityOps) Suc(a Term) *TermWrapper { return v.SucOp.Apply(a) }

// Even is the atom nat_even(a).
func (v *parityOps) Even(a Term) *TermWrapper { return v.NatEven.Apply(a) }

// Div is nat_div(a, b), the quotient.
func (v *parityOps) Div(a, b Term) Term { return v.NatDiv.Apply(a, b) }

// Mod is nat_mod(a, b), the remainder.
func (v *parityOps) Mod(a, b Term) *TermWrapper { return v.NatMod.Apply(a, b) }

// LessThan is the order atom a < b.
func (v *parityOps) LessThan(a, b Term) Term { return v.Lt.Apply(a, b) }
