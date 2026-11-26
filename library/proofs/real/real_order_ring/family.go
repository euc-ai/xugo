// family.go — the real_order_ring family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars (`var LessEqRefl =
// family.Add(...)`); they never call InstallCNFCache — the replay
// harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=<real_order_ring.MEMBER> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_order_ring go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path, and the base name fails `no such family`.

package real_order_ring

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

//go:embed real_order_ring.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_order_ring/real_order_ring.cnf.pb from
// it, and the registered entry prefix is the name's last segment
// (`real_order_ring.<Member>`). The vocabulary (vocab.go) is the
// chapter's statement alphabet, installed into every member's
// ParseScope before its first section.
var family = registry.NewFamily("real/real_order_ring", familyCNF).WithVocabSpec(vocab)

// OrderCalc is ℝ's instance of the ≤-chain kit: an estimate
//
//	a ≤ t₁ ≤ … ≤ b
//
// spelled as one leg per link, each carrying its own justification,
// with the transitivity groundings computed from the leg terms
// (proof.CalcOrder). Every chapter whose argument walks ℝ's order reads
// it here — a bound carried through an induction, an estimate on a
// sum — and reads real_construction.LessEqTrans through its own script exactly as
// it would to ground the transitivity by hand: the kit spares a
// consumer the local and the tuples, and the read is the consumer's
// dep.
//
// Exported for the reason tower/real_construction exports AddAC: ownership. The
// certificate a ≤-chain folds through is the order's transitivity, and
// ℝ's order is this chapter's subject, so an instance held by a
// consumer chapter would be one over a law it does not own — and,
// unexported there, one the next consumer could not borrow.
//
// Only the order half is certified. ℝ's equality is the kernel's own,
// so a chain that mixes `=` links with `≤` ones is CalcLeibniz, which
// rewrites with the equation, certifies nothing for it, and REFUSES a
// kit that supplies Eq. Eq, EqTrans and EqToLe therefore stay nil: an
// all-≤ chain and a Leibniz chain both run, and a .Calc leg tagged
// EqLeg panics at construction naming the missing Eq — the signal that
// the chain wanted CalcLeibniz, not a certificate for `=`.
func OrderCalc(ctx *Script) proof.CalcOrder {
	le := vocab.Handle(ctx, "Le")
	return proof.CalcOrder{
		Le:      func(x, y Term) Prop { return MakeProp(le.Apply(x, y)) },
		LeTrans: real_construction.LessEqTrans,
	}
}
