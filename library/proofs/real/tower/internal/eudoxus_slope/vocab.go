// vocab.go — the chapter's statement vocabulary as data, plus the
// term-building helpers every slope estimate is written in.
//
// The alphabet it installs is CONSTS only. A Free row can also carry a
// chapter's recurring free variables, but slope has almost none to
// carry: nearly every ctx.Var in the package is there to obtain the
// *TermWrapper its body builds terms with, and no ParseScope
// registration supplies that. The Skolem names are per-statement in
// any case — `x_0` is the subscript normal form of whichever ∀x heads
// that member's own statement, indexed past what is already in scope —
// and `d_0` lands at three types across the family (num in
// `lipschitz`, num→num in `LessEqExists`, nadd in `LessEqMulLeft`),
// the one name that could not be hoisted even if hoisting paid.
// Measured and declined.
//
// A body holds the handles as a local (`v := ops(ctx)`) and passes it
// to whatever branch functions it extracts; the family installs the
// same declarations into every member's ParseScope, so statement TEXT
// resolves them without the local.

package eudoxus_slope

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/registry"
)

// numPair is the ℕ pair constructor's type — the one name declared at
// a fixed instance of a polymorphic mint (pairs'); every other row
// reads its type off its constant's mint.
func numPair() HolType {
	return MakeFun(NumType, MakeFun(NumType, pairs.ProdType(NumType, NumType)))
}

// vocab is the chapter alphabet as data — one row per name.
var vocab = registry.NewVocabSpec(nil).
	OpsName("slopeVocab").
	Defined("dest_nadd").
	Defined("mk_nadd").
	Defined("is_nadd").
	Defined("nadd_eq").
	Defined("nadd_le").
	Defined("nadd_add").
	Defined("nadd_mul").
	Defined("nadd_of_num").
	Defined("nadd_inv").  // the reciprocal
	Defined("nadd_rinv"). // its pointwise inverse
	Term("nat_dist").     // nat_monus's ℕ-distance, on the ℕ pair
	Spelled(",", numPair).As("Pair").
	Term("+").As("Plus").
	Term("*").As("Times").
	Term("<=").As("LeOp").
	Term("<").As("LtOp").
	Term("suc").As("Suc")

// Nadd is `:nadd` — the nearly-additive sequences this family mints
// the tower's analysis on — as a phantom of the typed term surface,
// declared beside the mint per the vocabulary's decentralization rule
// (ext/holtype_phantom.go).
type Nadd struct{}

func (Nadd) Reify() ext.HolType { return MakeType("nadd") }

// Term-building helpers, writing x(n) for dest_nadd(x, n):

// at is a slope's underlying function value: at(x, n) = x(n).
func (v *slopeVocab) at(x, n Term) *TermWrapper { return v.DestNadd.Apply(x, n) }

// d is the ℕ-distance: d(a, b) = nat_dist((a, b)).
func (v *slopeVocab) d(a, b Term) *TermWrapper { return v.NatDist.Apply(v.Pair.Apply(a, b)) }

// sum / mul are the ℕ-operations: real_sum(a, b) = a + b, mul(a, b) = a·b.
func (v *slopeVocab) sum(a, b Term) *TermWrapper { return v.Plus.Apply(a, b) }
func (v *slopeVocab) mul(a, b Term) *TermWrapper { return v.Times.Apply(a, b) }

// le is the ℕ-order atom: le(a, b) = a ≤ b.
func (v *slopeVocab) le(a, b Term) *TermWrapper { return v.LeOp.Apply(a, b) }

// rel reads a binary relation const as the Prop-valued closure a Calc
// chain's Le / Eq field takes — `v.rel(v.NaddLe)` then says which
// relation the chain runs on and nothing else.
func (v *slopeVocab) rel(op *TermWrapper) func(p, q Term) Prop {
	return func(p, q Term) Prop {
		return MakeProp(op.Apply(p, q))
	}
}

// ZeroDefectClose is the zero-defect morphism preamble: unfold
// nadd_eq, witness the pointwise defect bound B := 0, and fix the
// index. The opening move of every law whose two sides agree
// pointwise (the of_num morphism laws, the additive identities) —
// what remains is a ground ℕ identity at the fixed index.
func (v *slopeVocab) ZeroDefectClose(ctx *Script) Action {
	return Chain(
		Unfold(NaddEqDef),
		Witness(ctx.Numeral(0)),
		StripQuant(),
	)
}
