package prop

import "github.com/euc-ai/xugo/ext"

// LeftConjuncts reads a conjunction along its left spine, the way the
// parser joins `H₁ ∧ H₂ ∧ … ∧ Hₙ`: the right child at each level is one
// conjunct as written, and the descent continues into the left child.
// A conjunct written as a parenthesized conjunction in the first place
// is read through, since nothing in the term tells it from two.
func LeftConjuncts(t Term) []Term {
	l, r, ok := MatchesAND(t)
	if !ok {
		return []Term{t}
	}
	return append(LeftConjuncts(l), r)
}

// ConjunctionOf joins the pieces at idx to the left, in order.
func ConjunctionOf(pieces []Term, idx []int) Term {
	t := pieces[idx[0]]
	for _, i := range idx[1:] {
		t = ext.WrapTerm(t).And(pieces[i]).Core()
	}
	return t
}

// ConjunctionFromPieces is `P_{idx₁}, …, P_{idxₘ} ⊢ ConjunctionOf(pieces, idx)`.
func ConjunctionFromPieces(pieces []Term, idx []int) *PropWrapper {
	if len(idx) == 1 {
		return Assume(pieces[idx[0]])
	}
	left := ConjunctionOf(pieces, idx[:len(idx)-1])
	step := ConclAND(left, pieces[idx[len(idx)-1]]) // left, Pₘ ⊢ left ∧ Pₘ
	if len(idx) == 2 {
		return step
	}
	return ConjunctionFromPieces(pieces, idx[:len(idx)-1]).DeriveTrans(step)
}

// ConjunctionPiece is `ConjunctionOf(pieces, idx) ⊢ P_{idx[k]}`. A piece
// that is itself a conjunction is taken whole, wherever it stands.
func ConjunctionPiece(pieces []Term, idx []int, k int) *PropWrapper {
	if len(idx) == 1 {
		return Assume(pieces[idx[0]])
	}
	last := len(idx) - 1
	left := ConjunctionOf(pieces, idx[:last])
	if k == last {
		return HypAND1(left, pieces[idx[last]])
	}
	return HypAND0(left, pieces[idx[last]]).DeriveTrans(ConjunctionPiece(pieces, idx[:last], k))
}
