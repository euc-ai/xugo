package omega

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A zero-sided equation, read in either orientation.
//
// The folds that carry a zero test through an operator are stated with the
// zero on the right: `inv x = &0` to `x = &0`, `−x = &0` to `x = &0`,
// `¬(x = &0)` to `&0 < x·x`, `int_rem(m, n) = &0` to divisibility. A
// statement spells an equation either way, and nothing else in the decider
// turns `¬(&0 = g · inv q)` round for them. So each such fold reads its
// equation through zeroSidedEq, and its result is spelled with the zero on
// the right whichever way the equation came.

// zeroSidedEq reads t as `x = zero` or `zero = x`: x, and for the second
// spelling turned, `⊢ t ⇔ (x = zero)`; turned is nil for the first.
func zeroSidedEq(t Term, isZero func(Term) bool) (x Term, turned *prop.PropWrapper, ok bool) {
	l, r, isEq := ext.MatchesEQ(t)
	switch {
	case !isEq:
		return nil, nil, false
	case isZero(r):
		return l, nil, true
	case isZero(l):
		return r, eqTurned(l, r), true
	}
	return nil, nil, false
}

// eqTurned is `⊢ (l = r) ⇔ (r = l)`.
func eqTurned(l, r Term) *prop.PropWrapper {
	lr, rl := eqT(l, r), eqT(r, l)
	return prop.Assume(rl).EqSym().Deduct(prop.Assume(lr).EqSym())
}

// afterTurn is fold, `⊢ (x = zero) ⇔ q`, read from the spelling turned
// came from: `⊢ t ⇔ q`. fold itself where turned is nil.
func afterTurn(turned, fold *prop.PropWrapper) *prop.PropWrapper {
	if turned == nil || fold == nil {
		return fold
	}
	return turned.EqTrans(fold)
}
