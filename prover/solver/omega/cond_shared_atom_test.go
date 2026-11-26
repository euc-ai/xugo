package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Two CONDs of one goal whose conditions share an atom are decided
// together. The split on the atom pins the first COND; the second is
// split on the same atom inside a branch that already holds it, so one
// arm of that split is the branch and the other denies a hypothesis of
// it. An arm the hypotheses deny is closed by that denial, on the
// three carriers.
func TestCond_TwoCondsOnOneAtom(t *testing.T) {
	installTestBundle(t)
	p, q := ext.Var("p", core.TypeBool()), ext.Var("q", core.TypeBool())
	notP := ext.Not(p).Core()
	decided := func(w *prop.PropWrapper) bool { return w != nil && prop.Rhs(w).AlphaEquals(prop.T) }

	// ℝ.
	one, zero := realLit(1), realLit(0)
	ind := func(c Term) Term { return ext.Cond(c, one, zero).Core() }
	both := realPlusT(ind(notP), ind(p))
	realDecidesTrue(t, "real: 1 ≤ COND(¬p, 1, 0) + COND(p, 1, 0)", realLeT(one, both))
	realDecidesTrue(t, "real: COND(¬p, 1, 0) + COND(p, 1, 0) = 1", eqT(both, one))
	// A COND inside a COND, and a condition that is an equivalence of the
	// two atoms: the signed indicator of p under q.
	signed := ext.Cond(q, ind(p), realNegT(ind(p))).Core()
	agree := ind(core.Eq(p, q))
	realDecidesTrue(t, "real: the signed indicator",
		eqT(realPlusT(signed, one), realPlusT(ind(q), agree)))
	// The arms do not close what is false: the sum is 1 and not 2.
	if decided(RealArithDecideWithHyps(nil)(realLeT(realLit(2), both))) {
		t.Errorf("real: 2 ≤ COND(¬p, 1, 0) + COND(p, 1, 0) is decided true")
	}

	// ℤ.
	intInd := func(c Term) Term { return ext.Cond(c, intLit(1), intLit(0)).Core() }
	intBoth := intPlusT(intInd(notP), intInd(p))
	intDecidesTrue(t, "int: 1 ≤ COND(¬p, 1, 0) + COND(p, 1, 0)", intLeT(intLit(1), intBoth))
	if decided(IntArithDecideWithHyps(nil)(intLeT(intLit(2), intBoth))) {
		t.Errorf("int: 2 ≤ COND(¬p, 1, 0) + COND(p, 1, 0) is decided true")
	}

	// ℕ.
	natInd := func(c Term) Term { return ext.Cond(c, tn("1"), tn("0")).Core() }
	natBoth := ext.Apply(natPlus, natInd(notP), natInd(p))
	if !decided(ArithDecideWithHyps(nil)(le(tn("1"), natBoth))) {
		t.Errorf("nat: 1 ≤ COND(¬p, 1, 0) + COND(p, 1, 0) is not decided")
	}
	if decided(ArithDecideWithHyps(nil)(le(tn("2"), natBoth))) {
		t.Errorf("nat: 2 ≤ COND(¬p, 1, 0) + COND(p, 1, 0) is decided true")
	}
}
