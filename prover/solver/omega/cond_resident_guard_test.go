package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A COND whose guard, or its negation, is a hypothesis is read at the
// branch the hypothesis selects — whatever the guard is. The deciders'
// own case splits read ARITHMETIC guards (an order atom, an equation
// of the carrier); a guard that is a membership or an opaque predicate
// is no atom of theirs, and without this the COND stays an unknown
// though the context says which arm it is. One rule on the three
// carriers, through the unified decider and the dedicated ones alike:
// the dedicated stacks decide the residual here, and the unified one —
// which this package's test bundle gives the ℕ leaves alone — is asked
// only that the COND is read at its arm.
func TestCond_GuardDecidedByAHypothesis(t *testing.T) {
	installTestBundle(t)
	g := ext.Var("g", core.TypeBool())
	notG := ext.Not(g).Core()
	decided := func(w *prop.PropWrapper) bool { return w != nil && prop.Rhs(w).AlphaEquals(prop.T) }

	// reads is the leaf's own guarantee, whatever bundles the stack has:
	// the COND is gone and its selected arm stands in its place.
	reads := func(w *prop.PropWrapper, residual Term) bool {
		return w != nil && (prop.Rhs(w).AlphaEquals(residual) || prop.Rhs(w).AlphaEquals(prop.T))
	}

	// ℝ — the three sequents of real_cardinality's ternary expansion.
	p, zero := realVar("p"), realLit(0)
	nonneg := realLeT(zero, p)
	then := ext.Cond(g, p, zero).Core()
	otherwise := ext.Cond(g, zero, p).Core()
	for _, row := range []struct {
		name     string
		hyps     []Term
		goal     Term
		residual Term // the goal with the COND read at the selected arm
	}{
		{"real: 0 ≤ COND(g, p, 0) under g", []Term{g, nonneg}, realLeT(zero, then), nonneg},
		{"real: |COND(g, p, 0)| ≤ p under g", []Term{g, nonneg}, realLeT(realAbsT(then), p), realLeT(realAbsT(p), p)},
		{"real: 0 ≤ COND(g, 0, p) under ¬g", []Term{notG, nonneg}, realLeT(zero, otherwise), nonneg},
	} {
		if !decided(RealArithDecideWithHyps(row.hyps)(row.goal)) {
			t.Errorf("%s: the dedicated ℝ decider does not decide it", row.name)
		}
		if w := ArithDecideWithHyps(row.hyps)(row.goal); !reads(w, row.residual) {
			t.Errorf("%s: the unified decider does not read the COND at its arm", row.name)
		}
	}

	// ℕ — true at the branch the hypothesis selects and at no other.
	a := tn("a")
	le := func(l, r Term) Term {
		tmpl := tb("l <= r")
		var subs []core.TermSubst
		for _, v := range tmpl.Frees(nil) {
			switch string(v.Name()) {
			case "l":
				subs = append(subs, core.MakeTermSubst(v, l))
			case "r":
				subs = append(subs, core.MakeTermSubst(v, r))
			}
		}
		return tmpl.Substitute(subs...)
	}
	aPlus1 := tn("a + 1")
	natThen := le(ext.Cond(g, a, aPlus1).Core(), a)
	if !decided(ArithDecideWithHyps([]Term{g})(natThen)) {
		t.Errorf("nat: COND(g, a, a + 1) ≤ a under g is not decided")
	}
	if !decided(ArithDecideWithHyps([]Term{notG})(le(ext.Cond(g, aPlus1, a).Core(), a))) {
		t.Errorf("nat: COND(g, a + 1, a) ≤ a under ¬g is not decided")
	}
	if decided(ArithDecideWithHyps(nil)(natThen)) {
		t.Errorf("nat: with no hypothesis about g the COND must stay undecided")
	}

	// ℤ.
	x := intVar("x")
	intThen := intLeT(ext.Cond(g, x, intPlusT(x, intLit(1))).Core(), x)
	if !decided(IntArithDecideWithHyps([]Term{g})(intThen)) {
		t.Errorf("int: COND(g, x, x + 1) ≤ x under g is not decided by the dedicated ℤ decider")
	}
	if w := ArithDecideWithHyps([]Term{g})(intThen); !reads(w, intLeT(x, x)) {
		t.Errorf("int: the unified decider does not read COND(g, x, x + 1) at its arm under g")
	}
}
