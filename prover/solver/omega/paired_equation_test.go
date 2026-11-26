package omega

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// A pair of comparisons is the rule the equation of its sides would be,
// read off both hypotheses, and only at a carrier the policy admits.
func TestPairedEquation_APairIsTheRuleItsEquationWouldBe(t *testing.T) {
	n, m := numVar("n"), numVar("m")
	pair := []Term{le(n, m), le(m, n)}
	stated := varEqSubsts([]Term{eqT(n, m)}, isNat, nil, ArithPolicy{})
	rules := varEqSubsts(pair, isNat, nil, ArithPolicy{Nat: true})
	if len(stated) != 1 || len(rules) != 1 {
		t.Fatalf("want one rule each way, got %d stated and %d paired", len(stated), len(rules))
	}
	rule := rules[0]
	if !rule.from.AlphaEquals(stated[0].from) || !rule.to.AlphaEquals(stated[0].to) {
		t.Errorf("the pair defines %v as %v, the equation %v as %v", rule.from, rule.to, stated[0].from, stated[0].to)
	}
	if !rule.eq.Conclusion().AlphaEquals(eqT(rule.from, rule.to)) {
		t.Errorf("the rule's theorem concludes %v", rule.eq.Conclusion())
	}
	if len(rule.eq.Hyps()) != 2 || !rule.eq.HasHyp(pair[0]) || !rule.eq.HasHyp(pair[1]) {
		t.Errorf("the rule's theorem rests on %v, not on the two comparisons", rule.eq.Hyps())
	}
	if len(rule.at) != 2 {
		t.Errorf("the rule is read off %v, not off two hypotheses", rule.at)
	}
	if got := varEqSubsts(pair, isNat, nil, ArithPolicy{}); len(got) != 0 {
		t.Error("a pair was read at a carrier the policy does not admit")
	}
}

// Where the order is discrete a strict comparison is the non-strict one
// next to it, and pairs as that.
func TestPairedEquation_AStrictNeighbourPairs(t *testing.T) {
	n, m := numVar("n"), numVar("m")
	hyps := []Term{le(n, m), lt(m, plus(n, Numeral(1)))}
	if got := varEqSubsts(hyps, isNat, nil, ArithPolicy{Nat: true}); len(got) != 1 {
		t.Errorf("n ≤ m beside m < n + 1 made %d rules", len(got))
	}
}

// Comparisons that do not bound one difference from both sides make no
// equation, and a conjunction is one hypothesis: it is not read apart, as
// a stated equation inside one is not.
func TestPairedEquation_NoPairNoRule(t *testing.T) {
	n, m, k := numVar("n"), numVar("m"), numVar("k")
	for _, hyps := range [][]Term{
		{le(n, m)},
		{le(n, m), le(m, plus(n, Numeral(1)))},
		{le(n, m), le(m, k), le(k, n)},
		{lt(n, plus(m, Numeral(1))), lt(m, plus(n, Numeral(1)))},
		{and(le(n, m), le(m, n))},
	} {
		if got := varEqSubsts(hyps, isNat, nil, ArithPolicy{Nat: true}); len(got) != 0 {
			t.Errorf("%v made the rule %v → %v", hyps, got[0].from, got[0].to)
		}
	}
}

// A decision reads a pair's variable at its definition, in the target and
// the context together, and the pair's own comparisons are the rule's:
// neither is decided, or rewritten, by the equation the two make.
func TestArithCtx_APairDefines(t *testing.T) {
	a, n, m := numVar("a"), numVar("n"), numVar("m")
	pair := []Term{le(n, m), le(m, n)}
	atN, atM := eqT(modT(a, n), Numeral(1)), eqT(modT(a, m), Numeral(1))
	if !closesUnder(t, append(pair, atN), atM) {
		t.Error("the hypothesis at n did not decide the goal at m")
	}
	if closesUnder(t, []Term{pair[0], atN}, atM) {
		t.Error("the goal closed on one comparison of the pair")
	}
	ctx := NewArithCtx(append(pair, atN))
	for i := range pair {
		if w := ctx.DecideExcept(i, pair[i]); w != nil {
			t.Errorf("%v was rewritten to %v under the others", pair[i], prop.Rhs(w))
		}
	}
}

// A strict target denies the opposite bound, and beside the bound's own
// opposite that is an equation: a hypothesis it makes false proves the
// target.
func TestArithCtx_AStrictTargetDeniesTheOppositeBound(t *testing.T) {
	a, n, m := numVar("a"), numVar("n"), numVar("m")
	apart := not(eqT(modT(a, n), modT(a, m)))
	if !closesUnder(t, []Term{le(n, m), apart}, lt(n, m)) {
		t.Error("n ≤ m and two atoms told apart did not give n < m")
	}
	if closesUnder(t, []Term{le(n, m), apart}, lt(m, n)) {
		t.Error("m < n closed beside n ≤ m")
	}
	if closesUnder(t, []Term{apart}, lt(n, m)) {
		t.Error("n < m closed with no comparison beside it")
	}
}
