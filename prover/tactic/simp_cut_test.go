package tactic

import (
	"fmt"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// twoRuleFeed is a rule set that feeds itself through two rules, neither
// self-embedding: f(x) = g(x) and g(x) = h(f(x)). The second restores
// the first's left side under one more h, without end. padding is the
// number of summands the goal carries beside the redex.
func twoRuleFeed(padding int) (goal Prop, rules []Prop, redex core.Term) {
	unary := MakeFun(TypeA, TypeA)
	f := ext.TestConst("feedF", unary)
	g := ext.TestConst("feedG", unary)
	h := ext.TestConst("feedH", unary)
	plus := ext.TestConst("feedPlus", MakeFun(TypeA, MakeFun(TypeA, TypeA)))
	P := ext.TestConst("feedP", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("feedQ", MakeFun(TypeA, TypeBool))
	x := ext.WrapTerm(Var("x", TypeA))
	a := ext.WrapTerm(Var("a", TypeA))

	rules = []Prop{
		testProp(ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core()),
		testProp(ForAll(x)(g.Apply(x).Eq(h.Apply(f.Apply(x)))).Core()),
	}
	body := f.Apply(a)
	for i := range padding {
		body = plus.Apply(body, ext.WrapTerm(Var(core.TermName(fmt.Sprintf("pad%d", i)), TypeA)))
	}
	redex = P.Apply(body).Core()
	return testProp(Q.Apply(a).Core(), redex), rules, redex
}

// returnsWithin runs f and fails the test when it has not returned in
// limit: a divergent rewrite that the whistle does not end holds the
// caller without end.
func returnsWithin(t *testing.T, limit time.Duration, f func()) {
	t.Helper()
	done := make(chan struct{})
	go func() {
		defer close(done)
		f()
	}()
	select {
	case <-done:
	case <-time.After(limit):
		t.Fatalf("no return within %v", limit)
	}
}

// A rule set that feeds itself through two rules is cut by the whistle,
// the cut ends the run, and the step is refused with nothing rewritten:
// on a small goal and on one whose size gives the first round the budget
// several compounding rounds would reach.
func TestSimpWith_TwoRuleFeedIsCutAndRefused(t *testing.T) {
	for _, padding := range []int{0, 120} {
		t.Run(fmt.Sprintf("padding %d", padding), func(t *testing.T) {
			hypGoal, rules, redex := twoRuleFeed(padding)
			goal := testProp(redex)

			var events []skeleton.WhistleEvent
			skeleton.OnWhistleFire = func(ev skeleton.WhistleEvent) { events = append(events, ev) }
			t.Cleanup(func() { skeleton.OnWhistleFire = nil })

			var sg *SubGoals
			returnsWithin(t, 60*time.Second, func() { sg = SimpWithExpand(goal, rules) })
			require.Nil(t, sg, "a cut run commits nothing")
			require.Len(t, events, 1, "one round is cut and no further round runs")
			assert.Equal(t, "DeepRewriteWhistled", events[0].Driver)
			assert.True(t, events[0].Term.AlphaEquals(redex), "the cut is of the first round's rewrite of the goal")

			// The refusal's wording reads the cut again and reports it to
			// no one: the step did.
			note := SimpCut(goal, rules, nil, goal.Conclusion())
			assert.Contains(t, note, "The divergence whistle cut the rewrite at firing")
			assert.Len(t, events, 1)
			assert.Empty(t, SimpRefusal(goal, rules, nil, goal.Conclusion()), "neither rule embeds itself")

			// At a hypothesis the run is cut the same way, and the cut is
			// worded for that target alone.
			events = nil
			var atHyp *SubGoals
			require.True(t, hypGoal.Hyp(0).AlphaEquals(redex))
			returnsWithin(t, 60*time.Second, func() { atHyp, _ = SimpWithExpandFlippedAt(hypGoal, 0, rules, nil) })
			require.Nil(t, atHyp)
			require.Len(t, events, 1)
			assert.Contains(t, SimpCut(hypGoal, rules, nil, redex), "The divergence whistle cut the rewrite at firing")
			assert.Empty(t, SimpCut(hypGoal, rules, nil, hypGoal.Conclusion()), "nothing fires on the conclusion")
		})
	}
}

// One of the two rules alone terminates: the whistle has nothing to cut
// and there is nothing to word.
func TestSimpWith_OneRuleOfTheFeedRewrites(t *testing.T) {
	_, rules, redex := twoRuleFeed(0)
	goal := testProp(redex)
	before := skeleton.WhistleFires()
	for _, rule := range rules {
		sg := SimpWithExpand(goal, []Prop{rule})
		if sg != nil {
			assert.False(t, sg.ChildGoal(sg.Size()-1).Conclusion().AlphaEquals(redex))
		}
		assert.Empty(t, SimpCut(goal, []Prop{rule}, nil, goal.Conclusion()))
	}
	require.NotNil(t, SimpWithExpand(goal, rules[:1]), "f(x) = g(x) rewrites the goal")
	assert.Equal(t, before, skeleton.WhistleFires())
}
