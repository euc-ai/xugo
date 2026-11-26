package tactic

// The residual of a simp step is the goal with its conclusion, or one
// of its hypotheses, rewritten, and whatever follows the step closes
// it. A residual whose hypotheses contradict one another is closed at
// ⊥, and the step's reconstruction must take that theorem back to the
// goal as it takes one that concludes the rewritten conclusion.

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// The rules of the rows below, over simpVars: f = g everywhere, g = h
// everywhere, and f = g under Q.
func simpContradictionRules() (everywhere, chained, underQ Prop) {
	x, _, f, g, h, _, Q := simpVars()
	everywhere = testProp(ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())
	chained = testProp(ForAll(x)(g.Apply(x).Eq(h.Apply(x))).Core())
	underQ = testProp(ForAll(x)(Q.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x)))).Core())
	return everywhere, chained, underQ
}

// A conclusion rewrite: the residual states the rewritten conclusion
// over the goal's hypotheses. The rule children are closed by their own
// statements; the residual, by a theorem that concludes ⊥ from the
// hypotheses. assertSubGoals then holds the reconstruction over full
// proofs, ⊥ proofs and proofs that drop hypotheses.
func TestSimpWith_ReconstructsAResidualClosedByContradiction(t *testing.T) {
	defer goleak.VerifyNone(t)
	_, a, f, _, _, P, Q := simpVars()
	everywhere, chained, underQ := simpContradictionRules()
	goal := testProp(P.Apply(f.Apply(a)).Core(), Q.Apply(a).Core())

	for _, row := range []struct {
		name  string
		rules []Prop
	}{
		{"one rule", []Prop{everywhere}},
		{"two rules chained", []Prop{everywhere, chained}},
		{"a rule under a condition the goal holds", []Prop{underQ}},
	} {
		t.Run(row.name, func(t *testing.T) {
			sg := SimpWithExpand(goal, row.rules)
			require.NotNil(t, sg)
			last := sg.Size() - 1
			residual := sg.ChildGoal(last)
			require.False(t, residual.Conclusion().Equals(F))
			require.False(t, residual.Conclusion().AlphaEquals(goal.Conclusion()), "the conclusion is rewritten")

			thms := make([]Prop, sg.Size())
			for i := range last {
				rule := sg.ChildGoal(i)
				thms[i] = testThm(rule.Conclusion(), rule.Hyps()...)
			}
			thms[last] = testThm(F, residual.Hyps()...)
			var thm Prop
			require.NotPanics(t, func() { thm = sg.Reconstruct(thms...) },
				"a residual closed by contradiction reconstructs")
			require.True(t, thm.Proved())
			require.True(t, IsStronger(thm, goal))

			assertSubGoals(t, sg, goal)
		})
	}
}

// A hypothesis rewrite leaves the conclusion as it stood, and its
// reconstruction reads the residual's theorem whatever it concludes.
func TestSimpWith_AtAHypothesis_ReconstructsAResidualClosedByContradiction(t *testing.T) {
	defer goleak.VerifyNone(t)
	_, a, f, _, _, P, Q := simpVars()
	everywhere, _, _ := simpContradictionRules()
	rewritten := P.Apply(f.Apply(a)).Core()
	goal := testProp(Q.Apply(a).Core(), rewritten)

	sg, image := SimpWithExpandFlippedAt(goal, hypIndexOf(goal, rewritten), []Prop{everywhere}, nil)
	require.NotNil(t, sg)
	require.True(t, sg.ChildGoal(sg.Size()-1).HasHyp(image))
	assertSubGoals(t, sg, goal)
}

// A rule that carries a hypothesis is a child like the residual: here a
// guarded equation the goal holds, used as a rule, `h ⊢ h`. Closed by
// contradiction it comes back as `h ⊢ ⊥`, which proves the rule ex
// falso, and the pipeline is re-run on the rule as stated.
func TestSimpWith_ReconstructsARuleClosedByContradiction(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, _, P, Q := simpVars()
	fact := ForAll(x)(Q.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x)))).Core()
	rule := testProp(fact, fact)
	goal := testProp(P.Apply(f.Apply(a)).Core(), fact, Q.Apply(a).Core())

	sg := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, sg)
	require.Equal(t, 2, sg.Size())
	require.True(t, sg.ChildGoal(0).AlphaEquals(rule))
	residual := sg.ChildGoal(1)

	var thm Prop
	require.NotPanics(t, func() {
		thm = sg.Reconstruct(testThm(F, fact), testThm(residual.Conclusion(), residual.Hyps()...))
	}, "a rule closed by contradiction reconstructs")
	require.True(t, thm.Proved())
	require.True(t, thm.Conclusion().Equals(goal.Conclusion()))
	require.True(t, IsStronger(thm, goal))

	assertSubGoals(t, sg, goal)
}
