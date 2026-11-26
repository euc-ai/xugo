package tactic

// A child's theorem may conclude ⊥ where the child's goal does not:
// IsStronger admits it, and a branch whose hypotheses contradict one
// another is closed so. A definition keeps the goal's conclusion, so
// its child states one, and the reconstruction must take a theorem of
// the child that concludes ⊥ back to the goal as it does one that
// concludes the child's conclusion. These tests hold that, for a
// contradiction among hypotheses that spell the name, among those and
// the definition, and among hypotheses the definition did not touch.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/require"
)

// letContradictionTerms is the vocabulary of the goals below: a point
// a, a map f, predicates P and Q on the points, and a proposition R.
func letContradictionTerms() (a, fa, P, Q, R core.Term) {
	point := core.MakeVarType("A")
	a = core.Var("a", point)
	fa = core.Apply(core.Var("f", MakeFun(point, point)), a)
	P = core.Var("P", MakeFun(point, core.TypeBool()))
	Q = core.Var("Q", MakeFun(point, core.TypeBool()))
	R = core.Var("R", core.TypeBool())
	return a, fa, P, Q, R
}

func TestLetTerm_ReconstructsAChildClosedByContradiction(t *testing.T) {
	a, fa, P, Q, R := letContradictionTerms()
	w := core.Var("w", fa.Type())
	definition := Eq(w, fa)
	holds, fails := core.Apply(P, w), Not(core.Apply(P, w))

	// P(f(a)), ¬P(f(a)) ⊢ Q(f(a)): the definition rewrites every
	// hypothesis and the conclusion.
	named := MakeProp(core.Apply(Q, fa), core.Apply(P, fa), Not(core.Apply(P, fa)))
	// R, ¬R ⊢ Q(a): the goal does not spell the defined term.
	untouched := MakeProp(core.Apply(Q, a), R, Not(R))

	for _, row := range []struct {
		name   string
		goal   Prop
		closed []core.Term // the hypotheses the child's ⊥ rests on
	}{
		{"hypotheses that spell the name", named, []core.Term{holds, fails}},
		{"those hypotheses and the definition", named, []core.Term{holds, fails, definition}},
		{"hypotheses the definition did not touch", untouched, []core.Term{R, Not(R)}},
	} {
		t.Run(row.name, func(t *testing.T) {
			sg := LetTermTactic(fa, "w")(row.goal)
			require.NotNil(t, sg)
			require.Equal(t, 1, sg.Size())
			child := sg.ChildGoal(0)
			require.True(t, child.HasHyp(definition), "the definition is resident:\n%s", prop.PrintProp(child))
			require.False(t, child.Conclusion().Equals(F), "the child keeps a conclusion:\n%s", prop.PrintProp(child))

			closed := core.TestThm(F, row.closed...)
			require.True(t, IsStronger(closed, child), "the ⊥ theorem is a theorem of the child")
			var thm Prop
			require.NotPanics(t, func() { thm = sg.Reconstruct(closed) },
				"a child closed by contradiction reconstructs")
			require.True(t, thm.Proved())
			require.True(t, IsStronger(thm, row.goal), "the reconstruction is a theorem of the goal:\n%s", prop.PrintProp(thm))
			require.False(t, thm.HasFreeName(w.Name()), "the name is instantiated away:\n%s", prop.PrintProp(thm))

			// Full proofs, ⊥ proofs and proofs that drop hypotheses.
			assertSubGoals(t, sg, row.goal)
		})
	}
}

// The control: a child closed at its own conclusion reconstructs to the
// goal's conclusion, read back through the definition.
func TestLetTerm_ReconstructsAChildClosedAtItsConclusion(t *testing.T) {
	_, fa, P, Q, _ := letContradictionTerms()
	goal := MakeProp(core.Apply(Q, fa), core.Apply(P, fa), Not(core.Apply(P, fa)))
	sg := LetTermTactic(fa, "w")(goal)
	require.NotNil(t, sg)
	child := sg.ChildGoal(0)
	thm := sg.Reconstruct(core.TestThm(child.Conclusion(), child.Hyps()...))
	require.True(t, thm.Proved())
	require.True(t, thm.Conclusion().Equals(goal.Conclusion()), "the goal's conclusion:\n%s", prop.PrintProp(thm))
	require.True(t, IsStronger(thm, goal))
}
