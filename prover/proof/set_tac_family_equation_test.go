// set_tac_family_equation_test.go — at a family of sets, the membership
// driver reads the equation between sets a membership rule introduces
// pointwise, as it reads one the goal states.
//
// Phase 0 unfolds a head whose occurrence has a bool result and only set
// arguments. At a family the element is itself a set, so set_member and
// insert pass that test there, and insert's `y = a` reaches the refuter
// as `∀e. y(e) ⇔ a(e)`. Closes at a family that must prove such an
// equation, or match it against one a hypothesis states, stand on that
// reading (the driver's header). At a ground element the equation is not
// one between functions and reaches the refuter as written.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

// hasEquationAt reports whether t holds an equation between two terms of
// type ty.
func hasEquationAt(t core.Term, ty core.HolType) bool {
	for st := range ext.SubTerms(t) {
		if l, _, ok := ext.MatchesEQ(st); ok && l.Type().Equals(ty) {
			return true
		}
	}
	return false
}

// insertMembership is y ∈ insert(a, s) at element type elem, s a set of
// elem, with its three variables.
func insertMembership(m miniSetTheory, elem core.HolType) (goal Prop, y, a, s *ext.TermWrapper) {
	y = ext.Var("y", elem)
	a = ext.Var("a", elem)
	s = ext.Var("s", core.MakeFun(elem, core.TypeBool()))
	concl := m.at(m.in, elem).Apply(y, m.at(m.insert, elem).Apply(a, s))
	return prop.MakeProp(concl.Core()), y, a, s
}

// expandedConclusion runs the membership driver on goal and returns its
// one residual's conclusion.
func expandedConclusion(t *testing.T, goal Prop) core.Term {
	t.Helper()
	sub := tactic.MembershipSetTacExpand(t.Context(), goal, DefaultSetTacConsts())
	require.NotNil(t, sub, "the driver rewrites the membership")
	require.Equal(t, 1, sub.Size())
	return sub.ChildGoal(0).Conclusion()
}

// At the ground element type the equation y = a reaches the refuter as
// written: it is not an equation between functions.
func TestSetTacMembership_InsertKeepsPointEquation(t *testing.T) {
	m := makeMiniSetTheory()
	goal, y, a, s := insertMembership(m, m.elemT)
	residual := expandedConclusion(t, goal)
	want := y.Eq(a).Or(s.Apply(y))
	require.True(t, residual.AlphaEquals(want.Core()), "got %s", ext.PrintTerm(residual))
}

// At a family of sets the equation y = a between sets reaches the
// refuter pointwise.
func TestSetTacMembership_FamilyReadsInsertEquationPointwise(t *testing.T) {
	m := makeMiniSetTheory()
	goal, y, a, s := insertMembership(m, m.setT)
	residual := expandedConclusion(t, goal)
	e := ext.Var("e", m.elemT)
	want := ext.ForAll(e)(y.Apply(e).Eq(a.Apply(e))).Or(s.Apply(y))
	require.True(t, residual.AlphaEquals(want.Core()), "got %s", ext.PrintTerm(residual))
	require.False(t, hasEquationAt(residual, m.setT), "no equation between sets survives: %s", ext.PrintTerm(residual))
}
