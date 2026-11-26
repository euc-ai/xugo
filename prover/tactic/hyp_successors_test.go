package tactic

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// hypSuccessorsEnv: Q, R : A → bool, f : A → A, the points a, b and the
// bool S the goals below are stated over.
type hypSuccessorsEnv struct {
	Q, R, f, a, b, S *ext.TermWrapper
}

func makeHypSuccessorsEnv() hypSuccessorsEnv {
	return hypSuccessorsEnv{
		Q: Var("Q", MakeFun(TypeA, TypeBool)),
		R: Var("R", MakeFun(TypeA, TypeBool)),
		f: Var("f", MakeFun(TypeA, TypeA)),
		a: Var("a", TypeA), b: Var("b", TypeA),
		S: Var("S", TypeBool),
	}
}

// requireSuccessor asserts that the hypothesis `from` of goal descends
// into the hypothesis `to` of child under the recorded map.
func requireSuccessor(t *testing.T, goal, child Prop, succ []int, from, to Term) {
	t.Helper()
	i := hypIndexOf(goal, from)
	require.NotEqual(t, NoSuccessor, i, "%s is a hypothesis of the goal", ext.PrintTerm(from))
	j := hypIndexOf(child, to)
	require.NotEqual(t, NoSuccessor, j, "%s is a hypothesis of the child", ext.PrintTerm(to))
	require.Equal(t, j, succ[i], "%s descends into %s", ext.PrintTerm(from), ext.PrintTerm(to))
}

// TestHypSuccessors_RwFollowsEveryRewrittenHypothesis: the rewrite to
// fixpoint reaches two hypotheses, and the recorded map sends each to
// its rewrite and the equality to itself, in either direction.
//
//	a = f(b), Q(f(b)), R(f(b)) ⊢ S   flipped, f(b) → a
//	f(b) = a, Q(f(b)), R(f(b)) ⊢ S   as written, f(b) → a
func TestHypSuccessors_RwFollowsEveryRewrittenHypothesis(t *testing.T) {
	e := makeHypSuccessorsEnv()
	fb := e.f.Apply(e.b)
	for _, dir := range []struct {
		name string
		eq   *ext.TermWrapper
		flip bool
	}{
		{"flipped", e.a.Eq(fb), true},
		{"as written", fb.Eq(e.a), false},
	} {
		t.Run(dir.name, func(t *testing.T) {
			goal := testProp(e.S.Core(), dir.eq.Core(), e.Q.Apply(fb).Core(), e.R.Apply(fb).Core())
			sg := RwHypTactic(hypIndexOf(goal, dir.eq.Core()), dir.flip)(goal)
			require.NotNil(t, sg)
			require.Equal(t, 1, sg.Size())
			child, succ := sg.ChildGoal(0), sg.HypSuccessors(0)
			require.Len(t, succ, 3)
			requireSuccessor(t, goal, child, succ, dir.eq.Core(), dir.eq.Core())
			requireSuccessor(t, goal, child, succ, e.Q.Apply(fb).Core(), e.Q.Apply(e.a).Core())
			requireSuccessor(t, goal, child, succ, e.R.Apply(fb).Core(), e.R.Apply(e.a).Core())
		})
	}
}

// TestHypSuccessors_TrivialSimplifySplitsAConjunctionWithoutASuccessor:
// the tidy's conjunction split leaves the conjunction no single
// successor, while the hypothesis beside it keeps its slot — through the
// fixpoint's composition of the component maps.
//
//	Q(a) ∧ R(a), S ⊢ Q(b)
func TestHypSuccessors_TrivialSimplifySplitsAConjunctionWithoutASuccessor(t *testing.T) {
	e := makeHypSuccessorsEnv()
	conj := e.Q.Apply(e.a).And(e.R.Apply(e.a))
	goal := testProp(e.Q.Apply(e.b).Core(), conj.Core(), e.S.Core())
	sg := TrivialSimplifyTactic(goal)
	require.NotNil(t, sg)
	require.Equal(t, 1, sg.Size())
	child, succ := sg.ChildGoal(0), sg.HypSuccessors(0)
	require.Equal(t, 3, child.NumHyps(), "the conjunction is split")
	require.Equal(t, NoSuccessor, succ[hypIndexOf(goal, conj.Core())])
	requireSuccessor(t, goal, child, succ, e.S.Core(), e.S.Core())
}

// TestHypSuccessors_SpecializeSendsTheSourceIntoItsInstance: a consumed
// ∀-source descends into the instance that replaces it; a kept one
// stands.
//
//	∀x. Q(x), S ⊢ R(a)
func TestHypSuccessors_SpecializeSendsTheSourceIntoItsInstance(t *testing.T) {
	e := makeHypSuccessorsEnv()
	x := Var("x", TypeA)
	source := ext.ForAll(x)(e.Q.Apply(x))
	goal := testProp(e.R.Apply(e.a).Core(), source.Core(), e.S.Core())
	spec := []SpecializeSpec{{HypIndex: hypIndexOf(goal, source.Core()), Witnesses: []Term{e.a.Core()}}}

	consumed := SpecializeTactic(spec, false)(goal)
	require.NotNil(t, consumed)
	child, succ := consumed.ChildGoal(0), consumed.HypSuccessors(0)
	requireSuccessor(t, goal, child, succ, source.Core(), e.Q.Apply(e.a).Core())
	requireSuccessor(t, goal, child, succ, e.S.Core(), e.S.Core())

	kept := SpecializeTactic(spec, true)(goal)
	require.NotNil(t, kept)
	child, succ = kept.ChildGoal(0), kept.HypSuccessors(0)
	requireSuccessor(t, goal, child, succ, source.Core(), source.Core())
}

// TestHypSuccessors_ClearHypsDropsTheNamedAndKeepsTheRest.
//
//	Q(a), R(a), S ⊢ Q(b)   clearing R(a)
func TestHypSuccessors_ClearHypsDropsTheNamedAndKeepsTheRest(t *testing.T) {
	e := makeHypSuccessorsEnv()
	goal := testProp(e.Q.Apply(e.b).Core(), e.Q.Apply(e.a).Core(), e.R.Apply(e.a).Core(), e.S.Core())
	dropped := hypIndexOf(goal, e.R.Apply(e.a).Core())
	sg := ClearHypsTactic([]int{dropped})(goal)
	require.NotNil(t, sg)
	child, succ := sg.ChildGoal(0), sg.HypSuccessors(0)
	require.Equal(t, NoSuccessor, succ[dropped])
	requireSuccessor(t, goal, child, succ, e.Q.Apply(e.a).Core(), e.Q.Apply(e.a).Core())
	requireSuccessor(t, goal, child, succ, e.S.Core(), e.S.Core())
}
