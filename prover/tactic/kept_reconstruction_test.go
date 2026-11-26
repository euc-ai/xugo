package tactic

// A step keeps what its reconstruction returned when it was made — on
// its children's own goals, and on them with the gate's stronger
// theorems in their place — and a fold reads its pieces' kept results
// in place of running them (SubGoals.reconstructOn). These tests hold
// that reading: which theorems it answers from what was kept, that a
// fold's runs then cost the fold's own step and nothing under it, and
// that a fold is still held to what its pieces return.

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"

	"github.com/stretchr/testify/require"
)

// withoutStrongerCloses runs the rest of the test as a proving process
// runs: no step is held to its children closed by a stronger theorem.
func withoutStrongerCloses(t *testing.T) {
	t.Helper()
	strongerCloses.on.Store(false)
	t.Cleanup(func() { strongerCloses.on.Store(true) })
}

// countedIffSplit is HypIffTactic with its reconstruction counted: the
// step it returns reconstructs through the split's own step and adds one
// to runs each time it is run.
func countedIffSplit(runs *int) Tactic {
	return func(goal Prop) *SubGoals {
		split := HypIffTactic(goal)
		if split == nil {
			return nil
		}
		return MakeSubGoals(goal, func(thms ...Prop) Prop {
			*runs++
			return split.Reconstruct(thms...)
		}, split.childrenGoals...)
	}
}

// foldRuns is how many times the reconstructions of the steps of a
// complete case analysis over k equivalences are run while it is built,
// each reading of the gate replacing every leaf. A step is run once on
// its children's own goals and, per reading, once per child and once
// with both: 1 + 3·readings. A fold over n leaves — every step above
// the lowest, whose children are leaves and which nothing folds — runs
// its own step once on the leaves' own goals and, per reading, once per
// leaf and once with all: 1 + (n + 1)·readings, and no step under it.
func foldRuns(k, readings int) int {
	steps := 1<<k - 1
	runs := steps * (1 + 3*readings)
	for height := 2; height <= k; height++ {
		folds, leaves := 1<<(k-height), 1<<height
		runs += folds * (1 + (leaves+1)*readings)
	}
	return runs
}

// TestFold_RunsItsOwnStepAndReadsTheStepsUnderIt: building a case
// analysis runs each step's reconstruction as many times as the step
// and the folds over it are run themselves. A fold that ran the subtree
// under it on every run would run the steps of six equivalences 16,540
// times under the gate; they are run 1,174 times.
func TestFold_RunsItsOwnStepAndReadsTheStepsUnderIt(t *testing.T) {
	readings := len(strongerCloseReadings)
	require.Equal(t, 1174, foldRuns(6, readings), "the count the comment above states")
	for _, k := range []int{2, 4, 6} {
		t.Run(fmt.Sprintf("%d equivalences under the gate", k), func(t *testing.T) {
			runs := 0
			s := mergeTactics(countedIffSplit(&runs))(iffHypGoal(k))
			require.NotNil(t, s)
			require.Equal(t, 1<<k, s.Size(), "the case analysis is complete")
			require.Equal(t, foldRuns(k, readings), runs)
			require.Empty(t, takeRefusals())
		})
	}
	t.Run("6 equivalences in a proving process", func(t *testing.T) {
		withoutStrongerCloses(t)
		runs := 0
		s := mergeTactics(countedIffSplit(&runs))(iffHypGoal(6))
		require.NotNil(t, s)
		require.Equal(t, 64, s.Size())
		require.Equal(t, foldRuns(6, 0), runs, "one run per step and one per fold")
	})
}

// TestReconstructOn_ReadsAKeptResultByObject: the step answers from what
// it kept only for the very theorems it ran on. A theorem that states
// what one of them states is another object, and the reconstruction is
// run on it.
func TestReconstructOn_ReadsAKeptResultByObject(t *testing.T) {
	q := core.Var("q", core.TypeBool())
	goal, child, _, guarded := doubleNegationStep(q)
	runs := 0
	step := MakeSubGoals(goal, func(thms ...Prop) Prop {
		runs++
		return guarded(thms...)
	}, child)
	made := runs
	require.Equal(t, 1+len(strongerCloseReadings), made, "its own goal, and the one child in each reading")

	own := step.reconstructOn([]Prop{child})
	require.Equal(t, made, runs, "the child's own goal is read")
	require.True(t, own.Core() == step.onOwnGoals.Core())

	for r, reading := range strongerCloseReadings {
		kept := step.reconstructOn([]Prop{step.held[r].stronger[0]})
		require.Equal(t, made, runs, "the theorem the gate replaced the child by is read: %s", reading.how)
		require.True(t, kept.Core() == step.held[r].returned[0].Core())
	}

	step.reconstructOn([]Prop{MakeProp(child.Conclusion(), child.Hyps()...)})
	require.Equal(t, made+1, runs, "a second statement of the child's goal is run")
	step.reconstructOn([]Prop{strongerCloseReadings[0].thm(child)})
	require.Equal(t, made+2, runs, "and so is a second statement of a theorem the gate made")
	require.Empty(t, takeRefusals())
}

// TestFold_IsHeldToWhatItsPiecesReturn: a step can take each of its
// children closed by the gate's two theorems and still break on what
// the step under it returns for one. Here the upper step drops g and
// reads h off a child closed by contradiction; made alone it is handed
// `h, k ⊢ ⊥`, which holds h. The step under it drops h, so the fold's
// one leaf is `k ⊢ c`: closed by contradiction it comes back up as
// `k ⊢ ⊥`, without h. The fold's gate refuses the fold on that, reading
// the lower step's kept result and running the upper step on it.
func TestFold_IsHeldToWhatItsPiecesReturn(t *testing.T) {
	require.Empty(t, takeRefusals(), "no test before this one left a refusal")
	c, g, h, k := core.Var("c", core.TypeBool()), core.Var("g", core.TypeBool()),
		core.Var("h", core.TypeBool()), core.Var("k", core.TypeBool())
	goal := MakeProp(c, g, h, k)

	lowerRuns := 0
	dropH := func(p Prop) *SubGoals {
		if p.HasHyp(g) || !p.HasHyp(h) {
			return nil
		}
		return MakeSubGoals(p, func(thms ...Prop) Prop {
			lowerRuns++
			return thms[0]
		}, MakeProp(p.Conclusion(), restHyps(p, hypIndexOf(p, h))...))
	}
	dropG := func(readsH bool) Tactic {
		return func(p Prop) *SubGoals {
			if !p.HasHyp(g) {
				return nil
			}
			return MakeSubGoals(p, func(thms ...Prop) Prop {
				if readsH && thms[0].Conclusion().Equals(F) {
					_ = thms[0].Hyp(hypIndexOf(thms[0], h))
				}
				return thms[0]
			}, MakeProp(p.Conclusion(), restHyps(p, hypIndexOf(p, g))...))
		}
	}

	require.NotPanics(t, func() { dropG(true)(goal) }, "made alone, the upper step takes its child in both readings")
	require.Empty(t, takeRefusals())

	refusal := func() (r any) {
		defer func() { r = recover() }()
		mergeTactics(dropG(true), dropH)(goal)
		return nil
	}()
	require.NotNil(t, refusal, "the fold is refused")
	require.True(t, utils.IsFault(refusal), "a refusal is a fault")
	text := fmt.Sprint(refusal)
	require.Contains(t, text, "tactic.go", "the refusal names the fold")
	require.Contains(t, text, "child(ren) [0] closed by contradiction")
	require.Equal(t, []string{text}, takeRefusals())
	require.Equal(t, 1+len(strongerCloseReadings), lowerRuns,
		"the lower step was run when it was made and read by the fold")

	folded := mergeTactics(dropG(false), dropH)(goal)
	require.NotNil(t, folded, "an upper step that reads no hypothesis folds")
	require.Equal(t, 1, folded.Size())
	require.Empty(t, takeRefusals())
}
