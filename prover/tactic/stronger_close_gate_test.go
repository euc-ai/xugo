package tactic

// The package's tests run under HoldStrongerCloses (TestMain), so a
// step built here is held at its creation to its children closed by a
// stronger theorem: by contradiction, and from no hypothesis. These
// tests hold the gate itself: what it refuses in each reading, what it
// accepts, which children it asks about, and that a refusal a recover
// swallowed still fails the run.

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"

	"github.com/stretchr/testify/require"
)

// doubleNegationStep is the step `Γ ⊢ ¬¬p` to its child `Γ ⊢ p`, with
// the two reconstructions the gate tells apart: bridging carries the
// child's theorem through `⊢ ¬¬p = p` whatever it concludes, and
// guarded returns a child closed by contradiction as it stands.
func doubleNegationStep(hyps ...core.Term) (goal, child Prop, bridging, guarded _TacticReconstruct) {
	p := core.Var("p", core.TypeBool())
	bridge := prop.DoubleNegRewrite(Not(Not(p)))
	goal = MakeProp(Not(Not(p)), hyps...)
	child = MakeProp(p, hyps...)
	bridging = func(thms ...Prop) Prop { return bridge.EqSym().EqMP(thms[0]) }
	guarded = func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) {
			return thms[0]
		}
		return bridge.EqSym().EqMP(thms[0])
	}
	return goal, child, bridging, guarded
}

// takeRefusals empties the gate's record and returns what it held, so a
// test that provokes a refusal does not fail the run with it.
func takeRefusals() []string {
	strongerCloses.mu.Lock()
	defer strongerCloses.mu.Unlock()
	refused := strongerCloses.refused
	strongerCloses.refused = nil
	return refused
}

func TestHoldStrongerCloses_RefusesAReconstructionThatBridgesBottom(t *testing.T) {
	require.Empty(t, takeRefusals(), "no test before this one left a refusal")
	q := core.Var("q", core.TypeBool())
	goal, child, bridging, guarded := doubleNegationStep(q)

	refusal := func() (r any) {
		defer func() { r = recover() }()
		MakeSubGoals(goal, bridging, child)
		return nil
	}()
	require.NotNil(t, refusal, "the bridging reconstruction is refused at the step's creation")
	require.True(t, utils.IsFault(refusal), "a refusal is a fault: a recover that reads failures raises it again")
	text := fmt.Sprint(refusal)
	require.Contains(t, text, "stronger_close_gate_test.go", "the refusal names where the step was made")
	require.Contains(t, text, "child(ren) [0] closed by contradiction")
	require.Equal(t, []string{text}, takeRefusals(), "the refusal is kept as well as panicked with")

	require.NotPanics(t, func() { MakeSubGoals(goal, guarded, child) })
	require.Empty(t, takeRefusals())
}

// TestHoldStrongerCloses_RefusesAReconstructionThatReadsAHypothesis: a
// reconstruction that reads a hypothesis off its child's theorem takes
// the child's own goal and the child closed by contradiction, both of
// which rest on the hypothesis, and breaks on the child closed from no
// hypothesis. The gate refuses it in that reading.
func TestHoldStrongerCloses_RefusesAReconstructionThatReadsAHypothesis(t *testing.T) {
	require.Empty(t, takeRefusals(), "no test before this one left a refusal")
	q := core.Var("q", core.TypeBool())
	goal, child, _, guarded := doubleNegationStep(q)
	reading := func(thms ...Prop) Prop {
		_ = thms[0].Hyp(0)
		return guarded(thms...)
	}

	refusal := func() (r any) {
		defer func() { r = recover() }()
		MakeSubGoals(goal, reading, child)
		return nil
	}()
	require.NotNil(t, refusal, "the reconstruction is refused at the step's creation")
	require.True(t, utils.IsFault(refusal), "a refusal is a fault")
	text := fmt.Sprint(refusal)
	require.Contains(t, text, "stronger_close_gate_test.go", "the refusal names where the step was made")
	require.Contains(t, text, "child(ren) [0] closed from no hypothesis")
	require.Equal(t, []string{text}, takeRefusals(), "the refusal is kept as well as panicked with")

	require.NotPanics(t, func() { MakeSubGoals(goal, guarded, child) },
		"a reconstruction that reads none takes the child in both readings")
	require.Empty(t, takeRefusals())
}

// A child that states ⊥ is closed by no theorem from no hypothesis, and
// one over a hypothesis is its own close by contradiction: the gate
// does not ask about it in either reading.
func TestHoldStrongerCloses_LeavesAChildThatStatesBottom(t *testing.T) {
	q, r := core.Var("q", core.TypeBool()), core.Var("r", core.TypeBool())
	goal, child := MakeProp(F, q, r), MakeProp(F, q)
	reading := func(thms ...Prop) Prop {
		_ = thms[0].Hyp(0)
		return thms[0]
	}
	require.NotPanics(t, func() { MakeSubGoals(goal, reading, child) })
	require.Empty(t, takeRefusals())
}

// A child with no hypothesis is closed by no stronger theorem than its
// own goal, and the gate does not ask about it.
func TestHoldStrongerCloses_LeavesAChildWithNoHypothesis(t *testing.T) {
	goal, child, bridging, _ := doubleNegationStep()
	require.NotPanics(t, func() { MakeSubGoals(goal, bridging, child) })
	require.Empty(t, takeRefusals())
}

// A refusal is a panic, and a recover that reads nothing can still drop
// it. The run's verdict reads the record, not the panic.
func TestHoldStrongerCloses_ARecoveredRefusalFailsTheRun(t *testing.T) {
	code, refused := strongerCloseVerdict(0)
	require.Zero(t, code)
	require.Empty(t, refused)

	q := core.Var("q", core.TypeBool())
	goal, child, bridging, _ := doubleNegationStep(q)
	func() {
		defer func() { _ = recover() }()
		MakeSubGoals(goal, bridging, child)
	}()
	code, refused = strongerCloseVerdict(0)
	require.Equal(t, 1, code)
	require.Len(t, refused, 1)
	code, _ = strongerCloseVerdict(2)
	require.Equal(t, 2, code, "a failing run keeps its own code")
	takeRefusals()
}
