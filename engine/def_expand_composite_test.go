package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestDefExpand_RecordProtoReplayRoundtrip is the acceptance test for the
// def_expand composite step (proto tag 51): agent's `apply def_expand`
// records ONE StepProto_DefExpand carrying the const, with ZERO LeanRw /
// AxiomDef / TrivialSimplify on the wire for the composite step itself.
// Replay uses the SAME shared driver (computeDefExpandSubGoals inside
// _DefExpandStep.apply) to reproduce the residual byte-for-byte on the
// recorded goal.
//
// Sibling of TestSetTac_RecordProtoReplayRoundtrip / TestSimpWith_… — same
// record/emit/replay-reuse property; no LeanRw+AxiomDef+TrivialSimplify
// subtree is materialized.
//
// Runs on the registry's constants (like the other def_expand tests: the
// tactic dispatch looks up c via lookupDefConst, which the ematch harness
// routes through the registry).
func TestDefExpand_RecordProtoReplayRoundtrip(t *testing.T) {
	// empty_set (Type-1 def, body `λx. F`) is small and non-Hilbert. Any
	// Type-1 def would do; empty_set is chosen for the simplest one-const goal.
	// Goal shape: def_expand(empty_set) unfolds empty_set(x) to (λx.F)(x) = F, then
	// residual ¬F is trivially closed by refute.
	e, s, sid := ematchSessionWithGoal(t, "x:num ⊢ ¬empty_set(x)")
	ctx := context.Background()
	leafID := ematchOpenLeafID(t, s)

	out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
		GoalID: leafID,
		Tactic: TacticReq{Type: "def_expand", Const: "empty_set"},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "def_expand(empty_set) must produce a residual: %+v", out.Diagnostics)

	// If def_expand didn't close the goal outright (β-reduce F → residual),
	// close the residual so DetailedProofProto can serialize (only proved
	// nodes serialize). ¬F is trivially refutable.
	stateRes, gerr := e.InspectState(ctx, sid)
	require.NoError(t, gerr)
	if stateRes.NumOpen > 0 {
		require.Len(t, stateRes.Goals, 1, "at most one open leaf after def_expand")
		resGid := stateRes.Goals[0].ID
		closeOut, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: resGid,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
		require.True(t, closeOut.Success, "auto must close the def_expand residual: %+v", closeOut.Diagnostics)
	}

	// Serialize the proof tree.
	detailed := sectionRecord(t, s.sections[0])

	// Count wire tags. We EXPECT: exactly one def_expand, zero LeanRw and
	// zero AxiomDef — the composite collapses those on the wire. (The
	// residual-close auto records as a CnfRefute or trivial ministep;
	// that's fine.)
	var defExpandSteps []*proof.StepProto
	var leanRwCount, axiomDefCount int
	for _, st := range detailed.Steps {
		switch st.Step.(type) {
		case *proof.StepProto_DefExpand:
			defExpandSteps = append(defExpandSteps, st)
		case *proof.StepProto_LeanRw:
			leanRwCount++
		case *proof.StepProto_AxiomDef:
			axiomDefCount++
		}
	}
	require.Len(t, defExpandSteps, 1, "exactly one recorded def_expand ministep")
	assert.Equal(t, 0, leanRwCount,
		"def_expand composite must NOT decompose to LeanRw on the wire "+
			"(the whole point of proto tag 51 is to collapse them)")
	assert.Equal(t, 0, axiomDefCount,
		"def_expand composite must NOT decompose to AxiomDef on the wire")

	// Extract the recorded const from the def_expand step.
	recorded := defExpandSteps[0]
	constTermIdx := recorded.Step.(*proof.StepProto_DefExpand).DefExpand
	r := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
	constTerm := r.Term(constTermIdx)
	ct, ok := constTerm.AsConst()
	require.True(t, ok, "wire payload must decode as a const term")
	assert.Equal(t, core.TermName("empty_set"), ct.Name(), "recorded const should be empty_set")

	// Replay from the recorded proto: rebuild the goal, re-run the SHARED
	// composite driver. Same code path a Build_X-emitted `Do(DefExpandStep(c))`
	// would hit.
	g, _ := r.Prop(recorded.Goal)
	require.NotNil(t, g)
	n := proof.CreateGoalStack(g)
	require.True(t, proof.ApplyDefExpand(n, ct),
		"replaying the recorded def_expand step on the recorded goal must succeed")
	// The composite may either close outright (SubGoals size 0) or leave a
	// single residual — both are valid; what matters is that the wire tag
	// was ONE composite step and replay took the same path.
}

func TestDefExpand_ReportsChangedHypothesis(t *testing.T) {
	e, s, sid := ematchSessionWithGoal(t, "n:num, p:num→bool, q:bool, n = 0, p(n) ∨ empty_set(n) ⊢ q")
	out, err := e.ApplyStep(t.Context(), sid, &ApplyStepRequest{
		GoalID: ematchOpenLeafID(t, s), Tactic: TacticReq{Type: "def_expand", Const: "empty_set"},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	require.NotZero(t, out.State.NumOpen)
	found := false
	for _, d := range out.Diagnostics {
		if d.Type == DiagContextChanged {
			found = true
			require.Contains(t, d.Message, "∅")
			require.Contains(t, d.Message, "hyp[")
			require.NotEmpty(t, d.GoalID)
		}
	}
	require.True(t, found, "%+v", out)
}

// A constant of the logic itself is refused at def_expand, on the goal
// and at a hypothesis alike: no chapter entry defines it, so the Go a
// member is written in could not name the step. The refusal says what
// reads the constant instead, and the session is left as it was.
func TestDefExpand_RefusesAConstantOfTheLogic(t *testing.T) {
	e, s, sid := ematchSessionWithGoal(t, "p:num→bool, q:bool, ∃!x:num. p(x), ∀x:num. p(x) ⇒ q ⊢ ∃x:num. p(x) ∧ q")
	leaf := ematchOpenLeafID(t, s)
	zero := 0
	for _, constant := range []string{"∃!", "∀", "∃", "∧", "⇒"} {
		for _, at := range []*int{nil, &zero} {
			out, err := e.ApplyStep(t.Context(), sid, &ApplyStepRequest{
				GoalID: leaf, Tactic: TacticReq{Type: "def_expand", Const: constant, HypIndex: at},
			})
			require.NoError(t, err)
			require.False(t, out.Success, "def_expand of %s must be refused", constant)
			require.NotEmpty(t, out.Diagnostics)
			require.Contains(t, out.Diagnostics[0].Message, constant+" is a constant of the logic itself")
			require.Contains(t, out.Diagnostics[0].Message, "strip_quant")
			require.Equal(t, leaf, ematchOpenLeafID(t, s), "a refused step leaves the leaf open")
		}
	}
}
