package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestByTactic_SparseTermSpecializePinsTheRung — a `by` premise whose
// term_specialize table is NOT a prefix of the stated binders (here
// finite_set.FiniteImage's `f`, skipping `s`) is the session spelling of the
// the chapter's `Where(dep, "f", …)`: the premise seeds the apply rung, the
// rung reads `s` off the goal, the leaf closes keylessly, the claim
// child certifies as a type instance of the entry, and the recorded
// composite carries the named table (no positional tuple).
func TestByTactic_SparseTermSpecializePinsTheRung(t *testing.T) {
	// The law is finite_set.FiniteImage, whose
	// statement — the form a key cite serves — reads ∀f s. finite(s) ⇒
	// finite(image(f, s)): the goal is its conclusion with the antecedent
	// resident, and pinning s (the SECOND binder) is the sparse table.
	e, sid, gid := autoWithTypeInstanceFixture(t,
		"s:(num → bool), f:(num → num) ⊢ finite(s) ⇒ finite(image(f, s))")
	s, _ := e.getSession(sid)
	root := s.goalIndex[gid].node
	stripped, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "intro"},
	})
	require.NoError(t, err)
	require.True(t, stripped.Success, "intro strips the antecedent into the context")
	require.Len(t, stripped.State.Goals, 1)

	finiteS := 0
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: stripped.State.Goals[0].ID,
		Tactic: TacticReq{
			Type:   "by",
			ByHyps: []ByHypSpec{{HypIndex: &finiteS}}, // the antecedent the rung discharges
			WithLemmas: []LemmaWithSpec{{
				Key:            autoWithFiniteImageKey,
				TermSpecialize: map[string]string{"s": "s"},
			}},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("by diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success, "the sparse table seeds the rung, which reads f off the goal")
	assert.Equal(t, 0, out.State.NumOpen)

	detailed := root.DetailedProofProto()
	require.NotNil(t, detailed)
	var byProto *proof.ByProto
	for _, st := range detailed.GetSteps() {
		if bp, ok := st.Step.(*proof.StepProto_By); ok {
			byProto = bp.By
		}
	}
	if assert.NotNil(t, byProto, "the by close must record a `by` composite") &&
		assert.Len(t, byProto.GetPremises(), 2) {
		pr := byProto.GetPremises()[1]
		if assert.Len(t, pr.GetNamed(), 1, "the named table is recorded") {
			assert.Equal(t, "s", pr.GetNamed()[0].GetBinder())
		}
		assert.Empty(t, pr.GetWitnesses(), "no positional tuple for a sparse table")
	}
}

// TestByTactic_SparseTermSpecializeUnknownBinder — a name that is no
// stated binder is refused at the door, listing the binders.
func TestByTactic_SparseTermSpecializeUnknownBinder(t *testing.T) {
	e, sid, gid := autoWithTypeInstanceFixture(t,
		"s:(num → bool), f:(num → (num → bool)) ⊢ finite(image(f, s)) ∨ ¬finite(s)")
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "by",
			WithLemmas: []LemmaWithSpec{{
				Key:            autoWithFiniteImageKey,
				TermSpecialize: map[string]string{"g": "f"},
			}},
		},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	assert.Contains(t, out.Diagnostics[len(out.Diagnostics)-1].Message, `∀-binder "g" not found`)
}
