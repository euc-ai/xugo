package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestByTactic_TermSpecializeFixingTypesIsExact — a `by` premise whose
// term_specialize witnesses fix every type variable of a polymorphic
// law is an explicit instance, the session twin of Go's typed `.At`:
// it installs EXACTLY (recorded `exact`, as under type_specialize), and
// its claim child certifies as a type instance of the entry. Left
// inexact, a witnessed law without its guard resident took its clause
// form at the inferred instance, and the close succeeded with a premise
// that "did not certify".
func TestByTactic_TermSpecializeFixingTypesIsExact(t *testing.T) {
	e, sid, gid := autoWithTypeInstanceFixture(t,
		"s:(num → bool), f:(num → (num → bool)) ⊢ finite(image(f, s)) ∨ ¬finite(s)")
	s, _ := e.getSession(sid)
	root := s.goalIndex[gid].node

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "by",
			WithLemmas: []LemmaWithSpec{{
				Key:            autoWithFiniteImageKey,
				TermSpecialize: map[string]string{"f": "f", "s": "s"},
			}},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("by diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success, "the witnesses fix A := num, B := num → bool; the instance installs and certifies")
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
		assert.Len(t, byProto.GetPremises(), 1) {
		pr := byProto.GetPremises()[0]
		assert.True(t, pr.GetExact(), "witnesses fixing every type variable are an explicit instance")
		assert.Len(t, pr.GetWitnesses(), 2)
	}
}

// TestByTactic_TermSpecializeAtTheGoalsOwnLettersIsExact — the instance
// the witnesses fix may be stated over the goal's OWN type letters: a
// law's `B` read at `A → bool`, or its two letters swapped. Every type
// variable of the law is bound by the tuple all the same, so the
// premise is as explicit as one at ground types, installs exactly and
// certifies. Whether the INSTANCE has type variables left is the wrong
// question: by it such a premise is inexact, takes its clause form, and
// the close ends "did not certify".
func TestByTactic_TermSpecializeAtTheGoalsOwnLettersIsExact(t *testing.T) {
	for _, tc := range []struct{ name, goal string }{
		{"a letter read at a type over the goal's letter",
			"s:(A → bool), f:(A → (A → bool)) ⊢ finite(image(f, s)) ∨ ¬finite(s)"},
		{"the law's two letters swapped",
			"s:(B → bool), f:(B → A) ⊢ finite(image(f, s)) ∨ ¬finite(s)"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e, sid, gid := autoWithTypeInstanceFixture(t, tc.goal)
			s, _ := e.getSession(sid)
			root := s.goalIndex[gid].node

			out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid,
				Tactic: TacticReq{
					Type: "by",
					WithLemmas: []LemmaWithSpec{{
						Key:            autoWithFiniteImageKey,
						TermSpecialize: map[string]string{"f": "f", "s": "s"},
					}},
				},
			})
			require.NoError(t, err)
			if !out.Success {
				t.Logf("by diagnostics: %+v", out.Diagnostics)
			}
			require.True(t, out.Success, "the witnesses bind both of the law's type variables; the instance installs and certifies")
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
				assert.Len(t, byProto.GetPremises(), 1) {
				assert.True(t, byProto.GetPremises()[0].GetExact(),
					"witnesses binding every type variable of the law are an explicit instance")
			}
		})
	}
}
