// cross_type_tactics_test.go — the session tactics that close the
// cross-type-level citation gap:
//
//   - `type_inst`: a polymorphic entry read AT a type instance —
//     the tactic that discharges the foreign-instance obligation a
//     polymorphic `lemma` install leaves open (§"a polymorphic dep
//     cited at a FOREIGN type instance leaves a residual no session
//     tactic can close");
//   - `by` + with_lemmas.type_specialize: the cross-type premise inside
//     a premise-disciplined close (§"Session `by`'s with_lemmas rejects
//     type_specialize");
//   - `ac_regroup`: the AC kit's goal face as a session move (§"the AC
//     regroup has no session tactic").
package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestTypeInstTactic_ClosesForeignInstance: the session goal is the
// finite_set.FiniteImage entry at a concrete instance (A:=num, B:=num→bool) — the
// exact leaf a polymorphic `lemma` install leaves open at a foreign
// instance. `type_inst` with the entry's key closes it, σ recovered from
// the goal itself.
func TestTypeInstTactic_ClosesForeignInstance(t *testing.T) {
	lemProp := finiteImageLemma(t)

	goalProp, err := parsePropTextInGoalScope(
		"∀s:(num → bool). ∀f:(num → (num → bool)). finite(image(f, s)) ∨ ¬finite(s)",
		lemProp, nil)
	require.NoError(t, err)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(goalProp)
	s.rebuildGoalIndex()
	var gid string
	for id, ge := range s.goalIndex {
		if ge.sectionID == 0 {
			gid = id
			break
		}
	}
	require.NotEmpty(t, gid)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "type_inst", LemmaKey: autoWithFiniteImageKey},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "type_inst must close the entry's own instance")
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestTypeInstTactic_NonInstanceErrors: a goal that is NOT a type
// instance of the entry errors with the tactic's own message instead of
// silently degrading.
func TestTypeInstTactic_NonInstanceErrors(t *testing.T) {
	lemProp := finiteImageLemma(t)

	goalProp, err := parsePropTextInGoalScope("s:(num → bool) ⊢ finite(s)", lemProp, nil)
	require.NoError(t, err)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(goalProp)
	s.rebuildGoalIndex()
	var gid string
	for id, ge := range s.goalIndex {
		if ge.sectionID == 0 {
			gid = id
			break
		}
	}

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "type_inst", LemmaKey: autoWithFiniteImageKey},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	assert.Contains(t, out.Diagnostics[len(out.Diagnostics)-1].Message, "not a type instance")
}

// TestByTactic_TypeSpecializedPremise: a `by` premise carrying an
// explicit type_specialize σ — the session spelling of the chapter
// `By(…, ctx.AtTypes(dep, τ…))` — resolves, installs EXACTLY (no
// goal-side re-adaptation), and the claim child closes through the
// type-instance auto-match channel.
func TestByTactic_TypeSpecializedPremise(t *testing.T) {
	e, sid, gid := autoWithTypeInstanceFixture(t,
		"s:(num → bool), f:(num → (num → bool)) ⊢ finite(image(f, s)) ∨ ¬finite(s)")

	// Capture the goal's node before the apply — a successful close
	// rebuilds the goal index, so the id does not survive it.
	s, _ := e.getSession(sid)
	root := s.goalIndex[gid].node

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "by",
			WithLemmas: []LemmaWithSpec{{
				Key:            autoWithFiniteImageKey,
				TypeSpecialize: map[string]string{"A": "num", "B": "(num → bool)"},
			}},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("by diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success,
		"by with a type_specialize'd premise must close: the σ'd install is exact "+
			"and its claim child is a type instance of the entry")
	assert.Equal(t, 0, out.State.NumOpen)

	// The recorded composite carries exact on the premise — the wire
	// contract that keeps replay on the exact-install path.
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
			"a type_specialize'd premise must record exact=true")
	}
}

// TestACRegroupTactic_ClosesRearrangement: the focused goal is the bare
// equation between two +-sums over one leaf multiset; `ac_regroup` with
// nat_arith.AddAssoc / nat_arith.AddSym derives the rearrangement and
// closes it — the leg real_ring's members had to leave open in-session
// (§"the AC regroup has no session tactic").
func TestACRegroupTactic_ClosesRearrangement(t *testing.T) {
	assocEntry, ok := registryEntry("nat_arith.AddAssoc")
	require.True(t, ok, "nat_arith.AddAssoc is registered")
	assocProp := assocEntry.Statement().Prop

	goalProp, err := parsePropTextInGoalScope(
		"a:num, b:num, c:num ⊢ (a + b) + c = c + (b + a)", assocProp, nil)
	require.NoError(t, err)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(goalProp)
	s.rebuildGoalIndex()
	var gid string
	for id, ge := range s.goalIndex {
		if ge.sectionID == 0 {
			gid = id
			break
		}
	}
	require.NotEmpty(t, gid)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:  "ac_regroup",
			Assoc: "nat_arith.AddAssoc",
			Sym:   "nat_arith.AddSym",
		},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "ac_regroup must close the rearrangement equation")
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestACRegroupTactic_NonEquationErrors: a non-equation goal surfaces
// the kit's own strip-the-binders diagnostic through the RPC error
// channel.
func TestACRegroupTactic_NonEquationErrors(t *testing.T) {
	assocEntry, ok := registryEntry("nat_arith.AddAssoc")
	require.True(t, ok, "nat_arith.AddAssoc is registered")
	assocProp := assocEntry.Statement().Prop

	goalProp, err := parsePropTextInGoalScope(
		"a:num, b:num ⊢ ∀c:num. (a + b) + c = c + (b + a)", assocProp, nil)
	require.NoError(t, err)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(goalProp)
	s.rebuildGoalIndex()
	var gid string
	for id, ge := range s.goalIndex {
		if ge.sectionID == 0 {
			gid = id
			break
		}
	}

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:  "ac_regroup",
			Assoc: "nat_arith.AddAssoc",
			Sym:   "nat_arith.AddSym",
		},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	assert.Contains(t, out.Diagnostics[len(out.Diagnostics)-1].Message, "strip the")
}
