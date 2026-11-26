package engine

// cite-node graft weakening — the record-side contract for root cause B
// (fork-prove-graft hyp-context mismatch).
//
// When the graft target was proved under a SMALLER hyp context than the
// citing focus (the standard fork-prove-graft shape: a worker session proves
// a ∀-closed claim hyp-free; the coordinator cites it under its full local
// context), ApplyCiteNode must materialize the weakening as an explicit
// _ClearHypsStep between the assert's claim child and the spliced worker
// subtree. Every recorded parent→child transition then matches its
// ministep's actual semantics, so replay re-derives the identical goal
// sequence from the recorded ministeps alone — no emit-side weakening
// inference.
//
// A splice that put the worker's root ministep directly on the claim
// child would record a step claiming (e.g.) "StripQuant: Γ_n ⊢ ψ →
// Γ_worker ⊢ ψ'", silently dropping hyps in a transition StripQuant cannot
// perform — a wire shape emit would have to invent compensators for.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

func TestCiteNodeGraft_WeakeningRecordedExplicitly(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	// --- Session A (the "worker"): prove ⊢ y = y hyp-free; the close
	// publishes it to the engine-global derivation pool. ---
	y := ext.Var("y", core.TypeBool())
	psi := prop.MakeProp(core.Eq(y, y))
	infoA, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sA, err := e.getSession(infoA.ID)
	require.NoError(t, err)
	resA, err := e.ApplyStep(ctx, infoA.ID, &ApplyStepRequest{
		GoalID: sA.AddGoal(psi),
		Tactic: TacticReq{Type: "refl"},
	})
	require.NoError(t, err)
	require.True(t, resA.Success)

	// --- Session B (the "coordinator"): focus {p, q ⊢ x = x} — two hyps
	// the worker's sequent does not carry. ---
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	x := ext.Var("x", core.TypeBool())
	focus := prop.MakeProp(core.Eq(x, x), p.Core(), q.Core())
	infoB, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sB, err := e.getSession(infoB.ID)
	require.NoError(t, err)
	resB, err := e.ApplyStep(ctx, infoB.ID, &ApplyStepRequest{
		GoalID: sB.AddGoal(focus),
		Tactic: TacticReq{Type: "cite-node", NodeID: closedNodeID(0, psi)},
	})
	require.NoError(t, err)
	require.True(t, resB.Success, "pool graft under a larger hyp context must succeed: %+v", resB.Diagnostics)

	// --- Live tree shape: assert → claim child {p,q ⊢ ψ} whose ministep is
	// the EXPLICIT ClearHyps bridge, whose single child is the worker's
	// hyp-free sequent (proved). ---
	root := sB.sections[0].root
	require.Len(t, root.Children(), 2)
	claim := root.Children()[0]
	require.True(t, claim.Proved(), "grafted claim branch must be closed")
	require.Equal(t, 2, claim.Goal.NumHyps(), "claim child inherits the full context")
	require.Len(t, claim.Children(), 1, "weakening bridge must be a 1-child step")
	worker := claim.Children()[0]
	require.Equal(t, 0, worker.Goal.NumHyps(), "bridge child is the worker's own hyp-free sequent")
	require.True(t, worker.Goal.AlphaEquals(psi))

	// Close the residual so the tree serializes.
	require.Len(t, resB.State.Goals, 1)
	resB2, err := e.ApplyStep(ctx, infoB.ID, &ApplyStepRequest{
		GoalID: resB.State.Goals[0].ID,
		Tactic: TacticReq{Type: "refl"},
	})
	require.NoError(t, err)
	require.True(t, resB2.Success)
	require.True(t, root.Proved())

	// --- Wire shape: Assert, ClearHyps(0,1), Refl (worker), Refl (residual).
	detailed := root.DetailedProofProto()
	require.NotNil(t, detailed)
	r := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
	require.Len(t, detailed.Steps, 4)

	_, isAssert := detailed.Steps[0].Step.(*proof.StepProto_Assert)
	require.True(t, isAssert, "step 0 must be Assert, got %T", detailed.Steps[0].Step)
	clearStep, isClear := detailed.Steps[1].Step.(*proof.StepProto_ClearHyps)
	require.True(t, isClear, "step 1 must be the EXPLICIT ClearHyps bridge, got %T", detailed.Steps[1].Step)
	require.Equal(t, []int32{0, 1}, clearStep.ClearHyps.GetHypIndices())
	_, isRefl := detailed.Steps[2].Step.(*proof.StepProto_Refl)
	require.True(t, isRefl, "step 2 must be the worker's Refl, got %T", detailed.Steps[2].Step)
	_, isRefl2 := detailed.Steps[3].Step.(*proof.StepProto_Refl)
	require.True(t, isRefl2, "step 3 must be the residual's Refl, got %T", detailed.Steps[3].Step)

	// --- Replay determinism: re-derive the whole goal sequence from the
	// recorded ministeps alone (the exported Apply* used by emitted code)
	// and check every node key matches the recorded anchor. This is exactly
	// the emit+Build_X contract; it must hold with ZERO compensators. ---
	recordedKey := func(i int) core.PropKey {
		g, _ := r.Prop(detailed.Steps[i].Goal)
		require.NotNil(t, g)
		return g.AlphaKey()
	}
	n := proof.CreateGoalStack(focus)
	require.Equal(t, recordedKey(0), n.Goal.AlphaKey())
	require.True(t, proof.ApplyAssert(n, psi))
	replayClaim, replayResidual := n.Children()[0], n.Children()[1]
	require.Equal(t, recordedKey(1), replayClaim.Goal.AlphaKey(),
		"claim child must land on the recorded ClearHyps input")
	require.True(t, proof.ApplyClearHyps(replayClaim, []int{0, 1}))
	require.Equal(t, recordedKey(2), replayClaim.Children()[0].Goal.AlphaKey(),
		"ClearHyps output must land on the recorded worker sequent")
	require.True(t, proof.ApplyRefl(replayClaim.Children()[0]))
	require.Equal(t, recordedKey(3), replayResidual.Goal.AlphaKey(),
		"residual child must land on the recorded goal")
	require.True(t, proof.ApplyRefl(replayResidual))
	require.True(t, n.Proved())
}
