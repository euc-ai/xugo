package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestLineage_ResumeThenRestoreCheckpoint(t *testing.T) {
	for _, tc := range []struct {
		name        string
		failedFirst bool
	}{
		{name: "auto_0"},
		{name: "auto_1"},
		{name: "after-quantifiers"},
		{name: "auto_0", failedFirst: true},
	} {
		label := tc.name
		if tc.failedFirst {
			label += "/after-failed-apply"
		}
		t.Run(label, func(t *testing.T) {
			name := tc.name
			ctx := context.Background()
			store, dir := proof.NewMemoryCNFStore(), t.TempDir()
			a := lineageEngine(store, dir)
			info, err := a.CreateSession(ctx)
			require.NoError(t, err)
			s, err := a.getSession(info.ID)
			require.NoError(t, err)
			goal := lineageText(t, s, "∀p q:bool. p ⇒ q")
			before := openGoalTexts(s)
			if tc.failedFirst {
				failed, err := a.ApplyStep(ctx, info.ID, &ApplyStepRequest{
					GoalID: goal,
					Tactic: TacticReq{Type: "known", LemmaKey: "missing_checkpoint_test_lemma"},
				})
				require.NoError(t, err)
				require.False(t, failed.Success)
			}
			stripped := lineageApply(t, a, info.ID, goal, "strip_quant")
			require.Len(t, stripped.Produced, 1)
			if name != "auto_0" {
				before = openGoalTexts(s)
			}
			if name == "after-quantifiers" {
				_, err = a.Checkpoint(ctx, info.ID, name)
				require.NoError(t, err)
			}
			lineageApply(t, a, info.ID, stripped.Produced[0].GoalID, "strip_imp")

			for range 3 {
				b := lineageEngine(store, dir)
				resumed, err := b.ResumeSession(ctx, info.ID)
				require.NoError(t, err)
				require.Nil(t, resumed.Diverged)
				checkpoints, err := b.ListCheckpoints(ctx, info.ID)
				require.NoError(t, err)
				var checkpoint string
				for _, cp := range checkpoints {
					if cp.Name == name {
						checkpoint = cp.ID
					}
				}
				require.NotEmpty(t, checkpoint)
				require.NoError(t, b.Restore(ctx, info.ID, checkpoint))
				sb, err := b.getSession(info.ID)
				require.NoError(t, err)
				assert.Equal(t, before, openGoalTexts(sb))
			}

			c := lineageEngine(store, dir)
			replayed, err := c.ResumeSession(ctx, info.ID)
			require.NoError(t, err)
			require.Nil(t, replayed.Diverged)
			assert.Equal(t, replayed.Events, replayed.Replayed)
			sc, err := c.getSession(info.ID)
			require.NoError(t, err)
			assert.Equal(t, before, openGoalTexts(sc))
		})
	}
}
