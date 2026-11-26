package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestWithLemmas_KeyAndTextRefused: a with_lemmas entry naming both a
// key and a text is refused by name in each verb that takes the list,
// and so is a `lemma` naming both. The text was read as the statement
// and the key as what certifies it, so the request ended in the
// engine's panic over a key that backs no promise at that statement;
// the refusal leaves the goal as it was.
func TestWithLemmas_KeyAndTextRefused(t *testing.T) {
	both := []LemmaWithSpec{{Key: "extended_nonneg_real.SeriesPartialLe", Text: "∀y:A. f(y) = z"}}
	for name, tactic := range map[string]TacticReq{
		"by":        {Type: "by", WithLemmas: both},
		"simp_with": {Type: "simp_with", WithLemmas: both},
		"auto_with": {Type: "auto_with", WithLemmas: both},
		"lemma":     {Type: "lemma", LemmaKey: both[0].Key, LemmaText: both[0].Text},
	} {
		t.Run(name, func(t *testing.T) {
			e := newEngine(testEnv())
			ctx := context.Background()
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, _ := e.getSession(info.ID)
			res := dsl.ParsePropText("f:A→B, x:A, z:B ⊢ f(x) = z")
			require.Empty(t, res.Errors, "parse: %v", res.Errors)
			gid := s.AddGoal(res.Prop)
			s.rebuildGoalIndex()

			var refusal string
			require.NotPanics(t, func() {
				out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: tactic})
				if err != nil {
					refusal = err.Error()
					return
				}
				require.False(t, out.Success, "the request is refused")
				require.Nil(t, out.EngineFault, "a refusal, not an engine fault")
				for _, d := range out.Diagnostics {
					refusal += d.Message + "\n"
				}
			})
			require.Contains(t, refusal, `names both key "extended_nonneg_real.SeriesPartialLe" and text`)

			state, err := e.InspectState(ctx, info.ID)
			require.NoError(t, err)
			require.Equal(t, 1, state.NumOpen, "the refusal leaves the goal as it was")
		})
	}
}
