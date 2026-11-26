package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestSimpWith_Flip_EngineDispatch exercises the LemmaWithSpec.Flip
// surface at the engine boundary: JSON reaches TacticReq, resolveSimpWithRules
// validates and threads the flip bit, engine dispatch calls
// ApplySimpWithFlipped, and the flipped rule fires right-to-left on the
// session's focused goal — closing where the natural direction can't.
//
// Proto/replay round-trip (SimpWithProto.rule_flip → decode → re-run
// via ApplySimpWithFlipped) is covered end-to-end in
// prover/proof's TestApplySimpWithFlipped_DriverEndToEnd —
// no need to duplicate it here.
//
// Fixture: rule `∀p:bool. p = h(p)` over the goal's own `h`, proved in
// a section of its own, since a rule given by text is used once it is
// proved. Natural direction rewrites `_` (any bool) to `h(_)`,
// expanding; flipped rewrites `h(_)` to `_`, contracting.
//
// Goal `Q ⊢ h(Q)` — the flipped rewrite of `h(Q)` in the conclusion
// yields `Q`, which is a goal hyp. The natural direction would wrap
// Q's occurrences in h — it can't reduce the conclusion to a hyp form.
func TestSimpWith_Flip_EngineDispatch(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("Q:bool, h:bool→bool, Q ⊢ h(Q)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	ruleText := "forall p:bool. p = h(p)"
	rule := dsl.ParsePropText("h:bool→bool ⊢ " + ruleText)
	require.Empty(t, rule.Errors, "parse: %v", rule.Errors)
	s.AddGoal(rule.Prop)
	s.rebuildGoalIndex()
	closeSectionTrusted(t, s.sections[1].root)

	// Actual: flip fires the rule right-to-left; `h(Q) → Q` in the
	// conclusion; the residual `⊢ Q` closes by `assumption` against
	// the Q hyp.
	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "simp_with",
			WithLemmas: []LemmaWithSpec{{Text: ruleText, Flip: true}},
		},
	})
	require.NoError(t, err, "simp_with flip:true must not error")
	require.True(t, out.Success,
		"simp_with with flip:true must fire the rule right-to-left")

	// Close every remaining leaf — the residual `⊢ Q` closes by
	// `assumption`.
	for {
		stateRes, gerr := e.InspectState(ctx, info.ID)
		require.NoError(t, gerr)
		if stateRes.NumOpen == 0 {
			break
		}
		closed := false
		for _, og := range stateRes.Goals {
			for _, tac := range []string{"assumption", "auto"} {
				aout, aerr := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
					GoalID: og.ID,
					Tactic: TacticReq{Type: tac},
				})
				if aerr == nil && aout.Success {
					closed = true
					break
				}
			}
			if closed {
				break
			}
		}
		if !closed {
			for i, og := range stateRes.Goals {
				t.Logf("open leaf [%d] id=%s: %s", i, og.ID, ext.PrintTerm(og.Statement.Conclusion()))
			}
			require.Fail(t, "every child must close by assumption/auto")
		}
	}
}

// TestSimpWith_Flip_RejectsNonEquationShape: flip:true on a fact-shaped
// rule (no equation head after ∀-strip) is a typed error at
// resolveSimpWithRules — the driver never sees an ill-formed input, and
// the session stays unchanged. This is the upfront-validation contract
// (tactic.RuleFlippable) that keeps the flip surface honest — even with a
// junky rule shape the agent gets a clear error naming the constraint.
func TestSimpWith_Flip_RejectsNonEquationShape(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("P:A->bool, a:A ⊢ P(a)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	// A fact rule: ∀x:A. P(x) has no equation head — flip is undefined.
	refusal := stepRefusal(t, e, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "simp_with",
			WithLemmas: []LemmaWithSpec{{Text: "forall x:A. P(x)", Flip: true}},
		},
	})
	assert.Contains(t, refusal, "flip:true needs an equation to turn around")
	stateRes, gerr := e.InspectState(ctx, info.ID)
	require.NoError(t, gerr)
	assert.Equal(t, 1, stateRes.NumOpen, "goal must remain open and unchanged")
}
