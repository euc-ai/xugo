package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestSimpWith_RecordProtoReplayRoundtrip is the acceptance test for the
// record/emit/replay-reuse design on simp_with: ONE recorded SimpWith
// ministep whose serialized proto carries the RESOLVED rule props, and
// whose replay re-runs the SAME executor (proof.ApplySimpWith) on the
// recorded goal, reproducing the identical children.
//
//  1. record: engine dispatch resolves the with_lemmas entries and
//     applies simp_with → _SimpWithStep ministep (a conditional Horn rule
//     whose side condition discharges against the goal hyp).
//  2. serialize: the section's DetailedProofProto through the wire.
//  3. decode: exactly one StepProto_SimpWith carrying the parsed rule.
//  4. replay: rebuild the recorded goal + rules from the proto pool and
//     re-run proof.ApplySimpWith — the identical call emitted Build_X
//     code (`Do(ctx.SimpWith(...))` → same _SimpWithStep.apply) executes.
func TestSimpWith_RecordProtoReplayRoundtrip(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// A VALID conditional congruence rule (∀x. x=a ⇒ f(x)=f(a)), which a
	// section of its own proves by bare `auto` (one paramodulation
	// step) — no registry fixture needed. The condition b=a discharges
	// against the goal hyp; the rewritten residual P(f(b))→P(f(a))
	// closes by `assumption` against the P(f(a)) hyp.
	res := dsl.ParsePropText(
		"f:num→num, P:num→bool, a:num, b:num, b = a, P(f(a)) ⊢ P(f(b))")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	ruleText := "forall x:num. (x = a) => (f(x) = f(a))"
	proveSectionByAuto(t, e, s, info.ID, "f:num→num, a:num ⊢ "+ruleText)
	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "simp_with",
			WithLemmas: []LemmaWithSpec{{Text: ruleText}},
		},
	})
	require.NoError(t, err)
	require.True(t, out.Success,
		"simp_with must fire the conditional rule with the b=a hyp discharge")

	// The rule's obligation closed on its section; close the residual by
	// assumption.
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
		require.True(t, closed, "every child must close by assumption/auto")
	}

	// (2) Serialize the proof tree.
	detailed := sectionRecord(t, s.sections[0])

	// (3) Locate the SimpWith ministep.
	var simpSteps []*proof.StepProto
	for _, st := range detailed.Steps {
		if _, ok := st.Step.(*proof.StepProto_SimpWith); ok {
			simpSteps = append(simpSteps, st)
		}
	}
	require.Len(t, simpSteps, 1, "exactly one recorded SimpWith ministep")
	recorded := simpSteps[0]
	ruleRefs := recorded.Step.(*proof.StepProto_SimpWith).SimpWith.GetRules()
	require.Len(t, ruleRefs, 1, "the single with_lemmas entry is recorded verbatim")

	// (4) Replay from the recorded proto: rebuild goal + rules, re-run the
	// shared executor, and verify the rewrite reproduced — conclusion
	// P(f(b)) → P(f(a)).
	r := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
	g, _ := r.Prop(recorded.Goal)
	require.NotNil(t, g)
	rules := make([]core.Prop, len(ruleRefs))
	for i, ref := range ruleRefs {
		rules[i], _ = r.Prop(ref)
		require.NotNil(t, rules[i])
	}
	n := proof.CreateGoalStack(g)
	require.True(t, proof.ApplySimpWith(n, rules),
		"replaying the recorded SimpWith step on the recorded goal must fire")
	leaves := n.UnsolvedLeaves()
	// The last leaf is the rewritten residual; the rule's obligation,
	// where the replay leaves one, stands before it.
	require.NotEmpty(t, leaves)
	residual := leaves[len(leaves)-1]
	parsedConcl := dsl.ParsePropText("f:num→num, P:num→bool, a:num ⊢ P(f(a))")
	require.Empty(t, parsedConcl.Errors)
	assert.True(t, residual.Goal.Conclusion().AlphaEquals(parsedConcl.Prop.Conclusion()),
		"residual conclusion must be the rewritten P(f(a)), got %v", residual.Goal)
}

// TestSimpWith_NoProgressFailsCleanly: progress-or-fail — a rule set that
// doesn't fire returns a diagnostic error and leaves the session state
// untouched (no recorded ministep, goal still open in original form).
func TestSimpWith_NoProgressFailsCleanly(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("P:num→bool, a:num ⊢ P(a)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "simp_with",
			WithLemmas: []LemmaWithSpec{{Text: "forall x:num. (x + 0 = x)"}},
		},
	})
	// Either a typed error or success=false is acceptable; the session
	// must stay unchanged either way.
	if err == nil {
		assert.False(t, out.Success)
	}
	stateRes, gerr := e.InspectState(ctx, info.ID)
	require.NoError(t, gerr)
	assert.Equal(t, 1, stateRes.NumOpen, "goal must remain open and unchanged")
}

// TestSimpWith_EmptyRuleListRejected: wire-level validation.
func TestSimpWith_EmptyRuleListRejected(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("P:num→bool, a:num ⊢ P(a)")
	require.Empty(t, res.Errors)
	gid := s.AddGoal(res.Prop)

	refusal := stepRefusal(t, e, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with"},
	})
	assert.Contains(t, refusal, "non-empty with_lemmas")
	stateRes, gerr := e.InspectState(ctx, info.ID)
	require.NoError(t, gerr)
	assert.Equal(t, 1, stateRes.NumOpen)
}

// A rule whose clause is an atom under a Horn antecedent is named as a
// closure rule at resolution (rule_shape): it rewrites nothing, so the
// no-progress failure is read at the rule rather than sent down the
// exposed-redex ladder.
func TestSimpWith_HornAtomClauseNamedClosure(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("P:num→bool, Q:num→bool, a:num ⊢ Q(a)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "simp_with",
			WithLemmas: []LemmaWithSpec{{Text: "∀x:num. P(x) ⇒ Q(x)"}},
		},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	named := false
	for _, d := range out.Diagnostics {
		if d.Type == DiagRuleShape {
			named = true
			assert.Contains(t, d.Message, "a closure rule")
		}
	}
	assert.True(t, named, "the closure clause is named in the diagnostics: %+v", out.Diagnostics)
	message := out.Diagnostics[len(out.Diagnostics)-1].Message
	assert.Contains(t, message, "a closure rule")
	assert.Contains(t, message, "does not itself rewrite the target",
		"the no-progress diagnostic explains the atom clause's role")
}
