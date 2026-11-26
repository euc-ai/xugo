package engine

import (
	"context"
	"strconv"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// textRuleSession is a session whose first section is goal, its one
// open leaf returned.
func textRuleSession(t *testing.T, e *Engine, goal string) (s *Session, sid, gid string) {
	t.Helper()
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ = e.getSession(info.ID)
	res := dsl.ParsePropText(goal)
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid = s.AddGoal(res.Prop)
	s.rebuildGoalIndex()
	return s, info.ID, gid
}

// proveSectionByAuto states text as a further section of s and closes
// it with auto.
func proveSectionByAuto(t *testing.T, e *Engine, s *Session, sid, text string) {
	t.Helper()
	res := dsl.ParsePropText(text)
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, out.Success, "auto closes %s", text)
}

// stepRefusal is what a refused step answers: its error, or the
// messages of a step that did not succeed and is no engine fault.
func stepRefusal(t *testing.T, e *Engine, sid string, req *ApplyStepRequest) string {
	t.Helper()
	out, err := e.ApplyStep(context.Background(), sid, req)
	if err != nil {
		return err.Error()
	}
	require.False(t, out.Success, "the step is refused")
	require.Nil(t, out.EngineFault, "a refusal, not an engine fault")
	var refusal string
	for _, d := range out.Diagnostics {
		refusal += d.Message + "\n"
	}
	return refusal
}

// TestSimpWith_UnprovedTextRuleRefused: a rule given by text names no
// registry entry, so nothing certifies it but a proved section of the
// session that states it. A step whose text rule fires and is stated by
// none is refused, naming the rule, and the session is as it was,
// whether the rule is monomorphic or carries type letters the set adapts
// against the goal. A polymorphic text rule once took a source key
// computed from its own statement and closed its child on a promise no
// entry backs; the false rule below then completed a false section.
//
//	f:A→B, x:A, z:B ⊢ f(x) = z      rule  ∀y:A. f(y) = z
func TestSimpWith_UnprovedTextRuleRefused(t *testing.T) {
	for _, verb := range []string{"simp_with", "simp_all"} {
		t.Run(verb, func(t *testing.T) {
			e := newEngine(testEnv())
			ctx := context.Background()
			_, sid, gid := textRuleSession(t, e, "f:A→B, x:A, z:B ⊢ f(x) = z")

			refusal := stepRefusal(t, e, sid, &ApplyStepRequest{
				GoalID: gid,
				Tactic: TacticReq{Type: verb, WithLemmas: []LemmaWithSpec{{Text: "∀y:A. f(y) = z"}}},
			})
			require.Contains(t, refusal, verb+": lemma #0 (text ∀y:A. f(y) = z) is a rule given by text, and nothing certifies it")
			require.Contains(t, refusal, "The session is unchanged.\n  the rule: ⊢ ∀y.(f(y) = z)")

			state, err := e.InspectState(ctx, sid)
			require.NoError(t, err)
			require.Equal(t, 1, state.NumOpen, "the refusal leaves the section as it was")
			require.Equal(t, "⊢ f(x) = z", prop.PrintProp(state.Goals[0].Statement))
			require.False(t, state.Complete)
		})
	}
}

// TestSimpWith_TextRuleCertifiedByAProvedSection: the same step with a
// rule a proved section of the session states. The rule's obligation
// closes on that section, and the step leaves the residual alone.
//
//	b = a, P(f(a)) ⊢ P(f(b))      rule  ∀x. x = a ⇒ f(x) = f(a)
func TestSimpWith_TextRuleCertifiedByAProvedSection(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	s, sid, gid := textRuleSession(t, e, "f:num→num, P:num→bool, a:num, b:num, b = a, P(f(a)) ⊢ P(f(b))")
	const rule = "∀x:num. x = a ⇒ f(x) = f(a)"
	step := &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Text: rule}}},
	}

	refusal := stepRefusal(t, e, sid, step)
	require.Contains(t, refusal, "is a rule given by text, and nothing certifies it", "refused before the rule is proved")

	proveSectionByAuto(t, e, s, sid, "f:num→num, a:num ⊢ "+rule)
	out, err := e.ApplyStep(ctx, sid, step)
	require.NoError(t, err)
	require.True(t, out.Success, "the rule fires once a section proves it: %v", out.Diagnostics)
	require.Len(t, out.AutoMatched, 1, "the rule's obligation closed on the proved section")

	state, err := e.InspectState(ctx, sid)
	require.NoError(t, err)
	require.Equal(t, 1, state.NumOpen, "the residual is the one open goal")
	require.Contains(t, prop.PrintProp(state.Goals[0].Statement), "⊢ P(f(a))")
}

// TestSimpWith_TextRuleTheGoalHolds: an equation the goal holds rewrites
// with no obligation, so its text is a rule with nothing proved beside
// it. A conditional rule's obligation is the rule under no hypothesis,
// which the hypothesis does not certify: the step is refused, naming the
// hypothesis, and the same step citing it by hyp_index stands.
func TestSimpWith_TextRuleTheGoalHolds(t *testing.T) {
	ctx := context.Background()
	t.Run("an equation", func(t *testing.T) {
		e := newEngine(testEnv())
		const rule = "∀x:num. f(x) = a"
		_, sid, gid := textRuleSession(t, e, "f:num→num, P:num→bool, a:num, b:num, "+rule+", P(a) ⊢ P(f(b))")
		out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: gid,
			Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Text: rule}}},
		})
		require.NoError(t, err)
		require.True(t, out.Success, "the equation rewrites: %v", out.Diagnostics)
	})
	t.Run("a conditional rule", func(t *testing.T) {
		e := newEngine(testEnv())
		const rule = "∀x:num. x = a ⇒ f(x) = f(a)"
		s, sid, gid := textRuleSession(t, e, "f:num→num, P:num→bool, a:num, b:num, "+rule+", b = a, P(f(a)) ⊢ P(f(b))")
		refusal := stepRefusal(t, e, sid, &ApplyStepRequest{
			GoalID: gid,
			Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Text: rule}}},
		})
		held := -1
		for i, h := range s.sections[0].root.Goal.Hyps() {
			if ext.MatchesFORALL(h).IsZero() {
				continue
			}
			held = i
		}
		require.GreaterOrEqual(t, held, 0)
		require.Contains(t, refusal, "The goal holds the rule as hypothesis "+strconv.Itoa(held)+": name it by `hyp_index: "+strconv.Itoa(held)+"`")

		out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: gid,
			Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &held}}},
		})
		require.NoError(t, err)
		require.True(t, out.Success, "the hypothesis is the rule: %v", out.Diagnostics)
	})
}

// TestSimpWith_TextRuleTheNormalizerDecides: a rule whose normal form is
// ⊤ closes on no proved section that states it, so the refusal of its
// text does not send the author to prove one. It names the route the
// rule has, and that route stands: the rule asserted, its claim closed,
// and the hypothesis it leaves cited by hyp_index.
//
//	Q ⊢ Q ∧ Q      rule  ∀p. p = (p ∧ p), turned around
func TestSimpWith_TextRuleTheNormalizerDecides(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	const rule = "∀p:bool. p = (p ∧ p)"
	s, sid, gid := textRuleSession(t, e, "Q:bool, Q ⊢ Q ∧ Q")
	step := &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Text: rule, Flip: true}}},
	}

	refusal := stepRefusal(t, e, sid, step)
	require.Contains(t, refusal, "its normal form is ⊤")
	require.Contains(t, refusal, "`assert` it with the same text")
	require.NotContains(t, refusal, "add-goal", "a section does not certify it")

	// A section that states the rule changes nothing: the step is
	// refused in the same words.
	stated := dsl.ParsePropText(rule)
	require.Empty(t, stated.Errors, "parse: %v", stated.Errors)
	s.AddGoal(stated.Prop)
	s.rebuildGoalIndex()
	closeSectionTrusted(t, s.sections[1].root)
	require.Equal(t, refusal, stepRefusal(t, e, sid, step))

	// The route the refusal names.
	out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "assert", ClaimText: rule}})
	require.NoError(t, err)
	require.True(t, out.Success, "assert: %v", out.Diagnostics)
	require.Len(t, out.Produced, 2, "the claim and the goal with the rule a hypothesis")
	claim, residual := out.Produced[0].GoalID, out.Produced[1].GoalID
	out, err = e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: claim, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, out.Success, "auto closes the claim: %v", out.Diagnostics)

	entry, _, err := e.resolveFocusedGoal(s, residual)
	require.NoError(t, err)
	held := -1
	for i, h := range entry.node.Goal.Hyps() {
		if !ext.MatchesFORALL(h).IsZero() {
			held = i
		}
	}
	require.GreaterOrEqual(t, held, 0, "the asserted rule is a hypothesis of the goal")
	out, err = e.ApplyStep(ctx, sid, &ApplyStepRequest{
		GoalID: residual,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &held, Flip: true}}},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "the hypothesis rewrites Q ∧ Q to Q: %v", out.Diagnostics)
}
