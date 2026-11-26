package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestComputeGoalChanges covers the diff helper directly — independent of
// any tactic. Three cases sketch the contract: identity → all zero;
// conclusion-only change → conclusion_changed=true; hyp-only changes →
// hyps_added/dropped counted, conclusion_changed=false.
func TestComputeGoalChanges(t *testing.T) {
	a := ext.Var("a", core.TypeBool())
	b := ext.Var("b", core.TypeBool())
	c := ext.Var("c", core.TypeBool())

	// before: a, b ⊢ c
	before := prop.MakeProp(c, a, b)

	t.Run("identity = all-zero", func(t *testing.T) {
		got := computeGoalChanges(before, before)
		assert.Equal(t, GoalChanges{}, got)
		assert.True(t, got.IsNoop())
	})

	t.Run("conclusion change only", func(t *testing.T) {
		after := prop.MakeProp(a.And(c), a, b) // hyps unchanged, concl c → a∧c
		got := computeGoalChanges(before, after)
		assert.Equal(t, GoalChanges{ConclusionChanged: true}, got)
		assert.False(t, got.IsNoop())
	})

	t.Run("hyp dropped only", func(t *testing.T) {
		after := prop.MakeProp(c, a) // dropped b
		got := computeGoalChanges(before, after)
		assert.Equal(t, GoalChanges{HypsDropped: 1}, got)
		assert.False(t, got.IsNoop())
	})

	t.Run("hyp added only", func(t *testing.T) {
		d := ext.Var("d", core.TypeBool())
		after := prop.MakeProp(c, a, b, d) // added d
		got := computeGoalChanges(before, after)
		assert.Equal(t, GoalChanges{HypsAdded: 1}, got)
		assert.False(t, got.IsNoop())
	})

	t.Run("mixed: hyp swapped (1 added + 1 dropped) + concl unchanged", func(t *testing.T) {
		d := ext.Var("d", core.TypeBool())
		after := prop.MakeProp(c, a, d) // dropped b, added d
		got := computeGoalChanges(before, after)
		assert.Equal(t, GoalChanges{HypsAdded: 1, HypsDropped: 1}, got)
		assert.False(t, got.IsNoop())
	})
}

// TestProbe_Changes_SplitConj surfaces the per-subgoal Changes diff for a
// branch outcome. split_conj on a ⊢ A∧B produces two subgoals (a ⊢ A and
// a ⊢ B); each has hyps unchanged and conclusion changed.
func TestProbe_Changes_SplitConj(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.And(q)))

	res, err := e.Probe(ctx, info.ID, &ProbeRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_conj"},
	})
	require.NoError(t, err)
	assert.Equal(t, ProbeSuccess, res.Outcome)
	assert.Equal(t, "branch", res.Effect)
	require.Len(t, res.Subgoals, 2)

	for i, sg := range res.Subgoals {
		assert.Equalf(t, 0, sg.Changes.HypsAdded, "subgoal %d: hyps_added", i)
		assert.Equalf(t, 0, sg.Changes.HypsDropped, "subgoal %d: hyps_dropped", i)
		assert.Truef(t, sg.Changes.ConclusionChanged, "subgoal %d: conclusion must differ from input", i)
		assert.Falsef(t, sg.Changes.IsNoop(), "subgoal %d must not be IsNoop", i)
	}
	assert.Equal(t, 1, s.buildStateView().NumOpen, "a probe does not commit the split")
}

// TestProbe_Changes_HypDroppedNotNoop: real `arith` recognizes an
// iff-tautology hyp (`∀x y z. (x ≤ y - z) ⇔ (x + z ≤ y)`),
// simplifies it to ⊤ and drops it; the resulting goal
// has the SAME conclusion but ONE fewer hyp. The printed Statement looks
// "unchanged" to a reader who only diffs the conclusion text;
// Changes.HypsDropped == 1 makes the structural progress explicit.
//
// Expected outcome:
//
//	Outcome    = success
//	Effect     = simplify   (NOT noop — something DID change)
//	Subgoals[0].Changes = {HypsDropped: 1, HypsAdded: 0, ConclusionChanged: false}
//	IsNoop()                = false
func TestProbe_Changes_HypDroppedNotNoop(t *testing.T) {
	installTestNatBundle() // of_num bridge
	installTestRealBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
	})

	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
	s, _ := e.getSession(info.ID)

	// That iff as a hyp; conclusion is a CONTINGENT real
	// claim (¬(M ≤ K), K free) that no rewrite decides — so the only progress
	// arith can make is dropping the tautology hyp. (The previous fixture
	// ¬(M ≤ M - &1) closes outright now that the unified arith stack carries
	// realMoveAcrossLeaf.)
	goalStr := "K:real, (forall x:real. forall y:real. forall z:real. (x <= y - z) <=> ((x + z) <= y)) " +
		"⊢ forall M:real. ~(M <= K)"
	pres := dsl.ParsePropText(goalStr)
	require.Empty(t, pres.Errors, "parse: %v", pres.Errors)
	goalID := s.AddGoal(pres.Prop)

	res, err := e.Probe(ctx, info.ID, &ProbeRequest{
		GoalID:   goalID,
		Tactic:   TacticReq{Type: "arith"},
		BudgetMs: 2000,
	})
	require.NoError(t, err)
	require.Equal(t, ProbeSuccess, res.Outcome,
		"arith should run (it identifies the hyp as a real-arith tautology); diagnostic=%q", res.Diagnostic)
	require.Len(t, res.Subgoals, 1, "expected one residual subgoal")

	ch := res.Subgoals[0].Changes
	t.Logf("Changes = %+v  (Effect = %q)", ch, res.Effect)

	// The hyp was dropped → hyps_dropped == 1. The conclusion is unchanged.
	assert.Equal(t, 1, ch.HypsDropped,
		"arith should have dropped the iff-tautology hyp (HypsDropped=1)")
	assert.Equal(t, 0, ch.HypsAdded, "no hyps added")
	assert.False(t, ch.ConclusionChanged,
		"conclusion unchanged: ¬(M ≤ K) is contingent — arith cannot decide it")
	assert.False(t, ch.IsNoop(),
		"a hyp WAS dropped — this is NOT a noop, regardless of how the printed "+
			"conclusion looks")
	assert.Equal(t, "simplify", res.Effect,
		"effect must be simplify (hyp dropped is meaningful progress)")
}

// TestApply_Changes_SplitConj is the apply-side mirror of
// TestProbe_Changes_SplitConj. After ApplyStep commits a split_conj,
// StepResult.Effect == "branch" and StepResult.Produced has one entry per
// new subgoal, each carrying its structural diff against the input.
func TestApply_Changes_SplitConj(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.And(q)))

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_conj"},
	})
	require.NoError(t, err)
	require.True(t, out.Success)
	assert.Equal(t, "branch", out.Effect)
	require.Len(t, out.Produced, 2)

	for i, pg := range out.Produced {
		assert.Equalf(t, 0, pg.Changes.HypsAdded, "produced[%d]: hyps_added", i)
		assert.Equalf(t, 0, pg.Changes.HypsDropped, "produced[%d]: hyps_dropped", i)
		assert.Truef(t, pg.Changes.ConclusionChanged,
			"produced[%d]: conclusion must differ", i)
	}
}

// TestApply_Changes_HypDropped is the apply-side mirror of
// TestProbe_Changes_HypDroppedNotNoop. Same scenario (real arith drops an
// iff-tautology hyp); apply reports Effect="simplify" + Produced[0].Changes
// with HypsDropped=1 — same shape probe reported, on the same call.
func TestApply_Changes_HypDropped(t *testing.T) {
	installTestNatBundle()
	installTestRealBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
	})

	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
	s, _ := e.getSession(info.ID)

	// Same contingent-conclusion fixture as TestProbe_Changes_HypDroppedNotNoop
	// (see the comment there — ¬(M ≤ M - &1) closes outright post-moveAcross).
	goalStr := "K:real, (forall x:real. forall y:real. forall z:real. (x <= y - z) <=> ((x + z) <= y)) " +
		"⊢ forall M:real. ~(M <= K)"
	pres := dsl.ParsePropText(goalStr)
	require.Empty(t, pres.Errors, "parse: %v", pres.Errors)
	goalID := s.AddGoal(pres.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID:   goalID,
		Tactic:   TacticReq{Type: "arith"},
		BudgetMs: 2000,
	})
	require.NoError(t, err)
	require.True(t, out.Success)
	assert.Equal(t, "simplify", out.Effect)
	require.Len(t, out.Produced, 1)

	ch := out.Produced[0].Changes
	t.Logf("apply Changes = %+v  Effect=%q", ch, out.Effect)
	assert.Equal(t, 1, ch.HypsDropped)
	assert.Equal(t, 0, ch.HypsAdded)
	assert.False(t, ch.ConclusionChanged)
	assert.False(t, ch.IsNoop())
}

// TestProbeApply_EffectParity is the cross-API regression: for the same
// (session, goal, tactic), probe.Effect and apply.Effect MUST agree.
// This is the contract the new shared classifyEffect enforces. Run on
// three representative shapes: branch (split_conj), simplify (arith
// hyp-drop), and close (refl).
func TestProbeApply_EffectParity(t *testing.T) {
	cases := []struct {
		name        string
		install     func()
		cleanup     func()
		setup       func(s *Session) string // adds goal, returns goalID
		tactic      TacticReq
		budgetMs    int
		wantEffect  string
		wantSuccess bool
	}{
		{
			name: "split_conj → branch",
			setup: func(s *Session) string {
				p := ext.Var("p", core.TypeBool())
				q := ext.Var("q", core.TypeBool())
				return s.AddGoal(prop.MakeProp(p.And(q)))
			},
			tactic:      TacticReq{Type: "split_conj"},
			wantEffect:  "branch",
			wantSuccess: true,
		},
		{
			name: "refl → close",
			setup: func(s *Session) string {
				a := ext.Var("a", core.TypeA())
				return s.AddGoal(prop.MakeProp(ext.WrapTerm(a).Eq(a)))
			},
			tactic:      TacticReq{Type: "refl"},
			wantEffect:  "close",
			wantSuccess: true,
		},
		{
			// A contingent atom (K free) — arith genuinely refuses. (The
			// prior fixture ¬(M ≤ M-&1) closes now that the unified arith
			// stack carries realMoveAcrossLeaf.)
			name: "arith on contingent ¬(M ≤ K) → fail (refuses)",
			install: func() {
				installTestNatBundle()
				installTestRealBundle()
			},
			cleanup: func() {
				setTestNatBundle(nil)
				setTestRealBundle(nil)
			},
			setup: func(s *Session) string {
				pres := dsl.ParsePropText("K:real ⊢ forall M:real. ~(M <= K)")
				return s.AddGoal(pres.Prop)
			},
			tactic:      TacticReq{Type: "arith"},
			budgetMs:    2000,
			wantEffect:  "", // empty when Outcome=fail / Success=false
			wantSuccess: false,
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if tc.install != nil {
				tc.install()
				t.Cleanup(tc.cleanup)
			}
			e := newEngine(testEnv())
			ctx := context.Background()

			// Probe in its own session, since probe needs an open goal too.
			info1, err := e.CreateSession(ctx)
			require.NoError(t, err)
			t.Cleanup(func() { _ = e.CloseSession(ctx, info1.ID) })
			s1, _ := e.getSession(info1.ID)
			gid1 := tc.setup(s1)
			probe, err := e.Probe(ctx, info1.ID, &ProbeRequest{
				GoalID:   gid1,
				Tactic:   tc.tactic,
				BudgetMs: tc.budgetMs,
			})
			require.NoError(t, err)

			// Apply on a fresh session with the same goal.
			info2, err := e.CreateSession(ctx)
			require.NoError(t, err)
			t.Cleanup(func() { _ = e.CloseSession(ctx, info2.ID) })
			s2, _ := e.getSession(info2.ID)
			gid2 := tc.setup(s2)
			apply, err := e.ApplyStep(ctx, info2.ID, &ApplyStepRequest{
				GoalID:   gid2,
				Tactic:   tc.tactic,
				BudgetMs: tc.budgetMs,
			})
			require.NoError(t, err)

			// Probe agreement:
			if tc.wantSuccess {
				assert.Equal(t, ProbeSuccess, probe.Outcome, "probe.Outcome")
				assert.Equal(t, tc.wantEffect, probe.Effect, "probe.Effect")
			} else {
				assert.NotEqual(t, ProbeSuccess, probe.Outcome,
					"probe.Outcome should not be success when apply refuses")
				assert.Empty(t, probe.Effect, "probe.Effect empty on non-success")
			}
			// Apply agreement:
			assert.Equal(t, tc.wantSuccess, apply.Success, "apply.Success")
			assert.Equal(t, tc.wantEffect, apply.Effect, "apply.Effect")
			if apply.Effect == "close" {
				assert.Empty(t, apply.Produced, "a close leaves no subgoal")
			}

			// The parity: probe.Effect == apply.Effect for the same call.
			assert.Equal(t, probe.Effect, apply.Effect,
				"probe.Effect must equal apply.Effect for the same (goal, tactic) — "+
					"this is the cross-API contract")
		})
	}
}
