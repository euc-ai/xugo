package engine

import (
	"context"
	"sort"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestCollectStructuralMoves verifies that each parameterless structural
// tactic is reported exactly when its shape precondition matches the goal,
// and is absent when it does not. The enumerator is the agent's primary
// surface for picking structural moves, so wrong applicability claims
// either send the agent down dead ends or hide useful peels.
func TestCollectStructuralMoves(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	a := ext.Var("a", core.TypeBool())
	b := ext.Var("b", core.TypeBool())

	// COND with bool branches so it sits at top level — easier to reason
	// about than a non-bool cond inside a polymorphic application.
	cond := ext.Cond(a, b, b)

	cases := []struct {
		name     string
		goal     core.Prop
		expected []string // sorted set of expected tactic names
	}{
		{
			"strip_imp on concl A⇒B",
			prop.MakeProp(P.Apply(x).Imply(Q.Apply(x))),
			[]string{"strip_imp"},
		},
		{
			"split_disj on hyp A∨B",
			prop.MakeProp(Q.Apply(x).Core(), P.Apply(x).Or(Q.Apply(x))),
			[]string{"split_disj"},
		},
		{
			// Wide A∧B∧C (≥3 leaf conjuncts): BOTH split_conj (binary
			// peel of A from B∧C) and split_conj_all (flatten all three)
			// are applicable. The agent picks; split_conj_all saves the
			// extra peel on a wide flat conjunction.
			"split_conj + split_conj_all on wide A∧B∧C",
			prop.MakeProp(P.Apply(x).And(Q.Apply(x).And(P.Apply(y)))),
			[]string{"split_conj", "split_conj_all"},
		},
		{
			// Binary A∧B (2 leaves): split_conj_all is shape-gated OUT
			// (it would just reproduce split_conj), so only split_conj
			// is surfaced — no redundant n-ary entry.
			"split_conj alone on binary A∧B: split_conj_all is not surfaced",
			prop.MakeProp(P.Apply(x).And(Q.Apply(x))),
			[]string{"split_conj"},
		},
		{
			// Only strip_quant fires here — strip_imp applies to a top-level
			// ⇒, but the conclusion is a top-level ∀ wrapping a ⇒. The agent
			// peels ∀ first, then re-explore reports strip_imp on the body.
			"strip_quant on concl ∀x.body (strip_imp must NOT leak through the binder)",
			prop.MakeProp(ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x)))),
			[]string{"strip_quant"},
		},
		{
			"cond_rewrite when goal contains COND",
			prop.MakeProp(cond),
			[]string{"cond_rewrite"},
		},
		{
			"strip_quant on hyp ∃x. body (existential gets peeled)",
			prop.MakeProp(P.Apply(y).Core(), ext.Exists(x)(P.Apply(x))),
			[]string{"strip_quant"},
		},
		{
			"atomic goal — no structural moves apply",
			prop.MakeProp(P.Apply(x).Core()),
			nil,
		},
		{
			// Dedup A∧A reports split_conj as applicable (produces ⊢A
			// via the dedup branch). The agent sees this as a valid
			// structural move; applying it succeeds with one subgoal.
			"split_conj on degenerate A∧A still reports as applicable",
			prop.MakeProp(P.Apply(x).And(P.Apply(x))),
			[]string{"split_conj"},
		},
		{
			// Trivial-collapse A⇒A: strip_imp NOT reported (A⇒A is
			// trivially T; strip_imp would be useless. Use auto/refute.)
			"strip_imp on degenerate A⇒A NOT reported (use auto/refute)",
			prop.MakeProp(P.Apply(x).Imply(P.Apply(x))),
			nil,
		},
		{
			// concl A ⇔ B — split_iff is the right move (gives A⊢B and
			// B⊢A). Before this surfaced, agents had only `case_split`
			// or `simplify`, both worse fits. `Eq` of two bool terms is
			// the term-level iff; the formatter prints it as `⇔`.
			//
			// `symm` and `congr` also fire here because A ⇔ B is `=`
			// at the term level with α-distinct sides (and `=` is what
			// our LEAN-style equality moves key off). All three are
			// real choices the agent might want — split_iff is the
			// idiomatic structural move, symm flips the direction, and
			// congr decomposes structurally.
			"split_iff on concl A⇔B",
			prop.MakeProp(P.Apply(x).Eq(Q.Apply(x))),
			[]string{"congr", "split_iff", "symm"},
		},
		{
			// Degenerate A⇔A: split_iff NOT reported. Same rationale as
			// strip_imp on A⇒A — simplify/auto trivializes it. `refl`
			// IS reported, because that's exactly the right move for
			// `t = t`.
			"split_iff on degenerate A⇔A NOT reported",
			prop.MakeProp(P.Apply(x).Eq(P.Apply(x))),
			[]string{"refl"},
		},
		{
			// hyp A ⇔ B → case-analyze. Distinct from split_iff (which
			// is for the conclusion).
			"split_hyp_iff on hyp A⇔B",
			prop.MakeProp(P.Apply(y).Core(), P.Apply(x).Eq(Q.Apply(x))),
			[]string{"split_hyp_iff"},
		},
		{
			// hyp A ⇒ B → case-analyze. Different from strip_imp (which
			// is for the conclusion).
			"split_hyp_imply on hyp A⇒B",
			prop.MakeProp(P.Apply(y).Core(), P.Apply(x).Imply(Q.Apply(x))),
			[]string{"split_hyp_imply"},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			moves := collectStructuralMoves(tc.goal)
			got := make([]string, 0, len(moves))
			for _, m := range moves {
				got = append(got, m.Tactic)
				assert.NotEmpty(t, m.Description, "description must be non-empty")
			}
			sort.Strings(got)
			expected := append([]string{}, tc.expected...)
			sort.Strings(expected)
			assert.Equal(t, expected, got, "applicability mismatch")
		})
	}
}

// TestApplyStripImp_OnTautology_ReturnsFailureNotPanic pins down the
// invariant that agent-callable structural tactics must return a clean
// "not applicable" result on degenerate shapes (here: A ⇒ A) instead of
// panicking. An assert in basic_tactics.go firing there would crash the
// engine — an HTTP 500 behind the serve's recover — for what is
// conceptually "the shape doesn't deserve this tactic, try something
// else (auto will close it)".
func TestApplyStripImp_OnTautology_ReturnsFailureNotPanic(t *testing.T) {
	p := ext.Var("p", core.TypeBool())
	target := prop.MakeProp(p.Imply(p)) // A ⇒ A

	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	s.AddGoal(target)
	s.rebuildGoalIndex()
	var goalID string
	for k := range s.goalIndex {
		goalID = k
	}

	require.NotPanics(t, func() {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "strip_imp"},
		})
		require.NoError(t, err)
		assert.False(t, res.Success,
			"strip_imp on A⇒A must return success=false, not crash; got success=true state=%+v",
			res.State)
		assert.NotEmpty(t, res.Diagnostics, "should report tactic_failure with repair hints")
	})
}

// TestApplyCondRewrite_OnNonCondGoal_Fails pins down the apply-gating
// semantics: agent calling apply{cond_rewrite} on a goal with no COND
// gets a clean failure, not a silent basic-rewrite under a misleading
// tactic name. The shape predicate in structural.go is the single
// source of truth for both the enumerator and direct-apply gating, so
// the two stay aligned: enumerator hides the option, apply rejects it.
func TestApplyCondRewrite_OnNonCondGoal_Fails(t *testing.T) {
	// p ⇒ q — no COND anywhere.
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	target := prop.MakeProp(p.Imply(q))

	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, _ := e.getSession(info.ID)
	s.AddGoal(target)
	s.rebuildGoalIndex()
	var goalID string
	for k := range s.goalIndex {
		goalID = k
	}

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "cond_rewrite"},
	})
	require.NoError(t, err)
	assert.False(t, res.Success,
		"cond_rewrite on a goal without COND must fail-with-diagnostic, "+
			"not silently invoke basic rewrites under a misleading name")
}

// TestApplySplitIff_OnIffGoal asserts split_iff actually applies and
// produces the expected two-direction subgoals via the apply RPC, not
// just that it appears in the structural-fact enumeration.
func TestApplySplitIff_OnIffGoal(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(P.Apply(x).Eq(Q.Apply(x)))

	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(target)
	s.rebuildGoalIndex()
	var goalID string
	for k := range s.goalIndex {
		goalID = k
	}

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_iff"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "split_iff must apply on a top-level A⇔B goal")
	assert.Equal(t, 2, res.State.NumOpen,
		"split_iff produces two subgoals (A⊢B and B⊢A); got num_open=%d",
		res.State.NumOpen)
}

// TestApplySplitConjAll_OnWideConj asserts split_conj_all applies via the
// apply RPC and flattens a wide A∧B∧C into THREE flat subgoals in one step
// (vs the two a single binary split_conj would yield).
func TestApplySplitConjAll_OnWideConj(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	// ⊢ P(x) ∧ Q(x) ∧ P(y)  (right-nested A∧(B∧C)).
	target := prop.MakeProp(P.Apply(x).And(Q.Apply(x).And(P.Apply(y))))

	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(target)
	s.rebuildGoalIndex()
	var goalID string
	for k := range s.goalIndex {
		goalID = k
	}

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "split_conj_all"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "split_conj_all must apply on a wide A∧B∧C goal")
	assert.Equal(t, 3, res.State.NumOpen,
		"split_conj_all flattens A∧B∧C into three flat subgoals; got num_open=%d",
		res.State.NumOpen)
}

// TestApplyHypIndex_TargetsRequestedHyp is the engine-RPC regression
// for split_disj ignoring hyp_index and always picking the first ∨-hyp:
// a caller asked to split hyp 15 (a specific ∨) but got hyp 13 split
// instead because the ministep did not consume the wire-level
// hyp_index. This test locks in the wire contract at the engine
// dispatch layer for the four hyp-targeted tactics sharing
// HypIndexProto: split_disj / split_hyp_iff / split_hyp_imply, and
// strip_quant, whose pick-first form strips a ∀-headed conclusion
// before it looks at any hyp and then opens the first ∃-hyp it scans
// to.
func TestApplyHypIndex_TargetsRequestedHyp(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	z := ext.Var("z", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	A := P.Apply(x)
	B := Q.Apply(y)
	C := R.Apply(z)
	G := ext.Var("g", core.TypeBool())

	// findIndex translates "the A∨C hyp" into whatever slot
	// MakeProp's canonical hyp sort put it in.
	findIndex := func(g core.Prop, target core.Term) int {
		for i := range g.NumHyps() {
			if g.Hyp(i).AlphaEquals(target) {
				return i
			}
		}
		return -1
	}
	setup := func(t *testing.T, target core.Prop) (*Engine, string, string) {
		e := newEngine(testEnv())
		ctx := context.Background()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)
		s.AddGoal(target)
		s.rebuildGoalIndex()
		var goalID string
		for k := range s.goalIndex {
			goalID = k
		}
		return e, info.ID, goalID
	}
	ctx := context.Background()
	// hasHyp checks a resulting GoalView for a specific hyp — the
	// discriminator between "split targeted the right ∨-hyp" and
	// "wrong pick".
	hasHyp := func(gv GoalView, want core.Term) bool {
		for _, h := range gv.Hypotheses {
			if h.AlphaEquals(want) {
				return true
			}
		}
		return false
	}

	// --- split_disj ------------------------------------------------------
	t.Run("split_disj/hyp_index steers to requested ∨-hyp", func(t *testing.T) {
		AorB := A.Or(B).Core()
		AorC := A.Or(C).Core()
		target := prop.MakeProp(G.Core(), AorB, AorC)
		iAC := findIndex(target, AorC)
		require.NotEqual(t, -1, iAC)

		e, sid, goalID := setup(t, target)
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "split_disj", HypIndex: &iAC},
		})
		require.NoError(t, err)
		require.True(t, res.Success)
		require.NotNil(t, res.State)
		require.Equal(t, 2, len(res.State.Goals))

		// split_disj hyp A∨C ⊢ G produces [A ⊢ G] and [C ⊢ G]. A goal
		// carrying B on either side would prove the "wrong hyp got
		// split" bug is back — B was a marker for A∨B, the other hyp.
		gotA, gotC := false, false
		for _, g := range res.State.Goals {
			if hasHyp(g, A.Core()) {
				gotA = true
			}
			if hasHyp(g, C.Core()) {
				gotC = true
			}
			assert.False(t, hasHyp(g, B.Core()),
				"split_disj hyp_index=A∨C must not touch A∨B; hyps=%v", g.Hypotheses)
		}
		assert.True(t, gotA, "expected an A ⊢ G branch")
		assert.True(t, gotC, "expected a C ⊢ G branch")
	})

	// --- split_hyp_iff ---------------------------------------------------
	t.Run("split_hyp_iff/hyp_index steers to requested ⇔-hyp", func(t *testing.T) {
		AiffB := A.Eq(B).Core()
		AiffC := A.Eq(C).Core()
		target := prop.MakeProp(G.Core(), AiffB, AiffC)
		iAC := findIndex(target, AiffC)
		require.NotEqual(t, -1, iAC)

		e, sid, goalID := setup(t, target)
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "split_hyp_iff", HypIndex: &iAC},
		})
		require.NoError(t, err)
		require.True(t, res.Success)
		// hyp A⇔C splits to A,C ⊢ G and ¬A,¬C ⊢ G. B must not appear
		// as an added hyp on either child.
		gotC := false
		for _, g := range res.State.Goals {
			if hasHyp(g, C.Core()) {
				gotC = true
			}
			assert.False(t, hasHyp(g, B.Core()),
				"split_hyp_iff hyp_index=A⇔C must not touch A⇔B")
		}
		assert.True(t, gotC, "expected a branch carrying C")
	})

	// --- split_hyp_imply -------------------------------------------------
	t.Run("split_hyp_imply/hyp_index steers to requested ⇒-hyp", func(t *testing.T) {
		AimpB := A.Imply(B).Core()
		AimpC := A.Imply(C).Core()
		target := prop.MakeProp(G.Core(), AimpB, AimpC)
		iAC := findIndex(target, AimpC)
		require.NotEqual(t, -1, iAC)

		e, sid, goalID := setup(t, target)
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "split_hyp_imply", HypIndex: &iAC},
		})
		require.NoError(t, err)
		require.True(t, res.Success)
		// hyp A⇒C splits to ¬A ⊢ G and C ⊢ G. B must not appear as
		// an added hyp on either child.
		gotC := false
		for _, g := range res.State.Goals {
			if hasHyp(g, C.Core()) {
				gotC = true
			}
			assert.False(t, hasHyp(g, B.Core()),
				"split_hyp_imply hyp_index=A⇒C must not touch A⇒B")
		}
		assert.True(t, gotC, "expected a branch carrying C (the consequent)")
	})

	// --- strip_quant -----------------------------------------------------
	t.Run("strip_quant/hyp_index opens the requested ∃-hyp and leaves the ∀-conclusion alone", func(t *testing.T) {
		w := ext.Var("w", core.TypeA())
		H := ext.Var("H", core.MakeFun(core.TypeA(), core.TypeBool()))
		exP := ext.Exists(x)(P.Apply(x))
		exQ := ext.Exists(y)(Q.Apply(y))
		concl := ext.ForAll(w)(H.Apply(w))
		target := prop.MakeProp(concl, exP, exQ)
		iQ := findIndex(target, exQ)
		require.NotEqual(t, -1, iQ)

		e, sid, goalID := setup(t, target)
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "strip_quant", HypIndex: &iQ},
		})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
		require.NotNil(t, res.State)
		require.Equal(t, 1, len(res.State.Goals))
		g := res.State.Goals[0]
		assert.True(t, g.Statement.Conclusion().AlphaEquals(concl),
			"a named ∃-hyp must not strip the conclusion; got %s", ext.PrintTerm(g.Statement.Conclusion()))
		assert.True(t, hasHyp(g, exP), "the other ∃-hyp must stand; hyps=%v", g.Hypotheses)
		assert.False(t, hasHyp(g, exQ), "the named ∃-hyp must be opened; hyps=%v", g.Hypotheses)
		assert.Equal(t, 2, len(g.Hypotheses), "one hyp replaced by its instance, nothing added or dropped")
	})

	t.Run("strip_quant/HypIndex=nil strips the ∀-conclusion first (pick-first)", func(t *testing.T) {
		w := ext.Var("w", core.TypeA())
		H := ext.Var("H", core.MakeFun(core.TypeA(), core.TypeBool()))
		exP := ext.Exists(x)(P.Apply(x))
		exQ := ext.Exists(y)(Q.Apply(y))
		target := prop.MakeProp(ext.ForAll(w)(H.Apply(w)), exP, exQ)

		e, sid, goalID := setup(t, target)
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "strip_quant"}, // no HypIndex
		})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
		require.Equal(t, 1, len(res.State.Goals))
		g := res.State.Goals[0]
		assert.True(t, ext.MatchesFORALL(g.Statement.Conclusion()).IsZero(), "pick-first strips the conclusion")
		assert.True(t, hasHyp(g, exP))
		assert.True(t, hasHyp(g, exQ))
	})

	// --- Failure paths — clean tactic_failure diagnostic, no wrong split.
	// ApplyStep converts engine-dispatch errors into a Diagnostic on
	// res.Success=false rather than returning err, so the assertions
	// key off the diagnostic message.
	t.Run("out-of-range hyp_index → tactic_failure diagnostic", func(t *testing.T) {
		AorB := A.Or(B).Core()
		target := prop.MakeProp(G.Core(), AorB)
		e, sid, goalID := setup(t, target)
		bad := target.NumHyps() + 5
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "split_disj", HypIndex: &bad},
		})
		require.NoError(t, err)
		require.False(t, res.Success, "out-of-range must fail cleanly")
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "out of range")
	})

	t.Run("wrong-shape hyp_index → tactic_failure diagnostic", func(t *testing.T) {
		// A single non-∨ hyp — asking split_disj to hit index 0 (which
		// is an atom, not A∨B) must decline cleanly.
		target := prop.MakeProp(G.Core(), A.Core())
		e, sid, goalID := setup(t, target)
		i := 0
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "split_disj", HypIndex: &i},
		})
		require.NoError(t, err)
		require.False(t, res.Success, "wrong shape must fail cleanly, not split some other hyp")
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "not A ∨ B")
	})

	t.Run("strip_quant/wrong-shape hyp_index → tactic_failure diagnostic", func(t *testing.T) {
		// A single atom hyp — asking strip_quant to open index 0 (not
		// ∃-headed) must decline cleanly, not strip the conclusion or
		// open some other hyp.
		target := prop.MakeProp(G.Core(), A.Core())
		e, sid, goalID := setup(t, target)
		i := 0
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "strip_quant", HypIndex: &i},
		})
		require.NoError(t, err)
		require.False(t, res.Success, "wrong shape must fail cleanly")
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "not ∃x. …")
	})

	// --- Back-compat: HypIndex=nil falls back to pick-first. ------------
	t.Run("HypIndex=nil → pick-first (back-compat)", func(t *testing.T) {
		AorB := A.Or(B).Core()
		target := prop.MakeProp(G.Core(), AorB)
		e, sid, goalID := setup(t, target)
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "split_disj"}, // no HypIndex
		})
		require.NoError(t, err)
		require.True(t, res.Success, "pick-first path must still work when HypIndex is omitted")
		require.Equal(t, 2, len(res.State.Goals))
	})
}

// TestInspect_CaseSplitDoesNotEnumerateLogicallyHeadedSubterms pins the
// case_split filtering: when a subterm is already covered by a dedicated
// structural move (split_conj on ∧, split_iff on ⇔, etc.), we don't
// surface it as a case_split candidate too. The redundant entry was
// noise — splitting on `A∧B` would always be strictly worse than the
// dedicated decomposition.
func TestInspect_CaseSplitDoesNotEnumerateLogicallyHeadedSubterms(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))

	// ⊢ (P(x) ∧ Q(x)) ⇒ (P(x) ∨ Q(x)) — both halves are logically-
	// headed bool subterms, which the enumerator must not list as
	// case_split candidates alongside the (correct) strip_imp.
	target := prop.MakeProp(P.Apply(x).And(Q.Apply(x)).Imply(P.Apply(x).Or(Q.Apply(x))))

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)

	res, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
	require.NoError(t, err)

	for _, f := range res.StructuralFacts {
		if f.Kind != "case_split" {
			continue
		}
		term := f.Params["term"]
		// No printed connective in the params — that's how we'd know
		// a logically-headed subterm slipped through.
		assert.NotContains(t, term, "∧", "case_split must not enumerate a ∧-headed subterm: %q", term)
		assert.NotContains(t, term, "∨", "case_split must not enumerate a ∨-headed subterm: %q", term)
		assert.NotContains(t, term, "⇒", "case_split must not enumerate a ⇒-headed subterm: %q", term)
		assert.NotContains(t, term, "⇔", "case_split must not enumerate a ⇔-headed subterm: %q", term)
	}
}

// TestInspect_CaseSplitDoesNotEnumerateGoalConclusion pins the more
// specific filter: the goal's own conclusion (and any hypothesis term)
// must never appear as a case_split candidate. Splitting on the thing
// you're proving is `goal ⊢ goal ∨ ¬goal` — useless.
func TestInspect_CaseSplitDoesNotEnumerateGoalConclusion(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	// concl = P(x), hyp = P(y) — both atomic bools. Without the filter,
	// both would appear as case_split candidates (which is silly: we're
	// trying to prove P(x) and we already have P(y) as a hyp; case-
	// splitting on either is useless).
	target := prop.MakeProp(P.Apply(x).Core(), P.Apply(y).Core())

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)

	res, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
	require.NoError(t, err)

	conclStr := ext.PrintTerm(target.Conclusion())
	for _, f := range res.StructuralFacts {
		if f.Kind != "case_split" {
			continue
		}
		assert.NotEqual(t, conclStr, f.Params["term"],
			"case_split must not enumerate the goal's own conclusion as a position")
		for _, h := range target.Hyps() {
			assert.NotEqual(t, ext.PrintTerm(h), f.Params["term"],
				"case_split must not enumerate a hypothesis as a position")
		}
	}
}

// TestCollectStructuralMoves_MergedIffSplitsAreNotOffered: inspect runs
// each move on a clone to verify it applies. A named ⇔ split whose two
// children the constructor merges into one declines, so the move is not
// offered — on the goal side (p ⊢ p ⇔ ⊥) and on the hypothesis side
// (p ⇔ q, p, q ⊢ r) alike — and the session's apply says why.
func TestCollectStructuralMoves_MergedIffSplitsAreNotOffered(t *testing.T) {
	p, q, r := ext.Var("p", core.TypeBool()), ext.Var("q", core.TypeBool()), ext.Var("r", core.TypeBool())
	for _, tc := range []struct {
		name, move string
		goal       core.Prop
	}{
		{"goal split", "split_iff", prop.MakeProp(p.Eq(ext.F), p)},
		{"hypothesis split", "split_hyp_iff", prop.MakeProp(r, p.Eq(q), p, q)},
	} {
		t.Run(tc.name, func(t *testing.T) {
			for _, move := range collectStructuralMoves(tc.goal) {
				assert.NotEqual(t, tc.move, move.Tactic)
			}
			assert.Contains(t, tacticNoProgressDiagnostic(tc.move), "subsumes")
		})
	}
}
