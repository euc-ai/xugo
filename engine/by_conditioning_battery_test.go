package engine

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils/wallclock"
	"github.com/stretchr/testify/require"
)

// TestByConditioning_Battery checks the supported conditioning routes:
// splitting premises, opening goals, grounding, beta reduction, denotation
// and arithmetic. Every attempted close is a regression assertion.
func TestByConditioning_Battery(t *testing.T) {
	if testing.Short() {
		t.Skip("battery needs the real corpus; skipped under -short")
	}

	env := testEnv()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
	}
	env.LibraryThms = serve.InductionPrinciples()
	serve.RegisterAll(env)
	serve.InstallProofPolicy()
	installTestNatBundle()
	e := newEngine(env)
	ctx := context.Background()
	// Separate sessions keep a proved arm from closing another as a sibling.
	newRow := func(t *testing.T) (*Session, string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		return s, info.ID
	}
	addGoal := func(t *testing.T, s *Session, text string) string {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver:      envConstResolver(s.env),
			StrictResolution:   true,
			FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "add-goal %q", text)
		s.mu.Lock()
		defer s.mu.Unlock()
		return s.AddGoal(parsed.Prop)
	}
	timedApply := func(sid, goalID string, req TacticReq) (*StepResult, time.Duration, error) {
		t0 := time.Now()
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: goalID, Tactic: req})
		return res, time.Since(t0), err
	}
	mustApply := func(t *testing.T, sid, goalID string, req TacticReq) *StepResult {
		t.Helper()
		res, _, err := timedApply(sid, goalID, req)
		require.NoError(t, err, "apply %s on %s", req.Type, goalID)
		require.NotNil(t, res)
		require.True(t, res.Success, "%s: %v", req.Type, res.Diagnostics)
		return res
	}
	strip := func(t *testing.T, sid, goalID string, types ...string) string {
		t.Helper()
		for _, typ := range types {
			res := mustApply(t, sid, goalID, TacticReq{Type: typ})
			require.Len(t, res.Produced, 1, "strip %s", typ)
			goalID = res.Produced[0].GoalID
		}
		return goalID
	}
	requireClose := func(t *testing.T, label string, res *StepResult, err error, took time.Duration) {
		t.Helper()
		require.NoError(t, err, "%s (took %v)", label, took)
		require.NotNil(t, res)
		require.Equal(t, "close", res.Effect, "%s (took %v)", label, took)
		t.Logf("%s: closed in %v", label, took)
	}
	idx := func(i int) *int { return &i }
	bijArm := "∀f:(A → B). ∀s:(A → bool). ∀t:(B → bool). (∀x:A. x ∈ s ⇒ f(x) ∈ t) ⇒ ((∀x y:A. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y) ∧ (∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ⇒ ∃g:(B → A). (∀y:B. y ∈ t ⇒ g(y) ∈ s) ∧ ((∀y:B. y ∈ t ⇒ f(g(y)) = y) ∧ (∀x:A. x ∈ s ⇒ g(f(x)) = x)))"
	bijArmCurried := "∀f:(A → B). ∀s:(A → bool). ∀t:(B → bool). (∀x:A. x ∈ s ⇒ f(x) ∈ t) ⇒ ((∀x y:A. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y) ⇒ (∀y:B. y ∈ t ⇒ ∃x:A. x ∈ s ∧ f(x) = y) ⇒ ∃g:(B → A). (∀y:B. y ∈ t ⇒ g(y) ∈ s) ∧ ((∀y:B. y ∈ t ⇒ f(g(y)) = y) ∧ (∀x:A. x ∈ s ⇒ g(f(x)) = x)))"
	t.Run("SplitConjunction", func(t *testing.T) {
		s, sid := newRow(t)
		gid := strip(t, sid, addGoal(t, s, bijArmCurried),
			"strip_quant", "strip_imp", "strip_imp", "strip_imp")
		res, took, err := timedApply(sid, gid, TacticReq{Type: "set_tac"})
		requireClose(t, "guard: curried spelling (∧ pre-split), set_tac", res, err, took)
		s, sid = newRow(t)
		gid = strip(t, sid, addGoal(t, s, bijArm), "strip_quant", "strip_imp", "strip_imp")
		res, took, err = timedApply(sid, gid, TacticReq{Type: "by", Settac: true,
			ByShape: &ByShapeReq{Normalized: true},
			ByHyps:  []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}}})
		requireClose(t, "BySets(Normalized, carries, injAndSurj)", res, err, took)
		s, sid = newRow(t)
		gid = strip(t, sid, addGoal(t, s, bijArm), "strip_quant", "strip_imp", "strip_imp")
		res, took, err = timedApply(sid, gid, TacticReq{Type: "by", Settac: true,
			ByHyps: []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}}})
		requireClose(t, "BySets with the ∧ premise unsplit", res, err, took)
		s, sid = newRow(t)
		gid = strip(t, sid, addGoal(t, s, bijArm), "strip_quant", "strip_imp", "strip_imp")
		res, took, err = timedApply(sid, gid, TacticReq{Type: "set_tac"})
		requireClose(t, "set_tac: conjunction premise", res, err, took)
	})
	noFolding := "∀f:(A → B). ∀s:(A → bool). ∀u:(B → bool). (∀k:(A → bool). k ⊆ s ⇒ ∃t:(B → bool). t ⊆ u ∧ set_comprehension(λGEN%PVAR%118:A. ∃x:A. comprehension_spec(GEN%PVAR%118, x ∈ s ∧ f(x) ∈ t, x)) = k) ⇒ ∀x y:A. x ∈ s ∧ y ∈ s ∧ f(x) = f(y) ⇒ x = y"
	imageInside := "∀f:(A → B). ∀s:(A → bool). ∀u:(B → bool). (∀k:(A → bool). k ⊆ s ⇒ ∃t:(B → bool). t ⊆ u ∧ set_comprehension(λGEN%PVAR%118:A. ∃x:A. comprehension_spec(GEN%PVAR%118, x ∈ s ∧ f(x) ∈ t, x)) = k) ⇒ image(f, s) ⊆ u"
	t.Run("StripGoalPrefix", func(t *testing.T) {
		wallclock.SkipOnSlowMachine(t)
		s, sid := newRow(t)
		gid := strip(t, sid, addGoal(t, s, noFolding), "strip_quant", "strip_imp")
		res, took, err := timedApply(sid, gid, TacticReq{Type: "set_tac"})
		requireClose(t, "guard: noFolding stripped, set_tac", res, err, took)

		res, took, err = timedApply(sid, addGoal(t, s, imageInside), TacticReq{Type: "set_tac"})
		requireClose(t, "imageInside through the membership driver", res, err, took)
		s, sid = newRow(t)
		res, took, err = timedApply(sid, addGoal(t, s, noFolding),
			TacticReq{Type: "by", Settac: true})
		requireClose(t, "premise-free BySets on the ∀-closed implication", res, err, took)
		s, sid = newRow(t)
		res, took, err = timedApply(sid, addGoal(t, s, noFolding), TacticReq{Type: "set_tac"})
		requireClose(t, "set_tac: closed implication", res, err, took)
	})
	sepArm := "∀f:(A → B). ∀s:(A → bool). ∀u:(B → bool). (∀t t':(B → bool). t ⊆ u ∧ t' ⊆ u ∧ set_comprehension(λGEN%PVAR%124:A. ∃x:A. comprehension_spec(GEN%PVAR%124, x ∈ s ∧ f(x) ∈ t, x)) = set_comprehension(λGEN%PVAR%157:A. ∃x:A. comprehension_spec(GEN%PVAR%157, x ∈ s ∧ f(x) ∈ t', x)) ⇒ t = t') ⇒ (∀y:B. y ∈ u ⇒ ∃x:A. x ∈ s ∧ f(x) = y)"
	t.Run("ExplicitWitnessesForWideForall", func(t *testing.T) {
		s, sid := newRow(t)
		gid := strip(t, sid, addGoal(t, s, sepArm),
			"strip_quant", "strip_imp", "strip_quant", "strip_imp")
		res, took, err := timedApply(sid, gid, TacticReq{Type: "by", Settac: true,
			ByHyps: []ByHypSpec{
				{HypIndex: idx(0)},
				{HypIndex: idx(0), Terms: []string{"{y}", "∅"}},
				{HypIndex: idx(1)}}})
		requireClose(t, "guard: BySets(separated, separated.At({y}, ∅), yInU)", res, err, took)
	})
	s5Row := "∀P:(num → bool). ∀F:(num → num). ∀k:num. (∀g:(num → num). ∀j:num. P(g(j))) ⇒ P(F(k))"
	t.Run("BetaAtInstall", func(t *testing.T) {
		s, sid := newRow(t)
		gid := strip(t, sid, addGoal(t, s, s5Row), "strip_quant", "strip_imp")
		res, took, err := timedApply(sid, gid, TacticReq{Type: "by",
			ByHyps: []ByHypSpec{{HypIndex: idx(0), Terms: []string{"λi:num. F(i)", "k"}}}})
		requireClose(t, "guard: By witness path grounds and closes", res, err, took)

		s, sid = newRow(t)
		gid = strip(t, sid, addGoal(t, s, s5Row), "strip_quant", "strip_imp")
		res = mustApply(t, sid, gid, TacticReq{Type: "instantiate",
			HypIndex: idx(0), Terms: []string{"λi:num. F(i)", "k"}})
		require.Len(t, res.Produced, 1)
		node := s.goalIndex[res.Produced[0].GoalID].node
		for i, hyp := range node.Goal.Hyps() {
			require.True(t, ext.BetaCollapse(ctx, hyp).AlphaEquals(hyp),
				"instantiate installed hyp[%d] un-β-reduced: %s", i, ext.PrintTerm(hyp))
		}
	})
	s6Row := "∀s:(num → bool). ∀f:(num → num). ∀g:(num → num). ∀E:num. nat_sum({x:num | x ∈ s ∧ f(x) = 0}, f) < E ⇒ nat_sum({x:num | x ∈ s ∧ g(x) = 0}, g) = nat_sum({x:num | x ∈ s ∧ f(x) = 0}, f) ⇒ nat_sum({x:num | x ∈ s ∧ g(x) = 0}, g) < E"
	t.Run("DenoteFatAtom", func(t *testing.T) {
		s, sid := newRow(t)
		gid := strip(t, sid, addGoal(t, s, s6Row), "strip_quant", "strip_imp", "strip_imp")
		res, took, err := timedApply(sid, gid, TacticReq{Type: "by",
			ByHyps:  []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}},
			ByShape: &ByShapeReq{Denoted: 2}})
		requireClose(t, "guard: by [0,1] denoted:2", res, err, took)

		s, sid = newRow(t)
		gid = strip(t, sid, addGoal(t, s, s6Row), "strip_quant", "strip_imp", "strip_imp")
		res, took, err = timedApply(sid, gid, TacticReq{Type: "by",
			ByHyps: []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}}})
		requireClose(t, "by [0,1] on un-denoted set-builder atoms", res, err, took)
		s6Auto := "∀s:(num → bool). ∀f:(num → num). ∀g:(num → num). ∀P:(num → bool). P(nat_sum({x:num | x ∈ s ∧ f(x) = 0}, f)) ⇒ nat_sum({x:num | x ∈ s ∧ g(x) = 0}, g) = nat_sum({x:num | x ∈ s ∧ f(x) = 0}, f) ⇒ P(nat_sum({x:num | x ∈ s ∧ g(x) = 0}, g))"
		s, sid = newRow(t)
		gid = strip(t, sid, addGoal(t, s, s6Auto), "strip_quant", "strip_imp", "strip_imp")
		res, took, err = timedApply(sid, gid, TacticReq{Type: "auto"})
		requireClose(t, "auto on un-denoted set-builder atoms", res, err, took)
	})
	advRow := "∀P:(num → bool). (∀x:num. P(x) ⇒ P(suc(x))) ⇒ P(0) ⇒ P(suc(suc(0)))"
	t.Run("KeepMidSearchInstances", func(t *testing.T) {
		s, sid := newRow(t)
		gid := strip(t, sid, addGoal(t, s, advRow), "strip_quant", "strip_imp", "strip_imp")
		res, took, err := timedApply(sid, gid, TacticReq{Type: "by",
			ByHyps: []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}}})
		requireClose(t, "guard: bare by chains through mid-search instances", res, err, took)
	})
	t.Run("PolynomialStep_ArithCloser", func(t *testing.T) {
		s, sid := newRow(t)
		_, err := e.Define(&DefineRequest{
			SessionID: sid,
			Recursive: &DefineRecursive{
				Name: "zz_sumto_ac",
				Type: "num → num",
				Equations: []string{
					"zz_sumto_ac(0) = 0",
					"∀n:num. zz_sumto_ac(suc(n)) = zz_sumto_ac(n) + suc(n)",
				},
			},
		})
		require.NoError(t, err)
		gauss := addGoal(t, s, "∀n:num. 2 * zz_sumto_ac(n) = n * suc(n)")
		ind := mustApply(t, sid, gauss, TacticReq{Type: "induction", Const: "n"})
		require.Len(t, ind.Produced, 2)
		base := mustApply(t, sid, ind.Produced[0].GoalID, TacticReq{Type: "simp"})
		require.Len(t, base.Produced, 1)
		closed := mustApply(t, sid, base.Produced[0].GoalID, TacticReq{Type: "arith"})
		require.Equal(t, "close", closed.Effect)

		step := mustApply(t, sid, ind.Produced[1].GoalID, TacticReq{Type: "simp"})
		require.Len(t, step.Produced, 1)
		res, took, err := timedApply(sid, step.Produced[0].GoalID, TacticReq{Type: "arith"})
		requireClose(t, "arith consumes the induction hypothesis as a constraint", res, err, took)
	})
	t.Run("ArithGrounding_WideLawAtTheGoal", func(t *testing.T) {
		s, sid := newRow(t)
		g := addGoal(t, s, "∀P:num→bool. ∀x:num. (∀y:num. y < 3 ⇒ P(y)) ⇒ x + 1 < 3 ⇒ P(x)")
		stripped := mustApply(t, sid, g, TacticReq{Type: "strip_quant"})
		require.Len(t, stripped.Produced, 1)
		imp1 := mustApply(t, sid, stripped.Produced[0].GoalID, TacticReq{Type: "strip_imp"})
		require.Len(t, imp1.Produced, 1)
		imp2 := mustApply(t, sid, imp1.Produced[0].GoalID, TacticReq{Type: "strip_imp"})
		require.Len(t, imp2.Produced, 1)
		h0, h1 := 0, 1
		res, took, err := timedApply(sid, imp2.Produced[0].GoalID, TacticReq{Type: "by", Arith: true,
			ByHyps: []ByHypSpec{{HypIndex: &h0}, {HypIndex: &h1}}})
		requireClose(t, "arith grounds the law at x and decides its guard", res, err, took)
	})
}
