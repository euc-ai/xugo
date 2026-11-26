package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Regressions for the `instantiate` type-adaptation gap (three independent sub-agents, on three list lemmas, walled on the
// same shape):
//
//   - A session goal's Skolem frees carry FRESH anonymous type vars
//     (e.g. `s₀ : ?27361→bool`, minted by strip_quant on a session
//     goal).
//   - A polymorphic registry lemma resident as a ∀-hyp carries its own
//     NAMED type vars (`∀s:(A→bool). ...`).
//   - `instantiate` on that hyp at the Skolem term failed with
//     `term "s₀" ... term has type ?27361→bool but expected A→bool`,
//     even though specializing the HYP's type vars to the witness's is
//     exactly what `lemma` + `type_specialize` does — the workaround
//     agents burned dozens of round-trips on.
//
// The fix: when a witness's type does not equal the ∀-binder's but the
// binder type MATCHES it under a substitution σ of the hyp's type vars
// (hyp side only — the witness stays rigid), and the hyp is backed by a
// registry entry, the engine re-derives the hyp at σ (recorded as the
// existing clear_hyps + lemma_preserve-with-source + specialize
// ministeps; the σ-instance claim child closes through the
// type-instance channel against the entry) and grounds THAT. No new
// proto shapes.
//
// The fixture mirrors auto_with_type_instance_test.go: the registry's
// finite_set.FiniteImage entry (∀s:(A→bool). ∀f:(A→B). finite(image(f,s))
// ∨ ¬finite(s)) resident as a hyp, goal frees at either an anonymous
// type var (the verbatim wall) or a concrete type.
// groundText is FiniteImage's ground disjunction at the desired
// witness types — parsed in the entry's const scope; its frees (s0, f0)
// become the goal's Skolem-shaped free vars (put in scope via vacuous
// self-equality hyps, the lemmaSpecHarness pattern), and its conclusion
// is the expected σ-ground-instance the tests assert on.
func instantiateAdaptFixture(
	t *testing.T, groundText string,
) (e *Engine, sessionID, goalID string, lemHyp, ground, workConcl core.Term) {
	t.Helper()

	lemProp := finiteImageLemma(t)
	require.Contains(t, ext.PrintTermWithPolyBinders(lemProp.Conclusion()),
		"∀f:(var:A → var:B)",
		"the finite_set.FiniteImage entry must have f at A→B (distinct vars)")

	// Parse the expected ground instance in the entry's const scope so
	// finite / image resolve as registered constants.
	frame, err := parsePropTextInGoalScope(groundText, lemProp, nil)
	require.NoError(t, err)
	ground = frame.Conclusion()

	// Session goal: the polymorphic entry's statement resident as a
	// hyp; s0/f0 in scope via vacuous hyps; an unrelated bool free var
	// as the working conclusion so the residual stays open.
	lemHyp = lemProp.Conclusion()
	workConcl = core.Var("q", core.TypeBool())
	hyps := []core.Term{lemHyp}
	for _, v := range ground.Frees(nil) {
		hyps = append(hyps, core.Eq(v, v))
	}
	target := core.MakeProp(workConcl, hyps...)

	e = newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID = s.AddGoal(target)
	return e, info.ID, goalID, lemHyp, ground, workConcl
}

// hypIndexOf returns the index of the hyp α-equal to `h` in the goal
// registered under goalID.
func hypIndexOf(t *testing.T, e *Engine, sessionID, goalID string, h core.Term) int {
	t.Helper()
	s, serr := e.getSession(sessionID)
	require.NoError(t, serr)
	entry, ok := s.goalIndex[goalID]
	require.True(t, ok, "goal %s not in session index", goalID)
	for i := range entry.node.Goal.NumHyps() {
		if entry.node.Goal.Hyp(i).AlphaEquals(h) {
			return i
		}
	}
	t.Fatalf("hyp %s not found in goal %s", ext.PrintTerm(h), goalID)
	return -1
}

// TestApply_InstantiateTypeAdapt_AnonymousTypeVarWitness is the
// verbatim wall: witnesses typed at a fresh ANONYMOUS type var (?27361)
// against the entry's named A/B binders. Multi-witness form exercises σ
// accumulation across rungs (s pins A, then f's binder type is already
// A-substituted and pins B).
func TestApply_InstantiateTypeAdapt_AnonymousTypeVarWitness(t *testing.T) {
	e, sid, gid, lemHyp, ground, workConcl := instantiateAdaptFixture(t,
		"s0:(?27361 → bool), f0:(?27361 → ?27361) ⊢ finite(image(f0, s0)) ∨ ¬finite(s0)")
	idx := hypIndexOf(t, e, sid, gid, lemHyp)

	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:     "instantiate",
			HypIndex: &idx,
			Terms:    []string{"s0", "f0"},
		},
	})
	require.NoError(t, err)
	if !res.Success {
		t.Fatalf("instantiate must type-adapt the hyp to the witnesses' anonymous "+
			"type var; diagnostics: %+v", res.Diagnostics)
	}

	require.Equal(t, 1, res.State.NumOpen,
		"exactly one open subgoal (claim child must close via the "+
			"type-instance channel); goals: %+v", res.State.Goals)
	hyps := findWorkingHyps(t, res, workConcl)

	// The ground instance at the ?27361 instance must be present:
	// finite(image(f0,s0)) ∨ ¬finite(s0).
	foundGround := false
	for _, h := range hyps {
		if h.AlphaEquals(ground) {
			foundGround = true
		}
		// The stale A/B-typed ∀-hyp must be gone — it is replaced by the
		// σ-instance (which the terms-form specialize then consumes).
		assert.False(t, h.AlphaEquals(lemHyp),
			"the original named-type-var ∀-hyp must be cleared; hyps=%v",
			printedHyps(hyps))
	}
	assert.True(t, foundGround,
		"working goal must carry the ground σ-instance %s; hyps=%v",
		ext.PrintTerm(ground), printedHyps(hyps))
}

// TestApply_InstantiateTypeAdapt_ConcreteTypeWitness is the concrete-
// instance flavor (A:=num, B:=num) — the same adaptation with a ground
// σ instead of a var→var rename.
func TestApply_InstantiateTypeAdapt_ConcreteTypeWitness(t *testing.T) {
	e, sid, gid, lemHyp, ground, workConcl := instantiateAdaptFixture(t,
		"s0:(num → bool), f0:(num → num) ⊢ finite(image(f0, s0)) ∨ ¬finite(s0)")
	idx := hypIndexOf(t, e, sid, gid, lemHyp)

	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:     "instantiate",
			HypIndex: &idx,
			Terms:    []string{"s0", "f0"},
		},
	})
	require.NoError(t, err)
	if !res.Success {
		t.Fatalf("instantiate must type-adapt the hyp to concrete witness types; "+
			"diagnostics: %+v", res.Diagnostics)
	}
	require.Equal(t, 1, res.State.NumOpen)

	hyps := findWorkingHyps(t, res, workConcl)
	foundGround := false
	for _, h := range hyps {
		if h.AlphaEquals(ground) {
			foundGround = true
		}
	}
	assert.True(t, foundGround,
		"working goal must carry the ground σ-instance %s; hyps=%v",
		ext.PrintTerm(ground), printedHyps(hyps))
}

// TestApply_InstantiateTypeAdapt_SessionCompletes drives the adapted
// chain all the way to a CLOSED session: the working conclusion IS the
// ground σ-instance, so after the adapted instantiate the residual is
// `…, instance ⊢ instance` and `assumption` (or the auto pipeline)
// closes it. This forces the full reconstruction path over the
// clear_hyps + lemma_preserve + specialize + type-instance-close chain
// — the IsStronger asserts in updateUpwards would panic on any unsound
// reconstruction shape.
func TestApply_InstantiateTypeAdapt_SessionCompletes(t *testing.T) {
	lemProp := finiteImageLemma(t)

	frame, err := parsePropTextInGoalScope(
		"s0:(?27361 → bool), f0:(?27361 → ?27361) ⊢ finite(image(f0, s0)) ∨ ¬finite(s0)",
		lemProp, nil)
	require.NoError(t, err)
	ground := frame.Conclusion()
	lemHyp := lemProp.Conclusion()
	target := core.MakeProp(ground, lemHyp)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, serr := e.getSession(info.ID)
	require.NoError(t, serr)
	gid := s.AddGoal(target)
	idx := hypIndexOf(t, e, info.ID, gid, lemHyp)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:     "instantiate",
			HypIndex: &idx,
			Terms:    []string{"s0", "f0"},
		},
	})
	require.NoError(t, err)
	if !res.Success {
		t.Fatalf("adapted instantiate must apply; diagnostics: %+v", res.Diagnostics)
	}
	if !res.State.Complete {
		require.Equal(t, 1, res.State.NumOpen, "goals: %+v", res.State.Goals)
		res2, err2 := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: res.State.Goals[0].ID,
			Tactic: TacticReq{Type: "assumption"},
		})
		require.NoError(t, err2)
		if !res2.Success {
			t.Fatalf("assumption must close `…, instance ⊢ instance`; diagnostics: %+v",
				res2.Diagnostics)
		}
		res = res2
	}
	assert.True(t, res.State.Complete,
		"session must reach complete through the adapted chain; state: %+v", res.State)
	assert.Equal(t, 0, res.State.NumOpen)
}

// TestApply_InstantiateTypeAdapt_ResidualChainReconstructs closes the
// session through the RESIDUAL of the adapted chain (unlike
// SessionCompletes, whose goal the σ-instance closes outright): the
// working conclusion is a self-equality unrelated to the entry, so the
// adapted instantiate must land the ground instance as a hyp, and the
// follow-up `assumption`/`refl` close forces updateUpwards to
// kernel-reconstruct through specialize → lemma_preserve(+claim close)
// → clear_hyps.
func TestApply_InstantiateTypeAdapt_ResidualChainReconstructs(t *testing.T) {
	lemProp := finiteImageLemma(t)

	frame, err := parsePropTextInGoalScope(
		"s0:(?27361 → bool), f0:(?27361 → ?27361) ⊢ finite(image(f0, s0)) ∨ ¬finite(s0)",
		lemProp, nil)
	require.NoError(t, err)
	ground := frame.Conclusion()
	lemHyp := lemProp.Conclusion()

	// Conclusion `s0 = s0`: NOT derivable from the entry (the install
	// must take the hyp path, unlike SessionCompletes), and α-equal to
	// one of the vacuous scope hyps, so `assumption` closes the residual
	// afterwards.
	var conclEq core.Term
	hyps := []core.Term{lemHyp}
	for _, v := range ground.Frees(nil) {
		hyps = append(hyps, core.Eq(v, v))
		if string(v.Name()) == "s0" {
			conclEq = core.Eq(v, v)
		}
	}
	require.NotNil(t, conclEq)
	target := core.MakeProp(conclEq, hyps...)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, serr := e.getSession(info.ID)
	require.NoError(t, serr)
	gid := s.AddGoal(target)
	idx := hypIndexOf(t, e, info.ID, gid, lemHyp)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:     "instantiate",
			HypIndex: &idx,
			Terms:    []string{"s0", "f0"},
		},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	if !res.State.Complete {
		require.Equal(t, 1, res.State.NumOpen, "goals: %+v", res.State.Goals)
		res2, err2 := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: res.State.Goals[0].ID,
			Tactic: TacticReq{Type: "assumption"},
		})
		require.NoError(t, err2)
		require.True(t, res2.Success, "diagnostics: %+v", res2.Diagnostics)
		res = res2
	}
	// Closing the residual forces updateUpwards to kernel-reconstruct
	// through specialize → lemma_preserve(+claim close) → clear_hyps;
	// any unsound reconstruction shape panics on its IsStronger assert.
	assert.True(t, res.State.Complete, "state: %+v", res.State)
	assert.Equal(t, 0, res.State.NumOpen)
}

// TestApply_InstantiateTypeAdapt_ExplicitTypeSpecializeBadName: an
// unknown type-var name errors loudly (never a silent no-op).
func TestApply_InstantiateTypeAdapt_ExplicitTypeSpecializeBadName(t *testing.T) {
	e, sid, gid, lemHyp, _, _ := instantiateAdaptFixture(t,
		"s0:(num → bool), f0:(num → num) ⊢ finite(image(f0, s0)) ∨ ¬finite(s0)")
	idx := hypIndexOf(t, e, sid, gid, lemHyp)

	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:           "instantiate",
			HypIndex:       &idx,
			Terms:          []string{"s0", "f0"},
			TypeSpecialize: map[string]string{"NoSuchVar": "num"},
		},
	})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "NoSuchVar",
		"error must name the unknown type var")
}

// TestApply_InstantiateTypeAdapt_SingleConstKeepsAdaptedForall: the
// single-`const` form defaults to keeping the source ∀ available. After
// adaptation the KEPT source is the σ-instance (the stale named-var
// form is cleared — it was unusable at the goal's types, which is the
// whole premise).
func TestApply_InstantiateTypeAdapt_SingleConstKeepsAdaptedForall(t *testing.T) {
	e, sid, gid, lemHyp, _, workConcl := instantiateAdaptFixture(t,
		"s0:(num → bool), f0:(num → num) ⊢ finite(image(f0, s0)) ∨ ¬finite(s0)")
	idx := hypIndexOf(t, e, sid, gid, lemHyp)

	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:     "instantiate",
			HypIndex: &idx,
			Const:    "s0",
		},
	})
	require.NoError(t, err)
	if !res.Success {
		t.Fatalf("single-const adapted instantiate must apply; diagnostics: %+v",
			res.Diagnostics)
	}
	require.Equal(t, 1, res.State.NumOpen,
		"claim child must close; goals: %+v", res.State.Goals)

	hyps := findWorkingHyps(t, res, workConcl)
	// Expect: a ∀-headed σ-instance source kept (keep defaults true for
	// the const form) + the partial instance ∀f. finite(image(f,s0)) ∨
	// ¬finite(s0); the stale A/B form gone.
	sawForall := false
	for _, h := range hyps {
		assert.False(t, h.AlphaEquals(lemHyp),
			"stale named-var ∀-hyp must be cleared; hyps=%v", printedHyps(hyps))
		if !ext.MatchesFORALL(h).IsZero() {
			sawForall = true
		}
	}
	assert.True(t, sawForall,
		"const form keeps the adapted ∀ source; hyps=%v", printedHyps(hyps))
}

// TestApply_InstantiateTypeAdapt_UnbackedHypErrors: a hyp that is NOT
// backed by a registry entry cannot be soundly re-derived at σ (a
// hyp's type vars are sequent-scoped — there is no per-hyp kernel
// PropTypeInst), so the engine must fail loudly with the σ it computed
// and the manual recipe, never adapt silently.
func TestApply_InstantiateTypeAdapt_UnbackedHypErrors(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	n := core.Var("n", numType)

	// Goal: ∀x:A. P(x), n=n ⊢ n=n — the ∀-hyp is ad-hoc (free predicate
	// var), not a registry entry's statement.
	forallHyp := ext.ForAll(x)(P.Apply(x)).Core()
	target := prop.MakeProp(core.Eq(n, n), forallHyp, core.Eq(n, n))
	idx := -1
	for i := range target.NumHyps() {
		if target.Hyp(i).AlphaEquals(forallHyp) {
			idx = i
		}
	}
	require.GreaterOrEqual(t, idx, 0)

	err := applyToSingleGoalExpectErr(t, target.Core(), TacticReq{
		Type:     "instantiate",
		HypIndex: &idx,
		Const:    "n",
	})
	require.Error(t, err)
	// The error must carry the computed σ and the manual recipe —
	// without them an agent fishes the fresh type-var name out of a
	// parse error.
	assert.Contains(t, err.Error(), `type_specialize:{"A":"num"}`,
		"error must name the computed σ recipe: %v", err)
	assert.Contains(t, err.Error(), "backing",
		"error must explain the theorem-backing requirement: %v", err)
}
