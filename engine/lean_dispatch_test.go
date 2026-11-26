package engine

import (
	"context"
	"fmt"
	"github.com/euc-ai/xugo/library/registry"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// applyToSingleGoal is a small helper for the LEAN-dispatch tests: create
// a session, add a goal, and immediately apply the given tactic. Returns
// the StepResult for assertion.
func applyToSingleGoal(t *testing.T, target core.Prop, tactic TacticReq) (*StepResult, *Engine, string, string) {
	t.Helper()
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: tactic,
	})
	require.NoError(t, err)
	return res, e, info.ID, goalID
}

func TestApply_Assumption(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))

	// Goal: P(x) ⊢ P(x). Assumption closes immediately.
	target := prop.MakeProp(P.Apply(x).Core(), P.Apply(x).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "assumption"})
	require.True(t, res.Success)
	assert.True(t, res.State.Complete)
	assert.Equal(t, 0, res.State.NumOpen)
}

func TestApply_Refl(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	target := prop.MakeProp(x.Eq(x).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "refl"})
	require.True(t, res.Success)
	assert.True(t, res.State.Complete)
}

func TestApply_LeftRight(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	A := P.Apply(x)
	B := y.Eq(y) // a different bool

	target := prop.MakeProp(A.Or(B).Core())

	// Left: ⊢ A∨B → ⊢ A
	resL, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "left"})
	require.True(t, resL.Success)
	assert.Equal(t, 1, resL.State.NumOpen)

	// Right: ⊢ A∨B → ⊢ B (auto-matches via a proved sibling if one states B;
	// here B = y=y so it should auto-close to T after a single right-then-refl
	// chain — but `right` alone produces a single subgoal without auto closure
	// of the children, since right is a structural decomposition).
	resR, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "right"})
	require.True(t, resR.Success)
}

// TestApply_ClearDropsHyp covers the single-drop case through clear's
// only param — `hyp_indices: [i]`. (A single drop is just a one-element
// set; there is no `hyp_index` form for clear.)
func TestApply_ClearDropsHyp(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	junk := ext.Var("junk", core.TypeBool())

	// Goal: junk, P(x) ⊢ P(x). Drop `junk`, then P(x) ⊢ P(x) remains.
	target := prop.MakeProp(P.Apply(x).Core(), junk.Core(), P.Apply(x).Core())
	idx := -1
	for i := 0; i < target.NumHyps(); i++ {
		if target.Hyp(i).AlphaEquals(junk.Core()) {
			idx = i
		}
	}
	require.GreaterOrEqual(t, idx, 0, "junk must be a hyp")

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "clear", HypIndices: []int{idx}})
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)
	g := res.State.Goals[0].Statement
	assert.Equal(t, 1, g.NumHyps(), "one hyp dropped")
	assert.False(t, g.HasHyp(junk.Core()), "the dropped hyp is gone")
	assert.True(t, g.Conclusion().AlphaEquals(P.Apply(x).Core()), "conclusion unchanged")
}

func TestApply_ClearErrors(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(P.Apply(x).Core(), P.Apply(x).Core()) // 1 hyp

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)

	// ApplyStep converts a tactic error into a Success:false result with a
	// diagnostic (not a Go error). Missing hyp_indices → required-field message.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "clear"}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "hyp_indices")

	// out-of-range hyp_indices → range message.
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "clear", HypIndices: []int{9}}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "out of range")
}

// TestApply_ClearMultipleHyps covers the batch form: hyp_indices drops
// several hyps in ONE apply. Indices are given in the agent-visible
// (current-goal) numbering, deliberately ascending here — the engine
// drops highest-first internally, so no caller-side shift compensation.
func TestApply_ClearMultipleHyps(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	junk1 := ext.Var("junk1", core.TypeBool())
	junk2 := ext.Var("junk2", core.TypeBool())

	// Goal: junk1, junk2, P(x) ⊢ P(x). Drop both junks in one call.
	target := prop.MakeProp(P.Apply(x).Core(), junk1.Core(), junk2.Core(), P.Apply(x).Core())
	require.Equal(t, 3, target.NumHyps())
	var drops []int
	for i := 0; i < target.NumHyps(); i++ {
		if target.Hyp(i).AlphaEquals(junk1.Core()) || target.Hyp(i).AlphaEquals(junk2.Core()) {
			drops = append(drops, i)
		}
	}
	require.Len(t, drops, 2)

	res, e, sessionID, _ := applyToSingleGoal(t, target, TacticReq{Type: "clear", HypIndices: drops})
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)
	g := res.State.Goals[0].Statement
	assert.Equal(t, 1, g.NumHyps(), "two hyps dropped in one apply")
	assert.False(t, g.HasHyp(junk1.Core()))
	assert.False(t, g.HasHyp(junk2.Core()))
	assert.True(t, g.Conclusion().AlphaEquals(P.Apply(x).Core()), "conclusion unchanged")

	// Close the residual and pin the recorded shape: the batch apply must
	// serialize as ONE clear_hyps ministep (a single tree node carrying
	// the index set), not an N-deep ClearHyp chain.
	res2, err := e.ApplyStep(context.Background(), sessionID, &ApplyStepRequest{
		GoalID: res.State.Goals[0].ID,
		Tactic: TacticReq{Type: "assumption"},
	})
	require.NoError(t, err)
	require.True(t, res2.Success)
	require.True(t, res2.State.Complete)

	s, err := e.getSession(sessionID)
	require.NoError(t, err)
	detailed := s.sections[0].root.DetailedProofProto()
	require.NotNil(t, detailed, "section root must be proved")
	batchSteps := 0
	for _, st := range detailed.Steps {
		if step, ok := st.Step.(*proof.StepProto_ClearHyps); ok {
			batchSteps++
			assert.Len(t, step.ClearHyps.GetHypIndices(), 2)
		}
	}
	assert.Equal(t, 1, batchSteps, "batch clear records ONE clear_hyps ministep")
}

func TestApply_ClearMultipleHypsErrors(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	junk := ext.Var("junk", core.TypeBool())
	target := prop.MakeProp(P.Apply(x).Core(), junk.Core(), P.Apply(x).Core()) // 2 hyps

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)

	// Duplicate index → rejected before any drop.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID,
		Tactic: TacticReq{Type: "clear", HypIndices: []int{0, 0}}})
	require.NoError(t, err)
	require.False(t, res.Success)
	assert.Contains(t, res.Diagnostics[0].Message, "duplicate")

	// Out-of-range entry → rejected before any drop.
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID,
		Tactic: TacticReq{Type: "clear", HypIndices: []int{0, 9}}})
	require.NoError(t, err)
	require.False(t, res.Success)
	assert.Contains(t, res.Diagnostics[0].Message, "out of range")
}

func TestApply_Symm(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	target := prop.MakeProp(x.Eq(y).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "symm"})
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)
	// New conclusion should be y = x.
	expected := y.Eq(x).Core()
	assert.True(t, res.State.Goals[0].Statement.Conclusion().AlphaEquals(expected))
}

func TestApply_Funext(t *testing.T) {
	// Use λ-headed sides so prop.FunEqRewrite takes the FunEq path
	// directly (both-AbsTerm branch) and the result is ∀-headed in a
	// single rewrite step. For non-AbsTerm sides like `f = g` (vars),
	// FunEqRewrite does one-step η-expansion instead, which is also
	// valid funext but doesn't immediately surface the ∀ form — the
	// agent would call funext again. Both shapes are exercised by the
	// kernel tests; here we pin down the AbsTerm-AbsTerm path because
	// it's what LEAN-fluent agents will most often hit.
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeA()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeA()))
	lhs := x.To(P.Apply(x).Core()) // λx. P(x)
	rhs := x.To(Q.Apply(x).Core()) // λx. Q(x)
	target := prop.MakeProp(lhs.Eq(rhs).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "funext"})
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)
	assert.False(t, ext.MatchesFORALL(res.State.Goals[0].Statement.Conclusion()).IsZero(), "funext on λx.P(x) = λx.Q(x) should produce a ∀-headed conclusion")
}

// TestApply_FunextTakesEveryFunctionEquation: the session's `funext`
// takes what its tactic rewrites, every equation between functions in
// the conclusion — a conjunct, or one under a binder its sides mention,
// as the one at the top — in one step, as the Go `Funext()` does. A
// conclusion that holds none is refused by its shape.
func TestApply_FunextTakesEveryFunctionEquation(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	fun := core.MakeFun(core.TypeA(), core.TypeA())
	P, Q, R := ext.Var("P", fun), ext.Var("Q", fun), ext.Var("R", fun)
	lam := func(f *ext.TermWrapper) *ext.TermWrapper { return x.To(f.Apply(x)) }
	first := lam(P).Eq(lam(Q))
	second := lam(Q).Eq(lam(R))
	res, _, _, _ := applyToSingleGoal(t, prop.MakeProp(first.And(second).Core()), TacticReq{Type: "funext"})
	require.True(t, res.Success, "funext on a conjunction of function equations: %+v", res.Diagnostics)
	require.Equal(t, 1, res.State.NumOpen)
	left, right, ok := ext.MatchesAND(res.State.Goals[0].Statement.Conclusion())
	require.True(t, ok, "the conclusion stays a conjunction: %s", ext.PrintTerm(res.State.Goals[0].Statement.Conclusion()))
	assert.False(t, ext.MatchesFORALL(left).IsZero(), "the first conjunct is pointwise: %s", ext.PrintTerm(left))
	assert.False(t, ext.MatchesFORALL(right).IsZero(), "the second conjunct is pointwise: %s", ext.PrintTerm(right))

	// Under a binder the equation's sides mention, as at the top.
	h := ext.Var("h", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeA()))
	under := ext.ForAll(y)(x.To(h.Apply(y, x)).Eq(h.Apply(y)))
	res, _, _, _ = applyToSingleGoal(t, prop.MakeProp(under.Core()), TacticReq{Type: "funext"})
	require.True(t, res.Success, "funext on a function equation under a binder: %+v", res.Diagnostics)
	require.Equal(t, 1, res.State.NumOpen)
	outer := ext.MatchesFORALL(res.State.Goals[0].Statement.Conclusion())
	require.False(t, outer.IsZero())
	assert.False(t, ext.MatchesFORALL(outer.Body()).IsZero(), "the equation under the binder is pointwise: %s",
		ext.PrintTerm(res.State.Goals[0].Statement.Conclusion()))

	err := applyToSingleGoalExpectErr(t, prop.MakeProp(x.Eq(y).And(y.Eq(x)).Core()), TacticReq{Type: "funext"})
	require.ErrorContains(t, err, "goal shape does not match")
}

func TestApply_Congr(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	target := prop.MakeProp(f.Apply(a).Eq(f.Apply(b)).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "congr"})
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)
	// Subgoal should be a = b.
	assert.True(t, res.State.Goals[0].Statement.Conclusion().AlphaEquals(a.Eq(b).Core()))
}

// TestApply_CongrArg pins the full RPC dispatch for congr_arg: equality
// hyp (a = b)@0 plus a function `f` (in scope via the conclusion) adds
// the hyp f(a) = f(b) and leaves one subgoal.
func TestApply_CongrArg(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	// Goal: (a = b) ⊢ f(a) = f(b). f is in scope via the conclusion, so
	// the term-DSL parse of "f" resolves. The added hyp then closes the
	// conclusion by auto-match, but we only assert congr_arg applied.
	target := prop.MakeProp(f.Apply(a).Eq(f.Apply(b)).Core(), a.Eq(b).Core())
	idx := 0
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "congr_arg",
		Const:    ext.PrintTerm(f),
		HypIndex: &idx,
	})
	require.True(t, res.Success, "congr_arg should succeed; diagnostics: %+v", res.Diagnostics)
}

func TestApply_CongrArg_RequiresHypIndex(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	target := prop.MakeProp(f.Apply(a).Eq(f.Apply(b)).Core(), a.Eq(b).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "congr_arg",
		Const: ext.PrintTerm(f),
	})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "requires hyp_index")
}

func TestApply_CongrArg_HypNotEquality(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	// hyp 0 is P(a), not an equality.
	target := prop.MakeProp(f.Apply(a).Eq(f.Apply(a)).Core(), P.Apply(a).Core())
	idx := 0
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "congr_arg",
		Const:    ext.PrintTerm(f),
		HypIndex: &idx,
	})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "not an equality")
}

func TestApply_CongrArg_DomainMismatch(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	// g : B → B, equality is over A.
	g := ext.Var("g", core.MakeFun(ext.TypeB, ext.TypeB))
	target := prop.MakeProp(a.Eq(b).Core(), g.Eq(g).Core())
	idx := 0
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "congr_arg",
		Const:    ext.PrintTerm(g),
		HypIndex: &idx,
	})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "domain")
}

// TestApply_CongrFun pins the dual dispatch: function-equality hyp
// (f = g)@0 plus argument `x` adds the hyp f(x) = g(x).
func TestApply_CongrFun(t *testing.T) {
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	g := ext.Var("g", core.MakeFun(core.TypeA(), core.TypeA()))
	x := ext.Var("x", core.TypeA())
	// Goal: (f = g) ⊢ f(x) = g(x). x and f,g in scope via concl/hyp.
	target := prop.MakeProp(f.Apply(x).Eq(g.Apply(x)).Core(), f.Eq(g).Core())
	idx := 0
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "congr_fun",
		Const:    ext.PrintTerm(x),
		HypIndex: &idx,
	})
	require.True(t, res.Success, "congr_fun should succeed; diagnostics: %+v", res.Diagnostics)
}

func TestApply_CongrFun_NonFunctionEquality(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	x := ext.Var("x", core.TypeA())
	// hyp (a = b) — sides are TypeA, not functions.
	target := prop.MakeProp(a.Eq(b).Core(), a.Eq(b).Core())
	idx := 0
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "congr_fun",
		Const:    ext.PrintTerm(x),
		HypIndex: &idx,
	})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "not functions")
}

// TestApply_Rw pins the full RPC dispatch for rw: equality hyp
// (f(m) = d)@idx rewrites f(m)→d across BOTH another hyp and the
// conclusion in one step — the fixpoint behavior subst lacks.
func TestApply_Rw(t *testing.T) {
	m := ext.Var("m", core.TypeA())
	d := ext.Var("d", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))

	eq := f.Apply(m).Eq(d).Core()
	target := prop.MakeProp(Q.Apply(f.Apply(m).Core()).Core(),
		eq, P.Apply(f.Apply(m).Core()).Core())
	idx := -1
	for i := 0; i < target.NumHyps(); i++ {
		if target.Hyp(i).Equals(eq) {
			idx = i
		}
	}
	require.GreaterOrEqual(t, idx, 0, "equality must be a hyp")

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "rw",
		HypIndex: &idx,
	})
	require.True(t, res.Success, "rw should succeed; diagnostics: %+v", res.Diagnostics)
	require.Equal(t, 1, res.State.NumOpen)
	g := res.State.Goals[0].Statement
	assert.True(t, g.Conclusion().AlphaEquals(Q.Apply(d).Core()),
		"conclusion must rewrite to Q(d), got %v", g.Conclusion())
	assert.True(t, g.HasHyp(P.Apply(d).Core()), "hyp P(f(m)) must rewrite to P(d)")
}

// TestApply_Rw_Flip pins the reversed direction: hyp (f(m) = d)@idx
// with flip rewrites d→f(m) in the conclusion.
func TestApply_Rw_Flip(t *testing.T) {
	m := ext.Var("m", core.TypeA())
	d := ext.Var("d", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))

	eq := f.Apply(m).Eq(d).Core()
	target := prop.MakeProp(Q.Apply(d).Core(), eq)
	idx := 0
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "rw",
		HypIndex: &idx,
		Flip:     true,
	})
	require.True(t, res.Success, "flipped rw should succeed; diagnostics: %+v", res.Diagnostics)
	require.Equal(t, 1, res.State.NumOpen)
	assert.True(t, res.State.Goals[0].Statement.Conclusion().AlphaEquals(
		Q.Apply(f.Apply(m).Core()).Core()),
		"conclusion must rewrite d→f(m), got %v",
		res.State.Goals[0].Statement.Conclusion())
}

func TestApply_Rw_Errors(t *testing.T) {
	m := ext.Var("m", core.TypeA())
	d := ext.Var("d", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	eq := f.Apply(m).Eq(d).Core()
	goalID := s.AddGoal(prop.MakeProp(Q.Apply(f.Apply(m).Core()).Core(), eq))

	// Missing hyp_index → required-field message.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID, Tactic: TacticReq{Type: "rw"}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "requires hyp_index")

	// Out-of-range index.
	bad := 9
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID, Tactic: TacticReq{Type: "rw", HypIndex: &bad}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "out of range")

	// Non-equality hyp.
	notEqID := s.AddGoal(prop.MakeProp(Q.Apply(m).Core(), P.Apply(m).Core()))
	idx := 0
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: notEqID, Tactic: TacticReq{Type: "rw", HypIndex: &idx}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "not an equality")

	// No occurrence of the oriented side → "no effect" with direction hint.
	noOccID := s.AddGoal(prop.MakeProp(Q.Apply(m).Core(), eq))
	idx2 := 0
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: noOccID, Tactic: TacticReq{Type: "rw", HypIndex: &idx2}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "no effect")
}

func TestApply_Subst_OutOfRange(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	target := prop.MakeProp(x.Eq(x).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "subst",
		HypIndex: new(5),
	})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "out of range")
}

func TestApply_Subst_HypNotEquality(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(x.Eq(x).Core(), P.Apply(x).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "subst",
		HypIndex: new(0),
	})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "not an equality")
}

func TestApply_Trans(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	c := ext.Var("c", core.TypeA())
	// Conclusion `a = c` with `b` already in scope as a free var (mentioned in a hyp).
	hyp := a.Eq(b)
	target := prop.MakeProp(a.Eq(c).Core(), hyp.Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "trans",
		Const: ext.PrintTerm(b),
	})
	require.True(t, res.Success, "trans should succeed; diagnostics: %+v", res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen)
}

// TestApply_Trans_NovelMiddle is the left-distributivity-shaped case of
// `trans` rejecting witness terms that do not appear in the
// goal. The middle term `f(a)` is well-typed against the goal's
// free-var context (`f`, `a` both already in scope via hyps) but is
// not literally a subterm — the engine must fall back to
// dsl.ParseTermText so trans can synthesize the bridge.
func TestApply_Trans_NovelMiddle(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	c := ext.Var("c", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))

	// Goal: a = c. Hyps put f and b in scope as free vars.
	target := prop.MakeProp(
		a.Eq(c).Core(),
		f.Apply(b).Eq(c).Core(),
	)
	// Middle `f(a)` is constructible from in-scope vars but appears
	// nowhere as a subterm. The fast path misses; the parser fallback
	// activates with expected = TypeA (the equality side type).
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "trans",
		Const: "f(a)",
	})
	require.True(t, res.Success, "trans with novel middle should succeed; diagnostics: %+v", res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen, "trans produces two subgoals: a = f(a) and f(a) = c")
}

// TestApply_Trans_NovelMiddle_Rejects_FreshVar pins the scope guard:
// a middle term that introduces a name not already free in the goal
// gets rejected, same rule `assert` enforces. Without this, the
// parser fallback would silently smuggle in fresh variables.
func TestApply_Trans_NovelMiddle_Rejects_FreshVar(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	c := ext.Var("c", core.TypeA())
	target := prop.MakeProp(a.Eq(c).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "trans",
		Const: "d", // d is fresh — not free in the goal
	})
	assert.False(t, res.Success, "fresh free var must be rejected")
	require.NotEmpty(t, res.Diagnostics)
	// The parser fails on missing-type before the scope guard runs,
	// but either diagnostic is acceptable as long as it surfaces the
	// problem clearly. We assert on the umbrella "term ... not found"
	// prefix that wraps both cases.
	assert.Contains(t, res.Diagnostics[0].Message, `"d"`)
}

// TestApply_Trans_NovelMiddle_NamesGoalConstant pins the constant-scope
// fix: a novel middle term that names a defined constant already present
// in the goal (here predecessor) must resolve that name as the constant — not as
// a fresh free variable. Before goalConstScope was threaded into the
// term-DSL parse, only the five built-in nat encoders resolved by name;
// every other constant (predecessor, SUB, …) parsed as a free var and was then
// rejected by the scope guard with "references unbound variable predecessor",
// even though predecessor is right there in the goal as a constant.
func TestApply_Trans_NovelMiddle_NamesGoalConstant(t *testing.T) {
	num := dsl.NumType
	preMeta := core.MakeConstMeta("predecessor", core.MakeFun(num, num))
	pre := ext.WrapTerm(core.MakeConstTerm(preMeta, core.MakeFun(num, num)))
	b := ext.Var("b", num)
	c := ext.Var("c", num)

	// Goal: predecessor(b) = b ⊢ b = c. The hyp puts predecessor into the goal as a
	// constant so goalConstScope can harvest it. Middle `predecessor(c)` is not a
	// subterm (forces the parser slow path) but names only predecessor (const) and
	// c (free, in the goal).
	target := prop.MakeProp(b.Eq(c).Core(), pre.Apply(b.Core()).Eq(b.Core()).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "trans",
		Const: "predecessor(c)",
	})
	require.True(t, res.Success,
		"trans middle naming a goal constant must resolve predecessor as a constant; diagnostics=%+v",
		res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen,
		"trans produces two subgoals: b = predecessor(c) and predecessor(c) = c")
}

// TestApply_Trans_NovelMiddle_NamesRegisteredConstantNotInGoal pins the
// term-parameter registry resolver: a trans bridge may name polymorphic
// registered constants that do not occur anywhere in the current
// goal/hyps. Without ParseScope.ConstResolver seeded by
// resolveTermWithFallback, image would parse as an undeclared function
// in value position and fail with "cannot infer result type of
// undeclared function \"image\"".
func TestApply_Trans_NovelMiddle_NamesRegisteredConstantNotInGoal(t *testing.T) {
	typeA := core.MakeVarType("TA")
	typeB := core.MakeVarType("TB")
	typeC := core.MakeVarType("TC")
	opType := core.MakeVarType("TOP")
	num := dsl.NumType
	setA := core.MakeFun(typeA, core.TypeBool())
	setC := core.MakeFun(typeC, core.TypeBool())

	mgr := registry.GetConstMetaManager()
	mgr.LoadOrStoreConstMeta(core.MakeConstMeta("image",
		core.MakeFun(
			core.MakeFun(core.MakeVarType("A"), core.MakeVarType("B")),
			core.MakeFun(core.MakeFun(core.MakeVarType("A"), core.TypeBool()),
				core.MakeFun(core.MakeVarType("B"), core.TypeBool())))))
	mgr.LoadOrStoreConstMeta(core.MakeConstMeta("o",
		core.MakeFun(
			core.MakeFun(core.MakeVarType("B"), core.MakeVarType("C")),
			core.MakeFun(core.MakeFun(core.MakeVarType("A"), core.MakeVarType("B")),
				core.MakeFun(core.MakeVarType("A"), core.MakeVarType("C"))))))

	lhs := ext.Var("lhs", num)
	rhs := ext.Var("rhs", num)
	iterate := ext.Var("iterate", core.MakeFun(opType, setC, core.MakeFun(typeC, num), num))
	op := ext.Var("op", opType)
	f := ext.Var("f", core.MakeFun(typeB, typeC))
	g := ext.Var("g", core.MakeFun(typeA, typeB))
	s := ext.Var("s", setA)
	h := ext.Var("h", core.MakeFun(typeC, num))

	// image and o are intentionally absent from the goal. The trivial hyps
	// only put the free variables' types into the parser context.
	target := prop.MakeProp(lhs.Eq(rhs).Core(),
		iterate.Eq(iterate.Core()).Core(),
		op.Eq(op.Core()).Core(),
		f.Eq(f.Core()).Core(),
		g.Eq(g.Core()).Core(),
		s.Eq(s.Core()).Core(),
		h.Eq(h.Core()).Core(),
	)
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "trans",
		Const: "iterate(op, image(o(f, g), s), h)",
	})
	require.True(t, res.Success,
		"trans bridge must resolve registered image/o without prior goal occurrence; diagnostics=%+v",
		res.Diagnostics)
	assert.Equal(t, 2, res.State.NumOpen)
}

// TestApply_Trans_AcceptsBothSubscriptForms pins per-tactic subscript-form
// consistency. The printer Unicode-upgrades `m_0` → `m₀`; the fast path's
// `ext.PrintTerm(s) == spec` only matches the Unicode form. The slow path
// (dsl.ParseTermText) is supposed to cover the ASCII form via in-scope
// var resolution. This test exercises both.
//
// An agent's report: "trans.const requires Unicode m₀;
// must use lemma.text-style m_0 elsewhere — per-tactic inconsistency".
// If this test passes, the diagnosis is incorrect for trans; if it fails,
// resolveTermWithFallback's slow path needs the same fix as case_split.
func TestApply_Trans_AcceptsBothSubscriptForms(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	c := ext.Var("c", core.TypeA())
	m0 := ext.Var("m_0", core.TypeA())
	// Goal: a = c, with m_0 free in a hyp so it's in scope. Middle = m_0.
	target := prop.MakeProp(a.Eq(c).Core(), m0.Eq(a).Core())

	printed := ext.PrintTerm(m0)
	require.Equal(t, "m₀", printed,
		"test invariant: printer must Unicode-upgrade the subscript")

	for _, form := range []string{"m₀" /* Unicode, fast path */, "m_0" /* ASCII, slow path */} {
		form := form
		t.Run("input="+form, func(t *testing.T) {
			res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
				Type:  "trans",
				Const: form,
			})
			require.True(t, res.Success,
				"trans must accept both subscript forms; diagnostics=%+v", res.Diagnostics)
			assert.Equal(t, 2, res.State.NumOpen, "trans produces two subgoals")
		})
	}
}

// TestApply_Trans_NovelMiddle_Rejects_WrongType pins the
// expected-type contract: a middle whose type doesn't match the
// equality's sides is rejected via the parser's type-mismatch
// diagnostic rather than silently building an ill-typed subgoal.
func TestApply_Trans_NovelMiddle_Rejects_WrongType(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	c := ext.Var("c", core.TypeA())
	// `q` is a bool free var; its type can't match the TypeA
	// equality.
	q := ext.Var("q", core.TypeBool())
	target := prop.MakeProp(a.Eq(c).Core(), q.Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "trans",
		Const: "q",
	})
	assert.False(t, res.Success, "type-mismatched middle must be rejected")
	require.NotEmpty(t, res.Diagnostics)
	// `q` is a subterm of a hyp so the fast path returns it; the
	// type mismatch then surfaces from proof.ApplyTrans rather than
	// the parser. Either path is acceptable — the test pins the
	// *outcome* (failure), not the specific diagnostic source.
}

func TestApply_ByContra_NotEnumeratedButDispatchable(t *testing.T) {
	// Per Decision 5: by_contra is dispatchable via apply but is NOT
	// enumerated by inspect's structural_facts (its shape predicate
	// fires on essentially every non-⊥ goal — too noisy to surface).
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(P.Apply(x).Core())

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)

	// Inspect: by_contra must NOT appear in structural_facts.
	insRes, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
	require.NoError(t, err)
	for _, f := range insRes.StructuralFacts {
		assert.NotEqual(t, "by_contra", f.Kind,
			"by_contra must not appear in inspect's structural_facts (Decision 5)")
	}

	// Apply: by_contra still works when invoked directly.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "by_contra"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "by_contra must dispatch successfully on a non-⊥ goal")
	require.Equal(t, 1, res.State.NumOpen)
	// New goal: P(x), ¬P(x) ⊢ ⊥ — auto-match might close it via contradict.
	if !res.State.Complete {
		assert.True(t, res.State.Goals[0].Statement.Conclusion().Equals(ext.F),
			"by_contra subgoal must have ⊥ as conclusion")
	}
}

func TestApply_ByContra_OnFalseGoal_Fails(t *testing.T) {
	// by_contra on a goal that is already ⊥ is refused by name rather
	// than expanded into `¬⊥ ⊢ ⊥`, a refutation of a tautology's
	// negation.
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	gid := s.AddGoal(prop.MakeProp(ext.F))
	refusal := stepRefusal(t, e, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by_contra"}})
	assert.Contains(t, refusal, "already ⊥")
}

func TestSmartIntro_Imply(t *testing.T) {
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	target := prop.MakeProp(p.Imply(q).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "intro"})
	require.True(t, res.Success, "intro on A⇒B should dispatch via strip_imp")
	require.Equal(t, 1, res.State.NumOpen)
	// New goal: p ⊢ q.
	g := res.State.Goals[0]
	assert.True(t, g.Statement.Conclusion().AlphaEquals(q.Core()))
}

func TestSmartIntro_Forall(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(ext.ForAll(x)(P.Apply(x)))
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "intro"})
	require.True(t, res.Success, "intro on ∀x.P(x) should dispatch via strip_quant")
	require.Equal(t, 1, res.State.NumOpen)
	// New goal concl is P(x') (with possibly a freshened name).
	abs := ext.MatchesFORALL(res.State.Goals[0].Statement.Conclusion())
	assert.True(t, abs.IsZero(), "intro must consume the outer ∀")
}

func TestSmartIntro_NeitherShape(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	// concl is atomic — neither ⇒ nor ∀.
	target := prop.MakeProp(P.Apply(x).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{Type: "intro"})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message,
		"neither A ⇒ B nor ∀x. P")
}

// TestStructuralFacts_NewTactics verifies inspect's enumerator surfaces
// the new LEAN-style structural moves (assumption / refl / left / right /
// funext / symm / congr / subst / trans) when their shape predicates fire,
// and that by_contra is conspicuously absent (Decision 5).
func TestStructuralFacts_NewTactics(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	g := ext.Var("g", core.MakeFun(core.TypeA(), core.TypeA()))

	cases := []struct {
		name    string
		goal    core.Prop
		want    []string // kinds that MUST appear
		notWant []string // kinds that MUST NOT appear
	}{
		{
			"assumption when concl matches a hyp",
			prop.MakeProp(P.Apply(x).Core(), P.Apply(x).Core()),
			[]string{"assumption"},
			[]string{"by_contra"},
		},
		{
			"refl when concl is t = t",
			prop.MakeProp(x.Eq(x).Core()),
			[]string{"refl"},
			[]string{"by_contra", "symm", "congr"},
		},
		{
			"left/right when concl is A∨B",
			prop.MakeProp(P.Apply(x).Or(P.Apply(y)).Core()),
			[]string{"left", "right"},
			[]string{"by_contra"},
		},
		{
			// `congr` is filtered out here because both sides are atomic
			// vars — TermDiff's only candidate is the whole-term
			// fallback (which we reject) and phase 2 needs AppliedTerm
			// chains, so the apply-side verification in
			// collectStructuralMoves removes it from the surface.
			"funext when concl is f = g (function-typed)",
			prop.MakeProp(f.Eq(g).Core()),
			[]string{"funext", "symm", "trans"},
			[]string{"by_contra", "congr"},
		},
		{
			// Same atomic-var rationale: `congr` doesn't apply to
			// `a = b` for atomic a, b. `symm` and `trans` do.
			"symm + trans when concl is a = b (atomic)",
			prop.MakeProp(a.Eq(b).Core()),
			[]string{"symm", "trans"},
			[]string{"by_contra", "congr"},
		},
		{
			// `congr` DOES apply when sides are AppliedTerm chains —
			// here `f(a) = f(b)` decomposes to `a = b`.
			"congr when concl is f(a) = f(b)",
			prop.MakeProp(f.Apply(a).Eq(f.Apply(b)).Core()),
			[]string{"congr", "symm", "trans"},
			[]string{"by_contra"},
		},
		{
			// subst is gated on actual progress (eqSimplify shrinks the
			// goal). Q(x) = x is the canonical pattern: rewrite Q(x) → x
			// in P(Q(x), y) shrinks to P(x, y).
			"subst when the equality hyp actually rewrites a subterm",
			func() core.Prop {
				P2 := ext.Var("P2", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
				Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeA()))
				return prop.MakeProp(P2.Apply(Q.Apply(x).Core(), y.Core()).Core(), Q.Apply(x).Eq(x).Core())
			}(),
			[]string{"subst"},
			[]string{"by_contra"},
		},
		{
			// Negative gate: `x = y` with concl P(x) does NOT shrink
			// (P(x) and P(y) are the same size), so subst would fail
			// at apply time. Inspect must NOT enumerate it — facts are
			// applicable, not just shape-matching.
			"subst NOT enumerated when the rewrite leaves goal size unchanged",
			prop.MakeProp(P.Apply(x).Core(), x.Eq(y).Core()),
			nil,
			[]string{"subst"},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			e := newEngine(testEnv())
			ctx := context.Background()
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, _ := e.getSession(info.ID)
			goalID := s.AddGoal(tc.goal)
			res, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
			require.NoError(t, err)

			kinds := make(map[string]bool)
			for _, f := range res.StructuralFacts {
				kinds[f.Kind] = true
			}
			for _, w := range tc.want {
				assert.True(t, kinds[w],
					"expected %q in structural_facts; got %v", w, structuralFactsKinds(res.StructuralFacts))
			}
			for _, n := range tc.notWant {
				assert.False(t, kinds[n],
					"unexpected %q in structural_facts; got %v", n, structuralFactsKinds(res.StructuralFacts))
			}
		})
	}
}

func structuralFactsKinds(facts []StructuralFact) []string {
	out := make([]string, 0, len(facts))
	for _, f := range facts {
		out = append(out, f.Kind)
	}
	return out
}

// TestStructuralFacts_SubstHypIndexParam verifies that when subst is
// surfaced, the hyp_index param round-trips as a string (matching the
// existing convention for case_split's "term" and induction's "var").
// The agent reads the string, parses to int, and feeds it back via
// tactic.hyp_index — which must round-trip the same value.
//
// Both equality hyps below use the `f(x) = x` shape so subst actually
// makes progress on the conclusion (the enumerator is gated on apply
// succeeding — see structural.go §3c).
func TestStructuralFacts_SubstHypIndexParam(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeA()))
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeA()))

	// Conclusion mentions both Q(x) and R(y); each rewrite shrinks it.
	concl := P.Apply(Q.Apply(x).Core(), R.Apply(y).Core()).Core()
	target := prop.MakeProp(concl, Q.Apply(x).Eq(x).Core(), R.Apply(y).Eq(y).Core())

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)
	res, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
	require.NoError(t, err)

	var substIndices []string
	for _, f := range res.StructuralFacts {
		if f.Kind != "subst" {
			continue
		}
		idx, ok := f.Params["hyp_index"]
		require.True(t, ok, "subst fact must carry hyp_index param: %+v", f)
		substIndices = append(substIndices, idx)
	}
	assert.Contains(t, substIndices, "0", "hyp 0 (Q(x) = x) should rewrite Q(x) → x in concl")
	assert.Contains(t, substIndices, "1", "hyp 1 (R(y) = y) should rewrite R(y) → y in concl")
}

// (CLI alias dispatch — apply / unfold / use / specialize / simp /
// cases / rfl — is covered by TestTacticReqFromInput_LeanAliases in
// engine/cmd/xugo/main_test.go. The engine accepts only canonical
// names, so any check here would just retest the engine's canonical
// dispatch rather than the alias rewrite layer that lives in the CLI.)

// TestCLIAlias_LeanRwRejectsNonEq verifies that lean_rw fails with the
// typed error when pointed at a non-equality lemma. We don't need the
// CLI binary to test this — the lemma-precondition check lives in the
// engine layer, behind a non-empty Lemma field.
func TestCLIAlias_LeanRwRejectsNonEq(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))

	// A non-equality lemma: ∀x. P(x) ⇒ (P(x) ∨ Q(x)). Conclusion (after
	// stripping ∀) is `P(x) ⇒ ...` — not an equality.
	nonEqLemma := prop.MakeProp(ext.ForAll(x)(P.Apply(x).Imply(P.Apply(x).Or(Q.Apply(x)))))

	target := prop.MakeProp(P.Apply(x).Or(Q.Apply(x)).Core(), P.Apply(x).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "lean_rw",
		Lemma: nonEqLemma,
	})
	assert.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.True(t,
		strings.Contains(res.Diagnostics[0].Message, "lean_rw expects an equality lemma"),
		"expected typed error about non-equality lemma; got %q",
		res.Diagnostics[0].Message)
}

// TestApply_Instantiate_TargetsHypByIndex covers the load-bearing
// behavior of the hyp_index parameter on `instantiate`: when two
// ∀-hyps share the witness's binder type, the agent uses hyp_index to
// reach a specific one. The former no-index first-match sugar was
// retired so agents face ONE grounding action — passing no index is
// now a hard error (verified below).
func TestApply_Instantiate_TargetsHypByIndex(t *testing.T) {
	x1 := ext.Var("x", core.TypeA())
	x2 := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))

	// Two ∀-hyps over TypeA. hyp_index=0 reaches P; hyp_index=1 reaches Q.
	target := prop.MakeProp(
		R.Apply(y).Core(),
		ext.ForAll(x1)(P.Apply(x1)).Core(),
		ext.ForAll(x2)(Q.Apply(x2)).Core(),
	)

	t.Run("missing hyp_index is a hard error", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:  "instantiate",
			Const: ext.PrintTerm(y),
		})
		require.False(t, res.Success, "instantiate without hyp_index must be rejected")
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "hyp_index",
			"diagnostic must name the missing parameter")
	})

	t.Run("hyp_index=1: reaches second ∀-hyp (Q)", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			Const:    ext.PrintTerm(y),
			HypIndex: new(1),
		})
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Equal(t, 1, res.State.NumOpen)
		hasPy, hasQy := scanHyps(res.State.Goals[0].Statement, P.Apply(y).Core(), Q.Apply(y).Core())
		assert.True(t, hasQy, "hyp_index=1 must add Q(y) (from hyp 1)")
		assert.False(t, hasPy, "hyp_index=1 must NOT add P(y) (hyp 0 not targeted)")
	})

	t.Run("hyp_index=0: reaches first ∀-hyp (P) explicitly", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			Const:    ext.PrintTerm(y),
			HypIndex: new(0),
		})
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		hasPy, hasQy := scanHyps(res.State.Goals[0].Statement, P.Apply(y).Core(), Q.Apply(y).Core())
		assert.True(t, hasPy)
		assert.False(t, hasQy)
	})
}

// TestApply_Instantiate_HypIndexErrors pins the typed-error contract
// for bad hyp_index inputs (mirrors subst's range / shape checks).
func TestApply_Instantiate_HypIndexErrors(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	z := ext.Var("z", core.TypeBool()) // free var of a different type for the mismatch case
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	B := ext.Var("B", core.MakeFun(core.TypeBool(), core.TypeBool()))

	// Hyp 0 (P(y)) is not ∀-headed; hyp 1 is ∀ over TypeA.
	// B(z) is in scope so witness `z` resolves at the witness-finding
	// stage (lets the mismatch test reach the binder-type check
	// instead of bouncing on "witness not found in goal").
	target := prop.MakeProp(
		Q.Apply(y).Core(),
		P.Apply(y).Core(),
		ext.ForAll(x)(P.Apply(x)).Core(),
		B.Apply(z).Core(),
	)

	t.Run("out of range", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			Const:    ext.PrintTerm(y),
			HypIndex: new(99),
		})
		assert.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "out of range")
	})

	t.Run("not ∀-headed", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			Const:    ext.PrintTerm(y),
			HypIndex: new(0),
		})
		assert.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "not ∀-headed")
	})

	t.Run("binder type mismatch", func(t *testing.T) {
		// A fresh goal with a single ∀-hyp over TypeA and a witness
		// `z` of TypeBool in scope (so witness resolution succeeds and
		// dispatch reaches the binder-type check). hyp_index=0 points
		// at the ∀; the type mismatch is the failure mode under test.
		mismatchTarget := prop.MakeProp(
			Q.Apply(y).Core(),
			ext.ForAll(x)(P.Apply(x)).Core(), // ∀ over TypeA
			B.Apply(z).Core(),                // brings z:TypeBool into scope
		)
		// Locate the ∀-hyp by scanning — MakeProp may reorder.
		idx := -1
		for i := 0; i < mismatchTarget.NumHyps(); i++ {
			if !ext.MatchesFORALL(mismatchTarget.Hyp(i)).IsZero() {
				idx = i
				break
			}
		}
		require.GreaterOrEqual(t, idx, 0, "test goal must contain a ∀-hyp")
		res, _, _, _ := applyToSingleGoal(t, mismatchTarget, TacticReq{
			Type:     "instantiate",
			Const:    ext.PrintTerm(z),
			HypIndex: new(idx),
		})
		assert.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		// A reconcilable binder/witness type mismatch is not a bare
		// rejection (engine/instantiate_type_adapt.go): the engine
		// computes the hyp-side σ ({"A":"bool"} here) and, because the
		// ad-hoc hyp is no registry entry's statement, fails with the σ
		// recipe. The test pins that contract: the diagnostic must NAME
		// the σ, so the agent never has to fish type-var names out of a
		// parse error.
		msg := res.Diagnostics[0].Message
		assert.Contains(t, msg, `type_specialize:{"A":"bool"}`,
			"diagnostic must carry the computed σ recipe; got: %s", msg)
	})
}

// TestApply_Instantiate_TermsForm covers the multi-witness `terms`
// form: ONE apply grounds a 2-binder ∀-hyp at [y, w] via the composite
// `specialize` ministep — only the final instance R(y,w) lands (the
// intermediate partial ∀-hyp never materializes) and the source ∀-hyp
// is consumed unless `keep`. One recorded line, where an instantiate →
// inspect → instantiate → clear grounding ladder would stand.
func TestApply_Instantiate_TermsForm(t *testing.T) {
	x1 := ext.Var("x", core.TypeA())
	x2 := ext.Var("v", core.TypeA())
	y := ext.Var("y", core.TypeA())
	w := ext.Var("w", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeBool())))
	S := ext.Var("S", core.MakeFun(core.TypeA(), core.TypeBool()))

	all := ext.ForAll(x1, x2)(R.Apply(x1, x2)).Core()
	partial := ext.ForAll(x2)(R.Apply(y, x2)).Core()
	// S(w) keeps w in scope so the text-DSL witness resolves.
	target := prop.MakeProp(S.Apply(y).Core(), all, S.Apply(w).Core())
	allIdx := -1
	for i := range target.NumHyps() {
		if target.Hyp(i).AlphaEquals(all) {
			allIdx = i
			break
		}
	}
	require.GreaterOrEqual(t, allIdx, 0, "test goal must contain the ∀∀-hyp")

	t.Run("default: final instance added, source consumed, no partial", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			HypIndex: new(allIdx),
			Terms:    []string{ext.PrintTerm(y), ext.PrintTerm(w)},
		})
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Equal(t, 1, res.State.NumOpen)
		g := res.State.Goals[0].Statement
		hasInst, hasAll := scanHyps(g, R.Apply(y, w).Core(), all)
		assert.True(t, hasInst, "final ground instance R(y,w) must be a hyp")
		assert.False(t, hasAll, "source ∀-hyp must be consumed")
		hasPartial, _ := scanHyps(g, partial, partial)
		assert.False(t, hasPartial, "intermediate partial ∀v.R(y,v) must never materialize")
	})

	t.Run("keep: source stays resident", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			HypIndex: new(allIdx),
			Terms:    []string{ext.PrintTerm(y), ext.PrintTerm(w)},
			Keep:     true,
		})
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		g := res.State.Goals[0].Statement
		hasInst, hasAll := scanHyps(g, R.Apply(y, w).Core(), all)
		assert.True(t, hasInst)
		assert.True(t, hasAll, "keep:true must leave the source ∀-hyp resident")
	})

	t.Run("terms requires hyp_index", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:  "instantiate",
			Terms: []string{ext.PrintTerm(y)},
		})
		assert.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "requires `hyp_index`")
	})

	t.Run("terms and const are mutually exclusive", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			HypIndex: new(allIdx),
			Const:    ext.PrintTerm(y),
			Terms:    []string{ext.PrintTerm(y)},
		})
		assert.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "mutually exclusive")
	})

	t.Run("more terms than the hyp binds", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type:     "instantiate",
			HypIndex: new(allIdx),
			Terms:    []string{ext.PrintTerm(y), ext.PrintTerm(w), ext.PrintTerm(y)},
		})
		assert.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "binders are exhausted")
	})
}

// TestStructuralFacts_InstantiateHypIndex pins the inspect emission
// contract: each ∀-hyp gets a fact with both `var` (human hint) and
// `hyp_index` (the canonical selector apply consumes). Without
// hyp_index, the second ∀-hyp would be enumerated but unreachable.
func TestStructuralFacts_InstantiateHypIndex(t *testing.T) {
	x1 := ext.Var("x", core.TypeA())
	x2 := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))

	target := prop.MakeProp(
		R.Apply(y).Core(),
		ext.ForAll(x1)(P.Apply(x1)).Core(),
		ext.ForAll(x2)(Q.Apply(x2)).Core(),
	)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)
	res, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
	require.NoError(t, err)

	var indices []string
	for _, f := range res.StructuralFacts {
		if f.Kind != "instantiate" {
			continue
		}
		idx, hasIdx := f.Params["hyp_index"]
		require.True(t, hasIdx, "instantiate fact must carry hyp_index param: %+v", f)
		_, hasVar := f.Params["var"]
		assert.True(t, hasVar, "instantiate fact must keep `var` as a human-readable hint: %+v", f)
		indices = append(indices, idx)
	}
	assert.Contains(t, indices, "0", "hyp 0 (∀x. P x) must produce an instantiate fact")
	assert.Contains(t, indices, "1", "hyp 1 (∀x. Q x) must produce an instantiate fact")
}

// TestApply_Instantiate_NewHypsIndex verifies that the apply response's
// new_hyps reports the hypothesis instantiate introduced WITH its correct
// 0-based index in the resulting goal's canonically-sorted hyp list. The
// agent uses this to target the new hyp (e.g. instantiate's partial-∀)
// without re-inspecting: the hyp list is kept in canonical sort order, so
// adding a hyp re-sorts and renumbers it, making a pre-apply index stale.
// Regression guard for the instantiate index-staleness hazard.
func TestApply_Instantiate_NewHypsIndex(t *testing.T) {
	x1 := ext.Var("x", core.TypeA())
	x2 := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeBool()))
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))

	// Two ∀-hyps over TypeA; conclusion R(y) keeps the goal open.
	target := prop.MakeProp(
		R.Apply(y).Core(),
		ext.ForAll(x1)(P.Apply(x1)).Core(),
		ext.ForAll(x2)(Q.Apply(x2)).Core(),
	)

	check := func(t *testing.T, res *StepResult, expected core.Term) {
		t.Helper()
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Equal(t, 1, res.State.NumOpen)
		require.Len(t, res.NewHyps, 1, "instantiate adds exactly one hyp")
		nh := res.NewHyps[0]
		goal := res.State.Goals[0]
		assert.Equal(t, goal.ID, nh.GoalID, "new_hyps goal_id matches the resulting open goal")
		// The reported index must actually locate the new hyp in the
		// resulting goal's (canonically-sorted) hyp list — the whole point.
		require.GreaterOrEqual(t, nh.Index, 0)
		require.Less(t, nh.Index, goal.Statement.NumHyps())
		assert.True(t, goal.Statement.Hyp(nh.Index).AlphaEquals(expected),
			"new_hyps index %d must point at the added hyp; got %s, want %s",
			nh.Index, ext.PrintTerm(goal.Statement.Hyp(nh.Index)), ext.PrintTerm(expected))
		assert.Equal(t, ext.PrintTerm(expected), nh.Term, "new_hyps term matches the added hyp")
	}

	t.Run("hyp_index=1 adds Q(y); new_hyps locates it by index", func(t *testing.T) {
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type: "instantiate", Const: ext.PrintTerm(y), HypIndex: pIntForInstantiate(1),
		})
		check(t, res, Q.Apply(y).Core())
	})

	t.Run("hyp_index=0 adds P(y); new_hyps locates it by index", func(t *testing.T) {
		// Prior to the retirement of the no-index first-match sugar,
		// this case exercised the "no hyp_index" fall-through. The
		// composite specialize dispatch requires hyp_index; passing 0
		// hits the same target (P at hyp 0) and preserves the coverage
		// of NewHyps' index reporting for the composite path.
		res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
			Type: "instantiate", Const: ext.PrintTerm(y), HypIndex: pIntForInstantiate(0),
		})
		check(t, res, P.Apply(y).Core())
	})
}

// scanHyps reports whether the printed hyps of `p` α-contain the two
// witness terms. Helper for instantiate-targeting assertions.
func scanHyps(p core.Prop, want1, want2 core.Term) (has1, has2 bool) {
	for h := range p.HypIter() {
		if h.AlphaEquals(want1) {
			has1 = true
		}
		if h.AlphaEquals(want2) {
			has2 = true
		}
	}
	return
}

// TestStructuralFacts_SubstApplyContract pins the inspect/apply
// contract for subst: every subst fact emitted by inspect must
// succeed when applied. The enumerator gates on proof.ApplySubst
// (see structural.go §3c); without that gate, this test would fail
// for any goal where the equality hyp doesn't shrink the goal (the
// motivating regression — `P(x), x = y` would be enumerated but
// fail at apply because P(x) and P(y) are the same size).
func TestStructuralFacts_SubstApplyContract(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	P2 := ext.Var("P2", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeA(), core.TypeA()))

	cases := []struct {
		name string
		goal core.Prop
	}{
		// Positive: subst applies; inspect should surface it AND apply
		// should succeed.
		{
			"Q(x) = x rewrites Q(x) in P2(Q(x), y)",
			prop.MakeProp(P2.Apply(Q.Apply(x).Core(), y.Core()).Core(), Q.Apply(x).Eq(x).Core()),
		},
		// Negative: x = y doesn't shrink P(x); inspect must NOT surface
		// it. The contract test below would catch it because there's no
		// subst fact to assert against.
		{
			"x = y does not shrink P(x), so subst is not enumerated",
			prop.MakeProp(P.Apply(x).Core(), x.Eq(y).Core()),
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			e := newEngine(testEnv())
			ctx := context.Background()
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, _ := e.getSession(info.ID)
			goalID := s.AddGoal(tc.goal)
			res, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
			require.NoError(t, err)

			// For each subst fact emitted, applying it must succeed.
			// Use a fresh session for each apply so they don't compose.
			for _, f := range res.StructuralFacts {
				if f.Kind != "subst" {
					continue
				}
				idxStr := f.Params["hyp_index"]
				var idx int
				_, err := fmt.Sscanf(idxStr, "%d", &idx)
				require.NoError(t, err)
				e2 := newEngine(testEnv())
				info2, _ := e2.CreateSession(ctx)
				s2, _ := e2.getSession(info2.ID)
				goalID2 := s2.AddGoal(tc.goal)
				applyRes, err := e2.ApplyStep(ctx, info2.ID, &ApplyStepRequest{
					GoalID: goalID2,
					Tactic: TacticReq{Type: "subst", HypIndex: new(idx)},
				})
				require.NoError(t, err)
				assert.True(t, applyRes.Success,
					"inspect surfaced subst hyp_index=%d but apply failed: %+v",
					idx, applyRes.Diagnostics)
			}
		})
	}
}

// TestApply_LeanRwExpansion is the regression test for the size-decrease
// guard fix: lean_rw must apply equational lemmas where the RHS is
// LARGER than the LHS (extensionality, COND distribution, biconditional
// folds). Before the fix, eqSimplify rejected such rewrites with a
// monotonicity check; the lemma fell through to lemmaHypMatchTactic
// which silently added it as a hypothesis instead of rewriting.
//
// The shape mirrors a case the agent reported on componentwise vector equality: an iff
// lemma whose r2l direction expands a small LHS into a bigger RHS
// inside the goal.
func TestApply_LeanRwExpansion(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeBool()))
	g := ext.Var("g", core.MakeFun(core.TypeA(), core.TypeBool()))
	h := ext.Var("h", core.MakeFun(core.TypeA(), core.TypeBool()))

	// Iff lemma: ∀x. f(x) ⇔ (g(x) ∧ h(x)). The RHS is larger than the LHS,
	// so applying this as a rewrite to f(a) is an expansion that the old
	// size guard rejected.
	expandLemma := prop.MakeProp(
		ext.ForAll(a)(
			f.Apply(a).Eq(g.Apply(a).And(h.Apply(a).Core()).Core()).Core(),
		),
	)
	require.True(t, lemmaConclIsEquality(expandLemma),
		"sanity: ∀x. f(x) ⇔ ... must be classified as an equality lemma")

	// Goal: ⊢ f(a). After lean_rw, the conclusion should be rewritten —
	// the residual goal's conclusion must NOT alpha-equal the original
	// (otherwise the rewrite was silently dropped).
	target := prop.MakeProp(f.Apply(a).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "lean_rw",
		Lemma: expandLemma,
	})
	require.True(t, res.Success,
		"lean_rw must succeed on expansion-style iff lemma; diagnostics: %+v",
		res.Diagnostics)
	require.GreaterOrEqual(t, res.State.NumOpen, 1,
		"lean_rw expansion must leave at least the rewritten residual open")

	// Find the residual leaf and verify its conclusion is not alpha-equal
	// to f(a) (i.e. the rewrite actually transformed the goal).
	original := f.Apply(a).Core()
	rewriteVisible := false
	for _, leaf := range res.State.Goals {
		concl := leaf.Statement.Conclusion()
		if !concl.AlphaEquals(original) {
			rewriteVisible = true
			break
		}
	}
	assert.True(t, rewriteVisible,
		"lean_rw must produce a residual leaf whose conclusion differs from f(a) — got %+v",
		res.State.Goals)
}

func TestApply_LeanRwConjunctiveOriginalImageClause(t *testing.T) {
	setTy := core.MakeFun(core.TypeA(), core.TypeBool())
	empty := ext.TestConst("empty_set", setTy)
	image := ext.TestConst("image", core.MakeFun(core.MakeFun(core.TypeA(), core.TypeA()), setTy, setTy))
	insert := ext.TestConst("insert", core.MakeFun(core.TypeA(), setTy, setTy))
	card := ext.TestConst("card", core.MakeFun(setTy, dsl.NumType))

	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	x := ext.Var("x", core.TypeA())
	s := ext.Var("s", setTy)

	emptyClause := image.Apply(f, empty).Eq(empty)
	insertClause := image.Apply(f, insert.Apply(x, s)).Eq(insert.Apply(f.Apply(x), image.Apply(f, s)))
	imageClauses := prop.MakeProp(emptyClause.And(insertClause))

	target := prop.MakeProp(card.Apply(image.Apply(f, empty)).Eq(card.Apply(empty)))
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "lean_rw",
		Lemma: imageClauses,
	})
	require.True(t, res.Success,
		"lean_rw must accept conjunctive equation bundles and rewrite with the matching clause; diagnostics: %+v",
		res.Diagnostics)

	want := card.Apply(empty).Eq(card.Apply(empty))
	rewriteVisible := false
	for _, leaf := range res.State.Goals {
		if leaf.Statement.Conclusion().AlphaEquals(want) {
			rewriteVisible = true
			break
		}
	}
	assert.True(t, rewriteVisible,
		"lean_rw with a set_image.ImageClauses-style original bundle must expose rewritten residual %s; got %+v",
		ext.FormatTerm(want, false), res.State.Goals)
}

// TestApply_LemmaDoesNotExpandLikeLeanRw pins down that the lemma tactic
// (NOT lean_rw) preserves its current behavior on the same expansion
// case: it does not bypass the size guard. This is the behavior split
// the fix introduces — agents who explicitly want directional rewrite
// pick lean_rw; lemma keeps its best-effort multi-strategy semantics
// including the hypMatching fallback.
//
// We don't assert specific failure shape here (the lemma tactic has
// several fallbacks; the exact one that fires is an implementation
// detail). We only assert that whatever it produces, the conclusion
// is NOT rewritten in the way lean_rw rewrites it. The intent is to
// document the divergence rather than over-specify.
func TestApply_LemmaDoesNotExpandLikeLeanRw(t *testing.T) {
	a := ext.Var("a", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeBool()))
	g := ext.Var("g", core.MakeFun(core.TypeA(), core.TypeBool()))
	h := ext.Var("h", core.MakeFun(core.TypeA(), core.TypeBool()))

	expandLemma := prop.MakeProp(
		ext.ForAll(a)(
			f.Apply(a).Eq(g.Apply(a).And(h.Apply(a).Core()).Core()).Core(),
		),
	)
	target := prop.MakeProp(f.Apply(a).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "lemma",
		Lemma: expandLemma,
	})
	if !res.Success {
		// Acceptable: lemma may legitimately reject this case.
		return
	}
	// If lemma succeeded, the residual leaf's conclusion (if there is
	// one matching f(a) shape) must still α-equal f(a) — i.e. lemma
	// fell through to the hypMatching fallback (adds as hyp, conclusion
	// unchanged) rather than rewriting like lean_rw does.
	original := f.Apply(a).Core()
	for _, leaf := range res.State.Goals {
		// Skip the lemma-itself child (its conclusion α-equals the lemma).
		if leaf.Statement.Conclusion().AlphaEquals(expandLemma.Conclusion()) {
			continue
		}
		assert.True(t, leaf.Statement.Conclusion().AlphaEquals(original),
			"lemma tactic must not rewrite f(a) when size guard rejects; got %s",
			prop.PrintProp(leaf.Statement))
	}
}

// TestApply_LemmaPreservesInstantiatedHyps is the engine-level
// regression for `lemma` re-normalizing the hyp context and dropping
// previously-built ground instantiations: after a manual
// `instantiate`, applying `lemma` with an unrelated ∀-fact must keep
// the ground-specialized hyp — a dispatch through ApplyLemma lets the
// resident ∀-equation absorb its own instance back to the ∀-form,
// forcing the agent to re-instantiate after every lemma load.
func TestApply_LemmaPreservesInstantiatedHyps(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	c := ext.Var("c", core.TypeA())
	f := ext.TestConst("f", core.MakeFun(core.TypeA(), core.TypeA()))
	g := ext.TestConst("g", core.MakeFun(core.TypeA(), core.TypeA()))
	R := ext.TestConst("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	P := ext.TestConst("P", core.MakeFun(core.TypeA(), core.TypeBool()))

	forallEq := ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x))) // ∀x. f(x) = g(x)
	ground := f.Apply(c).Eq(g.Apply(c))                  // f(c) = g(c)
	unrelated := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())

	// Goal: {∀x. f(x)=g(x)} ⊢ P(c) — c in scope as a goal free var.
	target := prop.MakeProp(P.Apply(c).Core(), forallEq.Core())

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)

	// Step 1: manual instantiate at the ground witness c.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "instantiate", Const: "c", HypIndex: pIntForInstantiate(0)},
	})
	require.NoError(t, err)
	require.True(t, res.Success)
	require.Equal(t, 1, res.State.NumOpen)
	require.True(t, res.State.Goals[0].Statement.HasHyp(ground.Core()),
		"instantiate must add the ground instance")
	goalID = res.State.Goals[0].ID

	// Step 2: load an unrelated ∀-lemma.
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "lemma", Lemma: unrelated},
	})
	require.NoError(t, err)
	require.True(t, res.Success)

	// The residual goal (the non-lemma-obligation one) must retain BOTH
	// the ∀-form and the ground instance, plus the new lemma hyp.
	var residual core.Prop
	for _, g := range res.State.Goals {
		if g.Statement.Conclusion().AlphaEquals(P.Apply(c).Core()) {
			residual = g.Statement
		}
	}
	require.NotNil(t, residual, "residual goal must remain open")
	assert.True(t, residual.HasHyp(forallEq.Core()), "∀-form survives")
	assert.True(t, residual.HasHyp(ground.Core()),
		"ground instantiation must survive the lemma load (the KI regression)")
	assert.True(t, residual.AnyHyp(unrelated.Conclusion().AlphaEquals),
		"the loaded lemma landed as a hyp")
}

// A `subst` refused by its size guard names `rw` on the same hypothesis
// as its FIRST repair hint: the goal `x = f(y) ⊢ P(x)` orients the
// equation bigger-to-smaller (f(y) → x), the conclusion carries no
// f(y), so subst has no effect — and the generic hints, which walk the
// goal's definable constants, would never say so.
func TestApply_Subst_SizeGuardHintsRwFirst(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(P.Apply(x).Core(), x.Eq(f.Apply(y)).Core())
	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:     "subst",
		HypIndex: new(0),
	})
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	last := res.Diagnostics[len(res.Diagnostics)-1]
	assert.Contains(t, last.Message, "no rewrite reduced the goal size")
	require.NotEmpty(t, last.RepairHints, "the size-guard refusal carries repair hints")
	assert.Contains(t, last.RepairHints[0].Description, "try rw (hyp_index 0)",
		"rw on the refused hypothesis is the first hint, not an unfold: %+v", last.RepairHints)
}
