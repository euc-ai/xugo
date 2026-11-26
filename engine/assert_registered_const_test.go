package engine

import (
	"context"
	"github.com/euc-ai/xugo/library/registry"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestParsePropTextInGoalScope_RegisteredConstNotInGoal pins the
// ParseScope.ConstResolver contract: an assert/lemma claim may name a
// registered constant that does NOT occur in the surrounding goal.
// goalConstScope alone (goal-local) would leave such a name as a fresh
// free variable, and either (a) the type-inferencer would reject it as
// an undeclared head, or (b) the assert frees-⊆-goal scope guard would
// reject the resulting parse.
//
// Mirrors the agent's complaint shape from the nadd metric layer:
// an assert claim like `∃B:num. ∀n:num. nat_dist(dest_nadd(...)) ≤ B` where
// the goal is over `x:nadd` but never applies `dest_nadd` itself.
func TestParsePropTextInGoalScope_RegisteredConstNotInGoal(t *testing.T) {
	naddType := core.MakeCompositeType(core.MakeMetaType("nadd", 0))
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))

	// Seed dest_nadd into the process-global const registry, like a
	// chapter's mint. dest_nadd is intentionally NOT placed into the goal.
	mgr := registry.GetConstMetaManager()
	mgr.LoadOrStoreConstMeta(core.MakeConstMeta(
		"dest_nadd", core.MakeFun(naddType, core.MakeFun(numType, numType))))

	// Goal: ⊢ x = x where x:nadd is a free var. dest_nadd is absent.
	x := ext.Var("x", naddType)
	goal := prop.MakeProp(core.Eq(x, x)).Core()

	// Without the resolver this fails with "cannot infer result type of
	// undeclared function 'dest_nadd' applied to (nadd, num); declare it ..."
	claimText := "∃B:num. ∀n:num. dest_nadd(x, n) ≤ B"
	claim, err := parsePropTextInGoalScope(claimText, goal, nil)
	require.NoError(t, err, "registry-resolved dest_nadd must parse without being declared")
	require.NotNil(t, claim)
	// dest_nadd must have landed as a ConstTerm, not a free variable.
	for _, v := range claim.Conclusion().Frees(nil) {
		assert.NotEqual(t, "dest_nadd", string(v.Name()),
			"dest_nadd must resolve as a registered constant, not leak as a free var")
	}
}

// TestApplyStep_AssertClaimText_RegisteredConst is the end-to-end counterpart:
// an `assert` whose claim arrives as raw ClaimText naming a registered
// constant absent from the goal parses, the assert scope guard accepts it
// (because dest_nadd is now a ConstTerm and not a free var), and the
// tactic applies — splitting the goal into the claim subgoal and the
// continuation.
func TestApplyStep_AssertClaimText_RegisteredConst(t *testing.T) {
	naddType := core.MakeCompositeType(core.MakeMetaType("nadd", 0))
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))

	mgr := registry.GetConstMetaManager()
	mgr.LoadOrStoreConstMeta(core.MakeConstMeta(
		"dest_nadd", core.MakeFun(naddType, core.MakeFun(numType, numType))))

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	x := ext.Var("x", naddType)
	// Goal: ⊢ x = x. Trivial conclusion; we only care that assert applies.
	goalID := s.AddGoal(prop.MakeProp(core.Eq(x, x)))

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{
			Type:      "assert",
			ClaimText: "∃B:num. ∀n:num. dest_nadd(x, n) ≤ B",
		},
	})
	require.NoError(t, err,
		"assert.text naming a registered const not in goal must succeed; got: %v", err)
	require.True(t, res.Success)
	assert.Equal(t, 2, res.State.NumOpen,
		"assert splits into the claim subgoal and the continuation")
}

// TestApplyStep_AssertClaimText_UnknownNameStillRejected pins the negative
// side end to end: the DSL may infer the type of an undeclared function from
// its arithmetic context, but assert's frees-⊆-goal scope guard must reject
// the resulting fresh free variable.
func TestApplyStep_AssertClaimText_UnknownNameStillRejected(t *testing.T) {
	naddType := core.MakeCompositeType(core.MakeMetaType("nadd", 0))
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	x := ext.Var("x", naddType)
	goalID := s.AddGoal(prop.MakeProp(core.Eq(x, x)))

	// NO_SUCH_CONST_xyz is neither a registered const nor a goal free var.
	// Parsing could infer it as nadd→num→num from the surrounding ≤
	// expression; the claim door's strict resolution rejects it AT
	// THE PARSE, naming the repair — earlier and better-located than the
	// downstream unbound-variable guard, which is the backstop for
	// non-text claim ingress.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{
			Type:      "assert",
			ClaimText: "∃B:num. ∀n:num. NO_SUCH_CONST_xyz(x, n) ≤ B",
		},
	})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "strict resolution")
	assert.Contains(t, res.Diagnostics[0].Message, `"NO_SUCH_CONST_xyz"`)
}
