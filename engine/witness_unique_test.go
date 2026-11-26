package engine

import (
	"context"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// TestWitness_UniqueExistence pins the session's `witness` on a goal
// `∃!x. P(x)`: it leaves one goal, P at the witness together with the
// claim that P holds of nothing else, and that goal is the two
// hypotheses of this leaf, so a `by` over them closes it.
func TestWitness_UniqueExistence(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// ∀z:A. (P(z) ∧ Q(z)) ⇒ (∀y:A. P(y) ∧ Q(y) ⇒ y = z) ⇒ ∃!x:A. P(x) ∧ Q(x)
	A := core.TypeA()
	P := ext.Var("P", core.MakeFun(A, core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(A, core.TypeBool()))
	x, y, z := ext.Var("x", A), ext.Var("y", A), ext.Var("z", A)
	holds := func(v *ext.TermWrapper) *ext.TermWrapper { return P.Apply(v).And(Q.Apply(v)) }
	goal := prop.MakeProp(ext.ForAll(z)(
		holds(z).Imply(
			ext.ForAll(y)(holds(y).Imply(ext.Eq(y, z))).Imply(
				ext.Unique(x)(holds(x))))))

	goalID := s.AddGoal(goal)
	leaf := goalID
	for _, step := range []string{"strip_quant", "strip_imp", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: leaf, Tactic: TacticReq{Type: step}})
		require.NoError(t, err)
		require.True(t, res.Success, step)
		require.Equal(t, 1, res.State.NumOpen)
		leaf = res.State.Goals[0].ID
	}

	// The structural facts offer the witness on the ∃! conclusion.
	explored, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: leaf})
	require.NoError(t, err)
	offered := false
	for _, fact := range explored.StructuralFacts {
		if fact.Kind == "witness" {
			offered = true
		}
	}
	assert.True(t, offered, "an ∃! conclusion must offer `witness`")

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: leaf, Tactic: TacticReq{Type: "witness", Const: "z"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "witness must apply on a goal ∃!x. P(x)")
	require.Equal(t, 1, res.State.NumOpen, "the ∃!-introduction leaves one goal")

	// The goal left is `holds(z₀) ∧ (∀y. holds(y) ⇒ y = z₀)`: each
	// conjunct is a hypothesis of the leaf.
	left := res.State.Goals[0]
	at, only, isAnd := ext.MatchesAND(left.Statement.Conclusion())
	require.True(t, isAnd, "expected a conjunction, got %s", ext.PrintTerm(left.Statement.Conclusion()))
	assert.True(t, left.Statement.HasHyp(at), "the first conjunct is the body at the witness")
	assert.True(t, left.Statement.HasHyp(only), "the second conjunct says the body holds of nothing else")

	first, second := 0, 1
	res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: left.ID, Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &first}, {HypIndex: &second}}},
	})
	require.NoError(t, err)
	require.True(t, res.Success)
	assert.Equal(t, 0, res.State.NumOpen, "the two hypotheses close the goal the witness left")
}

// TestWitness_UniqueExistenceWrongType pins the refusal: a witness of
// another type does not open an ∃! goal, which stays as it stood.
func TestWitness_UniqueExistenceWrongType(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	A := core.TypeA()
	P := ext.Var("P", core.MakeFun(A, core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(core.TypeBool(), core.TypeBool()))
	b := ext.Var("b", core.TypeBool())
	x := ext.Var("x", A)
	// ∀b:bool. Q(b) ⇒ ∃!x:A. P(x): b is free in the leaf, at the wrong type.
	goalID := s.AddGoal(prop.MakeProp(ext.ForAll(b)(Q.Apply(b).Imply(ext.Unique(x)(P.Apply(x))))))
	leaf := goalID
	for _, step := range []string{"strip_quant", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: leaf, Tactic: TacticReq{Type: step}})
		require.NoError(t, err)
		require.True(t, res.Success, step)
		leaf = res.State.Goals[0].ID
	}

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: leaf, Tactic: TacticReq{Type: "witness", Const: "b"},
	})
	require.True(t, err != nil || !res.Success, "a bool witness must not open ∃!x:A. P(x)")

	after, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: leaf})
	require.NoError(t, err)
	require.Equal(t, 1, after.NumOpen)
	assert.False(t, ext.MatchesUNIQUE(after.Goals[0].Statement.Conclusion()).IsZero(),
		"the refused witness leaves the ∃! goal as it stood")
}

// TestWitness_UniqueExistenceTypesTheWitness pins where the witness
// text takes its type: from the ∃! binder. `λv. v` spells no type of
// its own and is read at the binder's `A → A`.
func TestWitness_UniqueExistenceTypesTheWitness(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	A := core.TypeA()
	fun := core.MakeFun(A, A)
	R := ext.Var("R", core.MakeFun(fun, core.TypeBool()))
	f := ext.Var("f", fun)
	// ∃!f:(A → A). R(f)
	goalID := s.AddGoal(prop.MakeProp(ext.Unique(f)(R.Apply(f))))

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID, Tactic: TacticReq{Type: "witness", Const: "λv. v"},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "the witness text is read at the ∃! binder's type")
	require.Equal(t, 1, res.State.NumOpen)

	v := ext.Var("v", A)
	at, _, isAnd := ext.MatchesAND(res.State.Goals[0].Statement.Conclusion())
	require.True(t, isAnd)
	assert.True(t, at.AlphaEquals(R.Apply(v.To(v)).Core()), "expected R(λv. v), got %s", ext.PrintTerm(at))
}
