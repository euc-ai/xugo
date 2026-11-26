package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestInspect_StructuralFactsInductionOnListVariable: a goal with a
// free variable of a datatype the env serves an induction principle for
// advertises the induction in inspect's structural facts, under the
// tactic's own wire field. An enumeration reading num_induction alone
// would never list a list-typed variable the tactic accepts (probe
// answers `branch`).
func TestInspect_StructuralFactsInductionOnListVariable(t *testing.T) {
	principle := tactic.ListInductProp()
	env := testEnv()
	env.LibraryThms = map[string]core.Thm{
		"list_induction": core.TestThm(principle.Conclusion(), principle.Hyps()...),
	}
	tmpl, err := tactic.AnalyzeInductionPrinciple(env.LibraryThms["list_induction"])
	require.NoError(t, err)

	l := ext.Var("l", tmpl.IndexType)
	P := ext.Var("P", core.MakeFun(tmpl.IndexType, core.TypeBool()))
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(prop.MakeProp(P.Apply(l).Core()))

	res, err := e.Inspect(ctx, info.ID, &InspectRequest{})
	require.NoError(t, err)
	var consts []string
	for _, f := range res.StructuralFacts {
		if f.Kind == "induction" {
			consts = append(consts, f.Params["const"])
		}
	}
	assert.Contains(t, consts, "l", "induction on the list-typed variable must be advertised under `const`; facts: %+v", res.StructuralFacts)
}

// TestInspect_StructuralFactsInductionAtConcreteElementType: the same,
// with the variable at a CONCRETE element type — `l : list(num)`, which
// is what every goal in a monomorphic chapter carries. The principle's
// index type is `list(A)`, so exact type equality misses the variable
// while the tactic accepts it; the fact must be advertised for an
// INSTANCE of the index type too.
func TestInspect_StructuralFactsInductionAtConcreteElementType(t *testing.T) {
	principle := tactic.ListInductProp()
	env := testEnv()
	env.LibraryThms = map[string]core.Thm{
		"list_induction": core.TestThm(principle.Conclusion(), principle.Hyps()...),
	}
	tmpl, err := tactic.AnalyzeInductionPrinciple(env.LibraryThms["list_induction"])
	require.NoError(t, err)

	// list(num) — the index type list(A) at a concrete element type.
	listOfNum := core.MakeCompositeType(tmpl.IndexType.(core.CompositeType).Meta(), ext.NumType)
	l := ext.Var("l", listOfNum)
	P := ext.Var("P", core.MakeFun(listOfNum, core.TypeBool()))
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(prop.MakeProp(P.Apply(l).Core()))

	res, err := e.Inspect(ctx, info.ID, &InspectRequest{})
	require.NoError(t, err)
	var consts []string
	for _, f := range res.StructuralFacts {
		if f.Kind == "induction" {
			consts = append(consts, f.Params["const"])
		}
	}
	assert.Contains(t, consts, "l",
		"induction on a list(num) variable must be advertised — the principle's index type is list(A); facts: %+v", res.StructuralFacts)
}
