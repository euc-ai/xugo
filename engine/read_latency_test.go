package engine

import (
	"context"
	"os"
	"os/exec"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils/wallclock"
	"github.com/stretchr/testify/require"
)

// readLatencyBudget bounds the first and repeated calls after production
// engine startup. Each run uses a fresh process, so earlier tests cannot
// precompute the corpus keys or warm a request's caches.
const readLatencyBudget = 100 * time.Millisecond

// TestReadLatency_AgentPrimitives checks inspect, probe and retrieve after
// startup in a fresh process. Corpus statement preparation is outside the
// request budget, as it is for the server; the readings walk may overlap it.
func TestReadLatency_AgentPrimitives(t *testing.T) {
	wallclock.SkipOnSlowMachine(t)
	if os.Getenv("XUGO_TEST_READ_LATENCY_CHILD") == "" {
		cmd := exec.CommandContext(t.Context(), os.Args[0], "-test.run=^TestReadLatency_AgentPrimitives$", "-test.v", "-test.timeout=1m")
		cmd.Env = append(os.Environ(), "XUGO_TEST_READ_LATENCY_CHILD=1")
		out, err := cmd.CombinedOutput()
		t.Logf("%s", out)
		require.NoError(t, err, "read latency in a fresh process")
		return
	}
	env := testEnv()
	e := NewEngine(env)
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Pick a fixture goal that the agent would plausibly inspect. We use
	// one that touches both a custom const (`F`) and a tautology shape so
	// the structural-fact enumerator and the const-driven retrieve groups
	// both have something to do.
	x := ext.Var("x", TypeInd)
	metaF := core.MakeConstMeta("F", core.MakeFun(TypeInd, core.TypeBool()))
	F := ext.Const(metaF, core.MakeFun(TypeInd, core.TypeBool()))
	goalProp := prop.MakeProp(ext.ForAll(x)(F.Apply(x).Imply(F.Apply(x))))
	goalID := s.AddGoal(goalProp)

	s.rebuildGoalIndex()
	for k := range s.goalIndex {
		goalID = k
	}

	// --- inspect ---
	timeBudget(t, "inspect cold", func() {
		_, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
		require.NoError(t, err)
	})
	timeBudget(t, "inspect warm", func() {
		_, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: goalID})
		require.NoError(t, err)
	})

	// --- probe(auto) ---
	timeBudget(t, "probe(auto)", func() {
		_, err := e.Probe(ctx, info.ID, &ProbeRequest{
			GoalID:   goalID,
			Tactic:   TacticReq{Type: "auto"},
			BudgetMs: 200,
		})
		require.NoError(t, err)
	})

	// --- probe(structural) — strip_quant on a ∀-headed goal ---
	timeBudget(t, "probe(strip_quant)", func() {
		_, err := e.Probe(ctx, info.ID, &ProbeRequest{
			GoalID:   goalID,
			Tactic:   TacticReq{Type: "strip_quant"},
			BudgetMs: 200,
		})
		require.NoError(t, err)
	})

	// --- retrieve(goal) cold + warm ---
	timeBudget(t, "retrieve(goal) cold", func() {
		_, err := e.Retrieve(ctx, info.ID, &RetrieveRequest{
			Mode: RetrieveByGoal, GoalID: goalID, BudgetMs: 1000,
		})
		require.NoError(t, err)
	})
	timeBudget(t, "retrieve(goal) warm", func() {
		_, err := e.Retrieve(ctx, info.ID, &RetrieveRequest{
			Mode: RetrieveByGoal, GoalID: goalID, BudgetMs: 1000,
		})
		require.NoError(t, err)
	})

	// --- retrieve(consts) ---
	timeBudget(t, "retrieve(consts)", func() {
		_, err := e.Retrieve(ctx, info.ID, &RetrieveRequest{
			Mode: RetrieveByConsts, Consts: []string{"F"}, MaxPerGroup: 10,
		})
		require.NoError(t, err)
	})

	// --- retrieve(name_pattern), cold then warm ---
	timeBudget(t, "retrieve(name_pattern)", func() {
		_, err := e.Retrieve(ctx, info.ID, &RetrieveRequest{
			Mode: RetrieveByName, NamePattern: "Assoc", MaxPerGroup: 10,
		})
		require.NoError(t, err)
	})
	timeBudget(t, "retrieve(name_pattern) warm", func() {
		_, err := e.Retrieve(ctx, info.ID, &RetrieveRequest{
			Mode: RetrieveByName, NamePattern: "Assoc", MaxPerGroup: 10,
		})
		require.NoError(t, err)
	})
}

// timeBudget runs fn and fails the test if it takes longer than
// readLatencyBudget. Uses t.Helper so the failure points at the caller.
func timeBudget(t *testing.T, label string, fn func()) {
	t.Helper()
	start := time.Now()
	fn()
	elapsed := time.Since(start)
	if elapsed > readLatencyBudget {
		t.Errorf("%s took %v, exceeds budget %v", label, elapsed, readLatencyBudget)
	} else {
		t.Logf("%s: %v", label, elapsed)
	}
}
