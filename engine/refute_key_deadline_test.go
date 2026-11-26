package engine

import (
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// wideRefuteLeaf adds to a fresh session a leaf whose refute is keyed in
// seconds: binders hypotheses ∀x. S(x, aᵢ, aⱼ) and ground hypotheses
// R(aᵢ, aⱼ), concluding c. The key is the normal form of them all in one
// disjunction, nine seconds on an idle machine with 32 and 300
// (prover/proof's wideLeaf is the same leaf, and says where they go).
func wideRefuteLeaf(t *testing.T, e *Engine, binders, ground int) (sid, gid string) {
	t.Helper()
	const pool = 24
	typeA := core.TypeA()
	a := make([]core.Term, pool)
	for i := range a {
		a[i] = ext.Var(core.TermName(fmt.Sprintf("a%d", i)), typeA)
	}
	R := ext.Var("R", core.MakeFun(typeA, typeA, core.TypeBool()))
	S := ext.Var("S", core.MakeFun(typeA, typeA, typeA, core.TypeBool()))
	x := ext.Var("x", typeA)
	var hyps []core.Term
	for i := range binders {
		hyps = append(hyps, ext.ForAll(x)(S.Apply(x, a[i%pool], a[(i/pool)%pool])))
	}
	for j := range ground {
		hyps = append(hyps, R.Apply(a[j%pool], a[(j/pool)%pool]))
	}
	info, err := e.CreateSession(t.Context())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	s.mu.Lock()
	gid = s.AddGoal(prop.MakeProp(ext.Var("c", core.TypeBool()), hyps...))
	s.mu.Unlock()
	return info.ID, gid
}

// TestRefute_TheKeyNormalizationIsCutOffAtTheBudget: the budget of a
// request reaches inside the normalization that keys a refute. On a leaf
// whose key takes nine seconds, a probe of `set_tac`, of `by` over every
// hypothesis and of `auto` each answer unknown(timeout) at the budget,
// naming the normalization, and the engine records no overrun. The `by`
// is spelled raw, the refute its one attempt: a laddered one runs the
// keyless probe ahead of the first rung that computes a key, and on a
// leaf this wide a one-second budget ends there on a loaded machine. A
// normalization that read no clock held the probe some eight seconds
// past its budget, which the engine wrote down as an overrun, and
// answered `fail` for `set_tac` once it had run out.
func TestRefute_TheKeyNormalizationIsCutOffAtTheBudget(t *testing.T) {
	if testing.Short() {
		t.Skip("a nine-second normalization, cut at its budget")
	}
	var overran []*FaultRecord
	overrunObserver = func(record *FaultRecord) { overran = append(overran, record) }
	t.Cleanup(func() { overrunObserver = nil })

	e := newEngine(testEnv())
	// The probes change nothing, so one leaf serves them all: adding it
	// is itself the nine seconds, the session keying its goal.
	sid, gid := wideRefuteLeaf(t, e, 32, 300)
	hyps := make([]ByHypSpec, 332)
	for i := range hyps {
		hyps[i] = ByHypSpec{HypIndex: &i}
	}
	// The leaf's refuter is built in milliseconds, so the budget ends
	// inside the normalization; a unit of it is at most one sort of the
	// disjunction, under a second here, and the slack is for a loaded
	// machine.
	const budget, slack = time.Second, 4 * time.Second
	const inside = "was cut off inside the pre-CNF normalization of the sequent"

	for _, row := range []struct {
		name   string
		tactic TacticReq
		reads  string
	}{
		{"probe of set_tac", TacticReq{Type: "set_tac"}, "set_tac " + inside},
		{"probe of by", TacticReq{Type: "by", ByHyps: hyps, ByShape: &ByShapeReq{Raw: true}}, "close " + inside},
		{"probe of auto", TacticReq{Type: "auto"}, "auto " + inside},
	} {
		t.Run(row.name, func(t *testing.T) {
			var res *ProbeResult
			var err error
			elapsed := answersWithin(t, budget+slack, func() {
				res, err = e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()), Tactic: row.tactic})
			})
			require.NoError(t, err)
			require.Equal(t, ProbeUnknown, res.Outcome, "diagnostic: %s", res.Diagnostic)
			require.Equal(t, ProbeReasonTimeout, res.Reason)
			require.Contains(t, res.Diagnostic, row.reads)
			require.Nil(t, res.EngineFault)
			t.Logf("answered after %v", elapsed)
		})
	}

	assert.Empty(t, overran, "a run ended more than %v past its budget", overrunRecordAfter)
}
