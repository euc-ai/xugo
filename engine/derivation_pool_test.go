package engine

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"
)

// mkClosedReflNode builds a closed goal-stack node proving `v = v` (with
// optional hyps) via Refl — the smallest kernel-verified derivation the
// pool tests can traffic in.
func mkClosedReflNode(t *testing.T, varName string, hyps ...core.Term) *proof.GoalStackNode {
	t.Helper()
	v := ext.Var(core.TermName(varName), core.TypeBool())
	n := proof.CreateGoalStack(prop.MakeProp(core.Eq(v, v), hyps...))
	require.True(t, proof.ApplyRefl(n), "Refl must close %s = %s", varName, varName)
	require.True(t, n.Proved())
	return n
}

// TestDerivationPool_CrossSessionGraft is the happy path: session A closes
// `⊢ y = y`; the close publishes to the engine-global pool; session B —
// which has no closed subtrees of its own — cites the SAME node id and the
// graft lands via the pool, leaving B's residual goal carrying `y = y` as
// a hyp. B then completes, proving the grafted subtree reconstructs
// through B's kernel path (updateUpwards / subGoals.Reconstruct over the
// shared cert).
func TestDerivationPool_CrossSessionGraft(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	// --- Session A: prove ⊢ y = y via refl. ---
	infoA, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sA, err := e.getSession(infoA.ID)
	require.NoError(t, err)

	y := ext.Var("y", core.TypeBool())
	psi := prop.MakeProp(core.Eq(y, y))
	goalIDA := sA.AddGoal(psi)

	resA, err := e.ApplyStep(ctx, infoA.ID, &ApplyStepRequest{
		GoalID: goalIDA,
		Tactic: TacticReq{Type: "refl"},
	})
	require.NoError(t, err)
	require.True(t, resA.Success)
	require.True(t, resA.State.Complete, "session A's section must be fully closed")

	// The close must have published ⊢ y=y to the pool.
	stats := e.DerivationPoolStats()
	require.GreaterOrEqual(t, stats.Published, uint64(1), "close must publish to the pool")
	require.GreaterOrEqual(t, stats.Entries, 1)

	// --- Session B: goal ⊢ x = x; graft ⊢ y = y from the pool. ---
	infoB, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sB, err := e.getSession(infoB.ID)
	require.NoError(t, err)

	x := ext.Var("x", core.TypeBool())
	goalIDB := sB.AddGoal(prop.MakeProp(core.Eq(x, x)))

	// The id session A's inspect would report for the closed node: the
	// section prefix is presentation-only, the hash part is the sequent's
	// canonical AlphaKey prefix.
	nodeID := closedNodeID(0, psi)

	resB, err := e.ApplyStep(ctx, infoB.ID, &ApplyStepRequest{
		GoalID: goalIDB,
		Tactic: TacticReq{Type: "cite-node", NodeID: nodeID},
	})
	require.NoError(t, err)
	require.True(t, resB.Success, "cross-session cite-node must succeed via the pool; diagnostics: %+v", resB.Diagnostics)

	root := sB.sections[0].root
	require.Len(t, root.Children(), 2, "cite-node opens assert's two-child structure")
	assert.True(t, root.Children()[0].Proved(), "grafted first branch must be closed")
	assert.False(t, root.Children()[1].Proved())
	assert.True(t, root.Children()[1].Goal.HasHyp(core.Eq(y, y)),
		"residual goal must carry the grafted conclusion as a hyp")

	poolStats := e.DerivationPoolStats()
	assert.GreaterOrEqual(t, poolStats.Hits, uint64(1), "the graft must be a pool hit")

	// Close the residual and confirm B's section fully reconstructs — the
	// shared cert from A's subtree flows through B's kernel reconstruction.
	require.Len(t, resB.State.Goals, 1)
	resB2, err := e.ApplyStep(ctx, infoB.ID, &ApplyStepRequest{
		GoalID: resB.State.Goals[0].ID,
		Tactic: TacticReq{Type: "refl"},
	})
	require.NoError(t, err)
	require.True(t, resB2.Success)
	require.True(t, resB2.State.Complete, "session B must fully close after the graft")
	require.True(t, root.Proved())
}

// TestDerivationPool_HypGateRejectsPoolHit pins the soundness gate on the
// pool path: a pooled derivation whose sequent carries a hyp NOT present
// in the citing focus must be rejected with the exact same gate as the
// same-session case — never grafted.
func TestDerivationPool_HypGateRejectsPoolHit(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	// Session A: close {p ⊢ y = y} (refl's ⊢ y=y cert is stronger than the
	// hyp-bearing goal, so the node closes with the hyp in its sequent).
	infoA, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sA, err := e.getSession(infoA.ID)
	require.NoError(t, err)

	p := ext.Var("p", core.TypeBool())
	y := ext.Var("y", core.TypeBool())
	psi := prop.MakeProp(core.Eq(y, y), p.Core())
	goalIDA := sA.AddGoal(psi)
	resA, err := e.ApplyStep(ctx, infoA.ID, &ApplyStepRequest{
		GoalID: goalIDA,
		Tactic: TacticReq{Type: "refl"},
	})
	require.NoError(t, err)
	require.True(t, resA.Success)
	require.True(t, resA.State.Complete)

	// Session B: focus ⊢ x = x has NO hyp p — the gate must reject.
	infoB, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sB, err := e.getSession(infoB.ID)
	require.NoError(t, err)

	x := ext.Var("x", core.TypeBool())
	goalIDB := sB.AddGoal(prop.MakeProp(core.Eq(x, x)))

	resB, err := e.ApplyStep(ctx, infoB.ID, &ApplyStepRequest{
		GoalID: goalIDB,
		Tactic: TacticReq{Type: "cite-node", NodeID: closedNodeID(0, psi)},
	})
	require.NoError(t, err)
	require.False(t, resB.Success, "hyp-superset pool entry must NOT graft")
	require.NotEmpty(t, resB.Diagnostics)
	assert.Contains(t, resB.Diagnostics[0].Message, "hyp context",
		"rejection must be the hyp-subset soundness gate")

	// And the focus must be untouched (still one open leaf, no children).
	require.Len(t, sB.sections[0].root.Children(), 0)
}

// TestDerivationPool_RecordingMatchesSameSession is the replay
// self-containment check: the DetailedProofProto recorded for a
// cross-session (pool-resolved) cite-node graft must be identical to the
// one recorded for a same-session cite-node of the same derivation. Since
// the same-session recording is known to be replay-self-contained (the
// cited subtree's ministeps are inlined into the stored assert's first
// branch — no pool, no session state needed at replay), byte-identity
// proves the pool path inherits that property: the pool changed WHERE the
// subtree was found, not what got recorded.
func TestDerivationPool_RecordingMatchesSameSession(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	y := ext.Var("y", core.TypeBool())
	x := ext.Var("x", core.TypeBool())
	psi := prop.MakeProp(core.Eq(y, y))
	target := prop.MakeProp(core.Eq(x, x))
	psiNodeID := closedNodeID(0, psi)

	// closeVia runs `refl` on the (single) open goal of session `id`.
	closeVia := func(id string, goalID string) *StepResult {
		res, err := e.ApplyStep(ctx, id, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "refl"},
		})
		require.NoError(t, err)
		require.True(t, res.Success)
		return res
	}

	// --- Session 1 (baseline, same-session cite): section 0 proves ψ,
	// section 1 proves the target via cite-node (LOCAL hit — the pool is
	// never consulted because lookupClosedNode wins) + refl. ---
	info1, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s1, err := e.getSession(info1.ID)
	require.NoError(t, err)

	closeVia(info1.ID, s1.AddGoal(psi))
	goalID1 := s1.AddGoal(target)
	res1, err := e.ApplyStep(ctx, info1.ID, &ApplyStepRequest{
		GoalID: goalID1,
		Tactic: TacticReq{Type: "cite-node", NodeID: psiNodeID},
	})
	require.NoError(t, err)
	require.True(t, res1.Success)
	require.Len(t, res1.State.Goals, 1)
	closeVia(info1.ID, res1.State.Goals[0].ID)
	require.True(t, s1.sections[1].root.Proved())

	// --- Session 2 (pool path): ONLY the target goal; ψ resolves via the
	// engine-global pool (published by session 1's close). ---
	info2, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s2, err := e.getSession(info2.ID)
	require.NoError(t, err)

	goalID2 := s2.AddGoal(target)
	res2, err := e.ApplyStep(ctx, info2.ID, &ApplyStepRequest{
		GoalID: goalID2,
		Tactic: TacticReq{Type: "cite-node", NodeID: psiNodeID},
	})
	require.NoError(t, err)
	require.True(t, res2.Success, "pool-resolved cite must succeed; diagnostics: %+v", res2.Diagnostics)
	require.Len(t, res2.State.Goals, 1)
	closeVia(info2.ID, res2.State.Goals[0].ID)
	require.True(t, s2.sections[0].root.Proved())

	// --- The recorded step structures must be identical. ---
	proto1 := s1.sections[1].root.DetailedProofProto()
	proto2 := s2.sections[0].root.DetailedProofProto()
	require.NotNil(t, proto1)
	require.NotNil(t, proto2)
	require.True(t, proto.Equal(proto1, proto2),
		"pool-grafted recording must be structurally identical to the same-session recording")

	// Byte-identity under deterministic marshaling — the strongest form of
	// "replay cannot tell the difference".
	m := proto.MarshalOptions{Deterministic: true}
	b1, err := m.Marshal(proto1)
	require.NoError(t, err)
	b2, err := m.Marshal(proto2)
	require.NoError(t, err)
	require.Equal(t, b1, b2, "recorded protos must be byte-identical")
}

// TestDerivationPool_CapEviction: the pool holds at most `cap` entries;
// overflow evicts least-recently-used; an evicted key just misses.
func TestDerivationPool_CapEviction(t *testing.T) {
	pool := NewDerivationPool(8)
	nodes := make([]*proof.GoalStackNode, 20)
	for i := range nodes {
		nodes[i] = mkClosedReflNode(t, fmt.Sprintf("v%d", i))
		require.True(t, pool.Publish(nodes[i], "sessA"))
	}
	stats := pool.Stats()
	assert.Equal(t, 8, stats.Entries)
	assert.Equal(t, uint64(20), stats.Published)
	assert.Equal(t, uint64(12), stats.Evictions)

	// Oldest entries were evicted; the most recent survive.
	assert.Empty(t, pool.CandidatesForNodeID(closedNodeID(0, nodes[0].Goal)),
		"LRU-evicted entry must miss")
	assert.Len(t, pool.CandidatesForNodeID(closedNodeID(3, nodes[19].Goal)), 1,
		"recent entry must hit regardless of the id's section prefix")

	// Duplicate publish dedupes (returns false, entry count unchanged).
	assert.False(t, pool.Publish(nodes[19], "sessB"))
	assert.Equal(t, 8, pool.Stats().Entries)
}

// TestDerivationPool_PublishUnprovedPanics pins the soundness posture:
// publishing an open node is an inconsistency and must panic, not warn.
func TestDerivationPool_PublishUnprovedPanics(t *testing.T) {
	pool := NewDerivationPool(0)
	v := ext.Var("v", core.TypeBool())
	open := proof.CreateGoalStack(prop.MakeProp(core.Eq(v, v)))
	require.Panics(t, func() { pool.Publish(open, "s") })
}

// TestDerivationPool_ConcurrencySmoke hammers Publish / CandidatesForNodeID /
// Stats from parallel goroutines. Run under -race; a small cap keeps the
// eviction path hot.
func TestDerivationPool_ConcurrencySmoke(t *testing.T) {
	pool := NewDerivationPool(32)
	nodes := make([]*proof.GoalStackNode, 64)
	ids := make([]string, len(nodes))
	for i := range nodes {
		nodes[i] = mkClosedReflNode(t, fmt.Sprintf("c%d", i))
		ids[i] = closedNodeID(0, nodes[i].Goal)
	}

	var wg sync.WaitGroup
	for w := 0; w < 8; w++ {
		wg.Add(1)
		go func(w int) {
			defer wg.Done()
			for round := 0; round < 20; round++ {
				for i := range nodes {
					switch (i + w + round) % 3 {
					case 0:
						pool.Publish(nodes[i], fmt.Sprintf("sess%d", w))
					case 1:
						pool.CandidatesForNodeID(ids[i])
					default:
						pool.Stats()
					}
				}
			}
		}(w)
	}
	wg.Wait()

	stats := pool.Stats()
	assert.LessOrEqual(t, stats.Entries, 32)
	assert.Greater(t, stats.Published, uint64(0))
}

// TestDerivationPool_NodeIDParsing pins the id-format tolerance: section
// prefix + closed/open marker are stripped; a bare full key also resolves.
func TestDerivationPool_NodeIDParsing(t *testing.T) {
	pool := NewDerivationPool(0)
	n := mkClosedReflNode(t, "w")
	require.True(t, pool.Publish(n, "s"))

	fullKey := string(n.Goal.AlphaKey())
	short := shortKey(n.Goal)

	for _, id := range []string{
		"s0_c" + short,   // the inspect closed-subtree form
		"s17_c" + short,  // any section index
		"s0_g" + short,   // open-goal form of the same sequent
		short,            // bare short key
		fullKey,          // bare full AlphaKey (programmatic)
		"s2_c" + fullKey, // prefixed full key
	} {
		assert.Len(t, pool.CandidatesForNodeID(id), 1, "id form %q must resolve", id)
	}
	assert.Empty(t, pool.CandidatesForNodeID("s0_c"+strings.Repeat("f", 16)))
	assert.Empty(t, pool.CandidatesForNodeID(""))

	// Nil pool is a safe no-op on every method.
	var nilPool *DerivationPool
	assert.Empty(t, nilPool.CandidatesForNodeID("s0_c"+short))
	assert.False(t, nilPool.Publish(n, "s"))
	assert.Zero(t, nilPool.Stats().Entries)
}
