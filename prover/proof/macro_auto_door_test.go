// macro_auto_door_test.go — the auto/AutoExpand door's conditioning
// ladder, pinned on the same in-memory store and fixture as the By
// stage (step_by_ground_test.go) and the raw set_tac door.
//
// The auto door's LIVE rung order is bare-first (see closeAutoLeaf's
// rung-order note: auto's ctx deadline is shared across a whole search
// cascade, and no measured wall is the auto door's), so its
// conditioned path is dormant live until a leaf appears where the bare
// refute fails and conditioning succeeds. What the door GUARANTEES,
// and what these tests pin:
//
//  1. LIVE: bare keeps first claim — the fixture (whose bare refute
//     closes) records NO plan and NO conditioned key: recording
//     behavior is byte-identical to the pre-door loop.
//  2. STRICT REPLAY of a conditioned recording: when the store carries
//     a plan + conditioned certificate for a leaf (recorded by the
//     conditioned path — the By/set_tac doors share the same
//     bare-leaf-keyed plan table), the macro's replay consumes them
//     mechanically: probe MISS → conditioning by plan → certificate
//     hit, zero live search.
//  3. Pre-door rows replay untouched: a certificate recorded by
//     the HISTORICAL loop (pipeline + bare per-leaf refute) still
//     closes at strict replay through rung 1's cache-only probe.
package proof

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestAutoDoor_LiveBareFirstRecordsNoPlan(t *testing.T) {
	goal := groundFixture(t)
	st := newGroundByStore()

	rec := groundTestEnv(t)
	st.wire(rec, true)
	n := CreateGoalStack(goal)
	require.True(t, rec.AutoExpand().Apply(n), "live AutoExpand must close")
	require.True(t, n.Proved())
	require.Empty(t, st.Plans(),
		"bare-first: a leaf the bare refute closes must record no plan")
	require.NotEmpty(t, st.Proofs(), "the bare refutation persisted its certificate")

	// And the recording replays via rung 1 exactly like a pre-door row.
	strict := groundTestEnv(t)
	st.wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, strict.AutoExpand().Apply(n2),
		"strict replay must close from the bare-keyed certificate")
	require.True(t, n2.Proved())
}

func TestAutoDoor_StrictReplayConsumesConditionedRecording(t *testing.T) {
	goal := groundFixture(t)
	st := newGroundByStore()

	// Record through the conditioned path directly (the door's dormant
	// live rung — exercised here so the strict consumption stays
	// pinned; the plan table is door-shared, so a By or raw-set_tac
	// recording of the same leaf produces the same artifacts).
	rec := groundTestEnv(t)
	st.wire(rec, true)
	probe := CreateGoalStack(goal)
	ok, changed := autoConditionedRefute(rec, t.Context(), probe)
	require.True(t, ok, "the conditioned close must succeed on the fixture")
	require.True(t, changed, "grounding (the manual's S4) must have instantiated the wide ∀-hyp")
	require.Len(t, st.Plans(), 1, "the grounding persisted its plan under the bare leaf key")
	require.NotEmpty(t, st.Proofs(), "the conditioned refutation persisted its certificate")

	// Strict replay through the whole macro: probe MISS → conditioned
	// (plan applies, certificate hits) — zero live search.
	strict := groundTestEnv(t)
	st.wire(strict, true)
	strict.RequireCNFCacheHit = true
	n := CreateGoalStack(goal)
	require.True(t, strict.AutoExpand().Apply(n),
		"strict replay must close from the recorded plan + conditioned certificate")
	require.True(t, n.Proved())
}

func TestAutoDoor_BareRecordedRowReplaysUntouched(t *testing.T) {
	goal := groundFixture(t)
	st := newGroundByStore()

	// Record a BARE row: the pre-refute pipeline, then one bare live
	// refute per residual leaf.
	rec := groundTestEnv(t)
	st.wire(rec, true)
	n := CreateGoalStack(goal)
	autoExpandPipeline(n, t.Context())
	for leaf := range n.unsolvedLeavesIter() {
		require.True(t, leaf.runStep(_CNFRefute{env: rec, ctx: t.Context()}),
			"the bare refute closes live (the refuter instantiates the wide ∀ mid-search)")
	}
	require.True(t, n.Proved())
	require.Empty(t, st.Plans(), "a bare close records no plan entry")
	require.NotEmpty(t, st.Proofs(), "the bare refutation persisted its certificate")

	strict := groundTestEnv(t)
	st.wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, strict.AutoExpand().Apply(n2),
		"the laddered macro must replay the bare-keyed certificate via the rung-1 probe")
	require.True(t, n2.Proved())
}
