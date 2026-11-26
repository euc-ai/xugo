// step_settac_door_test.go — the raw set_tac door's conditioning
// ladder, pinned on the same in-memory store and fixture as the
// By stage's own contract (step_by_ground_test.go):
//
//  1. RECORD: a live raw set_tac whose leaf needs grounding conditions
//     on rung 2 (grounding searches — the manual's S4), closes, and
//     persists BOTH artifacts —
//     the certificate under the CONDITIONED key, the plan entry under
//     the BARE leaf key.
//  2. STRICT REPLAY: with only those artifacts installed and
//     RequireCNFCacheHit armed, the same raw set_tac closes — the plan
//     applies mechanically (zero search) and the certificate hits.
//  3. THE PLAN IS LOAD-BEARING: strict replay without the plan panics
//     on the certificate MISS.
//  4. Pre-door rows replay untouched: a certificate recorded on
//     the BARE driver (how every row recorded before this door existed
//     was keyed) still closes at strict replay via rung 1's probe —
//     no plan entry, no conditioning, no re-record.
package proof

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// setTacDoorApply runs the raw door exactly as live dispatch and
// emitted text do (ApplySetTacMode → runStep → the laddered apply),
// with the standard vocabulary in membership mode.
func setTacDoorApply(n *GoalStackNode, env *ProverEnv) bool {
	names := make([]core.TermName, 0)
	for _, c := range StandardSetVocabulary() {
		names = append(names, core.TermName(c))
	}
	return ApplySetTacMode(n, env, context.Background(), names, SetTacMode_SET_TAC_MEMBERSHIP, nil)
}

func TestSetTacDoor_RecordThenStrictReplay(t *testing.T) {
	goal := groundFixture(t)
	st := newGroundByStore()

	// 1. RECORD — live run, empty store: rung 1's cache-only probe
	// misses, rung 2 conditions (S4 searches), the driver's refute
	// closes live on the conditioned leaf.
	rec := groundTestEnv(t)
	st.wire(rec, true)
	n := CreateGoalStack(goal)
	require.True(t, setTacDoorApply(n, rec), "live raw set_tac must close")
	require.True(t, n.Proved())

	require.Len(t, st.Plans(), 1, "exactly one plan entry (one working leaf)")
	require.NotEmpty(t, st.Proofs(), "the conditioned refutation must persist a certificate")
	var bareKey core.PropKey
	var entry *ByConditionPlanProto
	for k, p := range st.Plans() {
		bareKey, entry = k, p
	}
	require.NotEmpty(t, entry.Groundings, "the plan carries the e-match groundings")
	require.NotEmpty(t, entry.Replaced, "every binder was match-pinned — the wide source is replaced")
	require.NotEqual(t, string(bareKey), entry.ConditionedGoalKey,
		"conditioning must move the leaf off its bare key")
	require.Equal(t, string(planKey(goal)), string(bareKey),
		"the raw door's bare key is the sequent as the step received it")

	// 2. STRICT REPLAY — certificates + plans installed, no live search.
	strict := groundTestEnv(t)
	st.wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, setTacDoorApply(n2, strict),
		"strict replay must close from the recorded plan + certificate")
	require.True(t, n2.Proved())

	// 3. THE PLAN IS LOAD-BEARING — certificates alone cannot reproduce
	// the conditioned key.
	noPlan := groundTestEnv(t)
	st.wire(noPlan, false)
	noPlan.RequireCNFCacheHit = true
	n3 := CreateGoalStack(goal)
	func() {
		defer func() {
			r := recover()
			require.NotNil(t, r, "strict replay without the plan must fail loudly")
			assert.Contains(t, strings.ToLower(anyToString(r)), "cnf cache miss",
				"the failure is the certificate MISS, surfaced by the strict gate")
		}()
		setTacDoorApply(n3, noPlan)
	}()
}

// TestSetTacDoor_BareRecordedRowReplaysUntouched is the replay guarantee
// for the raw door: every set_tac proto recorded before this door existed
// keyed its refutes on the BARE driver's leaves. Such a row must keep
// closing at strict replay through rung 1's probe — no plan entry, no
// conditioning, no re-record.
func TestSetTacDoor_BareRecordedRowReplaysUntouched(t *testing.T) {
	goal := groundFixture(t)
	st := newGroundByStore()

	// Record the way the pre-door engine did: the bare driver, single
	// attempt (the bare flag is exactly that code path).
	rec := groundTestEnv(t)
	st.wire(rec, true)
	names := make([]core.TermName, 0)
	for _, c := range StandardSetVocabulary() {
		names = append(names, core.TermName(c))
	}
	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_SetTacStep{env: rec, ctx: t.Context(), consts: names,
		mode: SetTacMode_SET_TAC_MEMBERSHIP, bare: true}),
		"the bare driver closes live (the refuter instantiates the wide ∀ mid-search)")
	require.Empty(t, st.Plans(), "a bare close records no plan entry")
	require.NotEmpty(t, st.Proofs(), "the bare refutation persisted its certificate")

	strict := groundTestEnv(t)
	st.wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, setTacDoorApply(n2, strict),
		"the laddered door must replay the bare-keyed certificate via the rung-1 probe")
	require.True(t, n2.Proved())
}
