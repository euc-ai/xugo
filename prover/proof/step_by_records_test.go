// step_by_records_test.go — BySpec.Records: the rows the recorder would
// write for a close, reported to the session `by`/`probe` as it closes,
// not after a blob is written.
//
//  1. REFUTE + GROUNDING: a leaf the conditioned rung closes by a live
//     refute over a grounding plan reports the certificate key the store
//     received AND the plan key the stage persisted (groundFixture).
//  2. KEYLESS PRELUDE: a leaf the CNF closer's prelude finishes mints no
//     key, so Records reports nothing (commutedConjByGoal).
//  3. KEYLESS APPLY RUNG: a leaf the apply rung closes never reaches the
//     refuter, so Records reports nothing (a resident-premise `exact h`).
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// recordsSpec adds a Records sink to a BySpec, collecting the reported
// keys and plans into the returned pointers.
func recordsSpec(base BySpec, keys, plans *[]core.PropKey) BySpec {
	base.Records = func(k, p []core.PropKey) { *keys, *plans = k, p }
	return base
}

func TestByRecords_RefuteAndPlanAreReported(t *testing.T) {
	goal := groundFixture(t)
	st := NewMemoryCNFStore()
	env := groundTestEnv(t)
	env.ProofService.CNFStore = st

	var keys, plans []core.PropKey
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), recordsSpec(groundBySpec(goal), &keys, &plans)))
	require.True(t, n.Proved())

	// The reported certificate keys are exactly the store's written ones,
	// and the reported plan keys exactly its plan table — the report is
	// the recorder's rows, read off the same close.
	assert.Equal(t, keysOf(st.Proofs()), keysOf(keySlice(keys)), "reported keys ≠ the store's certificates")
	assert.Equal(t, keysOf(st.Plans()), keysOf(keySlice(plans)), "reported plans ≠ the store's plan rows")
	require.NotEmpty(t, keys, "the conditioned refute wrote a certificate — report it")
	require.Len(t, plans, 1, "the grounding stage persisted one plan — report it")
}

func TestByRecords_PreludeCloseReportsNothing(t *testing.T) {
	goal := commutedConjByGoal()
	env := groundTestEnv(t)
	env.ProofService.CNFStore = NewMemoryCNFStore()

	var keys, plans []core.PropKey
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), recordsSpec(residentSpec(goal), &keys, &plans)))
	require.True(t, n.Proved())
	assert.Empty(t, keys, "the prelude close mints no key")
	assert.Empty(t, plans, "the prelude close persists no plan")
}

func TestByRecords_ApplyRungCloseReportsNothing(t *testing.T) {
	// `b(a) ⊢ b(a)` — the conclusion IS a resident hyp, so the apply
	// rung closes it by `exact h`, keyless, before any refuter.
	b := ext.Var("b", core.MakeFun(TypeInd, core.TypeBool()))
	a := ext.Var("a", TypeInd)
	goal := prop.MakeProp(b.Apply(a).Core(), b.Apply(a).Core())
	env := groundTestEnv(t)
	env.ProofService.CNFStore = NewMemoryCNFStore()

	var keys, plans []core.PropKey
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), recordsSpec(residentSpec(goal), &keys, &plans)))
	require.True(t, n.Proved())
	assert.Empty(t, keys, "the apply rung reaches no refuter — no key")
	assert.Empty(t, plans, "the apply rung grounds nothing to persist")
}

// TestByRecords_StoredPlanIsReported: a grounding plan the conditioning
// stage applies from the store, rather than finds, is still a row of the
// close — the recording reads it or, from a blob without it, writes it.
// The second close of one leaf on one store reads the plan the first
// persisted, and reports it as the first did.
func TestByRecords_StoredPlanIsReported(t *testing.T) {
	goal := groundFixture(t)
	st := NewMemoryCNFStore()
	env := groundTestEnv(t)
	env.ProofService.CNFStore = st

	var keys, plans []core.PropKey
	first := CreateGoalStack(goal)
	require.True(t, ApplyByStep(first, env, t.Context(), recordsSpec(groundBySpec(goal), &keys, &plans)))
	require.Len(t, plans, 1, "the first close persists its grounding plan")
	persisted := plans

	keys, plans = nil, nil
	second := CreateGoalStack(goal)
	require.True(t, ApplyByStep(second, env, t.Context(), recordsSpec(groundBySpec(goal), &keys, &plans)))
	require.True(t, second.Proved())
	assert.Equal(t, keysOf(keySlice(persisted)), keysOf(keySlice(plans)),
		"the plan the stage applied from the store is a row of this close — report it")
	assert.NotEmpty(t, keys, "the conditioned refute read its certificate — report it")
}

// TestByRecords_SessionAndRecorderAgreeOnOneSpelling is sighting 6's
// negative control: the SAME premise list on the SAME leaf records the
// SAME rows whether the env is a plain live one (the session's `by`) or
// the recorder's (ByAuditReport wired, as record_cnf_test.go sets it).
// The By executor is one code path (fact.go: "executed by exactly the
// code that will replay it"), so a session close and the recorder's run
// of the SAME spelling never diverge — the sighted session-vs-recorder
// discrepancies are the SPELLING differing (the member's Go premise list
// vs the session transcript's), not the surface. Where they differ, the
// dry run — which runs the member's Go — is the keylessness oracle.
func TestByRecords_SessionAndRecorderAgreeOnOneSpelling(t *testing.T) {
	goal := groundFixture(t)

	sessionStore := NewMemoryCNFStore()
	sessionEnv := groundTestEnv(t)
	sessionEnv.ProofService.CNFStore = sessionStore
	var sKeys, sPlans []core.PropKey
	ns := CreateGoalStack(goal)
	require.True(t, ApplyByStep(ns, sessionEnv, t.Context(), recordsSpec(groundBySpec(goal), &sKeys, &sPlans)))

	recorderStore := NewMemoryCNFStore()
	recorderEnv := groundTestEnv(t)
	recorderEnv.ProofService.CNFStore = recorderStore
	recorderEnv.ByAuditReport = func(string) {} // the recorder harness's one wirer
	var rKeys, rPlans []core.PropKey
	nr := CreateGoalStack(goal)
	require.True(t, ApplyByStep(nr, recorderEnv, t.Context(), recordsSpec(groundBySpec(goal), &rKeys, &rPlans)))

	assert.Equal(t, keysOf(keySlice(sKeys)), keysOf(keySlice(rKeys)), "same spelling, same leaf: the certificate keys must agree across surfaces")
	assert.Equal(t, keysOf(keySlice(sPlans)), keysOf(keySlice(rPlans)), "same spelling, same leaf: the plan keys must agree across surfaces")
	assert.Equal(t, keysOf(sessionStore.Proofs()), keysOf(recorderStore.Proofs()), "the stores agree on certificates too")
	assert.Equal(t, keysOf(sessionStore.Plans()), keysOf(recorderStore.Plans()), "the stores agree on plans too")
}

// keySlice turns a []PropKey into a set keyed by the key, so keysOf can
// sort both the store's maps and the reported slices the same way.
func keySlice(keys []core.PropKey) map[core.PropKey]struct{} {
	out := make(map[core.PropKey]struct{}, len(keys))
	for _, k := range keys {
		out[k] = struct{}{}
	}
	return out
}
