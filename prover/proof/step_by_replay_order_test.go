// step_by_replay_order_test.go — the order a strict replay runs the By
// ladder's rungs in, held by the certificates it asks the store for.
// The store answers a rung under the key of its leaf's whole refute prop
// alone, so every ask is one such key computed — the normal form of the
// leaf, the replay's dominant cost on a wide one — and an ask the store
// does not hold is that cost paid for nothing. A replay asks for the
// certificates the recording wrote and no other: none for a leaf the
// keyless probe closes, the conditioned leaf's alone for a leaf the store
// holds a plan for, and the bare leaf's after that only where the plan's
// rung does not close.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/require"
)

// askCountingStore is a MemoryCNFStore that counts the certificates
// asked of it, and of those the ones it did not hold, and the same for
// the exact keys.
type askCountingStore struct {
	*MemoryCNFStore
	asked, missed           int
	exactAsked, exactMissed int
}

func (s *askCountingStore) ReadExactKey(exact core.PropKey) core.PropKey {
	s.exactAsked++
	key := s.MemoryCNFStore.ReadExactKey(exact)
	if key == "" {
		s.exactMissed++
	}
	return key
}

func (s *askCountingStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	s.asked++
	proof := s.MemoryCNFStore.ReadProof(key)
	if proof == nil {
		s.missed++
	}
	return proof
}

// strictReplayOn is a strict replay env reading st.
func strictReplayOn(t *testing.T, st CNFStore) *ProverEnv {
	t.Helper()
	env := groundTestEnv(t)
	env.ProofService.CNFStore = st
	env.RequireCNFCacheHit = true
	return env
}

// TestByReplay_AKeylessLeafIsAskedNoCertificate: the guarded law with
// its guard resident closes at the apply rung, which the keyless probe
// runs. A strict replay asks that probe first, so the leaf is closed
// with no key computed; asked after the bare probe, it would follow a
// miss at the bare leaf's key.
func TestByReplay_AKeylessLeafIsAskedNoCertificate(t *testing.T) {
	goal := guardedFixture(t)
	st := &askCountingStore{MemoryCNFStore: NewMemoryCNFStore()}

	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, strictReplayOn(t, st), t.Context(), guardedBySpec(goal)),
		"strict replay closes the leaf from an empty store")
	require.True(t, n.Proved())
	require.Zero(t, st.asked, "the keyless probe closes the leaf before any rung computes a key")
}

// TestByReplay_APlannedLeafIsAskedItsConditionedCertificateAlone: the
// recording of the leaf is a plan under its bare key and a certificate
// under the conditioned leaf's. The keyless probe does not close it and
// finds the plan, so the replay goes to the conditioned rung: one
// certificate asked, the one the store holds, and the bare leaf's key
// never computed.
func TestByReplay_APlannedLeafIsAskedItsConditionedCertificateAlone(t *testing.T) {
	goal := groundFixture(t)
	recorded := NewMemoryCNFStore()
	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = recorded
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), groundBySpec(goal)), "the live By closes")
	require.Len(t, recorded.Plans(), 1, "and records one plan")
	require.Len(t, recorded.Proofs(), 1, "and one certificate")

	st := &askCountingStore{MemoryCNFStore: recorded}
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strictReplayOn(t, st), t.Context(), groundBySpec(goal)),
		"strict replay closes on the two rows")
	require.True(t, n2.Proved())
	require.Equal(t, 1, st.asked, "one certificate is asked for: the conditioned leaf's")
	require.Zero(t, st.missed, "and the store holds it")
}

// TestByReplay_ABareLeafIsAskedItsOwnCertificate: a recording made on
// the bare spelling is a certificate under the bare leaf's key and no
// plan. The keyless probe does not close the leaf and finds no plan, so
// the bare probe is asked, and closes on that certificate.
func TestByReplay_ABareLeafIsAskedItsOwnCertificate(t *testing.T) {
	goal := groundFixture(t)
	st := &askCountingStore{MemoryCNFStore: recordBare(t, goal)}

	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, strictReplayOn(t, st), t.Context(), groundBySpec(goal)),
		"strict replay closes on the bare leaf's certificate")
	require.True(t, n.Proved())
	require.Equal(t, 1, st.asked, "one certificate is asked for: the bare leaf's")
	require.Zero(t, st.missed, "and the store holds it")
}

// TestByReplay_APlanWhoseRungDoesNotCloseLeavesTheBareProbeItsTurn: the
// store holds a plan for the leaf, not the certificate of the leaf it
// conditions to, and the bare leaf's certificate. The replay goes to the
// plan's rung first, which misses; the bare probe, passed over for it,
// is asked then and closes.
func TestByReplay_APlanWhoseRungDoesNotCloseLeavesTheBareProbeItsTurn(t *testing.T) {
	goal := groundFixture(t)
	conditioned := NewMemoryCNFStore()
	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = conditioned
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), groundBySpec(goal)), "the live By closes")

	st := &askCountingStore{MemoryCNFStore: recordBare(t, goal)}
	for key, plan := range conditioned.Plans() {
		st.WritePlan(key, plan)
	}
	require.Len(t, st.Plans(), 1, "the plan of the conditioned close")
	require.Len(t, st.Proofs(), 1, "and the bare leaf's certificate alone")

	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strictReplayOn(t, st), t.Context(), groundBySpec(goal)),
		"strict replay closes on the bare leaf's certificate")
	require.True(t, n2.Proved())
	require.Equal(t, 2, st.asked, "the conditioned leaf's certificate, then the bare leaf's")
	require.Equal(t, 1, st.missed, "the first of them the store does not hold")
}

// recordBare is a store holding the certificate a live close of goal on
// its bare spelling writes (Raw: the ladder off), and nothing else.
func recordBare(t *testing.T, goal Prop) *MemoryCNFStore {
	t.Helper()
	st := NewMemoryCNFStore()
	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	spec := groundBySpec(goal)
	spec.Shapes = []ByShape{Raw}
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), spec), "the bare spelling closes live")
	require.Empty(t, st.Plans(), "a bare close records no plan")
	require.Len(t, st.Proofs(), 1, "and one certificate")
	return st
}
