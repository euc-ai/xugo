// step_by_live_order_test.go — the order a live By runs the ladder's
// rungs in, a session's `by` and a session's resume alike, held as the
// strict replay's is (step_by_replay_order_test.go) by the certificates
// asked of the store: every ask is the key of a leaf's whole refute prop
// computed. A session's new leaf has no row, so an ask before the leaf is
// known to need a certificate is that key paid for a miss. A live By asks
// none for a leaf the keyless probe closes, and the bare leaf's and then
// the conditioned leaf's for a leaf it has to search — the recorder's
// order. What it does not share with a strict replay is the pass over the
// bare probe at a stored plan: a live store holds the plans of spellings
// since abandoned (TestByLadder_ClosesKeylessBeforeTheCache).
package proof

import (
	"testing"

	"github.com/stretchr/testify/require"
)

// liveOn is a live env — the refuter free to search — reading and
// writing st.
func liveOn(t *testing.T, st CNFStore) *ProverEnv {
	t.Helper()
	env := groundTestEnv(t)
	env.ProofService.CNFStore = st
	return env
}

// TestByLive_AKeylessLeafIsAskedNoCertificate: the guarded law with its
// guard resident closes at the apply rung, which the keyless probe runs
// first. The leaf is closed with no key computed and nothing written;
// asked after the bare probe, it would follow a miss at the bare leaf's
// key.
func TestByLive_AKeylessLeafIsAskedNoCertificate(t *testing.T) {
	goal := guardedFixture(t)
	st := &askCountingStore{MemoryCNFStore: NewMemoryCNFStore()}

	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, liveOn(t, st), t.Context(), guardedBySpec(goal)), "the live By closes")
	require.True(t, n.Proved())
	require.Zero(t, st.asked, "the keyless probe closes the leaf before any rung computes a key")
	require.Empty(t, st.Proofs(), "and the close writes no certificate")
	require.Empty(t, st.Plans(), "and no plan")
}

// TestByResume_AKeylessLeafIsAskedNoCertificate: a session's resume runs
// the live ladder with every refute cache-only, on the rows the session
// wrote. A leaf the session closed with no key has none there, and the
// resume closes it as the session did, asking for none.
func TestByResume_AKeylessLeafIsAskedNoCertificate(t *testing.T) {
	goal := guardedFixture(t)
	st := &askCountingStore{MemoryCNFStore: NewMemoryCNFStore()}

	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, liveOn(t, st), CNFCacheOnlyContext(t.Context()), guardedBySpec(goal)),
		"the resume closes the leaf from an empty store")
	require.True(t, n.Proved())
	require.Zero(t, st.asked, "with no certificate asked")
}

// TestByLive_ANewLeafIsAskedItsBareThenItsConditionedCertificate: a leaf
// the refuter has to close, on an empty store. The keyless probe does not
// close it and asks nothing; the bare probe keeps its place ahead of the
// search, and the conditioned rung asks for its own leaf's certificate
// before it searches. Two asks, both misses, and the search writes the
// plan and the conditioned leaf's certificate.
func TestByLive_ANewLeafIsAskedItsBareThenItsConditionedCertificate(t *testing.T) {
	goal := groundFixture(t)
	st := &askCountingStore{MemoryCNFStore: NewMemoryCNFStore()}

	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, liveOn(t, st), t.Context(), groundBySpec(goal)), "the live By closes")
	require.True(t, n.Proved())
	require.Equal(t, 2, st.asked, "the bare leaf's certificate, then the conditioned leaf's")
	require.Equal(t, 2, st.missed, "neither of which a new leaf has")
	require.Len(t, st.Plans(), 1, "the close records its plan")
	require.Len(t, st.Proofs(), 1, "and the conditioned leaf's certificate")
}

// TestByLive_APlannedLeafIsAskedItsBareCertificateFirst: the By run again
// on the rows its first close wrote. A strict replay reads the plan as
// the leaf's recorded close and passes over the bare probe; a live By
// asks the bare leaf's certificate first, as the recorder does, and then
// closes on the plan and the conditioned leaf's, with nothing searched.
func TestByLive_APlannedLeafIsAskedItsBareCertificateFirst(t *testing.T) {
	goal := groundFixture(t)
	recorded := NewMemoryCNFStore()
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, liveOn(t, recorded), t.Context(), groundBySpec(goal)), "the live By closes")
	require.Len(t, recorded.Plans(), 1, "and records one plan")
	require.Len(t, recorded.Proofs(), 1, "and one certificate")

	st := &askCountingStore{MemoryCNFStore: recorded}
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, liveOn(t, st), t.Context(), groundBySpec(goal)), "the By closes again")
	require.True(t, n2.Proved())
	require.Equal(t, 2, st.asked, "the bare leaf's certificate, then the conditioned leaf's")
	require.Equal(t, 1, st.missed, "the second of them the store holds")
	require.Len(t, st.Proofs(), 1, "so nothing is searched and nothing written")
}

// TestByLive_ABareLeafIsAskedItsOwnCertificate: a store holding the bare
// leaf's certificate and no plan. The keyless probe does not close the
// leaf, so the bare probe is asked next and closes on that certificate:
// no search, and no plan recorded over it.
func TestByLive_ABareLeafIsAskedItsOwnCertificate(t *testing.T) {
	goal := groundFixture(t)
	st := &askCountingStore{MemoryCNFStore: recordBare(t, goal)}

	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, liveOn(t, st), t.Context(), groundBySpec(goal)), "the live By closes")
	require.True(t, n.Proved())
	require.Equal(t, 1, st.asked, "one certificate is asked for: the bare leaf's")
	require.Zero(t, st.missed, "and the store holds it")
	require.Empty(t, st.Plans(), "the conditioned rung never ran")
}
