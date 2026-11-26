// step_exact_key_test.go — the exact-key table of the CNF store: the
// row a live refute writes with its certificate, the lookup that asks
// it before a certificate's key is computed, and the strict ladder's
// pass over its two certificate rungs on exact keys alone. What a
// lookup spares is the normal form of the leaf's whole refute prop, so
// the tests read the env's normalization cache, which holds one prop
// per refute prop a lookup normalized, beside the rows the store was
// asked for.
package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/require"
)

// twoConclusionsFixture is groundChainFixture with a second conclusion:
//
//	zk(a) = g(a),  g(a) = h(a),  h(a) = k(a)  ⊢  zk(a) = k(a) ∧ g(a) = k(a)
//
// The conditioned rung splits the conjunction and closes each conjunct
// by a refutation of its own, so its recording is two certificates, each
// with the exact key of its own leaf, and none under the bare leaf's.
func twoConclusionsFixture(t *testing.T) Prop {
	t.Helper()
	indFun := core.MakeFun(TypeInd, TypeInd)
	g, h, k := ext.Var("g", indFun), ext.Var("h", indFun), ext.Var("k", indFun)
	a := ext.Var("a", TypeInd)
	zk := ext.WrapTerm(zkConst)
	return prop.MakeProp(zk.Apply(a).Eq(k.Apply(a)).And(g.Apply(a).Eq(k.Apply(a))).Core(),
		zk.Apply(a).Eq(g.Apply(a)).Core(), g.Apply(a).Eq(h.Apply(a)).Core(), h.Apply(a).Eq(k.Apply(a)).Core())
}

// recordLive is the store a live close of goal by its resident premises
// leaves.
func recordLive(t *testing.T, goal Prop) *MemoryCNFStore {
	t.Helper()
	st := NewMemoryCNFStore()
	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), groundBySpec(goal)), "the live By closes")
	return st
}

// normalized is the number of refute props env's lookups normalized.
func normalized(env *ProverEnv) int { return env.cnfNormalizeCache().PreCNF.PropCacheSize() }

// TestExactKey_ALiveRefuteWritesTheRowWithItsCertificate: the row names
// the certificate the refute stored, by the key of the refute prop the
// stored goal's cold CNF gives — which is what lets rekey_cnf_blob
// rebuild the table from the certificates alone.
func TestExactKey_ALiveRefuteWritesTheRowWithItsCertificate(t *testing.T) {
	goal := groundChainFixture(t)
	st := recordBare(t, goal)
	rows := st.ExactKeys()
	require.Len(t, rows, 1, "one row for the one certificate")
	env := groundTestEnv(t)
	for exact, key := range rows {
		proof := st.Proofs()[key]
		require.NotNil(t, proof, "the row names the stored certificate")
		stored, _ := ext.NewPoolReader(proof.Pool, env.ProofService.LoadConstMeta).Prop(proof.Goal)
		require.NotNil(t, stored)
		cold := refuter.CreateRefuterFromPreNormalized(t.Context(), stored, NewCNFNormalizeCache())
		require.NotNil(t, cold)
		require.Equal(t, cold.CNF().RefuteProp().AlphaKey(), exact,
			"the row's key is the key of the stored goal's cold refute prop")
	}
}

// TestExactKey_AReplayReadsItsCertificateWithNoNormalForm: a strict
// replay of the recorded leaf asks the exact key, is told the
// certificate, and closes on it with no refute prop normalized. The same
// certificates in a store with no row are found by their key, which
// costs the normal form.
func TestExactKey_AReplayReadsItsCertificateWithNoNormalForm(t *testing.T) {
	goal := groundChainFixture(t)
	recorded := recordBare(t, goal)

	st := &askCountingStore{MemoryCNFStore: recorded}
	env := strictReplayOn(t, st)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), groundBySpec(goal)), "strict replay closes on the row")
	require.True(t, n.Proved())
	require.Equal(t, 1, st.asked, "one certificate is read")
	require.Zero(t, st.missed)
	require.Zero(t, normalized(env), "and no refute prop is normalized for it")

	rowless := &askCountingStore{MemoryCNFStore: copyOfStore(recorded)}
	require.Empty(t, rowless.ExactKeys(), "the fixture: the certificates with no exact key")
	env = strictReplayOn(t, rowless)
	n = CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), groundBySpec(goal)), "strict replay closes by the certificate's key")
	require.True(t, n.Proved())
	require.Equal(t, 1, rowless.asked)
	require.Zero(t, rowless.missed)
	require.Positive(t, normalized(env), "which is the key of a normal form")
}

// TestExactKey_ARowWhoseCertificateIsGoneIsNoAnswer: the table is an
// index of the certificates, and a row that names none decides nothing:
// the lookup goes on to the certificate's key.
func TestExactKey_ARowWhoseCertificateIsGoneIsNoAnswer(t *testing.T) {
	goal := groundChainFixture(t)
	recorded := recordBare(t, goal)
	stale := copyOfStore(recorded)
	for exact := range recorded.ExactKeys() {
		stale.WriteExactKey(exact, "prop_no_such_certificate")
	}

	st := &askCountingStore{MemoryCNFStore: stale}
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, strictReplayOn(t, st), t.Context(), groundBySpec(goal)),
		"strict replay closes by the certificate's key")
	require.True(t, n.Proved())
	require.Positive(t, st.missed, "the certificate the stale row names is asked for and not held")
	require.Greater(t, st.asked, st.missed, "and the certificate under its key is read")
}

// TestExactKey_ARungOnExactKeysAloneEndsBeforeTheNormalForm: under the
// exact pass's mark a leaf with no row fails its rung with the mark's
// own refusal, and nothing is normalized for it.
func TestExactKey_ARungOnExactKeysAloneEndsBeforeTheNormalForm(t *testing.T) {
	goal := groundChainFixture(t)
	env := strictReplayOn(t, NewMemoryCNFStore())
	refusal := func() (text string) {
		defer func() { text = fmt.Sprint(recover()) }()
		env.tryCNFRefute(withExactKeysOnly(t.Context()), goal)
		return ""
	}()
	require.Contains(t, refusal, "tryCNFRefute[exactKeysOnly]")
	require.Zero(t, normalized(env))
}

// TestByReplay_TheExactPassClosesWhereTheBareKeyMisses: the recording
// closed at the conditioned rung, two certificates for the two
// conjuncts, and holds nothing for the bare leaf. A strict replay's
// exact pass asks the bare leaf's exact key, which has no row, then the
// two conjuncts', and closes with no refute prop normalized. Without
// the rows the ladder runs on the keys: the bare leaf's is computed and
// missed before the conditioned rung reads its two certificates.
func TestByReplay_TheExactPassClosesWhereTheBareKeyMisses(t *testing.T) {
	goal := twoConclusionsFixture(t)
	recorded := recordLive(t, goal)
	require.Len(t, recorded.Proofs(), 2, "a certificate for each conjunct")
	require.Len(t, recorded.ExactKeys(), 2, "each with its row")
	require.Empty(t, recorded.Plans(), "and no plan: nothing was grounded")

	st := &askCountingStore{MemoryCNFStore: recorded}
	env := strictReplayOn(t, st)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), groundBySpec(goal)), "strict replay closes in the exact pass")
	require.True(t, n.Proved())
	require.Equal(t, 2, st.asked, "the two conjuncts' certificates")
	require.Zero(t, st.missed)
	require.Equal(t, 1, st.exactMissed, "the bare leaf has no row")
	require.Zero(t, normalized(env), "and its key is never computed")

	rowless := &askCountingStore{MemoryCNFStore: copyOfStore(recorded)}
	env = strictReplayOn(t, rowless)
	n = CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), groundBySpec(goal)), "strict replay closes on the keys")
	require.True(t, n.Proved())
	require.Equal(t, 3, rowless.asked, "the bare leaf's certificate, then the two conjuncts'")
	require.Equal(t, 1, rowless.missed, "the first of them the store does not hold")
	require.Positive(t, normalized(env))
}
