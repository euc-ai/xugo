// congruence_test.go — ground congruence closure end-to-end (the
// order-gated same-size Simplifies demodulation; ext/clause/deduce.go):
// a ground equation between two same-size spellings serves as a
// PREMISE — the saturation normalizes every clause to the congruence
// class representative and the complementary literals meet as one atom
// — and the recorded proof replays from its proto.
package refuter

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// TestProveGroundCongruence: Q(m(x,z)), m(x,z) = m(z,x) ⊢ Q(m(z,x)) —
// the motivating shape: a same-size ground
// commutation equation cited as a fact, both spellings in play.
func TestProveGroundCongruence(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeA)
	m := Var("m", MakeFun(TypeA, TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	xz := m.Apply(x, z)
	zx := m.Apply(z, x)
	goal := TestProp(Q.Apply(zx), xz.Eq(zx), Q.Apply(xz))

	prover := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	defer cancel()
	proto := prover.Prove(ctx)
	require.True(t, prover.Refuted(), "the commutation premise must identify the two spellings")

	// The stored proof replays from its proto (the recipes carry the
	// demodulation steps; replay re-derives them search-free): rebuild a
	// refuter from the proto's own goal and reconstruct against it, the
	// way a family blob is verified.
	if proto != nil {
		metas := ext.InitConstMetaMap()
		storedGoal, _ := ext.NewPoolReader(proto.Pool, metas.Load).Prop(proto.Goal)
		require.NotNil(t, storedGoal)
		cache := &clause.CNFNormalizeCache{PreCNF: &clause.PreCNFCache{}}
		replay := CreateRefuterFromPreNormalized(t.Context(), storedGoal, cache)
		require.NotNil(t, replay)
		thm := replay.ReconstructStoredProof(t.Context(), proto, cache, metas.Load)
		assert.False(t, thm.IsZero(), "the recorded congruence refutation must reconstruct")
	}
}

// TestProveGroundCongruenceChain: a same-size equation CHAIN — the
// clauses interreduce to one representative across two links.
func TestProveGroundCongruenceChain(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	g := Var("g", MakeFun(TypeA, TypeA))
	h := Var("h", MakeFun(TypeA, TypeA))
	k := Var("k", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))

	ga, hb, kc := g.Apply(a), h.Apply(b), k.Apply(c)
	goal := TestProp(P.Apply(kc), ga.Eq(hb), hb.Eq(kc), P.Apply(ga))

	prover := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	defer cancel()
	proto := prover.Prove(ctx)
	require.True(t, prover.Refuted(), "the equation chain must normalize both spellings to one atom")

	if proto != nil {
		metas := ext.InitConstMetaMap()
		storedGoal, _ := ext.NewPoolReader(proto.Pool, metas.Load).Prop(proto.Goal)
		require.NotNil(t, storedGoal)
		cache := &clause.CNFNormalizeCache{PreCNF: &clause.PreCNFCache{}}
		replay := CreateRefuterFromPreNormalized(t.Context(), storedGoal, cache)
		require.NotNil(t, replay)
		thm := replay.ReconstructStoredProof(t.Context(), proto, cache, metas.Load)
		assert.False(t, thm.IsZero(), "the recorded chain refutation must reconstruct")
	}
}

// TestReconstructStoredProof_CertificateNotOfTheStoredGoal: a stored
// proof whose certificate refutes a clause its stored goal does not
// give is answered "no theorem" by the reconstruction itself, with no
// panic for the recover to read. The proof is a recorded one with a
// hypothesis the refutation uses taken out of its stored goal.
func TestReconstructStoredProof_CertificateNotOfTheStoredGoal(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	z := Var("z", TypeA)
	m := Var("m", MakeFun(TypeA, TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	xz := m.Apply(x, z)
	zx := m.Apply(z, x)
	goal := TestProp(Q.Apply(zx), xz.Eq(zx), Q.Apply(xz))

	prover := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	defer cancel()
	proto := prover.Prove(ctx)
	require.NotNil(t, proto, "the refutation must be recorded")

	metas := ext.InitConstMetaMap()
	storedGoal, _ := ext.NewPoolReader(proto.Pool, metas.Load).Prop(proto.Goal)
	require.NotNil(t, storedGoal)
	cache := &clause.CNFNormalizeCache{PreCNF: &clause.PreCNFCache{}}
	replay := CreateRefuterFromPreNormalized(t.Context(), storedGoal, cache)
	require.NotNil(t, replay)
	require.False(t, replay.reconstructStoredProof(t.Context(), proto, cache, metas.Load).IsZero(),
		"the proof as recorded must reconstruct")

	require.Len(t, proto.Goal.Hyps, 2)
	for drop := range proto.Goal.Hyps {
		kept := append([]uint32{}, proto.Goal.Hyps[:drop]...)
		kept = append(kept, proto.Goal.Hyps[drop+1:]...)
		stale := &CNFRefuteProofProto{
			Pool: proto.Pool,
			Goal: &ext.HolPropProto{Concl: proto.Goal.Concl, Hyps: kept},
			Root: proto.Root,
		}
		assert.NotPanics(t, func() {
			thm := replay.reconstructStoredProof(t.Context(), stale, cache, metas.Load)
			assert.True(t, thm.IsZero(), "a certificate using the hypothesis taken out (%d) proves nothing of the stored goal", drop)
		})
	}
}

// recordedProof is a refutation as the recorder stores it, the refuter
// its stored goal is replayed against, and what the replay reads.
func recordedProof(t *testing.T) (*CNFRefuteProofProto, *_Refuter, *clause.CNFNormalizeCache, ext.LoadConstMeta) {
	t.Helper()
	x := Var("x", TypeA)
	z := Var("z", TypeA)
	m := Var("m", MakeFun(TypeA, TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	xz := m.Apply(x, z)
	zx := m.Apply(z, x)
	goal := TestProp(Q.Apply(zx), xz.Eq(zx), Q.Apply(xz))

	prover := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	defer cancel()
	proto := prover.Prove(ctx)
	require.NotNil(t, proto, "the refutation must be recorded")

	metas := ext.InitConstMetaMap()
	storedGoal, _ := ext.NewPoolReader(proto.Pool, metas.Load).Prop(proto.Goal)
	require.NotNil(t, storedGoal)
	cache := &clause.CNFNormalizeCache{PreCNF: &clause.PreCNFCache{}}
	replay := CreateRefuterFromPreNormalized(t.Context(), storedGoal, cache)
	require.NotNil(t, replay)
	require.False(t, replay.ReconstructStoredProof(t.Context(), proto, cache, metas.Load).IsZero(),
		"the proof as recorded must reconstruct")
	return proto, replay, cache, metas.Load
}

// TestReconstructStoredProof_AStaleRecipeIsNoTheorem: a recipe that no
// longer runs is how a certificate is stale, and the reading reports it
// by a panic of its own or a failed assertion. Both are answered "no
// theorem": a node with no step, and a root whose recorded hypotheses
// are not the ones its replay leaves.
func TestReconstructStoredProof_AStaleRecipeIsNoTheorem(t *testing.T) {
	defer goleak.VerifyNone(t)
	proto, replay, cache, load := recordedProof(t)

	noStep := &CNFRefuteProofProto{Pool: proto.Pool, Goal: proto.Goal, Root: &RefuteStepProto{Hyps: proto.Root.Hyps}}
	require.PanicsWithValue(t, "Wrong node type.", func() { replay.reconstructStoredProof(t.Context(), noStep, cache, load) })
	require.True(t, replay.ReconstructStoredProof(t.Context(), noStep, cache, load).IsZero())

	require.NotEmpty(t, proto.Root.Hyps, "the fixture's root records its hypotheses")
	otherShape := &CNFRefuteProofProto{Pool: proto.Pool, Goal: proto.Goal,
		Root: &RefuteStepProto{Hyps: proto.Root.Hyps[1:], Replay: proto.Root.Replay, Step: proto.Root.Step}}
	breach := func() (r any) {
		defer func() { r = recover() }()
		replay.reconstructStoredProof(t.Context(), otherShape, cache, load)
		return nil
	}()
	require.True(t, utils.IsAssertionFailure(breach), "the recorded shape is checked by assertion: %v", breach)
	require.True(t, replay.ReconstructStoredProof(t.Context(), otherShape, cache, load).IsZero())
}

// TestReconstructStoredProof_ARuntimeErrorIsRaisedAgain: an error of the
// Go runtime inside the reading reports no certificate, so it is not
// answered "no theorem". The reading is handed no proof at all, which it
// dereferences.
func TestReconstructStoredProof_ARuntimeErrorIsRaisedAgain(t *testing.T) {
	defer goleak.VerifyNone(t)
	_, replay, cache, load := recordedProof(t)

	raised := func() (r any) {
		defer func() { r = recover() }()
		replay.ReconstructStoredProof(t.Context(), nil, cache, load)
		return nil
	}()
	require.NotNil(t, raised, "the nil dereference is raised")
	require.True(t, utils.IsFault(raised) && !utils.IsAssertionFailure(raised), "a runtime error: %v", raised)
}

// TestReconstructStoredProof_ACertificateOfTheRefutersOwnClausesIsReadUnnormalized:
// the refuter built from the proof's own goal has the clauses the
// certificate refutes, so the reading weakens the certificate to them
// and normalizes nothing: the normalization cache it is handed stays
// empty.
func TestReconstructStoredProof_ACertificateOfTheRefutersOwnClausesIsReadUnnormalized(t *testing.T) {
	defer goleak.VerifyNone(t)
	proto, replay, _, load := recordedProof(t)

	fresh := &clause.CNFNormalizeCache{PreCNF: &clause.PreCNFCache{}}
	require.False(t, replay.ReconstructStoredProof(t.Context(), proto, fresh, load).IsZero())
	require.Zero(t, fresh.PreCNF.PropCacheSize(), "no refute prop is normalized for a certificate of the refuter's own clauses")
}

// TestReconstructStoredProof_ACertificateUnderOtherNamesGoesThroughTheKeyForm:
// the same leaf spelled with other free variables has other clauses and
// the same key. Its refuter reads the certificate through the normal
// form the key is computed from, whether or not the key was looked up
// first, and the form the lookup computed is the one the reading uses.
func TestReconstructStoredProof_ACertificateUnderOtherNamesGoesThroughTheKeyForm(t *testing.T) {
	defer goleak.VerifyNone(t)
	proto, recorded, _, load := recordedProof(t)

	u := Var("u", TypeA)
	w := Var("w", TypeA)
	m := Var("m", MakeFun(TypeA, TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	uw := m.Apply(u, w)
	wu := m.Apply(w, u)
	renamed := TestProp(Q.Apply(wu), uw.Eq(wu), Q.Apply(uw))

	for _, lookupFirst := range []bool{false, true} {
		cache := &clause.CNFNormalizeCache{PreCNF: &clause.PreCNFCache{}}
		replay := CreateRefuterFromPreNormalized(t.Context(), renamed, cache)
		require.NotNil(t, replay)
		require.False(t, prop.IsStronger(recorded.CNF().RefuteProp(), replay.CNF().RefuteProp()),
			"the fixture's two spellings have different clauses")
		if lookupFirst {
			key := replay.KeyForm(t.Context(), cache)
			require.Equal(t, recorded.KeyForm(t.Context(), cache).AlphaKey(), key.AlphaKey(),
				"and one key")
		}
		thm := replay.ReconstructStoredProof(t.Context(), proto, cache, load)
		require.False(t, thm.IsZero(), "lookup first %v: the certificate reconstructs for the other spelling", lookupFirst)
		require.True(t, prop.IsStronger(thm, renamed), "and proves that spelling's goal")
	}
}
