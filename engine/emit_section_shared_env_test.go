package engine

// emit-section's CNF collection runs on an env of its own
// (proof.ProverEnv.CNFCaptureEnv). The engine's env is the one every
// session of a serve shares, so these tests hold a collection inside a
// store read and look at that env from outside: its mode flags and its
// store are as the sessions left them, and a session refuting live
// beside two held collections still reaches its live refuter.

import (
	"context"
	"sync/atomic"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// _BlockingCNFStore is a CNF store whose certificate reads, once armed,
// hold at a key the store has until the test releases them, announcing
// each held read on entered. A read at a key the store lacks — a fresh
// goal's — passes through, so a live refute beside a held collection
// runs to its write.
type _BlockingCNFStore struct {
	proof.CNFStore
	armed   atomic.Bool
	entered chan struct{}
	release chan struct{}
}

func newBlockingCNFStore() *_BlockingCNFStore {
	return &_BlockingCNFStore{
		CNFStore: proof.NewMemoryCNFStore(),
		entered:  make(chan struct{}, 64),
		release:  make(chan struct{}),
	}
}

func (s *_BlockingCNFStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	held := s.CNFStore.ReadProof(key)
	if s.armed.Load() && held != nil {
		select {
		case <-s.release:
		default:
			s.entered <- struct{}{}
			<-s.release
		}
	}
	return held
}

// resolutionGoal is ∀x. P(x) ⇒ Q(x), P(a) ⊢ Q(a): the instance x := a is
// the refuter's to find, so a Raw `by` on it is a resolution refute that
// writes a certificate.
func resolutionGoal() core.Prop {
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(TypeInd, core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(TypeInd, core.TypeBool())))
	a := ext.Var("a", TypeInd)
	x := ext.WrapTerm(ext.Var("x", TypeInd))
	return prop.MakeProp(Q.Apply(a).Core(),
		ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x))).Core(), P.Apply(a).Core())
}

// wideResolutionGoal is ∀x. P(x) ∧ R(x) ⇒ Q(x), P(b), R(b) ⊢ Q(b): a
// resolution refute like resolutionGoal's over a different clause set,
// so its certificate key is one no other goal of these tests writes.
func wideResolutionGoal() core.Prop {
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(TypeInd, core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(TypeInd, core.TypeBool())))
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(TypeInd, core.TypeBool())))
	b := ext.Var("b", TypeInd)
	x := ext.WrapTerm(ext.Var("x", TypeInd))
	return prop.MakeProp(Q.Apply(b).Core(),
		ext.ForAll(x)(P.Apply(x).And(R.Apply(x)).Imply(Q.Apply(x))).Core(),
		P.Apply(b).Core(), R.Apply(b).Core())
}

// byRawSession opens a session on goal's closed statement, strips its
// premises and closes the goal they leave with a Raw `by` over every
// hypothesis — the bare refute — returning the session id.
func byRawSession(t *testing.T, e *Engine, goal core.Prop) string {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	goalID := addStrippedGoal(t, e, info.ID, goal)
	hyps := make([]ByHypSpec, goal.NumHyps())
	for i := range hyps {
		idx := i
		hyps[i] = ByHypSpec{HypIndex: &idx}
	}
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "by", ByHyps: hyps, ByShape: &ByShapeReq{Raw: true}},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "the Raw by must close the goal; diagnostics: %v", res.Diagnostics)
	require.True(t, s.sections[0].root.Proved())
	return info.ID
}

func emitHeld(e *Engine, sid string) <-chan error {
	done := make(chan error, 1)
	go func() {
		_, err := e.EmitSection(&EmitSectionRequest{
			SessionID: sid, Section: 0, FuncName: "Build_Held", Family: "real/real_field",
		})
		done <- err
	}()
	return done
}

// TestEmitSection_CollectionLeavesSharedEnvUntouched holds one
// collection inside its certificate read and reads the engine's env
// from outside: not strict, not capture-only, and its store is the one
// the sessions write to.
func TestEmitSection_CollectionLeavesSharedEnvUntouched(t *testing.T) {
	store := newBlockingCNFStore()
	env := testEnv()
	env.ProofService.CNFStore = store
	e := newEngine(env)
	sid := byRawSession(t, e, resolutionGoal())
	require.Equal(t, 1, store.CNFStore.(*proof.MemoryCNFStore).Len(), "the live close wrote its certificate")

	store.armed.Store(true)
	done := emitHeld(e, sid)
	<-store.entered

	assert.False(t, env.RequireCNFCacheHit, "the collection's strictness is the collection's env's, not the engine's")
	assert.False(t, env.CNFCacheCaptureOnly, "the collection's capture-only mode is the collection's env's, not the engine's")
	assert.Same(t, store, env.ProofService.CNFStore, "the engine's store is the one the sessions write to, not the collection's capture")

	close(store.release)
	require.NoError(t, <-done)
}

// TestEmitSection_ConcurrentCollectionsLeaveLiveRefuteLive holds two
// sessions' collections inside their certificate reads while a third
// session closes a goal no certificate covers: its `by` reaches the live
// refuter, and both collections then complete.
func TestEmitSection_ConcurrentCollectionsLeaveLiveRefuteLive(t *testing.T) {
	store := newBlockingCNFStore()
	env := testEnv()
	env.ProofService.CNFStore = store
	e := newEngine(env)
	first := byRawSession(t, e, resolutionGoal())
	second := byRawSession(t, e, resolutionGoal())

	store.armed.Store(true)
	firstDone := emitHeld(e, first)
	secondDone := emitHeld(e, second)
	<-store.entered
	<-store.entered

	byRawSession(t, e, wideResolutionGoal())

	close(store.release)
	require.NoError(t, <-firstDone)
	require.NoError(t, <-secondDone)
}
