// refute_key_deadline_test.go — the key of a refute is the normal form of
// the whole refute prop, and on a wide leaf that normalization is the
// longest unit of the refute. The request's context reaches inside it
// (tryCNFRefute), and a By reports the cut as its own cut-off.
package proof

import (
	"context"
	"fmt"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/euc-ai/xugo/utils"
)

// wideLeaf is a leaf whose refute is keyed in seconds and built in
// milliseconds: binders hypotheses ∀x. S(x, aᵢ, aⱼ) and ground
// hypotheses R(aᵢ, aⱼ) over a pool of free variables, concluding c.
// Each hypothesis is a clause as it stands, so the refuter's own
// preparation is nothing; the key is the normal form of them all in one
// disjunction of binders+ground clauses, whose sort, which simplifies
// it first, is most of a second at 332 clauses and which the canonical
// form runs a dozen times. With 32 and 300 the key takes nine seconds
// on an idle machine. It is the shape of a set driver's unfolded
// residual, a few quantified laws among many membership facts.
func wideLeaf(binders, ground int) Prop {
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
	return prop.MakeProp(ext.Var("c", core.TypeBool()), hyps...)
}

// _CountingCNFStore counts the reads of its store: tryCNFRefute reads
// the store once it holds the key of the refute.
type _CountingCNFStore struct {
	CNFStore
	reads *atomic.Int32
}

func (s _CountingCNFStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	s.reads.Add(1)
	return s.CNFStore.ReadProof(key)
}

// TestCNFRefute_TheKeyNormalizationIsCutOffByTheRequestsContext: a
// refute whose request ends while its key is being computed raises a
// utils.Cut inside the normalization, a unit of it after the deadline,
// and never reads the store: no key was computed. A By over the leaf
// raises its own cut-off, naming the normalization as the stage. The By
// is spelled Raw, the refute its one attempt: a ladder runs the keyless
// probe ahead of the first rung that computes a key, the cache-only
// probe, and on a leaf this wide that probe is where a one-second
// deadline falls on a loaded machine. A normalization that read no
// clock ran its nine seconds out, read the store, and left the cut-off
// to the next poll of the request's context.
func TestCNFRefute_TheKeyNormalizationIsCutOffByTheRequestsContext(t *testing.T) {
	if testing.Short() {
		t.Skip("a nine-second normalization, cut at its deadline")
	}
	goal := wideLeaf(32, 300)
	// The leaf's refuter is built in milliseconds, so the deadline falls
	// inside the normalization; a unit of it is at most one sort of the
	// disjunction, under a second here, and the slack is for a loaded
	// machine.
	const deadline, slack = time.Second, 4 * time.Second
	const inside = "inside the pre-CNF normalization of the sequent"

	// run calls call under the deadline and returns what it panicked
	// with, how long it ran, and how often the store was read.
	run := func(call func(env *ProverEnv, ctx context.Context)) (raised any, elapsed time.Duration, reads int32) {
		env := makeStepTestEnv()
		var count atomic.Int32
		env.ProofService.CNFStore = _CountingCNFStore{NewMemoryCNFStore(), &count}
		ctx, cancel := context.WithTimeout(t.Context(), deadline)
		defer cancel()
		t0 := time.Now()
		func() {
			defer func() { raised = recover() }()
			call(env, ctx)
		}()
		return raised, time.Since(t0), count.Load()
	}

	t.Run("the refute raises a cut", func(t *testing.T) {
		raised, elapsed, reads := run(func(env *ProverEnv, ctx context.Context) {
			CreateGoalStack(goal).runStep(_CNFRefute{env: env, ctx: ctx})
		})
		cut, isCut := utils.AsCut(raised)
		require.True(t, isCut, "after %v the refute raised %v", elapsed, raised)
		require.Contains(t, cut.Where, inside)
		require.ErrorIs(t, cut.Cause, context.DeadlineExceeded)
		require.Zero(t, reads, "the store was read: the key was computed")
		require.Less(t, elapsed, deadline+slack, "cut %v after the deadline, %s", elapsed-deadline, cut.Where)
		t.Logf("cut %v after the deadline, %s", elapsed-deadline, cut.Where)
	})

	t.Run("a By raises its cut-off", func(t *testing.T) {
		// Every hypothesis is listed: a By hands its closer the listed
		// ones alone.
		spec := residentBySpec(goal)
		spec.Shapes = []ByShape{Raw}
		raised, elapsed, reads := run(func(env *ProverEnv, ctx context.Context) {
			ApplyByStep(CreateGoalStack(goal), env, ctx, spec)
		})
		cutOff, isCutOff := raised.(byCutOff)
		require.True(t, isCutOff, "after %v the By raised %v", elapsed, raised)
		require.Contains(t, cutOff.stage, inside)
		require.Zero(t, reads, "the store was read: the key was computed")
		require.Less(t, elapsed, deadline+slack, "cut off %v after the deadline, %s", elapsed-deadline, cutOff.stage)
		t.Logf("cut off %v after the deadline, %s", elapsed-deadline, cutOff.stage)
	})
}
