package proof

import (
	"runtime"
	"sync/atomic"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestRungFailure_ASearchFaultIsRaisedAgain: the By ladder reads a
// rung's recovered panic as that rung's failure and tries the next rung
// — except a fault, which it raises again: a later rung that closed the
// leaf would hide the break. A refutation one of whose goroutines
// panicked is one, and so is any panic carried off another goroutine.
func TestRungFailure_ASearchFaultIsRaisedAgain(t *testing.T) {
	carried := utils.Fault{Value: "Should not happen. (at proof_builder.go:397 in computeFinalThm)",
		Site: "proof_builder.go:397 in refuter.(*_ProofBuilder).computeFinalThm"}
	fault := refuter.SearchFault{Fault: carried}
	require.PanicsWithError(t, fault.Error(), func() { rungFailure(fault) })
	require.PanicsWithError(t, carried.Error(), func() { rungFailure(carried) })
	require.Equal(t, "By: CnfRefute failed", rungFailure("By: CnfRefute failed"),
		"any other panic is the rung's failure")
	require.Nil(t, rungFailure(nil), "no panic, no failure")
}

// TestRungFailure_AnAssertionFailureIsRaisedAgain: a failed Assert in a
// rung is an invariant breach, not that rung's failure — it is raised
// again as a search fault is, so no later rung closes over it.
func TestRungFailure_AnAssertionFailureIsRaisedAgain(t *testing.T) {
	breach := utils.AssertionFailed + " (at fact.go:1834 in proof.strongerLeaf)"
	require.PanicsWithValue(t, breach, func() { rungFailure(breach) })
	require.PanicsWithValue(t, utils.AssertionFailed, func() { rungFailure(utils.AssertionFailed) },
		"the bare text an ext invariant panics with")
	require.Equal(t, "ministep StripImp failed", rungFailure("ministep StripImp failed"),
		"any other text is the rung's failure")
}

// TestRungFailure_ARuntimeErrorIsRaisedAgain: a nil dereference, an
// index out of range or a failed type assertion in a rung is a defect
// of the code that ran, not that rung's failure — it is raised again
// as a failed assertion is, so no later rung closes over it.
func TestRungFailure_ARuntimeErrorIsRaisedAgain(t *testing.T) {
	broke := func() (r any) {
		defer func() { r = recover() }()
		var v any = "the shape the rung did not expect"
		return v.(int)
	}()
	require.Implements(t, (*runtime.Error)(nil), broke, "fixture: a failed type assertion")
	require.PanicsWithValue(t, broke, func() { rungFailure(broke) })
}

// _FaultingCNFStore raises a fault at its nth read of a proof, counted
// from one, and holds nothing: every other read is a MISS, so a live By
// refutes the leaf itself.
type _FaultingCNFStore struct {
	CNFStore
	reads *atomic.Int32
	nth   int32
	raise func()
}

func (s _FaultingCNFStore) ReadProof(core.PropKey) *refuter.CNFRefuteProofProto {
	if s.reads.Add(1) == s.nth {
		s.raise()
	}
	return nil
}

// TestBy_AFaultInsideARungIsRaisedNotClosedOver: the By's close reads
// the CNF store once per rung that reaches the refuter — the rung-1
// probe first, the conditioned rung second. A fault raised at either
// read — a failed assertion, a search fault, an error of the Go
// runtime — is raised by the By as it is: the conditioned rung's close
// does not fold it into its failure text, over which the bare retry
// rung, reading a MISS and refuting live, would close the leaf.
func TestBy_AFaultInsideARungIsRaisedNotClosedOver(t *testing.T) {
	searchFault := refuter.SearchFault{Fault: utils.Fault{Value: "a clause rule broke", Site: "deduce.go:1 in clause.rule"}}
	for _, row := range []struct {
		name  string
		raise func()
		is    func(r any) bool
	}{
		{"a failed assertion", func() { utils.Assert(false) }, utils.IsAssertionFailure},
		{"a search fault", func() { panic(searchFault) }, func(r any) bool { return r == any(searchFault) }},
		{"a nil dereference", func() { var p *core.PropKey; _ = *p }, func(r any) bool { _, ok := r.(runtime.Error); return ok }},
	} {
		for nth := int32(1); nth <= 2; nth++ {
			goal := threeLinkChain()
			env := makeStepTestEnv()
			var reads atomic.Int32
			env.ProofService.CNFStore = _FaultingCNFStore{NewMemoryCNFStore(), &reads, nth, row.raise}

			var raised any
			closed := func() (closed bool) {
				defer func() { raised = recover() }()
				return ApplyByStep(CreateGoalStack(goal), env, t.Context(), residentBySpec(goal))
			}()
			require.GreaterOrEqual(t, reads.Load(), nth, "fixture: the By reaches the store's read %d", nth)
			assert.False(t, closed, "%s at read %d: the By did not close over the fault", row.name, nth)
			assert.True(t, row.is(raised), "%s at read %d: raised as it is, got %v", row.name, nth, raised)
		}
	}
}
