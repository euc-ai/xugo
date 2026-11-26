package refuter

import (
	"context"
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// fakeProofNode is a _ProofNode of none of the types the builder handles
// (*_DeduceStep, *_MergeStep, *_ProofCache), so initializeRoot panics on
// it ("Unknown root node type"): a builder panic from a root the search
// hands setProof, standing in for an Assert deeper in the builder.
type fakeProofNode struct{}

func (fakeProofNode) Children() []_ProofNode       { return nil }
func (fakeProofNode) replaceChild(int, _ProofNode) {}
func (fakeProofNode) clone() _ProofNode            { return fakeProofNode{} }

// resolutionRefuter is a refuter over `P(a), ∀x. P(x) ⇒ Q(x) ⊢ Q(a)`: a
// goal no contradiction among the initial clauses closes, so the search
// runs, and one resolution refutes.
func resolutionRefuter(t *testing.T) *_Refuter {
	t.Helper()
	a := Var("a", TypeA)
	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	goal := TestProp(Q.Apply(a), P.Apply(a), ForAll(x)(P.Apply(x).Imply(Q.Apply(x))))
	r := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	require.NotNil(t, r)
	require.False(t, r.Refuted(), "the goal is not closed at the CNF stage")
	return r
}

// TestRefute_AStateWhoseBuilderPanickedSearchesNoFurther: the goal
// closes by one resolution, and a state over it refutes. A state whose
// proof builder panicked is a stopped search: it reports cancelled, not
// the success a search past the break would find.
func TestRefute_AStateWhoseBuilderPanickedSearchesNoFurther(t *testing.T) {
	r := resolutionRefuter(t)
	require.Equal(t, succeed, refuteStateFromCNF(r.CNF()).refute(t.Context()),
		"the goal closes: a cancelled below is the fault's, not saturation's")

	s := refuteStateFromCNF(r.CNF())
	require.False(t, s.setProof(fakeProofNode{}), "a builder panic commits no proof")
	require.False(t, s.isRefuted())
	require.Equal(t, cancelled, s.refute(t.Context()),
		"a search whose builder panicked is over, whatever it would have found")
	require.False(t, s.isRefuted())
}

// TestDivideConquer_AWorkersPanicIsTheSearchsFault: a divided clause
// that is nil makes the task divideConquer starts for it panic on a
// goroutine of its own, outside the proof builder. The process survives:
// the panic is recorded on the search's slot with its value, the site of
// the raise and the stack of that goroutine, the search is stopped, and
// the division reports cancelled without reading the sub-state that was
// never built.
func TestDivideConquer_AWorkersPanicIsTheSearchsFault(t *testing.T) {
	s := refuteStateFromCNF(resolutionRefuter(t).CNF())
	ctx, stop := context.WithCancel(t.Context())
	defer stop()
	s.fault.arm(stop, nil)

	status := s.divideConquer(ctx, &clause.ClauseDivision{DividedClauses: []*Clause{nil}})
	assert.Equal(t, cancelled, status, "a division whose worker panicked is a stopped search")
	assert.Error(t, ctx.Err(), "the first fault stops the search")

	fault := s.fault.recorded()
	require.NotNil(t, fault, "the worker's panic is recorded on the search's slot")
	assert.Contains(t, fmt.Sprint(fault.Value), "nil pointer dereference")
	assert.Contains(t, fault.Site, "clause.go:", "the site names the raise")
	assert.Contains(t, fault.Stack, "divideConquer", "the stack is the worker goroutine's")
	assert.Equal(t, cancelled, s.refute(t.Context()), "the state searches no further")
}

// TestSearch_RaisesAWorkersPanicAsItsFault: the search over a state one
// of whose goroutines panicked is no answer. It raises the fault on the
// goroutine that asked, naming the sequent the refutation ran on, and
// keeps nothing on the refuter.
func TestSearch_RaisesAWorkersPanicAsItsFault(t *testing.T) {
	r := resolutionRefuter(t)
	s := refuteStateFromCNF(r.CNF())
	s.fault.guard(func() { panic("a clause rule broke") })()
	fault := s.fault.recorded()
	require.NotNil(t, fault)
	assert.Contains(t, fault.Site, "search_fault_test.go:")

	defer func() {
		raised, ok := recover().(SearchFault)
		require.True(t, ok, "the search raises the fault, not an answer")
		assert.Equal(t, *fault, raised.Fault)
		assert.True(t, r.goal.AlphaEquals(raised.Goal), "the fault names the sequent refuted")
		carried, ok := utils.AsFault(raised)
		assert.True(t, ok, "a reader of faults finds the carried panic")
		assert.Equal(t, *fault, carried)
		assert.True(t, r.ProvedThm().IsZero(), "nothing is kept on the refuter")
	}()
	r.search(t.Context(), s)
	t.Fatal("the search returned instead of raising the fault")
}

// TestSearch_APanicOnItsOwnGoroutineIsItsFault: the goroutine that asks
// for the search runs clause rules too. An initial clause that is nil
// makes the search panic there, before it starts any other, and the
// search raises that panic as its fault like a worker's.
func TestSearch_APanicOnItsOwnGoroutineIsItsFault(t *testing.T) {
	r := resolutionRefuter(t)
	s := refuteStateFromCNF(r.CNF())
	s.origInitClauses[clause.ClauseKey("no clause")] = nil

	defer func() {
		raised, ok := recover().(SearchFault)
		require.True(t, ok, "the search raises a SearchFault")
		assert.Contains(t, fmt.Sprint(raised.Value), "nil pointer dereference")
		assert.Contains(t, raised.Stack, "deriveInitFunext", "the stack is the asking goroutine's")
		assert.True(t, r.goal.AlphaEquals(raised.Goal))
	}()
	r.search(t.Context(), s)
	t.Fatal("the search returned instead of raising the fault")
}

// TestInitialState_APanicBuildingItIsTheSearchsFault: the state a search
// starts from is built by checking the initial clauses against each
// other. A panic there — here a refuter holding no clause set — is
// raised as the search's fault, with the sequent to be refuted.
func TestInitialState_APanicBuildingItIsTheSearchsFault(t *testing.T) {
	r := &_Refuter{goal: resolutionRefuter(t).goal}
	defer func() {
		raised, ok := recover().(SearchFault)
		require.True(t, ok, "the construction's panic is raised as a SearchFault")
		assert.Contains(t, fmt.Sprint(raised.Value), "nil pointer dereference")
		assert.True(t, r.goal.AlphaEquals(raised.Goal))
	}()
	r.initialState()
	t.Fatal("the construction returned")
}

// TestSearch_AFaultAfterTheAnswerGoesToTheContextsReader: a
// contradiction check runs on a pool the search does not wait for. A
// panic in one after the search has answered is raised on no caller; it
// goes, with the sequent refuted, to the reader the caller's context
// carries.
func TestSearch_AFaultAfterTheAnswerGoesToTheContextsReader(t *testing.T) {
	r := resolutionRefuter(t)
	s := refuteStateFromCNF(r.CNF())
	var late []SearchFault
	ctx := WithLateFaultReport(t.Context(), func(fault SearchFault) { late = append(late, fault) })
	require.NotNil(t, r.search(ctx, s), "the search refutes the goal")
	require.Empty(t, late)

	s.fault.guard(func() { panic("a check still running broke") })()
	require.Len(t, late, 1, "the late fault reaches the context's reader")
	assert.Equal(t, "a check still running broke", late[0].Value)
	assert.Contains(t, late[0].Site, "search_fault_test.go:")
	assert.True(t, r.goal.AlphaEquals(late[0].Goal))
	assert.Nil(t, s.fault.recorded(), "the answered search keeps its answer")
}

// TestSearch_AFaultAfterTheAnswerWithNoReaderIsRaised: under a context
// that carries no reader a late fault is raised where it stands, never
// dropped.
func TestSearch_AFaultAfterTheAnswerWithNoReaderIsRaised(t *testing.T) {
	r := resolutionRefuter(t)
	s := refuteStateFromCNF(r.CNF())
	require.NotNil(t, r.search(t.Context(), s))

	defer func() {
		raised, ok := recover().(SearchFault)
		require.True(t, ok, "the late fault is raised")
		assert.Equal(t, "a check still running broke", raised.Value)
	}()
	s.fault.guard(func() { panic("a check still running broke") })()
	t.Fatal("the late fault was dropped")
}
