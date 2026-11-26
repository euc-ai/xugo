package refuter

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestSetProof_ContainsTheBuilderPanicAndRecordsTheFault: a panic inside
// the proof builder is caught by setProof — the process survives, the
// attempt commits nothing and the proof DAG is rolled back to empty — and
// is recorded on the search's fault slot with its value and site, which
// stops the search. A second panic is contained the same way and the
// first fault stays the search's.
func TestSetProof_ContainsTheBuilderPanicAndRecordsTheFault(t *testing.T) {
	s := refuteStateFromCNF(resolutionRefuter(t).CNF())
	stopped := false
	s.fault.arm(func() { stopped = true }, nil)

	committed := s.setProof(fakeProofNode{})
	assert.False(t, committed, "a builder panic commits no proof")
	assert.False(t, s.isRefuted(), "after a contained panic the state is not refuted")

	s.proof.RLock()
	rootNil := s.proof.root == nil
	thmNil := s.proof.clauseThm == nil
	nodes := len(s.proof.nodeSet)
	s.proof.RUnlock()
	assert.True(t, rootNil, "rollback clears proof.root")
	assert.True(t, thmNil, "rollback clears proof.clauseThm")
	assert.Equal(t, 0, nodes, "rollback clears proof.nodeSet")

	fault := s.fault.recorded()
	require.NotNil(t, fault, "the fault is recorded on the search's slot")
	assert.Equal(t, "Unknown root node type", fault.Value)
	assert.Contains(t, fault.Site, "proof_builder.go:", "the site names the builder's file and line")
	assert.Contains(t, fault.Site, "initializeRoot", "the site names the builder's function")
	assert.True(t, stopped, "the first fault stops the search")

	assert.False(t, s.setProof(fakeProofNode{}), "a second builder panic is contained too")
	assert.Same(t, fault, s.fault.recorded(), "the first fault stays the search's")
}

// TestSetProof_ValidationFailureIsNotPublished: a DAG the validator
// rejects is a builder panic like any other — recorded, not published to
// the shared cache.
func TestSetProof_ValidationFailureIsNotPublished(t *testing.T) {
	u := Var("u", MakeFun(TypeA, TypeBool))
	y := Var("y", TypeA)
	uy := u.Apply(y)

	positive := clause.MakeClause(uy)
	negative := clause.MakeClause(Not(uy))
	refutedThm := positive.Contradicts(negative)
	require.NotNil(t, refutedThm)

	initial := ClauseMap{
		positive.Key(): positive,
		negative.Key(): negative,
	}
	s := newRefuteState(
		&ext.VarList{},
		initial,
		ClauseMap{positive.Key(): positive}, // deliberately invalid double classification
		&_ActiveSet{m: make(ClauseMap)},
		emptyPassiveSet(),
		emptyDeductRecord(),
		&_AttemptRecords{},
		&_RefuteCache{},
		newClauseWhistle(initial),
		&_FaultSlot{},
	)

	assert.False(t, s.setProof(makeDeduceStep(refutedThm)),
		"the validator rejects a hypothesis that is both original and assumed")
	assert.Equal(t, 0, s.cache.proof.Size(),
		"a proof DAG does not enter the shared cache before validation succeeds")
	fault := s.fault.recorded()
	require.NotNil(t, fault)
	assert.Contains(t, fault.Value, "Proof validation failed")
	assert.Contains(t, fault.Site, "refuter.go:", "the validation panic is raised in setProof itself")

	// A cache entry with no ClauseThm (an in-progress DAG) is skipped by
	// the cache check, not a panic.
	s.cache.proof.Store(PropKey("nil-clause-thm"), emptyProof())
	assert.NotPanics(t, func() {
		s.checkCache(context.Background(), make(chan struct{}, 1))
	})
}

// TestSearch_ABuilderPanicOnACachedProofFailsTheRefutationNamingIt: the
// cross-context reuse path. A first search over the goal refutes it; a
// fresh state over the same clauses finds, in its shared cache, a proof
// of the same theorem whose DAG the builder cannot clone (its node set
// holds a node of no step type). The cache check does not signal
// success and the state is not refuted; the fault is recorded with the
// builder's panic and the site in the DAG's clone; and the search over
// that state is no answer — it raises the fault, naming both.
func TestSearch_ABuilderPanicOnACachedProofFailsTheRefutationNamingIt(t *testing.T) {
	r := resolutionRefuter(t)
	ctx := t.Context()
	proved := r.search(ctx, refuteStateFromCNF(r.CNF()))
	require.NotNil(t, proved, "the first search refutes the goal")
	thm := proved.refutedThm()

	s := refuteStateFromCNF(r.CNF())
	nodes := utils.EmptySet[_ProofNode]()
	nodes.Add(fakeProofNode{})
	s.cache.proof.Store(thm.AlphaKey(), &_ProofDAG{root: fakeProofNode{}, clauseThm: thm, nodeSet: nodes})

	signal := make(chan struct{}, 1)
	s.checkCache(ctx, signal)
	assert.Empty(t, signal, "a reuse whose builder panicked signals no success")
	assert.False(t, s.isRefuted())
	fault := s.fault.recorded()
	require.NotNil(t, fault, "the builder panic is the search's fault")
	assert.Equal(t, "Wrong node type.", fault.Value)
	assert.Contains(t, fault.Site, "proof_dag.go:")
	assert.Contains(t, fault.Site, "clone")

	defer func() {
		raised, ok := recover().(SearchFault)
		require.True(t, ok, "the search raises the fault, not an answer")
		assert.Equal(t, *fault, raised.Fault)
		assert.True(t, r.goal.AlphaEquals(raised.Goal), "the fault names the sequent the refutation ran on")
		assert.Contains(t, raised.Error(), "Wrong node type.")
		assert.Contains(t, raised.Error(), fault.Site)
		assert.True(t, r.ProvedThm().IsZero(), "nothing the faulted search found is kept on the refuter")
	}()
	r.provedThm, r.refutedCNFClauseThm = Thm{}, nil
	r.search(ctx, s)
	t.Fatal("the search over a faulted state returned instead of raising the fault")
}
