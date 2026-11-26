package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestByTactic_GuessedGroundingKeepsThePremise: the pointwise premise
// `∀d. d ∈ s ⇒ disjoint(x, d)` at the goal `disjoint(x, ⋃s)` matches
// through its conclusion alone, at d := ⋃s — an instance whose
// antecedent `⋃s ∈ s` nothing holds. The grounding stage keeps the
// premise wide beside that instance, and the conditioned rung closes
// the leaf: the set driver reaches the premise at the Skolem point of
// `a ∈ ⋃s`. The recorded plan grounds and replaces nothing. Replacing
// the premise, the conditioned attempt spent its budget and the bare
// rung closed the leaf after it, recording no plan.
func TestByTactic_GuessedGroundingKeepsThePremise(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	store := proof.NewMemoryCNFStore()
	e.env.ProofService.CNFStore = store

	sid, gid := bareArithLeaf(t, e, "s:set(set(A)), x:set(A) ⊢ (∀d:set(A). d ∈ s ⇒ disjoint(x, d)) ⇒ disjoint(x, ⋃s)", "strip_imp")
	zero := 0
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "by", Settac: true, ByHyps: []ByHypSpec{{HypIndex: &zero}}}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	assert.Equal(t, 0, res.State.NumOpen)

	plans := store.Plans()
	require.Len(t, plans, 1, "the conditioned rung closed the leaf and recorded its plan")
	for _, entry := range plans {
		require.Len(t, entry.Groundings, 1, "the premise grounded at ⋃s")
		assert.Empty(t, entry.Replaced, "a guess: the premise stays wide beside its instance")
	}
}
