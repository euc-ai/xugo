package proof

// The capturing store names the leaf each touched key stands for
// (CNFGoalNoter): the recorder's report reads it, so a "+1 new" is a
// leaf, not a key to hunt for.

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

func TestCapturingCNFStore_NotesTheLeafGoal(t *testing.T) {
	inner := NewMemoryCNFStore()
	held := core.PropKey("prop_held")
	inner.WriteProof(held, &refuter.CNFRefuteProofProto{})
	capture := NewCapturingCNFStore(inner)

	goalA := MakeProp(Var("p", TypeBool).Core())
	goalB := MakeProp(Var("q", TypeBool).Core())
	fresh := core.PropKey("prop_fresh")

	// A hit and a write are both noted; a store without the face is a no-op.
	require.NotNil(t, capture.ReadProof(held))
	noteCNFGoal(capture, held, goalA)
	capture.WriteProof(fresh, &refuter.CNFRefuteProofProto{})
	noteCNFGoal(capture, fresh, goalB)
	noteCNFGoal(inner, held, goalA)

	goals := capture.Goals()
	require.Len(t, goals, 2)
	require.True(t, goals[held].AlphaEquals(goalA))
	require.True(t, goals[fresh].AlphaEquals(goalB))

	// The first noted goal for a key wins.
	noteCNFGoal(capture, held, goalB)
	require.True(t, capture.Goals()[held].AlphaEquals(goalA))
	// Goals is a copy.
	delete(goals, held)
	require.Len(t, capture.Goals(), 2)
}
