package registry

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// An entry is found by its statement. A statement that has the entry's
// key and is not α-equal to it finds nothing: here g applied to a
// variable whose name runs on into the next key, beside the entry's own,
// a function whose name does applied to x (core.TermKey).
func TestEntriesStating_ComparesStatements(t *testing.T) {
	boolType := core.TypeBool()
	unary := core.MakeFun(boolType, boolType)
	stated := func() core.Prop {
		return core.MakeProp(core.Apply(core.Var("g_"+string(unary.Key())+"var_h", unary), core.Var("x", boolType)))
	}
	sharing := core.MakeProp(core.Apply(core.Var("g", unary), core.Var("h_"+string(unary.Key())+"var_x", boolType)))
	require.Equal(t, stated().AlphaKey(), sharing.AlphaKey(),
		"the two statements have two keys: this pair no longer shows what a shared key does")
	require.False(t, stated().AlphaEquals(sharing))

	fam := NewFamily("zz_entries_stating", nil)
	entry := fam.Add(ProofEntry{
		Name:   "Stated",
		stated: stated(),
		Build:  BuildSpec{Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})

	require.Equal(t, []*ProofEntry{entry}, EntriesStating(stated()), "a second build of the entry's statement")
	require.True(t, SomeEntryStates(stated()))
	require.Empty(t, EntriesStating(sharing), "a statement with the entry's key is not the entry's statement")
	require.False(t, SomeEntryStates(sharing))
}
