package engine

import (
	"testing"

	"github.com/euc-ai/xugo/library/carddata"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/require"
)

// The generated path must not elaborate, normalize or print the
// statement: an entry carrying just its registered identity has no
// statement cell, so any of those operations would fail here.
func TestCards_GeneratedTextNeedsNoStatement(t *testing.T) {
	for _, entry := range registry.All() {
		if !entry.IsCard() {
			continue
		}
		text, ok := carddata.Lookup(entry.Name, entry.Key)
		require.True(t, ok, "%s has no generated text", entry.Name)
		identity := &registry.ProofEntry{Name: entry.Name, Key: entry.Key}
		got := landedCardOf(identity)
		require.NoError(t, got.err)
		require.Equal(t, entry.Key, string(got.key))
		require.Equal(t, text.Statement, got.statement)
		require.Equal(t, text.StatementTyped, got.statementTyped)
		// A restatement with the same name must not reuse the text
		// under its old key; it needs a real statement to read.
		restated := &registry.ProofEntry{Name: entry.Name, Key: entry.Key + "-restated"}
		require.Error(t, landedCardOf(restated).err)
		return
	}
	t.Fatal("the corpus has no card")
}
