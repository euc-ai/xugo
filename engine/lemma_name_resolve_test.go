package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestLemmaKeySlot_Spellings pins the key slot's two spellings of one
// entry — its own key and its registered name — and refuses the
// library-theorem name it serves as (the pairs chapter's Fst serves
// fst_of_pair): a library-theorem name is not a cite spelling.
func TestLemmaKeySlot_Spellings(t *testing.T) {
	fst, ok := registry.ByServesAs("fst_of_pair")
	require.True(t, ok, "no entry serves fst_of_pair: the fixture names what the corpus no longer has")
	e := newEngine(serveLikeEnv(t))
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goal := prop.MakeProp(ext.T)

	for _, spelling := range []string{fst.Key, fst.Name} {
		p, err := e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: spelling}, goal)
		require.NoError(t, err, "spelling %q", spelling)
		n, _ := prop.Normalize(p)
		assert.Equal(t, fst.Key, string(n.AlphaKey()),
			"spelling %q must serve the entry's own statement", spelling)
	}
	_, err = e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: "fst_of_pair"}, goal)
	require.Error(t, err, "a served library-theorem name is not a cite spelling")
	assert.Contains(t, err.Error(), "names no proof-registry entry")
}

// TestLemmaKeySlot_BareEntryNameHint: a bare entry name (what the Go
// source spells, what Deps lists) stays a miss — the slot takes the
// FULL registered name — but the miss says so.
func TestLemmaKeySlot_BareEntryNameHint(t *testing.T) {
	var bare string
	for _, entry := range registry.All() {
		i := strings.LastIndex(entry.Name, ".")
		if i < 0 {
			continue
		}
		suffix := entry.Name[i+1:]
		if _, ok := registry.ByName(suffix); ok {
			continue
		}
		if _, ok := registry.ByServesAs(suffix); ok {
			continue
		}
		bare = suffix
		break
	}
	require.NotEmpty(t, bare, "no family-qualified entry with a free bare name in the registry")

	e := newEngine(testEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	_, err = e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: bare}, prop.MakeProp(ext.T))
	require.Error(t, err)
	assert.Contains(t, err.Error(), "FULL registered name",
		"a bare entry name should get the full-name hint; got: %v", err)
}
