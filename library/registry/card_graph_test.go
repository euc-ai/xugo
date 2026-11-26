package registry

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
)

// frontierEntry is an entry as a frontier reads one — its name, whether
// it is a card, the entries it stands on — and registers nowhere: a
// frontier reads none of the registry's tables.
func frontierEntry(name string, card bool, deps ...*ProofEntry) *ProofEntry {
	e := &ProofEntry{Name: name}
	if card {
		e.Build.Card = &CardSpec{Note: "a card of the test's graph"}
	}
	for _, d := range deps {
		e.Deps = append(e.Deps, d)
	}
	return e
}

// The frontier is the cards an entry reaches, itself included, sorted,
// each once however many paths reach it; a member reaching none has an
// empty one.
func TestCardFrontiers_ReachedCards(t *testing.T) {
	a := frontierEntry("zz.a", true)
	b := frontierEntry("zz.b", true)
	left := frontierEntry("zz.left", false, b, a)
	right := frontierEntry("zz.right", false, b)
	top := frontierEntry("zz.top", true, right, left)
	lone := frontierEntry("zz.lone", false)
	above := frontierEntry("zz.above", false, lone, top)

	frontiers := NewCardFrontiers()
	require.Equal(t, []string{"zz.a", "zz.b", "zz.top"}, frontiers.Of(above))
	require.Equal(t, []string{"zz.a", "zz.b", "zz.top"}, frontiers.Of(top))
	require.Equal(t, []string{"zz.a", "zz.b"}, frontiers.Of(left))
	require.Equal(t, []string{"zz.b"}, frontiers.Of(right))
	require.Equal(t, []string{"zz.a"}, frontiers.Of(a))
	require.Empty(t, frontiers.Of(lone))

	for _, e := range []*ProofEntry{a, b, left, right, top, lone, above} {
		require.Equal(t, frontiers.Of(e), CardFrontier(e), "%s: one entry's frontier is the one a shared reading holds", e.Name)
	}
}

// Reading every entry's frontier reads each entry's dependencies once.
// The graph is n entries, each standing on every entry before it: n
// reads in one reading, and n(n+1)/2 when each entry is read alone.
func TestCardFrontiers_ReadsEachEntryOnce(t *testing.T) {
	const n = 200
	var entries []*ProofEntry
	var cards [][]string
	for i := range n {
		isCard := i%3 == 0
		name := fmt.Sprintf("zz.e%03d", i)
		entries = append(entries, frontierEntry(name, isCard, entries...))
		var reached []string
		if i > 0 {
			reached = append(reached, cards[i-1]...)
		}
		if isCard {
			reached = append(reached, name)
		}
		cards = append(cards, reached)
	}

	frontiers := NewCardFrontiers()
	for i, e := range entries {
		require.Equal(t, cards[i], frontiers.Of(e), e.Name)
	}
	require.Equal(t, n, frontiers.walks, "one reading reads each entry's dependencies once")

	alone := 0
	for _, e := range entries {
		one := NewCardFrontiers()
		one.Of(e)
		alone += one.walks
	}
	require.Equal(t, n*(n+1)/2, alone, "an entry read alone reads every entry under it")
}

// A dependency that leads back to its entry is refused, the cycle
// named from the entry it closes at — whichever entry the reading
// started from.
func TestCardFrontiers_RefusesACycle(t *testing.T) {
	a := frontierEntry("zz.a", false)
	b := frontierEntry("zz.b", true, a)
	c := frontierEntry("zz.c", false, b)
	a.Deps = []EntryLike{c}
	above := frontierEntry("zz.above", false, a)

	const refusal = "proof registry: the dependencies of zz.a lead back to it: zz.a → zz.c → zz.b → zz.a — " +
		"no entry stands on itself (TestRegistryDAGIntegrity lists every cycle of the graph)"
	require.PanicsWithValue(t, refusal, func() { NewCardFrontiers().Of(a) })
	require.PanicsWithValue(t, refusal, func() { NewCardFrontiers().Of(above) })
	require.PanicsWithValue(t, refusal, func() { CardFrontier(a) })
}
