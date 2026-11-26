// card_graph.go — the cards read off the corpus DAG: what a member
// stands on, who stands on a card, and the cheap order to fill the
// cards in.
// Pure functions of the registry, shared by the session's `cards` view
// (engine/cards.go) and the corpus index (library/index) so the two
// agree.

package registry

import (
	"fmt"
	"sort"
	"strings"
)

// CardFrontier lists the cards an entry stands on: itself when it is a
// card, and every card its dependencies reach — through proved members
// as well, since a proof may use them. Registered names, sorted. Empty
// for a member the corpus proves outright. The walk is the whole of
// what the member stands on under two facts: a Build is served its
// dependencies and nothing else (a proved member's are the entries it
// was recorded reading), and no definition door stands on a card
// (gates.TestNoCardUnderADefinitionalDoor) — a constant is reached by
// name and a type by its terms, not through a dependency.
//
// A reader of many entries' frontiers asks one CardFrontiers for them.
func CardFrontier(e *ProofEntry) []string {
	return NewCardFrontiers().Of(e)
}

// CardFrontiers reads the card frontiers of many entries, each entry's
// dependencies read once. An entry's frontier is its own card and its
// dependencies' frontiers, so the one computed for an entry serves
// every entry standing on it: reading every member's frontier walks
// the corpus once, where a walk per member visits an entry once for
// each member above it.
//
// It holds the frontiers of the registry as it stood when they were
// read: a reader makes one for its reading and keeps it across no
// registration. Not for concurrent use.
type CardFrontiers struct {
	frontier map[*ProofEntry][]string
	// walking are the entries whose dependencies are being read, in
	// walk order, and open marks them: a dependency among them leads
	// back to itself.
	walking []*ProofEntry
	open    map[*ProofEntry]bool
	// walks counts the entries whose dependencies were read.
	walks int
}

// NewCardFrontiers is a CardFrontiers with no frontier read yet.
func NewCardFrontiers() *CardFrontiers {
	return &CardFrontiers{frontier: map[*ProofEntry][]string{}, open: map[*ProofEntry]bool{}}
}

// Of is CardFrontier of e. The list is shared with the frontiers of
// the entries standing on e: it is read, never written.
//
// A dependency that leads back to its entry panics, naming the cycle:
// the frontier is the union over a graph with none, and an entry
// standing on itself has no proof to stand on.
func (c *CardFrontiers) Of(e *ProofEntry) []string {
	if cards, read := c.frontier[e]; read {
		return cards
	}
	if c.open[e] {
		var cycle []string
		for i, x := range c.walking {
			if x == e {
				for _, y := range c.walking[i:] {
					cycle = append(cycle, y.Name)
				}
				break
			}
		}
		panic(fmt.Sprintf("proof registry: the dependencies of %s lead back to it: %s → %s — "+
			"no entry stands on itself (TestRegistryDAGIntegrity lists every cycle of the graph)",
			e.Name, strings.Join(cycle, " → "), e.Name))
	}
	c.open[e] = true
	c.walking = append(c.walking, e)
	var cards []string
	if e.IsCard() {
		cards = []string{e.Name}
	}
	c.walks++
	for _, d := range e.DepEntries() {
		cards = unionSorted(cards, c.Of(d))
	}
	c.walking = c.walking[:len(c.walking)-1]
	delete(c.open, e)
	c.frontier[e] = cards
	return cards
}

// unionSorted is the union of two sorted lists of distinct names,
// sorted: one of the two itself where it holds the other, a new list
// otherwise. Neither list is written.
func unionSorted(a, b []string) []string {
	if len(b) == 0 {
		return a
	}
	if len(a) == 0 {
		return b
	}
	size := 0
	for i, j := 0, 0; i < len(a) || j < len(b); size++ {
		switch {
		case j == len(b) || (i < len(a) && a[i] < b[j]):
			i++
		case i == len(a) || b[j] < a[i]:
			j++
		default:
			i, j = i+1, j+1
		}
	}
	switch size {
	case len(a):
		return a
	case len(b):
		return b
	}
	out := make([]string, 0, size)
	for i, j := 0, 0; i < len(a) || j < len(b); {
		switch {
		case j == len(b) || (i < len(a) && a[i] < b[j]):
			out = append(out, a[i])
			i++
		case i == len(a) || b[j] < a[i]:
			out = append(out, b[j])
			j++
		default:
			out = append(out, a[i])
			i, j = i+1, j+1
		}
	}
	return out
}

// CardCiters maps each card to the members whose dependencies name it
// directly, by registered name, sorted.
func CardCiters() map[*ProofEntry][]string {
	out := map[*ProofEntry][]string{}
	for _, m := range All() {
		for _, d := range m.DepEntries() {
			if d.IsCard() {
				out[d] = append(out[d], m.Name)
			}
		}
	}
	for _, names := range out {
		sort.Strings(names)
	}
	return out
}

// CardFillOrder lists the registered cards leaves first: a card after
// every card its dependencies reach, ties by the number of members
// standing on it (more first), then by name. It is the cheap order to
// fill them in, not a schedule: any card can be filled at any time, its
// proof citing the cards under it as the axioms they are, and filling
// leaves first only finds a false card before much is proved on it.
func CardFillOrder() []string {
	citers := CardCiters()
	var cards []*ProofEntry
	for _, e := range All() {
		if e.IsCard() {
			cards = append(cards, e)
		}
	}
	frontiers := NewCardFrontiers()
	below := map[*ProofEntry][]string{}
	for _, c := range cards {
		for _, name := range frontiers.Of(c) {
			if name != c.Name {
				below[c] = append(below[c], name)
			}
		}
	}
	sort.Slice(cards, func(i, j int) bool {
		a, b := cards[i], cards[j]
		if len(citers[a]) != len(citers[b]) {
			return len(citers[a]) > len(citers[b])
		}
		return a.Name < b.Name
	})
	var order []string
	placed := map[*ProofEntry]bool{}
	var place func(c *ProofEntry)
	place = func(c *ProofEntry) {
		if placed[c] {
			return
		}
		placed[c] = true
		for _, name := range below[c] {
			place(byName[name])
		}
		order = append(order, c.Name)
	}
	for _, c := range cards {
		place(c)
	}
	return order
}
