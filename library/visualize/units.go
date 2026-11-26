package visualize

// Units and reduction: what the graphs read the corpus through.
//
// A unit is what a graph draws as one node: a member registered alone,
// or a door call that registered several members from one literal
// (index.Door), in place of them. A call's deps are its parts' deps:
// the units' relation is the members' with each call folded into one
// node. It is acyclic — the registry refuses a citation cycle, and a
// door call's parts stand on each other and on entries registered
// before the call, so folding them closes none.
//
// A graph's edges are a dependency relation transitively reduced
// inside the nodes drawn (reduceScope): an edge is kept only where no
// other drawn node stands between its ends, so a drawing shows the
// skeleton and not every pair.

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/library/index"
)

// _Fold is the corpus with its door calls folded: its members and door
// calls by id, and its families by name.
type _Fold struct {
	corpus   *index.Corpus
	byID     map[string]*index.Member
	byDoor   map[string]*index.Door
	byFamily map[string]*index.Family
}

// foldDoors reads a corpus by unit.
func foldDoors(c *index.Corpus) *_Fold {
	fold := &_Fold{corpus: c, byID: make(map[string]*index.Member, len(c.Members)),
		byDoor: make(map[string]*index.Door, len(c.Doors)), byFamily: make(map[string]*index.Family, len(c.Families))}
	for _, m := range c.Members {
		fold.byID[m.ID] = m
	}
	for _, d := range c.Doors {
		fold.byDoor[d.ID] = d
	}
	for _, f := range c.Families {
		fold.byFamily[f.Name] = f
	}
	return fold
}

// of is the unit a member is drawn as: the door call that registered
// it, or itself.
func (fold *_Fold) of(id string) string {
	if d := fold.byID[id].Door; d != "" {
		return d
	}
	return id
}

// members are the members a unit stands for: a door call's parts, or
// the member.
func (fold *_Fold) members(u string) []*index.Member {
	d := fold.byDoor[u]
	if d == nil {
		return []*index.Member{fold.byID[u]}
	}
	parts := make([]*index.Member, len(d.Parts))
	for i, p := range d.Parts {
		parts[i] = fold.byID[p.Member]
	}
	return parts
}

// deps are a unit's deps as units, less itself: its members' deps in
// their declaration order, each unit once.
func (fold *_Fold) deps(u string) []string {
	seen := map[string]bool{u: true}
	var units []string
	for _, m := range fold.members(u) {
		for _, id := range m.Deps {
			if v := fold.of(id); !seen[v] {
				seen[v] = true
				units = append(units, v)
			}
		}
	}
	return units
}

func (fold *_Fold) family(u string) string { return fold.members(u)[0].Family }

// name is a unit's name: a door call's Name, or a member's bare name,
// its id's after the family's.
func (fold *_Fold) name(u string) string {
	if d := fold.byDoor[u]; d != nil {
		return d.Name
	}
	return u[strings.LastIndex(u, ".")+1:]
}

// status is a unit's stratum: a member's as the index has it
// (index.Member.Status), and a door call's "on_cards" where a part of it
// stands on a card, "proved" otherwise.
func (fold *_Fold) status(u string) string {
	members := fold.members(u)
	if fold.byDoor[u] == nil {
		return members[0].Status()
	}
	for _, m := range members {
		if len(m.Cards) > 0 {
			return "on_cards"
		}
	}
	return "proved"
}

// theorem says whether a unit is a theorem, a card or a postulate. A
// definition, a structure, a type and a door call are none.
func (fold *_Fold) theorem(u string) bool {
	if fold.byDoor[u] != nil {
		return false
	}
	switch fold.byID[u].Kind {
	case "theorem", "card", "postulate":
		return true
	case "definition", "structure", "type":
		return false
	}
	panic(fmt.Sprintf("visualize: %s is of kind %q, neither a theorem nor a definition", u, fold.byID[u].Kind))
}

// result says whether a unit is a result, what a count of what a unit
// stands on counts: a theorem or a card. A postulate is assumed, and
// counted no more than a definition is.
func (fold *_Fold) result(u string) bool {
	return fold.theorem(u) && fold.byID[u].Kind != "postulate"
}

// resolve reads a graph's argument as a unit: a door call by id or
// entry, else the unit of the one member it names by index id,
// registered name, own key or a bare name one member alone has
// (index.Corpus.ResolveOne).
func (fold *_Fold) resolve(ref string) (string, error) {
	if d := fold.byDoor[ref]; d != nil {
		return d.ID, nil
	}
	for _, d := range fold.corpus.Doors {
		if d.Entry == ref {
			return d.ID, nil
		}
	}
	m, err := fold.corpus.ResolveOne(ref)
	if err != nil {
		return "", fmt.Errorf("%v; nor is it a door call", err)
	}
	return fold.of(m.ID), nil
}

// _Edge says S depends on T, no node of the scope between them. Via
// marks a dependency through nodes outside the scope, no direct one.
type _Edge struct {
	S, T string
	Via  bool
}

// reduceScope is a scope's dependency relation, transitively reduced:
// an edge s → t for each two nodes of the scope where s depends on t —
// directly, or through nodes outside the scope (Via) — and no other
// node of the scope stands between them. deps gives a node's direct
// dependencies (a unit's deps, a family's Imports), and must be
// acyclic; the edges are listed in the scope's order, by s and then by
// t.
//
// One walk below the scope settles it. For every node n reached, down
// is the set of scope nodes n reaches by a path of one step or more,
// and below the scope nodes it reaches through another scope node on
// the way; s keeps an edge to each node of down(s) not in below(s).
// Both are bitsets over the scope, each node's computed once from its
// deps'.
func reduceScope(scope []string, deps func(string) []string) []_Edge {
	place := map[string]int{}
	for i, id := range scope {
		place[id] = i
	}
	words := (len(scope) + 63) / 64
	type reach struct{ down, below []uint64 }
	memo := map[string]*reach{}
	var walk func(id string) *reach
	walk = func(id string) *reach {
		if r, ok := memo[id]; ok {
			return r
		}
		r := &reach{down: make([]uint64, words), below: make([]uint64, words)}
		for _, d := range deps(id) {
			dr := walk(d)
			if j, ok := place[d]; ok {
				r.down[j/64] |= 1 << (j % 64)
				for w := range dr.down {
					r.below[w] |= dr.down[w]
				}
			}
			for w := range dr.down {
				r.down[w] |= dr.down[w]
				r.below[w] |= dr.below[w]
			}
		}
		memo[id] = r
		return r
	}
	edges := []_Edge{}
	for _, s := range scope {
		r := walk(s)
		direct := map[string]bool{}
		for _, d := range deps(s) {
			direct[d] = true
		}
		for j, t := range scope {
			if r.down[j/64]>>(j%64)&1 == 1 && r.below[j/64]>>(j%64)&1 == 0 {
				edges = append(edges, _Edge{S: s, T: t, Via: !direct[t]})
			}
		}
	}
	return edges
}
