package visualize

// A proof graph: a unit's proof drawn left to right as the results it
// stands on, the unit at the right edge. The units drawn are chosen
// from the dependency graph and nothing else — no list of results kept
// by hand, no count of citations — so any theorem of the corpus has
// one. A definition's proof holds no result to draw, and its graph is
// another (definitiongraph.go), laid out by the same columns.
//
// The cone of a unit is the unit and every unit it stands on. A unit's
// steps are the unit and the units of its own family it stands on
// through units of that family: what its chapter does for it. A family's
// spread is the number of families that stand on it, importing it
// directly or through others. A theorem here is a theorem, a card or a
// postulate; a definition, a structure or a type is a definition.
//
// A graph draws five parts of the cone.
//
// The chapter: every theorem of the unit's family in the cone, and the
// family's definitions those theorems cite that the unit cites itself
// or two of them cite — every one when they are three or fewer.
//
// The apexes of every other family that is not ambient. A family
// whose spread exceeds the spread of the unit's family by more than the
// grain's allowance is ambient, one the whole neighbourhood stands on —
// the reals under a chapter of analysis. A family's apexes are, of its
// theorems cited from another family that is not ambient, those that
// gather a part of their chapter under them and that no other gathers
// in turn. A theorem is a candidate when its steps count the grain's
// number of theorems, or two when the chapter cites it directly. A
// candidate is subsumed when another candidate of its family has it
// among its steps and is cited from every family that cites it; a
// candidate the chapter cites directly is never subsumed. Of the
// candidates left, those whose steps number at least 45% of the
// largest's are drawn, and those the chapter cites directly whatever
// their size: the directly cited first, then the larger, up to the
// grain's number for a family, and two more when one is cited directly.
//
// The ground: an ambient family's apexes — found the same way, among
// all the families of the cone — that the chapter or another family's
// apex cites directly. They are drawn apart, under a line across the
// drawing.
//
// The cards: every card in the cone, at every grain. A theorem is left
// out where it is proved, the rest of its neighbourhood standing for
// it; a card is not proved, and is no part of what may be left out. A
// card is drawn over the line, or under it where its family is ambient.
// The cards drawn are the target's card frontier (index.Member.Cards),
// itself aside.
//
// What a card cites: where the unit is a card, every unit its chapter
// names as its deps, at every grain — a theorem of any size, a
// definition of any family — drawn over the line, or under it where its
// family is ambient. A card has no proof to draw, and these are the
// results its proof is to cite.
//
// An edge between two units over the line says one stands on the other
// with no drawn unit between them (reduceScope), and is marked Via
// where it is no direct citation. An edge to a unit of the ground is a
// direct citation, and every one is drawn: all that is over the line
// stands on the ground through others. A unit of the ground that no
// drawn unit cites directly — a card, every other one being drawn for a
// citation — has the edges of the reduced relation over every unit
// drawn, each marked Via.
//
// The drawing is in columns. The unit is in the last, and every other
// node in the column just left of the leftmost node standing on it, so
// each sits as near the unit as its edges allow. The drawing is in two
// parts, the ground under the line and the rest over it, and each part
// is laid out by itself: a column's nodes of the
// part are ordered and placed by the weighted mean height of their
// neighbours in it, two neighbours changing places where that uncrosses
// edges, and set at the heights nearest their aims that keep the order
// and a row's distance between two nodes (spaced).

import (
	"fmt"
	"math"
	"math/bits"
	"slices"
	"sort"
	"strings"
	"sync"
	"unicode/utf8"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/index"
)

// ProofGraph is a unit drawn. A theorem's is its proof at each grain,
// the coarsest first. A definition's is one drawing, what it is built
// from and who uses it (definitiongraph.go), and Definition then counts
// who uses it. Target is the unit and Name its name; Revision names the
// corpus drawn where the caller knows it, and is the caller's to set.
type ProofGraph struct {
	Revision   string           `json:"revision,omitempty"`
	Target     string           `json:"target"`
	Name       string           `json:"name"`
	Definition *ProofDefinition `json:"definition,omitempty"`
	Grains     []ProofGrain     `json:"grains"`
}

// ProofGrain is a proof graph at one grain, laid out in the units of
// the page's viewBox: Width and Height the viewBox, Block a node's
// height, Axis the height of the target's centre line, and Line the
// height of the line the ground is drawn under, 0 where the graph draws
// none. Allowance, Theorems and PerFamily are the
// grain's rule, for the page to say. The nodes are listed column by
// column, each column top to bottom. Groups are the headings of the
// column right of a definition (definitiongraph.go).
type ProofGrain struct {
	Key       string        `json:"key"`
	Allowance int           `json:"allowance"`
	Theorems  int           `json:"theorems"`
	PerFamily int           `json:"per_family"`
	Width     int           `json:"width"`
	Height    int           `json:"height"`
	Block     float64       `json:"block"`
	Axis      float64       `json:"axis"`
	Line      float64       `json:"line,omitzero"`
	Columns   []ProofColumn `json:"columns"`
	Nodes     []ProofNode   `json:"nodes"`
	Edges     []ProofEdge   `json:"edges"`
	Groups    []ProofGroup  `json:"groups,omitempty"`
}

// ProofColumn is a column's left edge and width.
type ProofColumn struct {
	X float64 `json:"x"`
	W float64 `json:"w"`
}

// ProofNode is a unit drawn: a member, or a door call that
// registered several. Own marks a unit of the target's family, Ambient
// one of the ground, drawn under the line, and Definition a
// definition, a structure or a type. Steps counts the unit's steps.
// Status is the unit's stratum (index.Member.Status), Theorems the
// results it stands on in the whole corpus (_Fold.result), and Cards
// the cards among those. Statements are what the unit states, a
// member's one statement or a door call's part by part, and Gloss what
// its chapter says it is (index.Corpus.Description), its formulas
// typeset (typeset), a door call's that of its first part. X and Y are
// the node's top left corner, W its width.
//
// Use is set on a node right of a definition, and says how it uses the
// definition (definitiongraph.go). Such a node may stand for a family
// in place of a unit, or for the families not drawn: Users then counts
// the units it stands for and Families the families.
type ProofNode struct {
	ID         string           `json:"id"`
	Name       string           `json:"name"`
	Family     string           `json:"family"`
	Column     int              `json:"column"`
	Own        bool             `json:"own,omitzero"`
	Ambient    bool             `json:"ambient,omitzero"`
	Target     bool             `json:"target,omitzero"`
	Definition bool             `json:"definition,omitzero"`
	Steps      int              `json:"steps"`
	Status     string           `json:"status"`
	Theorems   int              `json:"theorems"`
	Cards      int              `json:"cards"`
	Statements []ProofStatement `json:"statements"`
	Gloss      string           `json:"gloss,omitempty"`
	Use        string           `json:"use,omitempty"`
	Users      int              `json:"users,omitzero"`
	Families   int              `json:"families,omitzero"`
	X          float64          `json:"x"`
	Y          float64          `json:"y"`
	W          float64          `json:"w"`
}

// ProofStatement is a member's statement as a node carries it: Member
// the member's bare name, Text the statement as its chapter states it
// (index.Member.Statement), Abbreviations the names Text spells as
// «Name», each with the term it stands for, and Reading the statement
// read in this encoding, where its author wrote one
// (index.Member.Reading). A definition's says what it mints: Shape the
// shape its door served (index.Member.Shape), Defines the constants and
// Type the type.
type ProofStatement struct {
	Member        string          `json:"member"`
	Text          string          `json:"text"`
	Abbreviations dsl.Abbrev      `json:"abbreviations,omitempty"`
	Reading       string          `json:"reading,omitempty"`
	Shape         string          `json:"shape,omitempty"`
	Defines       []ProofConstant `json:"defines,omitempty"`
	Type          string          `json:"type,omitempty"`
}

// ProofConstant is a constant a definition mints: its name, and the
// surface spelling its chapter declared for it, where it declared one
// (index.Definition.Notation).
type ProofConstant struct {
	Name     string `json:"name"`
	Notation string `json:"notation,omitempty"`
}

// ProofEdge says S stands on T, no drawn unit between them; Via
// marks one that is no direct citation. Where T is of the ground the
// edge is a direct citation, whatever lies between. It leaves T's right
// side at Y1 and reaches S's left side at Y2.
type ProofEdge struct {
	S   string  `json:"s"`
	T   string  `json:"t"`
	Via bool    `json:"via,omitzero"`
	Y1  float64 `json:"y1"`
	Y2  float64 `json:"y2"`
}

// _ProofGrainRule is a grain: the allowance a family's spread has over
// the target family's before the family is ambient, the theorems a
// candidate's steps must count, and the apexes a family may show.
type _ProofGrainRule struct {
	key       string
	allowance int
	theorems  int
	perFamily int
}

// proofGrains are the grains, the coarsest first.
var proofGrains = []_ProofGrainRule{
	{key: "compact", allowance: 11, theorems: 5, perFamily: 1},
	{key: "standard", allowance: 24, theorems: 3, perFamily: 2},
	{key: "deep", allowance: 49, theorems: 3, perFamily: 2},
}

// _Cone is a cone as a graph reads it — a unit's, or several units'
// together: the units in id
// order, each with its family, whether it is a theorem, whether it is
// a result (_Fold.result), whether it is a card, and its deps;
// a unit's steps as a bitset over the cone's units of its family
// (place its bit there), with their count and the count of theorems
// among them.
type _Cone struct {
	units    []string
	index    map[string]int
	family   []string
	theorem  []bool
	result   []bool
	card     []bool
	deps     [][]int
	depIDs   [][]string
	place    []int
	within   [][]uint64
	steps    []int
	theorems []int
	// counted is what under has counted, by unit.
	counted map[int][2]int
}

// cone reads the cone of the units given: they, and every unit one of
// them stands on.
func (fold *_Fold) cone(roots ...string) *_Cone {
	seen := map[string]bool{}
	k := &_Cone{index: map[string]int{}, counted: map[int][2]int{}}
	for _, root := range roots {
		if !seen[root] {
			seen[root] = true
			k.units = append(k.units, root)
		}
	}
	for at := 0; at < len(k.units); at++ {
		for _, d := range fold.deps(k.units[at]) {
			if !seen[d] {
				seen[d] = true
				k.units = append(k.units, d)
			}
		}
	}
	sort.Strings(k.units)
	n := len(k.units)
	k.family, k.theorem, k.result, k.card = make([]string, n), make([]bool, n), make([]bool, n), make([]bool, n)
	k.deps, k.depIDs = make([][]int, n), make([][]string, n)
	for i, u := range k.units {
		k.index[u], k.family[i], k.theorem[i], k.result[i] = i, fold.family(u), fold.theorem(u), fold.result(u)
		k.card[i] = fold.byDoor[u] == nil && fold.byID[u].Card
	}
	for i, u := range k.units {
		k.depIDs[i] = fold.deps(u)
		for _, d := range k.depIDs[i] {
			k.deps[i] = append(k.deps[i], k.index[d])
		}
	}

	// A unit's steps are itself and its deps' in its family; the walk
	// needs no guard, the units' relation being acyclic (reduceScope).
	size := map[string]int{}
	k.place = make([]int, n)
	for i := range k.units {
		k.place[i] = size[k.family[i]]
		size[k.family[i]]++
	}
	theorems := map[string][]uint64{}
	for i := range k.units {
		f := k.family[i]
		if theorems[f] == nil {
			theorems[f] = make([]uint64, (size[f]+63)/64)
		}
		if k.theorem[i] {
			theorems[f][k.place[i]/64] |= 1 << (k.place[i] % 64)
		}
	}
	k.within, k.steps, k.theorems = make([][]uint64, n), make([]int, n), make([]int, n)
	var walk func(i int) []uint64
	walk = func(i int) []uint64 {
		if k.within[i] != nil {
			return k.within[i]
		}
		set := make([]uint64, (size[k.family[i]]+63)/64)
		set[k.place[i]/64] |= 1 << (k.place[i] % 64)
		for _, d := range k.deps[i] {
			if k.family[d] == k.family[i] {
				for w, word := range walk(d) {
					set[w] |= word
				}
			}
		}
		k.within[i] = set
		for w, word := range set {
			k.steps[i] += bits.OnesCount64(word)
			k.theorems[i] += bits.OnesCount64(word & theorems[k.family[i]][w])
		}
		return set
	}
	for i := range k.units {
		walk(i)
	}
	return k
}

// under counts the results a unit stands on (_Fold.result), by one
// citation or through others, and the cards among them. A unit is
// counted once, however many grains draw it.
func (k *_Cone) under(u int) (theorems, cards int) {
	if counted, done := k.counted[u]; done {
		return counted[0], counted[1]
	}
	defer func() { k.counted[u] = [2]int{theorems, cards} }()
	seen := map[int]bool{u: true}
	for reached := []int{u}; len(reached) > 0; {
		at := reached[len(reached)-1]
		reached = reached[:len(reached)-1]
		for _, d := range k.deps[at] {
			if seen[d] {
				continue
			}
			seen[d] = true
			reached = append(reached, d)
			if k.result[d] {
				theorems++
			}
			if k.card[d] {
				cards++
			}
		}
	}
	return theorems, cards
}

// cards are the cards a unit of the cone stands on, by one citation or
// through others, in id order: in the unit's own cone, every card of it
// but the unit.
func (k *_Cone) cards(u int) []int {
	seen := map[int]bool{u: true}
	var cards []int
	for reached := []int{u}; len(reached) > 0; {
		at := reached[len(reached)-1]
		reached = reached[:len(reached)-1]
		for _, d := range k.deps[at] {
			if !seen[d] {
				seen[d] = true
				reached = append(reached, d)
				if k.card[d] {
					cards = append(cards, d)
				}
			}
		}
	}
	sort.Ints(cards)
	return cards
}

// among says whether u is one of v's steps.
func (k *_Cone) among(u, v int) bool {
	return k.family[u] == k.family[v] && k.within[v][k.place[u]/64]>>(k.place[u]%64)&1 == 1
}

// chapter is the part of the target's own family a proof graph draws,
// in id order: the target, the family's theorems in the cone, and the
// family's definitions those cite that the target cites or two of them
// cite — every one when they are three or fewer.
func (k *_Cone) chapter(target int) []int {
	own := k.family[target]
	var theorems []int
	for i := range k.units {
		if i == target || k.family[i] == own && k.theorem[i] {
			theorems = append(theorems, i)
		}
	}
	citers := map[int]int{}
	for _, u := range theorems {
		for _, d := range k.deps[u] {
			if k.family[d] == own && !k.theorem[d] {
				citers[d]++
			}
		}
	}
	kept := slices.Clone(theorems)
	for d, n := range citers {
		if n >= 2 || len(citers) <= 3 || slices.Contains(k.deps[target], d) {
			kept = append(kept, d)
		}
	}
	sort.Ints(kept)
	return slices.Compact(kept)
}

// familySpread counts, for every family, the families that stand on
// it: its importers, and theirs.
func familySpread(c *index.Corpus) map[string]int {
	at := map[string]int{}
	for i, f := range c.Families {
		at[f.Name] = i
	}
	byHeight := slices.Clone(c.Families)
	sort.SliceStable(byHeight, func(i, j int) bool { return byHeight[i].Height > byHeight[j].Height })
	above := make([][]uint64, len(c.Families))
	spread := map[string]int{}
	for _, f := range byHeight {
		set := make([]uint64, (len(c.Families)+63)/64)
		for _, importer := range f.Importers {
			j := at[importer]
			if above[j] == nil {
				panic(fmt.Sprintf("visualize: proof graph: %s imports %s and is no higher", importer, f.Name))
			}
			set[j/64] |= 1 << (j % 64)
			for w, word := range above[j] {
				set[w] |= word
			}
		}
		above[at[f.Name]] = set
		for _, word := range set {
			spread[f.Name] += bits.OnesCount64(word)
		}
	}
	return spread
}

// ambient says whether a unit's family is ambient at a grain, given
// the family the graph's target is of.
func (k *_Cone) ambient(u int, own string, spread map[string]int, rule _ProofGrainRule) bool {
	return spread[k.family[u]]-spread[own] > rule.allowance
}

// apexes are the apexes of the other families at a grain, given the
// chapter drawn: see the rule above. They are those of the families
// that are not ambient, found among those families; or, where grounds
// is set, those of the ambient families, found in the whole cone.
func (k *_Cone) apexes(chapter []int, spread map[string]int, rule _ProofGrainRule, grounds bool) []int {
	own := k.family[chapter[0]]
	active := make([]bool, len(k.units))
	for i := range k.units {
		active[i] = grounds || !k.ambient(i, own, spread, rule)
	}
	direct := map[int]bool{}
	for _, u := range chapter {
		for _, d := range k.deps[u] {
			if active[d] && k.theorem[d] && k.family[d] != own {
				direct[d] = true
			}
		}
	}
	// citing is, per theorem cited from another family, those families.
	citing := map[int]map[string]bool{}
	for u := range k.units {
		if !active[u] {
			continue
		}
		for _, d := range k.deps[u] {
			if active[d] && k.theorem[d] && k.family[d] != k.family[u] {
				if citing[d] == nil {
					citing[d] = map[string]bool{}
				}
				citing[d][k.family[u]] = true
			}
		}
	}
	cited := map[string][]int{}
	for d := range k.units {
		if citing[d] != nil {
			cited[k.family[d]] = append(cited[k.family[d]], d)
		}
	}
	var drawn []int
	for _, theorems := range cited {
		var candidates []int
		for _, u := range theorems {
			if k.theorems[u] >= rule.theorems || direct[u] && k.theorems[u] >= 2 {
				candidates = append(candidates, u)
			}
		}
		subsumed := func(u int) bool {
			return slices.ContainsFunc(candidates, func(v int) bool {
				if v == u || !k.among(u, v) {
					return false
				}
				for family := range citing[u] {
					if !citing[v][family] {
						return false
					}
				}
				return true
			})
		}
		var left []int
		largest, limit := 0, rule.perFamily
		for _, u := range candidates {
			if direct[u] || !subsumed(u) {
				left = append(left, u)
				largest = max(largest, k.steps[u])
			}
		}
		if slices.ContainsFunc(left, func(u int) bool { return direct[u] }) {
			limit += 2
		}
		var picked []int
		for _, u := range left {
			if direct[u] || float64(k.steps[u]) >= 0.45*float64(largest) {
				picked = append(picked, u)
			}
		}
		sort.SliceStable(picked, func(a, b int) bool {
			u, v := picked[a], picked[b]
			if direct[u] != direct[v] {
				return direct[u]
			}
			if k.steps[u] != k.steps[v] {
				return k.steps[u] > k.steps[v]
			}
			return u < v
		})
		for _, u := range picked[:min(limit, len(picked))] {
			if k.ambient(u, own, spread, rule) == grounds {
				drawn = append(drawn, u)
			}
		}
	}
	return drawn
}

// ground is the units of the ambient families a grain draws, given the
// chapter and the units it draws of the other families, the chapter's
// among them: the ambient families' apexes one of those cites directly.
func (k *_Cone) ground(chapter, over []int, spread map[string]int, rule _ProofGrainRule) []int {
	cited := map[int]bool{}
	for _, u := range over {
		for _, d := range k.deps[u] {
			cited[d] = true
		}
	}
	var drawn []int
	for _, u := range k.apexes(chapter, spread, rule, true) {
		if cited[u] {
			drawn = append(drawn, u)
		}
	}
	return drawn
}

// Proof draws the unit a member or a door call names (_Fold.resolve):
// a theorem's proof at every grain, a definition as what it is built
// from and who uses it (_Fold.definition). A node's gloss is read from
// its chapter file or README: a file that declares nothing where the
// registry has the node's member is an error, and so is a README that
// cannot be read.
func Proof(c *index.Corpus, ref string) (*ProofGraph, error) {
	fold := foldDoors(c)
	target, err := fold.resolve(ref)
	if err != nil {
		return nil, err
	}
	g := fold.draw(target, familySpread(c))
	if err := fold.gloss(g); err != nil {
		return nil, err
	}
	return g, nil
}

// draw draws a unit's graph, its nodes not yet glossed; spread is the
// corpus's (familySpread). The cards, and the units a card target cites,
// are drawn at every grain, after the ground is chosen, which they leave
// as it is.
func (fold *_Fold) draw(target string, spread map[string]int) *ProofGraph {
	g := &ProofGraph{Target: target, Name: fold.name(target)}
	if !fold.theorem(target) {
		fold.definition(g)
		return g
	}
	k := fold.cone(target)
	at := k.index[target]
	chapter := k.chapter(at)
	cards := k.cards(at)
	var cited []int
	if k.card[at] {
		cited = k.deps[at]
	}
	for _, rule := range proofGrains {
		drawn := append(slices.Clone(chapter), k.apexes(chapter, spread, rule, false)...)
		drawn = append(drawn, k.ground(chapter, drawn, spread, rule)...)
		drawn = append(drawn, cards...)
		drawn = append(drawn, cited...)
		sort.Ints(drawn)
		drawn = slices.Compact(drawn)
		under := func(u int) bool { return k.ambient(u, k.family[at], spread, rule) }
		g.Grains = append(g.Grains, fold.grain(k, at, drawn, under, rule))
	}
	return g
}

// statements are the statements of a unit's members, in the unit's
// order of them. A constant a member mints is one the index has a
// definition of.
func (fold *_Fold) statements(u string) []ProofStatement {
	members := fold.members(u)
	stated := make([]ProofStatement, len(members))
	for i, m := range members {
		stated[i] = ProofStatement{Member: m.ID[strings.LastIndex(m.ID, ".")+1:], Text: m.Statement, Abbreviations: m.Abbreviations,
			Reading: m.Reading, Shape: m.Shape, Type: m.DefinesType}
		for _, name := range m.Defines {
			d := fold.corpus.DefinitionOf(name)
			if d == nil {
				panic(fmt.Sprintf("visualize: %s mints %s, and the index has no definition of it", m.ID, name))
			}
			stated[i].Defines = append(stated[i].Defines, ProofConstant{Name: name, Notation: d.Notation})
		}
	}
	return stated
}

// node is a unit of a cone as a node carries it, where it is drawn left
// to the layout.
func (fold *_Fold) node(k *_Cone, place int, own string) ProofNode {
	u := k.units[place]
	theorems, cards := k.under(place)
	return ProofNode{
		ID: u, Name: fold.name(u), Family: k.family[place],
		Own: k.family[place] == own, Definition: !k.theorem[place],
		Steps:  k.steps[place],
		Status: fold.status(u), Theorems: theorems, Cards: cards, Statements: fold.statements(u),
	}
}

// gloss gives every node its gloss, each unit's read once and its
// formulas typeset, the units side by side. A node standing for a
// family has the family's (index.Family.Gloss); one standing for the
// families not drawn has none.
func (fold *_Fold) gloss(g *ProofGraph) error {
	var units []string
	seen := map[string]bool{}
	for _, grain := range g.Grains {
		for _, n := range grain.Nodes {
			if !seen[n.ID] {
				seen[n.ID] = true
				units = append(units, n.ID)
			}
		}
	}
	glosses, errs := make([]string, len(units)), make([]error, len(units))
	var reading sync.WaitGroup
	for i, u := range units {
		reading.Go(func() {
			switch {
			case u == usesMoreID:
				return
			case fold.byFamily[u] != nil:
				glosses[i] = fold.byFamily[u].Gloss
			default:
				if glosses[i], errs[i] = fold.corpus.Description(fold.members(u)[0]); errs[i] != nil {
					return
				}
			}
			if glosses[i], errs[i] = typeset(glosses[i]); errs[i] != nil {
				errs[i] = fmt.Errorf("visualize: the gloss of %s: %v", u, errs[i])
			}
		})
	}
	reading.Wait()
	gloss := map[string]string{}
	for i, u := range units {
		if errs[i] != nil {
			return errs[i]
		}
		gloss[u] = glosses[i]
	}
	for _, grain := range g.Grains {
		for i := range grain.Nodes {
			grain.Nodes[i].Gloss = gloss[grain.Nodes[i].ID]
		}
	}
	return nil
}

// A proof graph's page, in the units of its viewBox: a node's height,
// the distance between two nodes of a column and between two columns,
// the height the columns are first centred on, the top of the highest
// node, and the distance from the ground's line to the nearest node on
// either side. A
// column's width is proofGraphLetter for each letter of its longest
// name, or proofGraphFamilyLetter for each of its longest family line
// — the advances of the page's two label types — and proofGraphPad for
// the two ends.
const (
	proofGraphBlock        = 26.0
	proofGraphStep         = proofGraphBlock + 7.0
	proofGraphColumn       = 32.0
	proofGraphCentre       = 500.0
	proofGraphTop          = 16.0
	proofGraphApart        = 26.0
	proofGraphLetter       = 5.6
	proofGraphFamilyLetter = 4.7
	proofGraphPad          = 14.0
)

// familyTail is a family's last two path segments, what a node says of
// its family.
func familyTail(family string) string {
	parts := strings.Split(family, "/")
	if len(parts) <= 2 {
		return family
	}
	return strings.Join(parts[len(parts)-2:], "/")
}

// spaced is the heights nearest the aims, in least squares, that keep
// the aims' order and at least step between two neighbours — an
// isotonic regression by pooling adjacent violators (placeRow).
func spaced(aims []float64, step float64) []float64 {
	type group struct {
		sum   float64
		count int
	}
	var groups []group
	for i, aim := range aims {
		groups = append(groups, group{aim - float64(i)*step, 1})
		for n := len(groups); n >= 2 && groups[n-2].sum/float64(groups[n-2].count) > groups[n-1].sum/float64(groups[n-1].count); n = len(groups) {
			groups[n-2].sum += groups[n-1].sum
			groups[n-2].count += groups[n-1].count
			groups = groups[:n-1]
		}
	}
	at := make([]float64, 0, len(aims))
	for _, g := range groups {
		for range g.count {
			at = append(at, g.sum/float64(g.count)+float64(len(at))*step)
		}
	}
	return at
}

// _ProofColumns is a grain while it is laid out, or one of its two
// parts. The drawn units are numbered in id order; deps and citers are
// a unit's edges, column its column and centre the height of its centre
// line; columns lists each column top to bottom. A part (part) has the
// grain's units, columns and heights, and of the edges and of each
// column's units those of its side of the line.
type _ProofColumns struct {
	ids     []string
	family  []string
	deps    [][]int
	citers  [][]int
	column  []int
	centre  []float64
	columns [][]int
}

// part is the grain's part on one side of the line: under says of each
// unit whether it is drawn under it.
func (p *_ProofColumns) part(under []bool, side bool) *_ProofColumns {
	q := &_ProofColumns{ids: p.ids, family: p.family, column: p.column, centre: p.centre,
		deps: make([][]int, len(p.ids)), citers: make([][]int, len(p.ids)), columns: make([][]int, len(p.columns))}
	within := func(units []int) []int {
		var kept []int
		for _, u := range units {
			if under[u] == side {
				kept = append(kept, u)
			}
		}
		return kept
	}
	for u := range p.ids {
		if under[u] == side {
			q.deps[u], q.citers[u] = within(p.deps[u]), within(p.citers[u])
		}
	}
	for col, units := range p.columns {
		q.columns[col] = within(units)
	}
	return q
}

// place sets the heights of the units: the columns right to left, each
// under the units standing on it; then ten rounds left to right and
// back, each column between its neighbours on both sides, the last
// column left where it is.
func (p *_ProofColumns) place() {
	last := len(p.columns) - 1
	for col := last; col >= 0; col-- {
		first := map[int]float64{}
		for _, u := range p.columns[col] {
			first[u] = p.aim(u, p.citers[u], nil, proofGraphCentre)
		}
		p.settle(col, first, false, 0.28)
	}
	aims := func(col int, forward bool) map[int]float64 {
		of := map[int]float64{}
		for _, u := range p.columns[col] {
			if forward {
				of[u] = p.aim(u, p.deps[u], p.citers[u], p.centre[u])
			} else {
				of[u] = p.aim(u, p.citers[u], p.deps[u], p.centre[u])
			}
		}
		return of
	}
	for range 10 {
		for col := 1; col < last; col++ {
			p.settle(col, aims(col, true), true, 0.20)
		}
		for col := last - 1; col >= 0; col-- {
			p.settle(col, aims(col, false), true, 0.20)
		}
	}
}

// span is the top of the highest of the units and the foot of the
// lowest, over the columns.
func (p *_ProofColumns) span() (top, foot float64) {
	top, foot = math.Inf(1), math.Inf(-1)
	for _, units := range p.columns {
		for _, u := range units {
			top = math.Min(top, p.centre[u]-proofGraphBlock*0.5)
			foot = math.Max(foot, p.centre[u]+proofGraphBlock*0.5)
		}
	}
	return top, foot
}

// shift moves the units down by a distance.
func (p *_ProofColumns) shift(down float64) {
	for _, units := range p.columns {
		for _, u := range units {
			p.centre[u] += down
		}
	}
}

// aim is the weighted mean height of a unit's neighbours, first and
// then second: a neighbour one column away counts 1.5, one d columns
// away 1/d. A unit with none aims at otherwise. The products are
// rounded before they are added (_FamilyRows.aimAt).
func (p *_ProofColumns) aim(u int, first, second []int, otherwise float64) float64 {
	sum, total := 0.0, 0.0
	for _, neighbours := range [2][]int{first, second} {
		for _, v := range neighbours {
			weight := 1.5
			if d := p.column[v] - p.column[u]; d != 1 && d != -1 {
				weight = 1 / math.Abs(float64(d))
			}
			sum += float64(weight * p.centre[v])
			total += weight
		}
	}
	if total > 0 {
		return sum / total
	}
	return otherwise
}

// crossings counts the pairs of edges that cross between a column, in
// the order given, and the columns on either side: two edges of two
// units to the same side, the upper unit's ending lower.
func (p *_ProofColumns) crossings(order []int) int {
	total := 0
	for i, u := range order {
		for _, v := range order[i+1:] {
			for _, side := range [2][][]int{p.deps, p.citers} {
				for _, a := range side[u] {
					for _, b := range side[v] {
						if p.centre[a] > p.centre[b] {
							total++
						}
					}
				}
			}
		}
	}
	return total
}

// settle orders and places a column by its units' aims: sorted by aim,
// then by family and id; two neighbours whose aims are within 18
// changing places while that lowers the crossings; then spaced, and
// shifted by pull times the distance from the column's mean height to
// the centre. A column with no unit is left as it is.
func (p *_ProofColumns) settle(c int, aims map[int]float64, uncross bool, pull float64) {
	order := p.columns[c]
	if len(order) == 0 {
		return
	}
	sort.SliceStable(order, func(a, b int) bool {
		u, v := order[a], order[b]
		if aims[u] != aims[v] {
			return aims[u] < aims[v]
		}
		if p.family[u] != p.family[v] {
			return p.family[u] < p.family[v]
		}
		return p.ids[u] < p.ids[v]
	})
	if uncross && len(order) > 1 {
		best := p.crossings(order)
		for changed := true; changed; {
			changed = false
			for i := 0; i+1 < len(order); i++ {
				if math.Abs(aims[order[i]]-aims[order[i+1]]) > 18 {
					continue
				}
				order[i], order[i+1] = order[i+1], order[i]
				if n := p.crossings(order); n < best {
					best, changed = n, true
				} else {
					order[i], order[i+1] = order[i+1], order[i]
				}
			}
		}
	}
	wanted := make([]float64, len(order))
	for i, u := range order {
		wanted[i] = aims[u]
	}
	heights := spaced(wanted, proofGraphStep)
	sum := 0.0
	for _, y := range heights {
		sum += y
	}
	shift := pull * (proofGraphCentre - sum/float64(len(heights)))
	for i, u := range order {
		p.centre[u] = heights[i] + shift
	}
}

// grain lays out the drawn units of a cone, given by their places in
// it in id order, the target among them; ambient says which of them
// are drawn under the line.
func (fold *_Fold) grain(k *_Cone, target int, drawn []int, ambient func(int) bool, rule _ProofGrainRule) ProofGrain {
	n := len(drawn)
	p := &_ProofColumns{ids: make([]string, n), family: make([]string, n), deps: make([][]int, n), citers: make([][]int, n),
		column: make([]int, n), centre: make([]float64, n)}
	at := map[string]int{}
	under := make([]bool, n)
	for i, u := range drawn {
		p.ids[i], p.family[i], under[i] = k.units[u], k.family[u], ambient(u)
		at[k.units[u]] = i
	}
	head := at[k.units[target]]
	var above []string
	for i, id := range p.ids {
		if !under[i] {
			above = append(above, id)
		}
	}
	deps := func(id string) []string { return k.depIDs[k.index[id]] }
	edges := reduceScope(above, deps)
	citedBelow := map[string]bool{}
	for _, id := range p.ids {
		cited := map[string]bool{}
		for _, d := range deps(id) {
			if t, drawn := at[d]; drawn && under[t] && !cited[d] {
				cited[d] = true
				citedBelow[d] = true
				edges = append(edges, _Edge{S: id, T: d})
			}
		}
	}
	// A unit of the ground no drawn unit cites directly is joined to
	// the drawn units nearest that stand on it.
	alone := map[string]bool{}
	for i, id := range p.ids {
		if under[i] && !citedBelow[id] {
			alone[id] = true
		}
	}
	if len(alone) > 0 {
		for _, e := range reduceScope(p.ids, deps) {
			if alone[e.T] {
				edges = append(edges, e)
			}
		}
	}
	for _, e := range edges {
		s, t := at[e.S], at[e.T]
		p.deps[s] = append(p.deps[s], t)
		p.citers[t] = append(p.citers[t], s)
	}

	// The columns: the longest chain of edges under the target numbers
	// them, the target in the last, and a unit sits one column left of
	// the leftmost unit standing on it.
	depth := make([]int, n)
	for i := range depth {
		depth[i] = -1
	}
	var deep func(u int) int
	deep = func(u int) int {
		if depth[u] < 0 {
			depth[u] = 0
			for _, v := range p.deps[u] {
				depth[u] = max(depth[u], deep(v)+1)
			}
		}
		return depth[u]
	}
	last := 0
	for u := range n {
		last = max(last, deep(u))
	}
	for i := range p.column {
		p.column[i] = -1
	}
	var columnOf func(u int) int
	columnOf = func(u int) int {
		if p.column[u] < 0 {
			p.column[u] = last
			for _, s := range p.citers[u] {
				p.column[u] = min(p.column[u], columnOf(s)-1)
			}
		}
		return p.column[u]
	}
	p.columns = make([][]int, last+1)
	for u := range n {
		col := columnOf(u)
		if col < 0 || u != head && len(p.citers[u]) == 0 {
			panic(fmt.Sprintf("visualize: proof graph: %s is drawn in column %d of %d, %d units standing on it", p.ids[u], col, last+1, len(p.citers[u])))
		}
		p.columns[col] = append(p.columns[col], u)
	}
	for col, units := range p.columns {
		if len(units) == 0 {
			panic(fmt.Sprintf("visualize: proof graph: column %d of %s's graph is empty", col, k.units[target]))
		}
	}

	// A column is as wide as the longest label of its nodes.
	g := ProofGrain{Key: rule.key, Allowance: rule.allowance, Theorems: rule.theorems, PerFamily: rule.perFamily,
		Block: proofGraphBlock, Nodes: []ProofNode{}, Edges: []ProofEdge{}}
	x := 24.0
	for _, units := range p.columns {
		widest := 0.0
		for _, u := range units {
			name := utf8.RuneCountInString(fold.name(p.ids[u]))
			family := utf8.RuneCountInString(familyTail(p.family[u]))
			widest = math.Max(widest, math.Max(float64(name)*proofGraphLetter, float64(family)*proofGraphFamilyLetter))
		}
		w := round1(widest + proofGraphPad)
		g.Columns = append(g.Columns, ProofColumn{X: round1(x), W: w})
		x += w + proofGraphColumn
	}
	g.Width = int(math.Ceil(g.Columns[last].X + g.Columns[last].W + 24))

	// The heights: each part by itself, the part over the line from the
	// top of the page, the line under its lowest node, and the ground
	// under the line.
	over, ambients := p.part(under, false), p.part(under, true)
	over.place()
	top, foot := over.span()
	over.shift(proofGraphTop - top)
	foot += proofGraphTop - top
	if slices.Contains(under, true) {
		ambients.place()
		g.Line = round1(foot + proofGraphApart)
		top, _ = ambients.span()
		ambients.shift(g.Line + proofGraphApart - top)
		_, foot = ambients.span()
	}
	g.Height = max(120, int(math.Ceil(foot+18)))
	g.Axis = round1(p.centre[head])
	for col := range p.columns {
		p.columns[col] = append(over.columns[col], ambients.columns[col]...)
	}

	for col, units := range p.columns {
		left, w := g.Columns[col].X, g.Columns[col].W
		if left < 12 || left+w > float64(g.Width)-12 {
			panic(fmt.Sprintf("visualize: proof graph: column %d runs past a margin, from %v to %v of %d", col, left, left+w, g.Width))
		}
		for i, u := range units {
			y := p.centre[u] - proofGraphBlock*0.5
			if i > 0 && p.centre[units[i-1]]+proofGraphBlock+6.5 > p.centre[u]+1e-6 {
				panic(fmt.Sprintf("visualize: proof graph: %s and %s overlap in column %d", p.ids[units[i-1]], p.ids[u], col))
			}
			if y < proofGraphTop-0.5 || y+proofGraphBlock > float64(g.Height)-8 {
				panic(fmt.Sprintf("visualize: proof graph: %s runs past a margin, from %v to %v of %d", p.ids[u], y, y+proofGraphBlock, g.Height))
			}
			n := fold.node(k, k.index[p.ids[u]], p.family[head])
			n.Column, n.Ambient, n.Target = col, under[u], u == head
			n.X, n.Y, n.W = left, round1(y), w
			g.Nodes = append(g.Nodes, n)
		}
	}

	// A unit's edges are spread along its side in the order of the
	// heights they run to, 3.5 apart and over 14 at most.
	port := func(u int, others []int) map[int]float64 {
		order := slices.Clone(others)
		sort.SliceStable(order, func(a, b int) bool {
			if p.centre[order[a]] != p.centre[order[b]] {
				return p.centre[order[a]] < p.centre[order[b]]
			}
			return p.ids[order[a]] < p.ids[order[b]]
		})
		at := map[int]float64{}
		span := math.Min(14, float64(len(order)-1)*3.5)
		for j, o := range order {
			if len(order) == 1 {
				at[o] = round1(p.centre[u])
			} else {
				at[o] = round1(p.centre[u] + (-span*0.5 + span*float64(j)/float64(len(order)-1)))
			}
		}
		return at
	}
	right, left := make([]map[int]float64, n), make([]map[int]float64, n)
	for u := range n {
		right[u], left[u] = port(u, p.citers[u]), port(u, p.deps[u])
	}
	for _, e := range edges {
		s, t := at[e.S], at[e.T]
		if p.column[t] >= p.column[s] {
			panic(fmt.Sprintf("visualize: proof graph: %s stands on %s and is drawn no further right", e.S, e.T))
		}
		g.Edges = append(g.Edges, ProofEdge{S: e.S, T: e.T, Via: e.Via, Y1: right[t][s], Y2: left[s][t]})
	}
	return g
}
