package visualize

// A definition's graph: what the definition is built from, the
// definition, and who uses it, left to right.
//
// A definition stands on definitions, and the rule that draws a proof
// picks theorems, so a definition's proof graph would most often be the
// definition alone. Its page draws instead what a reader asks of a
// definition, once and at no grain.
//
// Left of it, what it is built from: every unit it cites, and every
// card it stands on, as on a theorem's page; laid out as a proof graph's
// nodes are (_Fold.grain) with no family ambient — an edge says one
// stands on the other with no drawn unit between them, and a unit sits
// one column left of the leftmost unit standing on it.
//
// Right of it, in one column, who uses it. A unit uses a definition
// where it stands on it — its proof cites the definition or opens a
// constant of it — or where its statement names a constant the
// definition mints: the index's two relations together
// (index.Member.Dependents, index.Corpus.UsedBy).
// How it uses it is one of three:
//
//   - defines: a definition whose statement names one of the constants;
//   - about: a theorem whose statement names one — a theorem about the
//     definition, wherever in the statement the name stands: a
//     hypothesis and a conclusion change places with the statement's
//     phrasing;
//   - cites: its statement names none, and its proof cites the
//     definition or opens a constant of it.
//
// The users of the definition's own family are drawn one by one, in
// those three groups, each in the chapter's order. Every other family is
// drawn as one node standing for its users, the family with the most
// first; where the families are more than usesFamilies, the last of
// those nodes stands for all that are left. Each group is under a
// heading, and an edge runs from the definition to every node of the
// column: the column is centred on the definition, and what is left of
// it is moved down where the column is the taller.

import (
	"fmt"
	"math"
	"slices"
	"sort"
	"strconv"
	"unicode/utf8"
)

// ProofDefinition counts who uses a definition: Users the units, and
// Families their families — the definition's own first, where a unit of
// it uses the definition, then the others, the one with the most users
// first. Uses are the three uses a unit may make of it, in the order a
// page lists them, each with its heading's words.
type ProofDefinition struct {
	Users    int               `json:"users"`
	Families []ProofFamilyUses `json:"families"`
	Uses     []ProofUse        `json:"uses"`
}

// ProofUse is a use a unit may make of a definition, and the words its
// group is headed by.
type ProofUse struct {
	Use   string `json:"use"`
	Label string `json:"label"`
}

// ProofFamilyUses is a family's units that use a definition: Count of
// them, and for a family drawn as one node the units themselves, by how
// they use it and then in the chapter's order.
type ProofFamilyUses struct {
	Family string      `json:"family"`
	Count  int         `json:"count"`
	Users  []ProofUser `json:"users,omitempty"`
}

// ProofUser is a unit that uses a definition: its name, how it uses
// the definition, and its stratum where that is not "proved".
type ProofUser struct {
	Name   string `json:"name"`
	Use    string `json:"use"`
	Status string `json:"status,omitempty"`
}

// ProofGroup is a heading in the column right of a definition: the use
// the nodes under it share, the heading's words, the count it gives —
// the nodes under it, or the other families, drawn or not — and where
// the words begin, X their left end and Y their baseline.
type ProofGroup struct {
	Use   string  `json:"use"`
	Label string  `json:"label"`
	Count int     `json:"count"`
	X     float64 `json:"x"`
	Y     float64 `json:"y"`
}

// How a unit uses a definition (ProofNode.Use, ProofUser.Use), and the
// use of the two nodes that stand for no unit: a family's users, and
// the families not drawn.
const (
	useDefines = "defines"
	useAbout   = "about"
	useCites   = "cites"
	useFamily  = "family"
	useMore    = "more"
)

// useGroups are the groups of the column right of a definition, top to
// bottom, each with its heading's words.
var useGroups = []struct{ use, label string }{
	{useDefines, "definitions built on it"},
	{useAbout, "theorems about it"},
	{useCites, "cite it in a proof"},
	{useFamily, "other families"},
}

// A definition's users on the page: usesFamilies is how many nodes the
// other families take at most, usesMoreID the id of the node standing
// for the families not drawn — no unit's and no family's. In the units
// of the page's viewBox, usesColumn is the distance from the
// definition's column to the users', wider than two columns stand apart
// for the edges that fan out across it, usesHeading the height a
// group's heading takes over its first node, and usesApart the distance
// more between two groups.
const (
	usesFamilies = 24
	usesMoreID   = "…"
	usesColumn   = 48.0
	usesHeading  = 13.0
	usesApart    = 10.0
)

// usesLine is the line under the name of a node standing for families:
// the units it stands for, as the page counts them.
func usesLine(users int) string {
	if users == 1 {
		return "1 user"
	}
	return strconv.Itoa(users) + " users"
}

// _Use is a unit that uses a definition, and how.
type _Use struct {
	unit, use string
}

// use is how a unit uses a definition minting the constants given.
func (fold *_Fold) use(u string, minted map[string]bool) string {
	states := false
	for _, m := range fold.members(u) {
		for _, name := range m.Constants {
			states = states || minted[name]
		}
	}
	switch {
	case !states:
		return useCites
	case !fold.theorem(u):
		return useDefines
	}
	return useAbout
}

// users are the units that use a definition, by family: each family's
// by use, in useGroups' order, and then in the chapter's order, a
// unit's place there its first member's.
func (fold *_Fold) users(target string) (byFamily map[string][]_Use) {
	minted := map[string]bool{}
	using := map[string]bool{}
	for _, m := range fold.members(target) {
		for _, name := range m.Defines {
			minted[name] = true
		}
		for _, id := range m.Dependents {
			using[fold.of(id)] = true
		}
		for _, use := range fold.corpus.UsedBy(m) {
			using[fold.of(use.Member)] = true
		}
	}
	delete(using, target)

	rank := map[string]int{}
	for i, group := range useGroups {
		rank[group.use] = i
	}
	byFamily = map[string][]_Use{}
	for u := range using {
		family := fold.family(u)
		byFamily[family] = append(byFamily[family], _Use{unit: u, use: fold.use(u, minted)})
	}
	for family, uses := range byFamily {
		place := map[string]int{}
		for i, m := range fold.byFamily[family].Members {
			if _, placed := place[fold.of(m.ID)]; !placed {
				place[fold.of(m.ID)] = i
			}
		}
		sort.Slice(uses, func(a, b int) bool {
			if rank[uses[a].use] != rank[uses[b].use] {
				return rank[uses[a].use] < rank[uses[b].use]
			}
			return place[uses[a].unit] < place[uses[b].unit]
		})
	}
	return byFamily
}

// definition draws a definition's graph: see the rule above.
func (fold *_Fold) definition(g *ProofGraph) {
	own := fold.family(g.Target)
	byFamily := fold.users(g.Target)

	// The other families, the one with the most users first.
	var others []string
	total := 0
	for family, uses := range byFamily {
		total += len(uses)
		if family != own {
			others = append(others, family)
		}
	}
	sort.Slice(others, func(a, b int) bool {
		if len(byFamily[others[a]]) != len(byFamily[others[b]]) {
			return len(byFamily[others[a]]) > len(byFamily[others[b]])
		}
		return others[a] < others[b]
	})
	folded := len(others)
	if folded > usesFamilies {
		folded = usesFamilies - 1
	}

	g.Definition = &ProofDefinition{Users: total, Families: []ProofFamilyUses{}}
	for _, of := range useGroups {
		if of.use != useFamily {
			g.Definition.Uses = append(g.Definition.Uses, ProofUse{Use: of.use, Label: of.label})
		}
	}
	if len(byFamily[own]) > 0 {
		g.Definition.Families = append(g.Definition.Families, ProofFamilyUses{Family: own, Count: len(byFamily[own])})
	}
	for i, family := range others {
		uses := ProofFamilyUses{Family: family, Count: len(byFamily[family])}
		if i < folded {
			for _, u := range byFamily[family] {
				user := ProofUser{Name: fold.name(u.unit), Use: u.use}
				if status := fold.status(u.unit); status != "proved" {
					user.Status = status
				}
				uses.Users = append(uses.Users, user)
			}
		}
		g.Definition.Families = append(g.Definition.Families, uses)
	}

	// What the definition is built from, the definition in the last of
	// those columns; the cone holds its own family's users too, to be
	// drawn as nodes.
	roots := []string{g.Target}
	for _, u := range byFamily[own] {
		roots = append(roots, u.unit)
	}
	k := fold.cone(roots...)
	at := k.index[g.Target]
	drawn := append([]int{at}, k.deps[at]...)
	drawn = append(drawn, k.cards(at)...)
	sort.Ints(drawn)
	drawn = slices.Compact(drawn)
	grain := fold.grain(k, at, drawn, func(int) bool { return false }, _ProofGrainRule{key: "definition"})

	// The column of users, group by group.
	type group struct {
		use, label string
		count      int
		nodes      []ProofNode
		lines      []string
	}
	var groups []group
	for _, of := range useGroups {
		gr := group{use: of.use, label: of.label}
		if of.use == useFamily {
			gr.count = len(others)
			for _, family := range others[:folded] {
				users := len(byFamily[family])
				gr.nodes = append(gr.nodes, ProofNode{ID: family, Name: familyTail(family), Family: family,
					Use: useFamily, Users: users, Statements: []ProofStatement{}})
				gr.lines = append(gr.lines, usesLine(users))
			}
			if left := others[folded:]; len(left) > 0 {
				users := 0
				for _, family := range left {
					users += len(byFamily[family])
				}
				gr.nodes = append(gr.nodes, ProofNode{ID: usesMoreID, Name: fmt.Sprintf("%d more families", len(left)),
					Use: useMore, Users: users, Families: len(left), Statements: []ProofStatement{}})
				gr.lines = append(gr.lines, usesLine(users))
			}
		} else {
			for _, u := range byFamily[own] {
				if u.use == of.use {
					n := fold.node(k, k.index[u.unit], own)
					n.Use = u.use
					gr.nodes = append(gr.nodes, n)
					gr.lines = append(gr.lines, familyTail(n.Family))
				}
			}
			gr.count = len(gr.nodes)
		}
		if len(gr.nodes) > 0 {
			groups = append(groups, gr)
		}
	}
	if len(groups) == 0 {
		g.Grains = []ProofGrain{grain}
		return
	}

	// The column is as wide as the longest of its labels and headings.
	column := len(grain.Columns)
	x := grain.Columns[column-1].X + grain.Columns[column-1].W + usesColumn
	widest, tall := 0.0, 0.0
	for i, gr := range groups {
		heading := fmt.Sprintf("%s · %d", gr.label, gr.count)
		widest = math.Max(widest, float64(utf8.RuneCountInString(heading))*proofGraphFamilyLetter)
		for j, n := range gr.nodes {
			widest = math.Max(widest, float64(utf8.RuneCountInString(n.Name))*proofGraphLetter)
			widest = math.Max(widest, float64(utf8.RuneCountInString(gr.lines[j]))*proofGraphFamilyLetter)
		}
		if i > 0 {
			tall += usesApart
		}
		tall += usesHeading + float64(len(gr.nodes))*proofGraphStep - (proofGraphStep - proofGraphBlock)
	}
	w := round1(widest + proofGraphPad)
	grain.Columns = append(grain.Columns, ProofColumn{X: round1(x), W: w})
	grain.Width = int(math.Ceil(x + w + 24))

	// The column is centred on the definition; what is left of it moves
	// down by whole units where the column would run past the top.
	top := grain.Axis - tall*0.5
	if down := math.Ceil(proofGraphTop - top); down > 0 {
		for i := range grain.Nodes {
			grain.Nodes[i].Y = round1(grain.Nodes[i].Y + down)
		}
		for i := range grain.Edges {
			grain.Edges[i].Y1, grain.Edges[i].Y2 = round1(grain.Edges[i].Y1+down), round1(grain.Edges[i].Y2+down)
		}
		grain.Axis = round1(grain.Axis + down)
		grain.Height += int(down)
		top += down
	}
	first := len(grain.Nodes)
	y := top
	for i, gr := range groups {
		if i > 0 {
			y += usesApart
		}
		grain.Groups = append(grain.Groups, ProofGroup{Use: gr.use, Label: gr.label, Count: gr.count, X: round1(x), Y: round1(y + usesHeading - 4)})
		y += usesHeading
		for _, n := range gr.nodes {
			n.Column, n.X, n.Y, n.W = column, round1(x), round1(y), w
			grain.Nodes = append(grain.Nodes, n)
			y += proofGraphStep
		}
		y -= proofGraphStep - proofGraphBlock
	}
	grain.Height = max(grain.Height, int(math.Ceil(y+18)))

	// The edges leave the definition's right side in the order of the
	// heights they run to, 3.5 apart and over 14 at most (_Fold.grain).
	users := grain.Nodes[first:]
	span := math.Min(14, float64(len(users)-1)*3.5)
	for j, n := range users {
		leaves := grain.Axis
		if len(users) > 1 {
			leaves += -span*0.5 + span*float64(j)/float64(len(users)-1)
		}
		grain.Edges = append(grain.Edges, ProofEdge{S: n.ID, T: g.Target, Y1: round1(leaves), Y2: round1(n.Y + proofGraphBlock*0.5)})
	}
	g.Grains = []ProofGrain{grain}
}
