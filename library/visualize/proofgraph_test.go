package visualize

import (
	"path"
	"slices"
	"sort"
	"testing"
	"unicode/utf8"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/library/index"
)

// A family's spread is the number of families whose imports reach it.
func TestFamilySpread(t *testing.T) {
	c, fold := load(t)
	want := map[string]int{}
	for _, f := range c.Families {
		for reached := range closure(f.Name, func(name string) []string { return fold.byFamily[name].Imports }) {
			want[reached]++
		}
	}
	spread := familySpread(c)
	for _, f := range c.Families {
		require.Equal(t, want[f.Name], spread[f.Name], f.Name)
	}
}

// A proof graph, on a spread of the corpus's theorems, on the theorem
// standing on the most cards and on the card citing the most definitions
// of other families, at every grain, checked against the rule worked out
// the plain way: the target's chapter drawn whole; every card under the
// target drawn, the target's card frontier; every unit a card target
// cites drawn; the other families' other nodes theorems cited from
// outside and within the grain's number; the ambient families' under the line, each but a card
// cited directly from over it, and the rest over it; the edges the
// units' relation reduced over the line, the direct citations under it,
// and the relation reduced over every node drawn into a node under the
// line that no node cites directly, inside the nodes drawn; every node
// one column left of the leftmost node standing on it, in a column as
// wide as its longest label; and the columns' nodes apart, inside the
// page.
func TestProofGraph(t *testing.T) {
	c, fold := load(t)
	spread := familySpread(c)
	deps := map[string][]string{}
	unitDeps := func(u string) []string {
		if _, read := deps[u]; !read {
			deps[u] = fold.deps(u)
		}
		return deps[u]
	}
	// under is, by unit, the theorems it stands on and the cards among
	// them, counted the plain way once.
	under := map[string][2]int{}
	isCard := func(u string) bool { return fold.byDoor[u] == nil && fold.byID[u].Card }
	mostCards := ""
	for _, u := range fold.units() {
		if fold.theorem(u) && (mostCards == "" || len(fold.byID[u].Cards) > len(fold.byID[mostCards].Cards)) {
			mostCards = u
		}
	}
	// citesElsewhere counts the definitions of other families a unit
	// cites: none is drawn but for a card target citing it.
	citesElsewhere := func(u string) int {
		n := 0
		for _, d := range unitDeps(u) {
			if fold.family(d) != fold.family(u) && !fold.theorem(d) {
				n++
			}
		}
		return n
	}
	mostCited := ""
	for _, u := range fold.units() {
		if isCard(u) && (mostCited == "" || citesElsewhere(u) > citesElsewhere(mostCited)) {
			mostCited = u
		}
	}
	drawn, alone, elsewhere := 0, 0, 0
	for _, target := range append(sample(c, fold, 401), mostCards, mostCited) {
		if !fold.theorem(target) {
			continue
		}
		drawn++
		g, err := Proof(c, target)
		require.NoError(t, err, target)
		require.Equal(t, target, g.Target)
		require.Equal(t, fold.name(target), g.Name)
		require.Nil(t, g.Definition, target)
		own := fold.family(target)
		cone := closure(target, unitDeps)
		cone[target] = true
		require.Len(t, g.Grains, len(proofGrains), target)
		// A card has no proof to draw, and every unit it cites is drawn.
		var cites []string
		if isCard(target) {
			cites = unitDeps(target)
		}
		// The target's card frontier, itself aside (index.Member.Cards):
		// what its dossier lists as its plan.
		var plan []string
		for _, m := range fold.members(target) {
			for _, id := range m.Cards {
				if u := fold.of(id); u != target && !slices.Contains(plan, u) {
					plan = append(plan, u)
				}
			}
		}
		for i, grain := range g.Grains {
			rule := proofGrains[i]
			require.Equal(t, rule.key, grain.Key)
			require.Equal(t, []int{rule.allowance, rule.theorems, rule.perFamily}, []int{grain.Allowance, grain.Theorems, grain.PerFamily})
			ambient := 0
			at := map[string]ProofNode{}
			perFamily := map[string]int{}
			var ids []string
			for _, n := range grain.Nodes {
				require.NotContains(t, at, n.ID, "%s is drawn twice", n.ID)
				require.True(t, cone[n.ID], "%s is drawn in the graph of %s and no part of its cone", n.ID, target)
				at[n.ID] = n
				ids = append(ids, n.ID)
				family := fold.family(n.ID)
				require.Equal(t, family, n.Family, n.ID)
				require.Equal(t, fold.name(n.ID), n.Name, n.ID)
				require.Equal(t, family == own, n.Own, n.ID)
				require.Equal(t, n.ID == target, n.Target, n.ID)
				require.Equal(t, !fold.theorem(n.ID), n.Definition, n.ID)
				if _, counted := under[n.ID]; !counted {
					theorems, cards := 0, 0
					for d := range closure(n.ID, unitDeps) {
						if fold.result(d) {
							theorems++
						}
						if fold.byDoor[d] == nil && fold.byID[d].Card {
							cards++
						}
					}
					under[n.ID] = [2]int{theorems, cards}
				}
				require.Equal(t, under[n.ID], [2]int{n.Theorems, n.Cards}, "%s: the results it stands on, and the cards among them", n.ID)
				require.Equal(t, fold.status(n.ID), n.Status, n.ID)
				if m := fold.byID[n.ID]; fold.byDoor[n.ID] == nil {
					// The index's own count: a member's cards are those it stands on, and itself where it is one.
					own := 0
					if m.Card {
						own = 1
					}
					require.Equal(t, len(m.Cards)-own, n.Cards, "%s: the index counts other cards under it", n.ID)
					require.Equal(t, n.Cards > 0 && !m.Card && !m.Postulate, n.Status == "on_cards", n.ID)
				}
				members := fold.members(n.ID)
				require.Len(t, n.Statements, len(members), n.ID)
				for j, m := range members {
					require.Equal(t, stated(c, m), n.Statements[j], m.ID)
					require.NotEmpty(t, m.Statement, m.ID)
				}
				require.Equal(t, [3]any{"", 0, 0}, [3]any{n.Use, n.Users, n.Families}, "%s: only a definition's graph has users", n.ID)
				require.Equal(t, spread[family]-spread[own] > rule.allowance, n.Ambient, "%s at the %s grain", n.ID, rule.key)
				if n.Ambient {
					ambient++
					require.GreaterOrEqual(t, n.Y, grain.Line+proofGraphApart-0.11, "%s is ambient and not under the line", n.ID)
				} else if grain.Line > 0 {
					require.LessOrEqual(t, n.Y+grain.Block, grain.Line-proofGraphApart+0.11, "%s is not ambient and not over the line", n.ID)
				}
				steps := 1
				for range closure(n.ID, func(u string) []string {
					var within []string
					for _, d := range unitDeps(u) {
						if fold.family(d) == family {
							within = append(within, d)
						}
					}
					return within
				}) {
					steps++
				}
				require.Equal(t, steps, n.Steps, n.ID)
				if !n.Own && !isCard(n.ID) && !slices.Contains(cites, n.ID) {
					require.False(t, n.Definition, "%s is a definition of another family", n.ID)
					perFamily[family]++
					require.LessOrEqual(t, perFamily[family], rule.perFamily+2, "%s shows more than the %s grain's number", family, rule.key)
					cited := false
					for u := range cone {
						cited = cited || fold.family(u) != family && slices.Contains(unitDeps(u), n.ID)
					}
					require.True(t, cited, "%s is drawn and no unit of another family cites it", n.ID)
				}
			}
			require.Contains(t, at, target)
			for _, d := range cites {
				require.Contains(t, at, d, "%s is a card and does not draw %s, which it cites, at the %s grain", target, d, rule.key)
				if fold.family(d) != own && !fold.theorem(d) {
					elsewhere++
				}
			}
			require.Equal(t, ambient > 0, grain.Line > 0, "the line is drawn where a node is under it")
			var cards []string
			for _, n := range grain.Nodes {
				if n.ID != target && isCard(n.ID) {
					cards = append(cards, n.ID)
				}
			}
			require.ElementsMatch(t, plan, cards, "%s at the %s grain draws every card it stands on, and no other", target, rule.key)
			if !isCard(target) {
				require.Len(t, cards, at[target].Cards, "%s: the cards drawn are those its node counts", target)
			}
			for _, n := range grain.Nodes {
				if !n.Ambient || isCard(n.ID) {
					continue
				}
				require.True(t, slices.ContainsFunc(grain.Nodes, func(m ProofNode) bool {
					return !m.Ambient && slices.Contains(unitDeps(m.ID), n.ID)
				}), "%s is drawn under the line and no node over it cites it", n.ID)
			}
			for u := range cone {
				if fold.family(u) == own && fold.theorem(u) {
					require.Contains(t, at, u, "a theorem of %s's chapter is not drawn at the %s grain", target, rule.key)
				}
			}

			sort.Strings(ids)
			var over []string
			for _, id := range ids {
				if !at[id].Ambient {
					over = append(over, id)
				}
			}
			want := reduced(over, unitDeps)
			citedBelow := map[string]bool{}
			for _, id := range ids {
				for _, d := range unitDeps(id) {
					if at[d].Ambient {
						want[[2]string{id, d}] = true
						citedBelow[d] = true
					}
				}
			}
			lone := map[string]bool{}
			for _, id := range ids {
				if at[id].Ambient && !citedBelow[id] {
					require.True(t, isCard(id), "%s is under the line, cited by no node, and no card", id)
					lone[id] = true
					alone++
				}
			}
			if len(lone) > 0 {
				for pair, direct := range reduced(ids, unitDeps) {
					if lone[pair[1]] {
						want[pair] = direct
					}
				}
			}
			got := map[[2]string]bool{}
			leftmost := map[string]int{}
			for _, e := range grain.Edges {
				s, t2 := at[e.S], at[e.T]
				got[[2]string{e.S, e.T}] = !e.Via
				require.Less(t, t2.Column, s.Column, "%s stands on %s", e.S, e.T)
				require.True(t, t2.Ambient || !s.Ambient, "%s is ambient and stands on %s, which is not", e.S, e.T)
				if col, seen := leftmost[e.T]; !seen || s.Column < col {
					leftmost[e.T] = s.Column
				}
				require.GreaterOrEqual(t, e.Y1, t2.Y, "%s → %s leaves %s", e.S, e.T, e.T)
				require.LessOrEqual(t, e.Y1, t2.Y+grain.Block, "%s → %s leaves %s", e.S, e.T, e.T)
				require.GreaterOrEqual(t, e.Y2, s.Y, "%s → %s reaches %s", e.S, e.T, e.S)
				require.LessOrEqual(t, e.Y2, s.Y+grain.Block, "%s → %s reaches %s", e.S, e.T, e.S)
			}
			require.Equal(t, want, got, "%s at the %s grain", target, rule.key)

			last := len(grain.Columns) - 1
			require.Equal(t, last, at[target].Column)
			require.InDelta(t, at[target].Y+grain.Block/2, grain.Axis, 0.11)
			columns := make([][]ProofNode, len(grain.Columns))
			widest := make([]float64, len(grain.Columns))
			order := 0
			for _, n := range grain.Nodes {
				name := utf8.RuneCountInString(n.Name)
				line := utf8.RuneCountInString(familyTail(n.Family))
				widest[n.Column] = max(widest[n.Column], float64(name)*proofGraphLetter+proofGraphPad, float64(line)*proofGraphFamilyLetter+proofGraphPad)
				if n.ID != target {
					require.Equal(t, leftmost[n.ID]-1, n.Column, "%s is not one column left of the leftmost node standing on it", n.ID)
				}
				require.Equal(t, grain.Columns[n.Column].X, n.X, n.ID)
				require.Equal(t, grain.Columns[n.Column].W, n.W, n.ID)
				require.GreaterOrEqual(t, n.Y, proofGraphTop-0.051, n.ID)
				require.LessOrEqual(t, n.Y+grain.Block, float64(grain.Height)-8, n.ID)
				if column := columns[n.Column]; len(column) > 0 {
					require.GreaterOrEqual(t, n.Y-column[len(column)-1].Y, grain.Block+6.4, "%s under %s", n.ID, column[len(column)-1].ID)
				} else {
					require.GreaterOrEqual(t, n.Column, order, "the nodes are listed column by column")
					order = n.Column
				}
				columns[n.Column] = append(columns[n.Column], n)
			}
			for col, column := range columns {
				require.NotEmpty(t, column, "column %d of %s at the %s grain", col, target, rule.key)
				require.InDelta(t, widest[col], grain.Columns[col].W, 0.051, "column %d is as wide as its longest label", col)
				if col > 0 {
					require.GreaterOrEqual(t, grain.Columns[col].X, grain.Columns[col-1].X+grain.Columns[col-1].W+proofGraphColumn-0.11)
				}
			}
			require.LessOrEqual(t, grain.Columns[last].X+grain.Columns[last].W, float64(grain.Width)-12)
		}
		again, err := Proof(c, target)
		require.NoError(t, err)
		require.Equal(t, g, again, "a second graph of %s differs from the first", target)
	}
	require.Greater(t, drawn, 15, "the sample holds theorems")
	require.Positive(t, alone, "no node under the line of the sample is cited by no node")
	require.Positive(t, elsewhere, "no card of the sample draws a definition of another family it cites")
}

// stated is a member's statement as a node carries it, read from the
// index the plain way.
func stated(c *index.Corpus, m *index.Member) ProofStatement {
	st := ProofStatement{Member: path.Ext(m.ID)[1:], Text: m.Statement, Abbreviations: m.Abbreviations,
		Reading: m.Reading, Shape: m.Shape, Type: m.DefinesType}
	for _, name := range m.Defines {
		st.Defines = append(st.Defines, ProofConstant{Name: name, Notation: c.DefinitionOf(name).Notation})
	}
	return st
}

// A theorem that stands on nothing is drawn alone; a member a door call
// registered is drawn as the call, whichever of them names it.
func TestProofGraphEnds(t *testing.T) {
	c, fold := load(t)
	var leaf *index.Member
	for _, m := range c.Members {
		if len(m.Deps) == 0 && m.Door == "" && fold.theorem(m.ID) {
			leaf = m
			break
		}
	}
	require.NotNil(t, leaf)
	g, err := Proof(c, leaf.ID)
	require.NoError(t, err)
	for _, grain := range g.Grains {
		require.Len(t, grain.Nodes, 1)
		require.Empty(t, grain.Edges)
		require.Len(t, grain.Columns, 1)
		require.True(t, grain.Nodes[0].Target)
	}

	door := c.Doors[0]
	atCall, err := Proof(c, door.ID)
	require.NoError(t, err)
	atPart, err := Proof(c, door.Parts[len(door.Parts)-1].Member)
	require.NoError(t, err)
	require.Equal(t, door.ID, atPart.Target)
	require.Equal(t, atCall, atPart)
	require.Equal(t, door.Name, atCall.Name)
	for _, grain := range atCall.Grains {
		for _, n := range grain.Nodes {
			if n.Target {
				require.Len(t, n.Statements, len(door.Parts), "a door call states what each of its parts states")
				require.Equal(t, path.Ext(door.Parts[0].Member)[1:], n.Statements[0].Member)
			}
		}
	}

	_, err = Proof(c, "no_such_family.NoSuchMember")
	require.Error(t, err)
}

// spaced keeps the aims' order and the step between neighbours, leaves
// aims already apart where they are, and sets a run of aims too close
// about their mean.
func TestSpaced(t *testing.T) {
	require.Empty(t, spaced(nil, 33))
	require.Equal(t, []float64{7}, spaced([]float64{7}, 33))
	require.Equal(t, []float64{0, 100, 200}, spaced([]float64{0, 100, 200}, 33))
	require.InDeltaSlice(t, []float64{67, 100, 133}, spaced([]float64{100, 100, 100}, 33), 1e-9)
	at := spaced([]float64{10, 20, 400, 405, 410, 1000}, 33)
	for i := 1; i < len(at); i++ {
		require.GreaterOrEqual(t, at[i]-at[i-1], 33-1e-9)
	}
	require.InDelta(t, 15, (at[0]+at[1])/2, 1e-9)
	require.InDelta(t, 405, (at[2]+at[3]+at[4])/3, 1e-9)
	require.InDelta(t, 1000, at[5], 1e-9)
}

// Every node of a proof graph is glossed from its chapter.
func TestProofGraphGloss(t *testing.T) {
	c, fold := load(t)
	target := ""
	for _, u := range sample(c, fold, 401) {
		if fold.theorem(u) && len(closure(u, fold.deps)) > 20 {
			target = u
			break
		}
	}
	require.NotEmpty(t, target)
	g, err := Proof(c, target)
	require.NoError(t, err)
	glossed := 0
	for _, grain := range g.Grains {
		for _, n := range grain.Nodes {
			gloss, err := c.Description(fold.members(n.ID)[0])
			require.NoError(t, err)
			gloss, err = typeset(gloss)
			require.NoError(t, err)
			require.Equal(t, gloss, n.Gloss, n.ID)
			if n.Gloss != "" {
				glossed++
			}
		}
	}
	require.Positive(t, glossed, "no node of %s's graph has a gloss", target)
}
