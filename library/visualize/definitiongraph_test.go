package visualize

import (
	"fmt"
	"slices"
	"sort"
	"testing"
	"unicode/utf8"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/library/index"
)

// mostCited is the definition the most members cite: one more families
// use than a page draws one by one.
func mostCited(c *index.Corpus, fold *_Fold) string {
	most, cited := "", -1
	for _, m := range c.Members {
		if u := fold.of(m.ID); !fold.theorem(u) && len(m.Dependents) > cited {
			most, cited = u, len(m.Dependents)
		}
	}
	return most
}

// A definition's graph, on a spread of the corpus's definitions and on
// the definition the most members cite, checked against the rule worked
// out the plain way: left of the definition every unit it cites and
// every card it stands on, under
// the units' relation reduced inside them; right of it one column, the
// users of its own family one by one under their use's heading and in
// the chapter's order, then the other families a node each, the one
// with the most users first, the families past the page's number under
// one node; an edge from the definition to each; the nodes apart,
// inside the page, and the definition at the column's middle.
func TestDefinitionGraph(t *testing.T) {
	c, fold := load(t)
	deps := map[string][]string{}
	unitDeps := func(u string) []string {
		if _, read := deps[u]; !read {
			deps[u] = fold.deps(u)
		}
		return deps[u]
	}
	targets := []string{mostCited(c, fold)}
	for _, u := range sample(c, fold, 53) {
		if !fold.theorem(u) {
			targets = append(targets, u)
		}
	}
	require.Greater(t, len(targets), 20, "the sample holds definitions")
	folded, unfolded := 0, 0
	for _, target := range targets {
		g, err := Proof(c, target)
		require.NoError(t, err, target)
		require.Equal(t, target, g.Target)
		require.NotNil(t, g.Definition, target)
		require.Len(t, g.Grains, 1, target)
		grain := g.Grains[0]
		own := fold.family(target)

		// Who uses it, from the index's two relations, and how.
		minted := map[string]bool{}
		users := map[string]bool{}
		for _, m := range fold.members(target) {
			for _, name := range m.Defines {
				minted[name] = true
			}
			for _, id := range m.Dependents {
				users[fold.of(id)] = true
			}
			for _, use := range c.UsedBy(m) {
				users[fold.of(use.Member)] = true
			}
		}
		delete(users, target)
		names := func(constants []string) bool {
			return slices.ContainsFunc(constants, func(name string) bool { return minted[name] })
		}
		use := func(u string) string {
			states := slices.ContainsFunc(fold.members(u), func(m *index.Member) bool { return names(m.Constants) })
			switch {
			case !states:
				return useCites
			case !fold.theorem(u):
				return useDefines
			}
			return useAbout
		}
		perFamily := map[string]int{}
		for u := range users {
			perFamily[fold.family(u)]++
		}
		require.Equal(t, len(users), g.Definition.Users, target)
		require.Len(t, g.Definition.Families, len(perFamily), target)
		require.Equal(t, []ProofUse{{useDefines, "definitions built on it"}, {useAbout, "theorems about it"}, {useCites, "cite it in a proof"}}, g.Definition.Uses)
		for i, f := range g.Definition.Families {
			require.Equal(t, perFamily[f.Family], f.Count, "%s in %s", f.Family, target)
			if f.Family == own {
				require.Zero(t, i, "the definition's own family is the first")
				require.Empty(t, f.Users, "its users are nodes")
			} else if i > 0 && g.Definition.Families[i-1].Family != own {
				prev := g.Definition.Families[i-1]
				require.True(t, prev.Count > f.Count || prev.Count == f.Count && prev.Family < f.Family, "%s before %s", prev.Family, f.Family)
			}
		}

		at := map[string]ProofNode{}
		head := -1
		for _, n := range grain.Nodes {
			require.NotContains(t, at, n.ID, "%s is drawn twice", n.ID)
			at[n.ID] = n
			if n.Target {
				head = n.Column
				require.Equal(t, target, n.ID)
			}
			require.False(t, n.Ambient, n.ID)
		}
		require.GreaterOrEqual(t, head, 0, target)
		require.Zero(t, grain.Line, target)
		require.InDelta(t, at[target].Y+grain.Block/2, grain.Axis, 0.11)

		// Left of it: what it cites, and no other unit.
		var left []string
		for _, n := range grain.Nodes {
			if n.Column <= head {
				left = append(left, n.ID)
				require.Empty(t, n.Use, n.ID)
				require.Equal(t, fold.family(n.ID), n.Family, n.ID)
				require.Equal(t, !fold.theorem(n.ID), n.Definition, n.ID)
				for j, m := range fold.members(n.ID) {
					require.Equal(t, stated(c, m), n.Statements[j], m.ID)
				}
			}
		}
		sort.Strings(left)
		cited := append([]string{target}, unitDeps(target)...)
		for u := range closure(target, unitDeps) {
			if fold.byDoor[u] == nil && fold.byID[u].Card && !slices.Contains(cited, u) {
				cited = append(cited, u)
			}
		}
		sort.Strings(cited)
		require.Equal(t, cited, left, "left of %s is what it cites, and every card it stands on", target)
		want := reduced(left, unitDeps)
		got := map[[2]string]bool{}
		fan := map[string]bool{}
		leftmost := map[string]int{}
		for _, e := range grain.Edges {
			s, t2 := at[e.S], at[e.T]
			require.Less(t, t2.Column, s.Column, "%s stands on %s", e.S, e.T)
			require.GreaterOrEqual(t, e.Y1, t2.Y, "%s → %s leaves %s", e.S, e.T, e.T)
			require.LessOrEqual(t, e.Y1, t2.Y+grain.Block, "%s → %s leaves %s", e.S, e.T, e.T)
			require.InDelta(t, s.Y+grain.Block/2, e.Y2, 7.1, "%s → %s reaches %s", e.S, e.T, e.S)
			if s.Column > head {
				require.Equal(t, target, e.T, "an edge to a user leaves the definition")
				require.False(t, e.Via)
				require.InDelta(t, s.Y+grain.Block/2, e.Y2, 0.051)
				fan[e.S] = true
				continue
			}
			got[[2]string{e.S, e.T}] = !e.Via
			if col, seen := leftmost[e.T]; !seen || s.Column < col {
				leftmost[e.T] = s.Column
			}
		}
		require.Equal(t, want, got, target)
		for _, id := range left {
			if id != target {
				require.Equal(t, leftmost[id]-1, at[id].Column, "%s is not one column left of the leftmost node standing on it", id)
			}
		}

		// Right of it: one column, group by group.
		var right []ProofNode
		for _, n := range grain.Nodes {
			if n.Column > head {
				require.Equal(t, head+1, n.Column, n.ID)
				require.Equal(t, len(grain.Columns)-1, n.Column, n.ID)
				require.True(t, fan[n.ID], "no edge runs from %s to %s", target, n.ID)
				right = append(right, n)
			}
		}
		require.Len(t, fan, len(right))
		if len(users) == 0 {
			require.Empty(t, right, target)
			require.Empty(t, grain.Groups, target)
			require.Equal(t, head, len(grain.Columns)-1)
			continue
		}
		rank := map[string]int{useDefines: 0, useAbout: 1, useCites: 2, useFamily: 3, useMore: 3}
		place := map[string]int{}
		for i, m := range fold.byFamily[own].Members {
			if _, placed := place[fold.of(m.ID)]; !placed {
				place[fold.of(m.ID)] = i
			}
		}
		widest := 0.0
		counted := map[string]int{}
		units, families, more := 0, 0, 0
		for i, n := range right {
			line := familyTail(n.Family)
			switch n.Use {
			case useFamily:
				require.Equal(t, n.Family, n.ID)
				require.NotEqual(t, own, n.Family)
				require.Equal(t, perFamily[n.Family], n.Users, n.ID)
				require.Equal(t, familyTail(n.Family), n.Name)
				require.Empty(t, n.Statements, n.ID)
				gloss, err := typeset(fold.byFamily[n.Family].Gloss)
				require.NoError(t, err)
				require.Equal(t, gloss, n.Gloss, n.ID)
				of := g.Definition.Families[slices.IndexFunc(g.Definition.Families, func(f ProofFamilyUses) bool { return f.Family == n.Family })]
				require.Len(t, of.Users, n.Users, n.ID)
				for j, user := range of.Users {
					u := n.Family + "." + user.Name
					require.True(t, users[u], "%s is listed and does not use %s", u, target)
					require.Equal(t, use(u), user.Use, u)
					if status := fold.status(u); status == "proved" {
						require.Empty(t, user.Status, u)
					} else {
						require.Equal(t, status, user.Status, u)
					}
					if j > 0 {
						require.LessOrEqual(t, rank[of.Users[j-1].Use], rank[user.Use], "%s: by use", n.Family)
					}
				}
				families++
				line = usesLine(n.Users)
			case useMore:
				require.Equal(t, usesMoreID, n.ID)
				require.Equal(t, len(right)-1, i, "the node for the families not drawn is the last")
				require.Equal(t, fmt.Sprintf("%d more families", n.Families), n.Name)
				more = n.Families
				left := 0
				for _, f := range g.Definition.Families {
					if f.Family != own && !slices.ContainsFunc(right, func(m ProofNode) bool { return m.ID == f.Family }) {
						left += f.Count
						require.Empty(t, f.Users, "%s is not drawn", f.Family)
					}
				}
				require.Equal(t, left, n.Users)
				line = usesLine(n.Users)
			default:
				require.True(t, users[n.ID], "%s is drawn and does not use %s", n.ID, target)
				require.Equal(t, own, n.Family, n.ID)
				require.Equal(t, use(n.ID), n.Use, n.ID)
				require.Equal(t, fold.status(n.ID), n.Status, n.ID)
				theorems, cards := 0, 0
				for d := range closure(n.ID, unitDeps) {
					if fold.result(d) {
						theorems++
					}
					if fold.byDoor[d] == nil && fold.byID[d].Card {
						cards++
					}
				}
				require.Equal(t, [2]int{theorems, cards}, [2]int{n.Theorems, n.Cards}, n.ID)
				if i > 0 && right[i-1].Use == n.Use {
					require.Less(t, place[right[i-1].ID], place[n.ID], "%s and %s in the chapter's order", right[i-1].ID, n.ID)
				}
				units++
			}
			counted[n.Use]++
			if i > 0 {
				require.LessOrEqual(t, rank[right[i-1].Use], rank[n.Use], "%s under %s", n.ID, right[i-1].ID)
				require.GreaterOrEqual(t, n.Y-right[i-1].Y, grain.Block+6.4, "%s under %s", n.ID, right[i-1].ID)
			}
			require.Equal(t, grain.Columns[n.Column].X, n.X, n.ID)
			require.Equal(t, grain.Columns[n.Column].W, n.W, n.ID)
			widest = max(widest, float64(utf8.RuneCountInString(n.Name))*proofGraphLetter, float64(utf8.RuneCountInString(line))*proofGraphFamilyLetter)
		}
		require.Equal(t, perFamily[own], units, "%s: its own family's users are drawn one by one", target)
		require.Equal(t, len(perFamily)-min(1, perFamily[own]), families+more, "%s: every other family is drawn or counted", target)
		require.LessOrEqual(t, families+min(1, more), usesFamilies, target)
		if more > 0 {
			folded++
			require.Equal(t, usesFamilies-1, families, target)
		} else if families > 0 {
			unfolded++
		}

		// The headings, each over its group's first node.
		var heads []string
		for _, n := range right {
			group := n.Use
			if group == useMore {
				group = useFamily
			}
			if len(heads) == 0 || heads[len(heads)-1] != group {
				heads = append(heads, group)
			}
		}
		require.Len(t, grain.Groups, len(heads), target)
		for i, group := range grain.Groups {
			require.Equal(t, heads[i], group.Use)
			count := counted[group.Use]
			if group.Use == useFamily {
				count = families + more
			}
			require.Equal(t, count, group.Count, "%s of %s", group.Use, target)
			at := slices.IndexFunc(right, func(n ProofNode) bool { return n.Use == group.Use || group.Use == useFamily && n.Use == useMore })
			first := right[at]
			require.Equal(t, first.X, group.X)
			require.Less(t, group.Y, first.Y, "the heading of %s is over its first node", group.Use)
			require.Greater(t, group.Y, first.Y-usesHeading, "the heading of %s is over its first node", group.Use)
			if at > 0 {
				require.Greater(t, group.Y-7.5, right[at-1].Y+grain.Block, "the heading of %s is under the group before it", group.Use)
			}
			widest = max(widest, float64(utf8.RuneCountInString(fmt.Sprintf("%s · %d", group.Label, group.Count)))*proofGraphFamilyLetter)
		}
		last := grain.Columns[len(grain.Columns)-1]
		require.InDelta(t, widest+proofGraphPad, last.W, 0.051, "the users' column is as wide as its longest label")
		require.InDelta(t, grain.Columns[head].X+grain.Columns[head].W+usesColumn, last.X, 0.11)
		require.LessOrEqual(t, last.X+last.W, float64(grain.Width)-12)
		top, foot := grain.Groups[0].Y+4-usesHeading, right[len(right)-1].Y+grain.Block
		require.InDelta(t, grain.Axis, (top+foot)/2, 0.6, "the column is centred on %s", target)
		for _, n := range grain.Nodes {
			require.GreaterOrEqual(t, n.Y, proofGraphTop-0.051, n.ID)
			require.LessOrEqual(t, n.Y+grain.Block, float64(grain.Height)-8, n.ID)
		}

		again, err := Proof(c, target)
		require.NoError(t, err)
		require.Equal(t, g, again, "a second graph of %s differs from the first", target)
	}
	require.Positive(t, folded, "no definition of the sample has more families than the page draws")
	require.Positive(t, unfolded, "no definition of the sample has its other families all drawn")
}
