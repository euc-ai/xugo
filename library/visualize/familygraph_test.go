package visualize

import (
	"math"
	"path"
	"sort"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/stretchr/testify/require"
)

// The family graph draws every family once, on the row of its height,
// in a block as wide as its name, with its README's introduction and
// its theorems by name; its edges
// are the imports reduced, each running down from the foot of a block
// to the top of another; a row's blocks keep their gap and the page's
// margins, and the fullest row runs from one margin to the other.
func TestFamilyGraph(t *testing.T) {
	c, fold := load(t)
	g, err := Families(c)
	require.NoError(t, err)
	require.Len(t, g.Nodes, len(c.Families))
	at := map[string]FamilyNode{}
	rows := map[int][]FamilyNode{}
	introduced := 0
	var names []string
	for _, n := range g.Nodes {
		f := fold.byFamily[n.Family]
		require.NotNil(t, f, n.Family)
		require.NotContains(t, at, n.Family)
		at[n.Family] = n
		names = append(names, n.Family)
		require.Equal(t, f.Height, n.Height, n.Family)
		require.Equal(t, f.Counts.Members, n.Members, n.Family)
		require.Equal(t, f.Counts.Cards, n.Cards, n.Family)
		cards, proved, postulates, provedTheorems, theoremsOnCards := 0, 0, 0, 0, 0
		var theorems, definitions []string
		for _, m := range f.Members {
			if fold.theorem(m.ID) {
				theorems = append(theorems, path.Ext(m.ID)[1:])
				switch m.Status() {
				case "proved":
					provedTheorems++
				case "card", "on_cards":
					theoremsOnCards++
				}
			}
			// A definition registered alone is listed by its name, a door
			// call by its own, where its first part stands.
			if d := fold.byDoor[m.Door]; d == nil && !fold.theorem(m.ID) {
				definitions = append(definitions, path.Ext(m.ID)[1:])
			} else if d != nil && d.Parts[0].Member == m.ID {
				definitions = append(definitions, d.Name)
			}
			switch m.Status() {
			case "proved":
				proved++
			case "postulate":
				postulates++
			}
		}
		require.Equal(t, proved, n.Proved, "%s: the proved are the members proved outright, a definition among them", n.Family)
		require.Equal(t, postulates, n.Postulates, n.Family)
		require.Equal(t, provedTheorems, n.ProvedTheorems, "%s: the proved are the theorems proved outright, no definition among them", n.Family)
		require.Equal(t, theoremsOnCards, n.TheoremsOnCards, "%s: the theorems not proved yet, cards and those standing on one", n.Family)
		require.Equal(t, len(theorems), provedTheorems+theoremsOnCards+postulates, "%s: a theorem is proved, on cards or a postulate", n.Family)
		require.Len(t, n.Theorems, len(theorems), n.Family)
		for i, th := range n.Theorems {
			require.Equal(t, theorems[i], th.Name, n.Family)
			m := fold.byID[n.Family+"."+th.Name]
			require.Equal(t, m.Status(), th.Status, th.Name)
			require.Equal(t, m.Card, th.Status == "card", th.Name)
			require.Equal(t, !m.Card && !m.Postulate && len(m.Cards) > 0, th.Status == "on_cards", th.Name)
			if th.Status == "card" {
				cards++
			}
		}
		require.Equal(t, n.Cards, cards, "%s: the cards are among the theorems", n.Family)
		require.Len(t, n.Definitions, len(definitions), n.Family)
		for i, d := range n.Definitions {
			require.Equal(t, definitions[i], d.Name, n.Family)
			u, err := fold.resolve(n.Family + "." + d.Name)
			require.NoError(t, err, "%s.%s names its page", n.Family, d.Name)
			require.False(t, fold.theorem(u), u)
			require.Equal(t, fold.status(u), d.Status, u)
		}
		gloss, err := typeset(f.Gloss)
		require.NoError(t, err, n.Family)
		require.Equal(t, gloss, n.Gloss, n.Family)
		for _, b := range n.Intro {
			require.False(t, strings.HasPrefix(b.Text, "|") || strings.HasPrefix(b.Text, "#"), "%s: a table's line or a heading is no prose: %s", n.Family, b.Text)
			require.True(t, b.Text != "" || len(b.Items) > 0 || b.Formula != "", "%s: a block says something", n.Family)
		}
		if len(n.Intro) > 0 {
			introduced++
		}
		letters := utf8.RuneCountInString(path.Base(n.Family))
		under := utf8.RuneCountInString(strings.TrimSuffix(n.Family, path.Base(n.Family)))
		require.InDelta(t, math.Max(float64(letters)*familyGraphLetter, float64(under)*familyGraphPathLetter)+familyGraphPad, n.W, 0.051, n.Family)
		require.InDelta(t, g.Base-float64(n.Height)*g.Step, n.Y, 0.051, n.Family)
		rows[n.Height] = append(rows[n.Height], n)
	}
	require.Greater(t, 2*introduced, len(g.Nodes), "most READMEs open with an introduction")
	require.Len(t, rows, g.Layers)
	require.Greater(t, float64(g.Height), g.Base+g.Block)
	right := float64(g.Width) - familyGraphRight
	fullest := 0.0
	for h, row := range rows {
		sort.Slice(row, func(i, j int) bool { return row[i].X < row[j].X })
		gap := familyGraphGap(len(row))
		require.GreaterOrEqual(t, row[0].X, familyGraphLeft-0.5, "height %d", h)
		last := row[len(row)-1]
		require.LessOrEqual(t, last.X+last.W, right+0.5, "height %d", h)
		fullest = math.Max(fullest, last.X+last.W-row[0].X)
		for i := 1; i < len(row); i++ {
			require.LessOrEqual(t, row[i-1].X+row[i-1].W+gap-0.5, row[i].X, "%s and %s on the row of height %d", row[i-1].Family, row[i].Family, h)
		}
	}
	require.InDelta(t, right-familyGraphLeft, fullest, 1, "the page is as wide as its fullest row")
	require.InDelta(t, 0.5*(familyGraphLeft+right), g.Axis, 0.5)

	sort.Strings(names)
	want := reduced(names, func(name string) []string { return fold.byFamily[name].Imports })
	got := map[[2]string]bool{}
	for _, e := range g.Edges {
		s, t2 := at[e.S], at[e.T]
		got[[2]string{e.S, e.T}] = true
		require.Greater(t, s.Height, t2.Height, "%s imports %s", e.S, e.T)
		require.GreaterOrEqual(t, e.X1, s.X, "%s → %s leaves %s", e.S, e.T, e.S)
		require.LessOrEqual(t, e.X1, s.X+s.W, "%s → %s leaves %s", e.S, e.T, e.S)
		require.GreaterOrEqual(t, e.X2, t2.X, "%s → %s reaches %s", e.S, e.T, e.T)
		require.LessOrEqual(t, e.X2, t2.X+t2.W, "%s → %s reaches %s", e.S, e.T, e.T)
	}
	require.Equal(t, want, got, "an import is always direct, so every reduced pair is one")
	require.Len(t, g.Edges, len(want))

	again, err := Families(c)
	require.NoError(t, err)
	require.Equal(t, g, again, "a second layout differs from the first")
}

// placeRow keeps a row's order and gaps inside the margins, leaves a
// block that has room at its aim, and packs the blocks whose aims
// collide about their weighted mean.
func TestPlaceRow(t *testing.T) {
	rows := func(widths, aims, weights []float64) (*_FamilyRows, []int) {
		ids := make([]int, len(widths))
		for i := range ids {
			ids[i] = i
		}
		return &_FamilyRows{left: 46, right: 1966, width: widths, aim: aims, weight: weights}, ids
	}
	gap := familyGraphGap(3)

	r, ids := rows([]float64{100, 100, 100}, []float64{300, 600, 900}, []float64{1, 1, 1})
	require.Equal(t, []float64{300, 600, 900}, r.placeRow(ids), "aims with room between them are kept")

	r, ids = rows([]float64{100, 100, 100}, []float64{500, 500, 500}, []float64{1, 1, 1})
	at := r.placeRow(ids)
	require.InDeltaSlice(t, []float64{500 - (100 + gap), 500, 500 + (100 + gap)}, at, 1e-9, "equal aims pack about the aim")

	r, ids = rows([]float64{100, 100}, []float64{500, 500}, []float64{3, 1})
	at = r.placeRow(ids)
	require.InDelta(t, 100+gap, at[1]-at[0], 1e-9)
	require.InDelta(t, 500, (3*at[0]+at[1])/4, 1e-9, "the heavier block is moved the less")

	r, ids = rows([]float64{100, 100, 100}, []float64{-50, 0, 5000}, []float64{1, 1, 1})
	at = r.placeRow(ids)
	require.GreaterOrEqual(t, at[0]-50, r.left)
	require.LessOrEqual(t, at[2]+50, r.right)
	for i := 1; i < len(at); i++ {
		require.GreaterOrEqual(t, at[i]-at[i-1], 100+gap-1e-9)
	}
}
