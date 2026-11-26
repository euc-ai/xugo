package visualize

import (
	"path"
	"slices"
	"sort"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/library/index"
	_ "github.com/euc-ai/xugo/library/proofs" // register the corpus
)

// corpusRoot is library/proofs relative to this package's directory.
const corpusRoot = "../proofs"

// load reads the corpus, and folds its door calls.
func load(t *testing.T) (*index.Corpus, *_Fold) {
	t.Helper()
	c, err := index.Load(corpusRoot)
	require.NoError(t, err)
	return c, foldDoors(c)
}

// closure is every node a node reaches over deps, by one step or more —
// the reach a graph's edges are checked against, computed the plain way.
func closure(start string, deps func(string) []string) map[string]bool {
	seen := map[string]bool{}
	var walk func(string)
	walk = func(id string) {
		for _, d := range deps(id) {
			if !seen[d] {
				seen[d] = true
				walk(d)
			}
		}
	}
	walk(start)
	return seen
}

// reduced is a scope's reduced relation worked out the plain way, from
// each node's reach: the pairs s, t of the scope where s reaches t and
// reaches no third node of the scope that reaches t, each with whether
// t is among s's direct deps.
func reduced(scope []string, deps func(string) []string) map[[2]string]bool {
	reach := map[string]map[string]bool{}
	for _, id := range scope {
		reach[id] = closure(id, deps)
	}
	direct := map[[2]string]bool{}
	for _, s := range scope {
	targets:
		for _, t := range scope {
			if !reach[s][t] {
				continue
			}
			for _, between := range scope {
				if reach[s][between] && reach[between][t] {
					continue targets
				}
			}
			direct[[2]string{s, t}] = slices.Contains(deps(s), t)
		}
	}
	return direct
}

// reduceScope keeps an edge where no node of the scope stands between
// its ends, and marks via the one that runs through a node outside.
func TestReduceScope(t *testing.T) {
	graph := map[string][]string{
		"top":   {"left", "right", "foot", "aside"},
		"left":  {"foot"},
		"right": {"mid"},
		"mid":   {"foot"},
		"aside": {},
		"foot":  {},
	}
	deps := func(id string) []string { return graph[id] }
	for _, scope := range [][]string{
		{"aside", "foot", "left", "mid", "right", "top"},
		{"foot", "right", "top"},
		{"foot", "top"},
		{"aside", "foot", "left"},
		{"top"},
	} {
		got := map[[2]string]bool{}
		for _, e := range reduceScope(scope, deps) {
			got[[2]string{e.S, e.T}] = !e.Via
		}
		require.Equal(t, reduced(scope, deps), got, "scope %v", scope)
	}
	require.Equal(t, []_Edge{{S: "right", T: "foot", Via: true}, {S: "top", T: "right"}}, reduceScope([]string{"foot", "right", "top"}, deps))
}

// A door call that registered several members is one unit in place of
// them: its parts name it, its deps are its parts' as units, itself
// left out, and a part's name, the call's id and the call's entry all
// resolve to it.
func TestUnits(t *testing.T) {
	c, fold := load(t)
	const groupOps = "algebra/group/group.GroupOps"
	d := fold.byDoor[groupOps]
	require.NotNil(t, d)
	require.Equal(t, "DefineData", d.Door)
	require.Equal(t, "group_ops", d.Type)
	require.Equal(t, "group.GroupOps", d.Entry)
	var parts []string
	fields := map[string][2]string{}
	for _, p := range d.Parts {
		parts = append(parts, path.Base(p.Member)[len("group."):])
		fields[p.Member] = [2]string{p.Field, p.Symbol}
		require.Equal(t, groupOps, fold.byID[p.Member].Door)
		require.Equal(t, groupOps, fold.of(p.Member))
	}
	require.Equal(t, []string{"GroupOpsInduction", "GroupOpsRecursion", "MkGroupInjective",
		"GroupMulDef", "GroupOneDef", "GroupInvDef", "GroupCarrierDef", "GroupOpsEq"}, parts)
	require.Equal(t, [2]string{"mul", "*"}, fields["algebra/group/group.GroupMulDef"])
	require.Equal(t, [2]string{"carrier", ""}, fields["algebra/group/group.GroupCarrierDef"])
	require.Equal(t, [2]string{"", ""}, fields["algebra/group/group.GroupOpsInduction"])

	var want []string
	for _, p := range d.Parts {
		for _, dep := range fold.byID[p.Member].Deps {
			if u := fold.of(dep); u != groupOps && !slices.Contains(want, u) {
				want = append(want, u)
			}
		}
	}
	require.Equal(t, want, fold.deps(groupOps))
	require.Equal(t, "GroupOps", fold.name(groupOps))
	require.Equal(t, "algebra/group/group", fold.family(groupOps))
	require.False(t, fold.theorem(groupOps))
	require.False(t, fold.result(groupOps))

	// A theorem and a card are results; a postulate is no result.
	kinds := map[string]bool{}
	for _, m := range c.Members {
		if m.Door == "" && !kinds[m.Kind] {
			kinds[m.Kind] = true
			want := m.Kind == "theorem" || m.Kind == "card"
			require.Equal(t, want, fold.result(m.ID), "%s, of kind %s", m.ID, m.Kind)
		}
	}
	require.True(t, kinds["postulate"], "the corpus holds no postulate")
	for _, ref := range []string{groupOps, "group.GroupOps", "group.GroupMulDef", "algebra/group/group.GroupOpsEq"} {
		u, err := fold.resolve(ref)
		require.NoError(t, err, ref)
		require.Equal(t, groupOps, u, ref)
	}
	_, err := fold.resolve("no_such_family.NoSuchMember")
	require.Error(t, err)

	for _, door := range c.Doors {
		require.Greater(t, len(door.Parts), 1, "%s registered one member", door.ID)
		for _, p := range door.Parts {
			m := fold.byID[p.Member]
			require.Equal(t, door.Family, m.Family, p.Member)
			require.Equal(t, fold.byID[door.Parts[0].Member].Source, m.Source, "%s is registered by the call's literal", p.Member)
		}
	}
	// A member registered alone is its own unit, and its deps its own
	// as units.
	for i, m := range c.Members {
		if i%97 != 0 || m.Door != "" {
			continue
		}
		require.Equal(t, m.ID, fold.of(m.ID))
		var deps []string
		for _, dep := range m.Deps {
			if u := fold.of(dep); !slices.Contains(deps, u) {
				deps = append(deps, u)
			}
		}
		require.Equal(t, deps, fold.deps(m.ID), m.ID)
	}
}

// sample is a spread of the corpus's units for the graphs' tests: every
// stride-th member's unit, a door call, and the last member of the
// highest family, which stands on the longest chain of chapters.
func sample(c *index.Corpus, fold *_Fold, stride int) []string {
	highest := c.Families[0]
	for _, f := range c.Families {
		if f.Height > highest.Height {
			highest = f
		}
	}
	units := map[string]bool{c.Doors[0].ID: true, fold.of(highest.Members[len(highest.Members)-1].ID): true}
	for i, m := range c.Members {
		if i%stride == 0 {
			units[fold.of(m.ID)] = true
		}
	}
	var list []string
	for u := range units {
		list = append(list, u)
	}
	sort.Strings(list)
	return list
}
