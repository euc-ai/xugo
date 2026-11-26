package visualize

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"maps"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/library/index"
)

// siteFile reads a file of the site into a value.
func siteFile(t *testing.T, s *Site, path string, into any) {
	t.Helper()
	data, err := s.File(path)
	require.NoError(t, err, path)
	require.NoError(t, json.Unmarshal(data, into), path)
}

// The site's two pages are their templates with the notice and what the
// pages share: they hold no graph, and ask for nothing outside the
// site.
func TestSitePages(t *testing.T) {
	c, _ := load(t)
	s := NewSite(c, "xugo browse --write")
	for _, path := range []string{siteFamiliesPage, siteProofPage} {
		data, err := s.File(path)
		require.NoError(t, err)
		page := string(data)
		require.True(t, strings.HasPrefix(page, "<!doctype html>\n<!-- Written by `xugo browse ‐‐write` from the proof registry (library/visualize). -->\n"), "%s: a comment holds no double hyphen", path)
		require.NotContains(t, page, pageNoticeSlot)
		require.NotContains(t, page, pageSharedSlot)
		require.Contains(t, page, "window.xugoSite = ", "%s holds what the pages share", path)
		require.Contains(t, page, "fetch(path)", "%s reads the site's files", path)
		for _, outside := range []string{"<link", " src=", "@import", "url(http", `fetch("http`, `href="/`, `href="http`} {
			require.NotContains(t, page, outside, "%s asks for nothing outside the site, and by no address of its own", path)
		}
	}
	_, err := s.File("no/such/file")
	require.ErrorIs(t, err, ErrNoPage)
}

// The family graph's layout is the family graph without what is said of
// a family; a family's file says it, and says of each of its units, in
// the chapter's order, what a page drawing the unit reads: of a theorem
// with it, the units it cites and those citing it, read from the index's
// members (index.Member.Deps, Dependents), and of a definition neither.
func TestSiteFamilies(t *testing.T) {
	c, fold := load(t)
	s := NewSite(c, "xugo browse")
	g, err := Families(c)
	require.NoError(t, err)
	var layout SiteFamilies
	siteFile(t, s, siteFamilies, &layout)
	require.Equal(t, []any{g.Width, g.Height, g.Axis, g.Base, g.Step, g.Block, g.Layers}, []any{layout.Width, layout.Height, layout.Axis, layout.Base, layout.Step, layout.Block, layout.Layers})
	require.Equal(t, g.Edges, layout.Edges)
	require.Len(t, layout.Nodes, len(g.Nodes))
	for i, n := range g.Nodes {
		require.Equal(t, SiteFamilyNode{Family: n.Family, Height: n.Height, Members: n.Members, Proved: n.Proved,
			ProvedTheorems: n.ProvedTheorems, TheoremsOnCards: n.TheoremsOnCards, Definitions: len(n.Definitions),
			Postulates: n.Postulates, Cards: n.Cards, X: n.X, Y: n.Y, W: n.W}, layout.Nodes[i])
	}

	deps := map[string][]string{}
	unitDeps := func(u string) []string {
		if _, read := deps[u]; !read {
			deps[u] = fold.deps(u)
		}
		return deps[u]
	}
	units, citers, plans := 0, 0, 0
	for i, n := range g.Nodes {
		if i%23 != 0 {
			continue
		}
		f := fold.byFamily[n.Family]
		var said SiteFamily
		siteFile(t, s, siteFamilyDir+n.Family+".json", &said)
		require.Equal(t, n.Family, said.Family)
		require.Equal(t, n.Gloss, said.Gloss, n.Family)
		require.Equal(t, encode(n.Intro), encode(said.Intro), n.Family)
		var want []string
		listed := map[string]bool{}
		for _, m := range f.Members {
			if u := fold.of(m.ID); !listed[u] {
				listed[u] = true
				want = append(want, u)
			}
		}
		require.Len(t, said.Units, len(want), n.Family)
		theorems, definitions := 0, 0
		for j, unit := range said.Units {
			u := want[j]
			units++
			require.Equal(t, fold.name(u), unit.Name, u)
			require.Equal(t, n.Family+"."+unit.Name, u, "a unit's id is its family's name, a dot, and its own")
			require.Equal(t, !fold.theorem(u), unit.Definition, u)
			require.Equal(t, fold.status(u), unit.Status, u)
			under := [2]int{}
			for d := range closure(u, unitDeps) {
				if fold.result(d) {
					under[0]++
				}
				if fold.byDoor[d] == nil && fold.byID[d].Card {
					under[1]++
				}
			}
			require.Equal(t, under, [2]int{unit.Theorems, unit.Cards}, "%s: the results it stands on, and the cards among them", u)
			members := fold.members(u)
			gloss, err := c.Description(members[0])
			require.NoError(t, err)
			gloss, err = typeset(gloss)
			require.NoError(t, err)
			require.Equal(t, gloss, unit.Gloss, u)
			require.Len(t, unit.Members, len(members), u)
			var uses, usedBy []string
			if fold.theorem(u) {
				cited := func(of func(*index.Member) []string) []string {
					set := map[string]bool{}
					for _, m := range members {
						for _, id := range of(m) {
							if v := fold.of(id); v != u {
								set[v] = true
							}
						}
					}
					return slices.Sorted(maps.Keys(set))
				}
				uses = cited(func(m *index.Member) []string { return m.Deps })
				usedBy = cited(func(m *index.Member) []string { return m.Dependents })
			}
			require.Equal(t, uses, unit.Uses, "%s: the units it cites", u)
			require.Equal(t, usedBy, unit.UsedBy, "%s: the units citing it", u)
			citers += len(usedBy)
			// A card's plan is what it cites, each unit by its kind:
			// a door call's a definition's.
			var plan *SitePlan
			if fold.byDoor[u] == nil && members[0].Card {
				plan = &SitePlan{}
				for _, d := range uses {
					kind := "definition"
					if fold.byDoor[d] == nil {
						kind = fold.byID[d].Kind
					}
					switch kind {
					case "theorem", "card":
						plan.Results++
					case "postulate":
						plan.Postulates++
					default:
						plan.Definitions++
					}
				}
				plans++
			}
			require.Equal(t, plan, unit.Plan, "%s: what its plan cites", u)
			for k, m := range members {
				require.Equal(t, encode(SiteMember{Kind: m.Kind, Status: m.Status(), ProofStatement: stated(c, m)}), encode(unit.Members[k]), m.ID)
				if fold.theorem(m.ID) {
					theorems++
				}
			}
			if unit.Definition {
				definitions++
			}
		}
		require.Len(t, n.Theorems, theorems, "%s: its members that are theorems are the family graph's", n.Family)
		require.Len(t, n.Definitions, definitions, "%s: its units that are definitions are the family graph's", n.Family)
	}
	require.Greater(t, units, 200, "the sample holds units")
	require.Positive(t, citers, "no theorem of the sample is cited")
	require.Positive(t, plans, "the sample holds no card")

	_, err = s.File(siteFamilyDir + "no/such_family.json")
	require.ErrorIs(t, err, ErrNoPage)
}

// joined is a unit's graph read back from the site as a page reads it:
// its page's layout with what the families' files say of the units
// drawn.
func joined(t *testing.T, s *Site, page *SitePage) *ProofGraph {
	said := map[string]*SiteFamily{}
	family := func(name string) *SiteFamily {
		if said[name] == nil {
			said[name] = &SiteFamily{}
			siteFile(t, s, siteFamilyDir+name+".json", said[name])
		}
		return said[name]
	}
	unit := func(family *SiteFamily, name string) SiteUnit {
		for _, u := range family.Units {
			if u.Name == name {
				return u
			}
		}
		t.Fatalf("%s says nothing of %s", family.Family, name)
		return SiteUnit{}
	}
	cut := func(id string) (string, string) {
		at := strings.LastIndex(id, ".")
		return id[:at], id[at+1:]
	}
	own, name := cut(page.Target)
	g := &ProofGraph{Target: page.Target, Name: name}
	if page.Definition != nil {
		d := *page.Definition
		d.Families = make([]ProofFamilyUses, len(page.Definition.Families))
		for i, f := range page.Definition.Families {
			d.Families[i] = ProofFamilyUses{Family: f.Family, Count: f.Count}
			for _, user := range f.Users {
				require.Empty(t, user.Status, "a user's stratum is its family's file's to say")
				if status := unit(family(f.Family), user.Name).Status; status != "proved" {
					user.Status = status
				}
				d.Families[i].Users = append(d.Families[i].Users, user)
			}
		}
		g.Definition = &d
	}
	for _, laid := range page.Grains {
		grain := ProofGrain{Key: laid.Key, Allowance: laid.Allowance, Theorems: laid.Theorems, PerFamily: laid.PerFamily,
			Width: laid.Width, Height: laid.Height, Block: laid.Block, Axis: laid.Axis, Line: laid.Line,
			Columns: laid.Columns, Nodes: make([]ProofNode, len(laid.Nodes)), Edges: make([]ProofEdge, len(laid.Edges)), Groups: laid.Groups}
		for i, n := range laid.Nodes {
			column := laid.Columns[n.Column]
			node := ProofNode{Column: n.Column, X: column.X, Y: n.Y, W: column.W, Ambient: n.Ambient, Target: n.Target, Use: n.Use,
				Users: n.Users, Families: n.Families, Statements: []ProofStatement{}}
			switch n.Use {
			case useFamily:
				node.ID, node.Name, node.Family, node.Gloss = n.ID, familyTail(n.ID), n.ID, family(n.ID).Gloss
			case useMore:
				node.ID, node.Name = n.ID, fmt.Sprintf("%d more families", n.Families)
			default:
				node.ID = page.Units[n.Unit]
				of, name := cut(node.ID)
				facts := unit(family(of), name)
				node.Name, node.Family, node.Own, node.Definition = name, of, of == own, facts.Definition
				node.Status, node.Theorems, node.Cards, node.Gloss = facts.Status, facts.Theorems, facts.Cards, facts.Gloss
				for _, m := range facts.Members {
					node.Statements = append(node.Statements, m.ProofStatement)
				}
			}
			grain.Nodes[i] = node
		}
		for i, e := range laid.Edges {
			grain.Edges[i] = ProofEdge{S: grain.Nodes[e.S].ID, T: grain.Nodes[e.T].ID, Via: e.Via, Y1: e.Y1, Y2: e.Y2}
		}
		g.Grains = append(g.Grains, grain)
	}
	return g
}

// A unit's page holds its graph's layout, and the layout with what the
// families' files say of the units drawn is the unit's graph, a node's
// count of steps left out: a page says nothing a family's file says.
func TestSitePage(t *testing.T) {
	c, fold := load(t)
	s := NewSite(c, "xugo browse")
	targets := append(sample(c, fold, 211), mostCited(c, fold))
	definitions := 0
	for _, target := range targets {
		data, err := s.File(siteProofDir + target + ".json")
		require.NoError(t, err, target)
		for _, said := range []string{`"statements"`, `"text"`, `"gloss"`, `"status"`, `"name":"` + fold.name(target) + `"`} {
			if said == `"name":"`+fold.name(target)+`"` && !fold.theorem(target) {
				continue // a definition's page names its users, and one may bear its name
			}
			require.NotContains(t, string(data), said, "%s's page says what a family's file says", target)
		}
		var page SitePage
		require.NoError(t, json.Unmarshal(data, &page))
		require.Equal(t, target, page.Target)
		require.IsIncreasing(t, append([]string{""}, page.Units...), target)

		want, err := Proof(c, target)
		require.NoError(t, err)
		if want.Definition != nil {
			definitions++
		}
		for gi := range want.Grains {
			for ni := range want.Grains[gi].Nodes {
				want.Grains[gi].Nodes[ni].Steps = 0
			}
		}
		require.JSONEq(t, string(encode(want)), string(encode(joined(t, s, &page))), target)
	}
	require.Greater(t, definitions, 3, "the sample holds definitions")

	// A member's registered name and a door call's part answer the page
	// of their unit; a name of no member answers none.
	door := c.Doors[0]
	var page SitePage
	siteFile(t, s, siteProofDir+door.Parts[len(door.Parts)-1].Member+".json", &page)
	require.Equal(t, door.ID, page.Target)
	_, err := s.File(siteProofDir + "no_such_family.NoSuchMember.json")
	require.ErrorIs(t, err, ErrNoPage)
	require.ErrorContains(t, err, "names no corpus member")
}

// counts counts, for every unit, what the cone of its own graph counts.
func TestSiteCounts(t *testing.T) {
	c, fold := load(t)
	under := fold.counts()
	require.Len(t, under, len(fold.units()))
	for _, u := range sample(c, fold, 401) {
		k := fold.cone(u)
		theorems, cards := k.under(k.index[u])
		require.Equal(t, [2]int{theorems, cards}, under[u], u)
	}
}

// The site served answers its files by their paths, "/" being the
// family graph's page, and refuses what is no reading.
func TestSiteServed(t *testing.T) {
	c, fold := load(t)
	s := NewSite(c, "xugo browse")
	server := httptest.NewServer(s)
	defer server.Close()
	get := func(path string) (int, string, string) {
		answer, err := http.Get(server.URL + path)
		require.NoError(t, err)
		defer answer.Body.Close()
		body, err := io.ReadAll(answer.Body)
		require.NoError(t, err)
		require.Equal(t, "no-store", answer.Header.Get("Cache-Control"), path)
		return answer.StatusCode, answer.Header.Get("Content-Type"), string(body)
	}
	for path, file := range map[string]string{
		"/":                siteFamiliesPage,
		"/index.html":      siteFamiliesPage,
		"/proof.html":      siteProofPage,
		"/" + siteFamilies: siteFamilies,
		"/" + siteFamilyDir + c.Families[0].Name + ".json":     siteFamilyDir + c.Families[0].Name + ".json",
		"/" + siteProofDir + sample(c, fold, 401)[0] + ".json": siteProofDir + sample(c, fold, 401)[0] + ".json",
	} {
		status, kind, body := get(path)
		require.Equal(t, http.StatusOK, status, path)
		want, err := s.File(file)
		require.NoError(t, err)
		require.Equal(t, string(want), body, path)
		if strings.HasSuffix(file, ".html") {
			require.Equal(t, "text/html; charset=utf-8", kind, path)
		} else {
			require.Equal(t, "application/json; charset=utf-8", kind, path)
		}
	}
	status, _, body := get("/" + siteProofDir + "no_such_family.NoSuchMember.json")
	require.Equal(t, http.StatusNotFound, status)
	require.Contains(t, body, "names no corpus member")
	status, _, _ = get("/no/such/page")
	require.Equal(t, http.StatusNotFound, status)
	answer, err := http.Post(server.URL+"/", "text/plain", strings.NewReader("x"))
	require.NoError(t, err)
	answer.Body.Close()
	require.Equal(t, http.StatusMethodNotAllowed, answer.StatusCode)
}

// The site's paths name every family once and every unit once, and a
// site written holds at each path the file the site answers there; it
// is written into an empty directory, and two paths a file system may
// take for one are refused.
func TestSiteWritten(t *testing.T) {
	c, fold := load(t)
	s := NewSite(c, "xugo browse --write")
	paths := s.Paths()
	seen := map[string]bool{}
	unit := map[string]bool{}
	for _, u := range fold.units() {
		unit[u] = true
	}
	families, units := 0, 0
	for _, path := range paths {
		require.False(t, seen[strings.ToLower(path)], "%s is a path twice, the case of its letters aside", path)
		seen[strings.ToLower(path)] = true
		switch {
		case strings.HasPrefix(path, siteFamilyDir):
			require.NotNil(t, fold.byFamily[strings.TrimSuffix(strings.TrimPrefix(path, siteFamilyDir), ".json")], path)
			families++
		case strings.HasPrefix(path, siteProofDir):
			require.True(t, unit[strings.TrimSuffix(strings.TrimPrefix(path, siteProofDir), ".json")], "%s is a unit's page", path)
			units++
		}
	}
	require.Equal(t, len(c.Families), families)
	require.Equal(t, len(unit), units)
	require.Len(t, paths, 3+families+units)
	for _, m := range c.Members {
		require.True(t, seen[strings.ToLower(siteProofDir+fold.of(m.ID)+".json")], "%s has no page", m.ID)
	}

	// A spread of the paths is written as the whole is.
	some := []string{siteFamiliesPage, siteProofPage, siteFamilies}
	for i, path := range paths[3:] {
		if i%397 == 0 {
			some = append(some, path)
		}
	}
	dir := filepath.Join(t.TempDir(), "site")
	size, err := s.write(dir, some)
	require.NoError(t, err)
	require.Equal(t, len(some), size.Files)
	bytes := int64(0)
	for _, path := range some {
		want, err := s.File(path)
		require.NoError(t, err)
		got, err := os.ReadFile(filepath.Join(dir, filepath.FromSlash(path)))
		require.NoError(t, err, path)
		require.Equal(t, string(want), string(got), path)
		bytes += int64(len(got))
	}
	require.Equal(t, bytes, size.Bytes)

	_, err = s.Write(dir)
	require.ErrorContains(t, err, "is not empty")
	_, err = s.write(t.TempDir(), []string{siteProofDir + "a/b.Name.json", siteProofDir + "a/b.name.json"})
	require.ErrorContains(t, err, "differ by the case of a letter alone")
	_, err = s.write(t.TempDir(), []string{"no/such/file"})
	require.True(t, errors.Is(err, ErrNoPage))
}
