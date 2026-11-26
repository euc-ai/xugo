package visualize

// The site: the corpus as pages to browse, a set of files with no
// program behind them. The same files are served as they are asked for
// (Site.ServeHTTP) and written to a directory to be published as they
// are (Site.Write).
//
// Two pages draw what the files under data/ hold. index.html is the
// family graph, and proof.html a unit's graph, the unit named by the
// address (proof.html?m=<family>.<Name>). Neither holds a graph: a page
// asks for its data and paints it.
//
// What is said of a unit is held once, with its family, in
// data/family/<family>.json: its statement, its gloss, its stratum, what
// it stands on and, for a theorem, the units it uses and those using it
// (SiteFamily), and with them the family's gloss and its README's
// introduction. A unit's page, data/proof/<family>.<Name>.json,
// holds its layout alone (SitePage): which units are drawn, where, and
// the edges between them. A unit is drawn on the pages of all that
// stands on it, so its statement held once is held forty times fewer.
// data/families.json is the family graph's layout (SiteFamilies).
//
// The pages' links are relative, so the site reads the same under any
// address it is published at; a search is the page's own, over the
// families' files.

import (
	"encoding/json"
	"errors"
	"fmt"
	"math/bits"
	"net/http"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"sort"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/library/index"
)

// The site's paths: its two pages, the family graph's layout, and the
// directories of the families' files and of the units' pages, a file
// there named by the family or the unit with ".json" after it.
const (
	siteFamiliesPage = "index.html"
	siteProofPage    = "proof.html"
	siteFamilies     = "data/families.json"
	siteFamilyDir    = "data/family/"
	siteProofDir     = "data/proof/"
)

// ErrNoPage is the error of a path the site holds no file at.
var ErrNoPage = errors.New("the site holds no such file")

// SiteFamilies is the family graph's layout: FamilyGraph without what
// is said of a family, which its own file holds.
type SiteFamilies struct {
	Width  int              `json:"width"`
	Height int              `json:"height"`
	Axis   float64          `json:"axis"`
	Base   float64          `json:"base"`
	Step   float64          `json:"step"`
	Block  float64          `json:"block"`
	Layers int              `json:"layers"`
	Nodes  []SiteFamilyNode `json:"nodes"`
	Edges  []FamilyEdge     `json:"edges"`
}

// SiteFamilyNode is a family's block and its counts (FamilyNode), and
// Definitions the number of its definitions as FamilyNode lists them, a
// door call that registered several members counted once.
type SiteFamilyNode struct {
	Family          string  `json:"family"`
	Height          int     `json:"height"`
	Members         int     `json:"members"`
	Proved          int     `json:"proved"`
	ProvedTheorems  int     `json:"proved_theorems"`
	TheoremsOnCards int     `json:"theorems_on_cards"`
	Definitions     int     `json:"definitions"`
	Postulates      int     `json:"postulates"`
	Cards           int     `json:"cards"`
	X               float64 `json:"x"`
	Y               float64 `json:"y"`
	W               float64 `json:"w"`
}

// SiteFamily is what the site says of a family and of its units, once:
// the family's one line, its formulas typeset, its README's
// introduction (readmeIntro), and its units in the chapter's order.
type SiteFamily struct {
	Family string        `json:"family"`
	Gloss  string        `json:"gloss,omitempty"`
	Intro  []ReadmeBlock `json:"intro"`
	Units  []SiteUnit    `json:"units"`
}

// SiteUnit is a unit as every page drawing it reads it (ProofNode): its
// name, whether it is a definition, its stratum, the results it stands
// on in the whole corpus (_Fold.result) and the cards among them, its
// gloss, and its members, a member registered alone being the one. A
// theorem's Uses are the units it cites (_Fold.deps) and its UsedBy the
// units citing it, each in id order: the registry's, whatever a page
// draws. A definition has neither, its own page drawing both. A card's
// Plan counts its Uses by kind; another unit has none.
type SiteUnit struct {
	Name       string       `json:"name"`
	Definition bool         `json:"definition,omitzero"`
	Status     string       `json:"status"`
	Theorems   int          `json:"theorems"`
	Cards      int          `json:"cards"`
	Gloss      string       `json:"gloss,omitempty"`
	Members    []SiteMember `json:"members"`
	Uses       []string     `json:"uses,omitempty"`
	UsedBy     []string     `json:"used_by,omitempty"`
	Plan       *SitePlan    `json:"plan,omitempty"`
}

// SitePlan is what a card's plan cites, the units its proof is to cite
// (_Fold.deps), by kind: the results (_Fold.result), the postulates,
// and the definitions, a structure, a type and a door call among them.
type SitePlan struct {
	Results     int `json:"results"`
	Postulates  int `json:"postulates"`
	Definitions int `json:"definitions"`
}

// SiteMember is a member of a unit: its kind (index.Member.Kind), its
// own stratum, and what it states.
type SiteMember struct {
	Kind   string `json:"kind"`
	Status string `json:"status"`
	ProofStatement
}

// SitePage is a unit's graph as its page holds it: the layout of
// ProofGraph, and nothing a family's file says. Units are the units
// drawn at any grain, in id order, and a node names its unit by its
// place there. Definition is ProofGraph's, a user's stratum left to its
// family's file.
type SitePage struct {
	Target     string           `json:"target"`
	Units      []string         `json:"units"`
	Definition *ProofDefinition `json:"definition,omitempty"`
	Grains     []SiteGrain      `json:"grains"`
}

// SiteGrain is ProofGrain with its nodes and edges as a page holds
// them.
type SiteGrain struct {
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
	Nodes     []SiteNode    `json:"nodes"`
	Edges     []SiteEdge    `json:"edges"`
	Groups    []ProofGroup  `json:"groups,omitempty"`
}

// SiteNode is a node's place: its unit's place among the page's Units,
// its column, which gives its left edge and its width, and the height
// of its top. A node standing for a family, or for the families not
// drawn, has no unit: ID is the family's name or usesMoreID, and Use,
// Users and Families are ProofNode's.
type SiteNode struct {
	Unit     int     `json:"u"`
	Column   int     `json:"c"`
	Y        float64 `json:"y"`
	Ambient  bool    `json:"ambient,omitzero"`
	Target   bool    `json:"target,omitzero"`
	ID       string  `json:"id,omitempty"`
	Use      string  `json:"use,omitempty"`
	Users    int     `json:"users,omitzero"`
	Families int     `json:"families,omitzero"`
}

// SiteEdge is ProofEdge, its ends named by their places among the
// grain's nodes.
type SiteEdge struct {
	S   int     `json:"s"`
	T   int     `json:"t"`
	Via bool    `json:"via,omitzero"`
	Y1  float64 `json:"y1"`
	Y2  float64 `json:"y2"`
}

// SiteSize is what a site written holds: its files and their bytes.
type SiteSize struct {
	Files int   `json:"files"`
	Bytes int64 `json:"bytes"`
}

// Site is the corpus as a site. command is the command that serves or
// writes it, which a page's first line names.
type Site struct {
	corpus  *index.Corpus
	command string
	fold    *_Fold
	spread  map[string]int

	counted sync.Once
	under   map[string][2]int
	citers  map[string][]string

	laidOut     sync.Once
	families    []byte
	familiesErr error
}

// NewSite reads a corpus as a site.
func NewSite(c *index.Corpus, command string) *Site {
	return &Site{corpus: c, command: command, fold: foldDoors(c), spread: familySpread(c)}
}

// units are the units of the corpus, each once, in its members' order.
func (fold *_Fold) units() []string {
	var units []string
	seen := map[string]bool{}
	for _, m := range fold.corpus.Members {
		if u := fold.of(m.ID); !seen[u] {
			seen[u] = true
			units = append(units, u)
		}
	}
	return units
}

// counts is, for every unit, the results it stands on, by one citation
// or through others, and the cards among them (_Cone.under), counted
// for the whole corpus in one walk: a unit's reach is a set of units,
// the union of its deps and of their reaches.
func (fold *_Fold) counts() map[string][2]int {
	units := fold.units()
	place := make(map[string]int, len(units))
	for i, u := range units {
		place[u] = i
	}
	words := (len(units) + 63) / 64
	theorems, cards := make([]uint64, words), make([]uint64, words)
	for i, u := range units {
		if fold.result(u) {
			theorems[i/64] |= 1 << (i % 64)
		}
		if fold.byDoor[u] == nil && fold.byID[u].Card {
			cards[i/64] |= 1 << (i % 64)
		}
	}
	// The walk needs no guard, the units' relation being acyclic
	// (reduceScope).
	reach := make([][]uint64, len(units))
	var walk func(i int) []uint64
	walk = func(i int) []uint64 {
		if reach[i] != nil {
			return reach[i]
		}
		set := make([]uint64, words)
		for _, d := range fold.deps(units[i]) {
			j := place[d]
			set[j/64] |= 1 << (j % 64)
			for w, word := range walk(j) {
				set[w] |= word
			}
		}
		reach[i] = set
		return set
	}
	under := make(map[string][2]int, len(units))
	for i, u := range units {
		var count [2]int
		for w, word := range walk(i) {
			count[0] += bits.OnesCount64(word & theorems[w])
			count[1] += bits.OnesCount64(word & cards[w])
		}
		under[u] = count
	}
	return under
}

// plan counts what a unit cites (_Fold.deps) by kind (SitePlan).
func (fold *_Fold) plan(u string) *SitePlan {
	plan := &SitePlan{}
	for _, d := range fold.deps(u) {
		switch {
		case fold.result(d):
			plan.Results++
		case fold.theorem(d):
			plan.Postulates++
		default:
			plan.Definitions++
		}
	}
	return plan
}

// citers is, for every unit, the units citing it (_Fold.deps), in id
// order.
func (fold *_Fold) citers() map[string][]string {
	citers := map[string][]string{}
	for _, u := range fold.units() {
		for _, d := range fold.deps(u) {
			citers[d] = append(citers[d], u)
		}
	}
	for _, list := range citers {
		sort.Strings(list)
	}
	return citers
}

// page is a page of the site: its template with the notice — the
// command that serves or writes the site — and with what both pages
// share (siteFragment), which reads the data and searches it. A
// template missing a slot is a defect of the tree, not of input.
func page(template, command string) []byte {
	for _, slot := range []string{pageNoticeSlot, pageSharedSlot} {
		if strings.Count(template, slot) != 1 {
			panic(fmt.Sprintf("visualize: a page template holds %q %d times, not once", slot, strings.Count(template, slot)))
		}
	}
	// "--" may not stand inside an HTML comment.
	notice := fmt.Sprintf("<!-- Written by `%s` from the proof registry (library/visualize). -->", strings.ReplaceAll(command, "--", "‐‐"))
	filled := strings.Replace(template, pageNoticeSlot, notice, 1)
	return []byte(strings.Replace(filled, pageSharedSlot, siteFragment, 1))
}

// encode is a value as a file of the site holds it. A value that does
// not encode — a coordinate that is no number — is a defect of the
// tree.
func encode(v any) []byte {
	data, err := json.Marshal(v)
	if err != nil {
		panic(fmt.Sprintf("visualize: %v", err))
	}
	return data
}

// Paths are the paths of the site's files: the two pages, the family
// graph's layout, every family's file and every unit's page.
func (s *Site) Paths() []string {
	paths := []string{siteFamiliesPage, siteProofPage, siteFamilies}
	for _, f := range s.corpus.Families {
		paths = append(paths, siteFamilyDir+f.Name+".json")
	}
	for _, u := range s.fold.units() {
		paths = append(paths, siteProofDir+u+".json")
	}
	return paths
}

// File is the file at a path of the site, and ErrNoPage for a path it
// holds none at. A unit's page is asked for by the unit's id, the name
// of every path in Paths; a member's registered name or own key, or a
// part of a door call, answers its unit's page too (_Fold.resolve).
func (s *Site) File(path string) ([]byte, error) {
	switch {
	case path == siteFamiliesPage:
		return page(familyGraphTemplate, s.command), nil
	case path == siteProofPage:
		return page(proofGraphTemplate, s.command), nil
	case path == siteFamilies:
		s.laidOut.Do(func() { s.families, s.familiesErr = s.layout() })
		return s.families, s.familiesErr
	case strings.HasPrefix(path, siteFamilyDir) && strings.HasSuffix(path, ".json"):
		f := s.fold.byFamily[strings.TrimSuffix(strings.TrimPrefix(path, siteFamilyDir), ".json")]
		if f == nil {
			return nil, fmt.Errorf("%w: %s names no family", ErrNoPage, path)
		}
		family, err := s.family(f)
		if err != nil {
			return nil, err
		}
		return encode(family), nil
	case strings.HasPrefix(path, siteProofDir) && strings.HasSuffix(path, ".json"):
		target, err := s.fold.resolve(strings.TrimSuffix(strings.TrimPrefix(path, siteProofDir), ".json"))
		if err != nil {
			return nil, fmt.Errorf("%w: %v", ErrNoPage, err)
		}
		return encode(sitePage(s.fold.draw(target, s.spread))), nil
	}
	return nil, fmt.Errorf("%w: %s", ErrNoPage, path)
}

// layout is the family graph's layout, encoded.
func (s *Site) layout() ([]byte, error) {
	g, err := Families(s.corpus)
	if err != nil {
		return nil, err
	}
	layout := SiteFamilies{Width: g.Width, Height: g.Height, Axis: g.Axis, Base: g.Base, Step: g.Step, Block: g.Block,
		Layers: g.Layers, Nodes: make([]SiteFamilyNode, len(g.Nodes)), Edges: g.Edges}
	for i, n := range g.Nodes {
		layout.Nodes[i] = SiteFamilyNode{Family: n.Family, Height: n.Height, Members: n.Members, Proved: n.Proved,
			ProvedTheorems: n.ProvedTheorems, TheoremsOnCards: n.TheoremsOnCards, Definitions: len(n.Definitions),
			Postulates: n.Postulates, Cards: n.Cards, X: n.X, Y: n.Y, W: n.W}
	}
	return encode(layout), nil
}

// family is what the site says of a family and of its units. A unit's
// gloss is read from its chapter file or README, and a file that
// declares nothing where the registry has the member is an error, as a
// README that cannot be read is (Proof).
func (s *Site) family(f *index.Family) (*SiteFamily, error) {
	s.counted.Do(func() { s.under, s.citers = s.fold.counts(), s.fold.citers() })
	gloss, err := typeset(f.Gloss)
	if err != nil {
		return nil, fmt.Errorf("visualize: family %s: %v", f.Name, err)
	}
	blocks, err := intro(s.corpus, f)
	if err != nil {
		return nil, fmt.Errorf("visualize: family %s: %v", f.Name, err)
	}
	family := &SiteFamily{Family: f.Name, Gloss: gloss, Intro: blocks, Units: []SiteUnit{}}
	listed := map[string]bool{}
	for _, m := range f.Members {
		u := s.fold.of(m.ID)
		if listed[u] {
			continue
		}
		listed[u] = true
		members := s.fold.members(u)
		gloss, err := s.corpus.Description(members[0])
		if err != nil {
			return nil, err
		}
		if gloss, err = typeset(gloss); err != nil {
			return nil, fmt.Errorf("visualize: the gloss of %s: %v", u, err)
		}
		unit := SiteUnit{Name: s.fold.name(u), Definition: !s.fold.theorem(u), Status: s.fold.status(u),
			Theorems: s.under[u][0], Cards: s.under[u][1], Gloss: gloss}
		if s.fold.theorem(u) {
			unit.Uses, unit.UsedBy = slices.Sorted(slices.Values(s.fold.deps(u))), s.citers[u]
		}
		if s.fold.byDoor[u] == nil && members[0].Card {
			unit.Plan = s.fold.plan(u)
		}
		for i, stated := range s.fold.statements(u) {
			unit.Members = append(unit.Members, SiteMember{Kind: members[i].Kind, Status: members[i].Status(), ProofStatement: stated})
		}
		family.Units = append(family.Units, unit)
	}
	return family, nil
}

// sitePage is a graph's layout as its page holds it.
func sitePage(g *ProofGraph) *SitePage {
	p := &SitePage{Target: g.Target, Units: []string{}}
	place := map[string]int{}
	for _, grain := range g.Grains {
		for _, n := range grain.Nodes {
			if _, listed := place[n.ID]; !listed && n.Use != useFamily && n.Use != useMore {
				place[n.ID] = 0
				p.Units = append(p.Units, n.ID)
			}
		}
	}
	sort.Strings(p.Units)
	for i, u := range p.Units {
		place[u] = i
	}
	if g.Definition != nil {
		d := *g.Definition
		d.Families = make([]ProofFamilyUses, len(g.Definition.Families))
		for i, f := range g.Definition.Families {
			d.Families[i] = ProofFamilyUses{Family: f.Family, Count: f.Count}
			for _, u := range f.Users {
				d.Families[i].Users = append(d.Families[i].Users, ProofUser{Name: u.Name, Use: u.Use})
			}
		}
		p.Definition = &d
	}
	for _, grain := range g.Grains {
		laid := SiteGrain{Key: grain.Key, Allowance: grain.Allowance, Theorems: grain.Theorems, PerFamily: grain.PerFamily,
			Width: grain.Width, Height: grain.Height, Block: grain.Block, Axis: grain.Axis, Line: grain.Line,
			Columns: grain.Columns, Nodes: make([]SiteNode, len(grain.Nodes)), Edges: make([]SiteEdge, len(grain.Edges)), Groups: grain.Groups}
		at := map[string]int{}
		for i, n := range grain.Nodes {
			at[n.ID] = i
			node := SiteNode{Column: n.Column, Y: n.Y, Ambient: n.Ambient, Target: n.Target, Use: n.Use, Users: n.Users, Families: n.Families}
			if n.Use == useFamily || n.Use == useMore {
				node.ID = n.ID
			} else {
				node.Unit = place[n.ID]
			}
			if column := grain.Columns[n.Column]; n.X != column.X || n.W != column.W {
				panic(fmt.Sprintf("visualize: %s is drawn at %v, %v wide, in a column at %v, %v wide", n.ID, n.X, n.W, column.X, column.W))
			}
			laid.Nodes[i] = node
		}
		for i, e := range grain.Edges {
			laid.Edges[i] = SiteEdge{S: at[e.S], T: at[e.T], Via: e.Via, Y1: e.Y1, Y2: e.Y2}
		}
		p.Grains = append(p.Grains, laid)
	}
	return p
}

// ServeHTTP answers the site's files as they are asked for, "/" being
// the family graph's page. An answer is never kept by the browser
// asking: the next asking is of the corpus as it is then.
func (s *Site) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet && r.Method != http.MethodHead {
		http.Error(w, "the site is read with GET", http.StatusMethodNotAllowed)
		return
	}
	path := strings.TrimPrefix(r.URL.Path, "/")
	if path == "" {
		path = siteFamiliesPage
	}
	w.Header().Set("Cache-Control", "no-store")
	body, err := s.File(path)
	switch {
	case errors.Is(err, ErrNoPage):
		http.Error(w, err.Error(), http.StatusNotFound)
		return
	case err != nil:
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	kind := "application/json; charset=utf-8"
	if strings.HasSuffix(path, ".html") {
		kind = "text/html; charset=utf-8"
	}
	w.Header().Set("Content-Type", kind)
	w.Write(body)
}

// Write writes the site into a directory, which it makes where there is
// none and which must hold nothing: a site written over another would
// keep the pages of members the corpus no longer has.
func (s *Site) Write(dir string) (SiteSize, error) {
	held, err := os.ReadDir(dir)
	if err != nil && !os.IsNotExist(err) {
		return SiteSize{}, err
	}
	if len(held) > 0 {
		return SiteSize{}, fmt.Errorf("%s is not empty: a site is written into an empty directory", dir)
	}
	return s.write(dir, s.Paths())
}

// write writes the files at the paths given, the processors side by
// side. Two paths that differ by the case of a letter alone are refused:
// a file system that tells no case apart would keep one of the two
// files.
func (s *Site) write(dir string, paths []string) (SiteSize, error) {
	folded := map[string]string{}
	for _, path := range paths {
		if other, held := folded[strings.ToLower(path)]; held {
			return SiteSize{}, fmt.Errorf("%s and %s differ by the case of a letter alone", other, path)
		}
		folded[strings.ToLower(path)] = path
	}
	var (
		mu      sync.Mutex
		size    SiteSize
		failed  error
		next    int
		writers sync.WaitGroup
	)
	for range runtime.NumCPU() {
		writers.Go(func() {
			for {
				mu.Lock()
				if failed != nil || next == len(paths) {
					mu.Unlock()
					return
				}
				path := paths[next]
				next++
				mu.Unlock()

				body, err := s.File(path)
				if err == nil {
					file := filepath.Join(dir, filepath.FromSlash(path))
					if err = os.MkdirAll(filepath.Dir(file), 0o755); err == nil {
						err = os.WriteFile(file, body, 0o644)
					}
				}
				mu.Lock()
				if err != nil && failed == nil {
					failed = fmt.Errorf("%s: %w", path, err)
				}
				size.Files++
				size.Bytes += int64(len(body))
				mu.Unlock()
			}
		})
	}
	writers.Wait()
	if failed != nil {
		return SiteSize{}, failed
	}
	return size, nil
}
