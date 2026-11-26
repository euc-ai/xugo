package index

import (
	"encoding/json"
	"path"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	_ "github.com/euc-ai/xugo/library/proofs" // register the corpus
	"github.com/euc-ai/xugo/library/registry"
)

// corpusRoot is library/proofs relative to this package's directory.
const corpusRoot = "../proofs"

func load(t *testing.T) *Corpus {
	t.Helper()
	c, err := Load(corpusRoot)
	require.NoError(t, err)
	return c
}

// The index holds exactly the registry: every registered entry under
// its id, and nothing else.
func TestIndexHoldsTheRegistry(t *testing.T) {
	c := load(t)
	require.Equal(t, len(registry.All()), len(c.Members))
	for _, e := range registry.All() {
		m, ok := c.Resolve(MemberID(e))
		require.True(t, ok, "%s is not indexed", e.Name)
		require.Equal(t, e.Name, m.Entry)
		byName, ok := c.Resolve(e.Name)
		require.True(t, ok)
		require.Same(t, m, byName, "%s resolves differently by id and by name", e.Name)
		byKey, ok := c.Resolve(e.Key)
		require.True(t, ok)
		require.Same(t, m, byKey, "%s resolves differently by id and by key", e.Name)
	}
	_, ok := c.Resolve("no/such.Member")
	require.False(t, ok)
}

// A bare name — the name after the family's — is no reference: it
// finds every member under it, family by family. A question of one
// member takes a bare name one member alone has and refuses one
// several have, listing them; the corpus's shared and lone names are
// picked at run time.
func TestBareNameFindsEveryMemberUnderIt(t *testing.T) {
	c := load(t)
	shared, alone := "", ""
	for _, m := range c.Members {
		under := c.ResolveBare(m.bare())
		require.Contains(t, under, m, "%s is not under its bare name", m.ID)
		switch {
		case len(under) > 1 && shared == "":
			shared = m.bare()
		case len(under) == 1 && alone == "":
			alone = m.bare()
		}
	}
	require.NotEmpty(t, shared, "the corpus has a bare name several members share")
	require.NotEmpty(t, alone)

	ms := c.ResolveBare(shared)
	ids := make([]string, len(ms))
	for i, m := range ms {
		require.Equal(t, shared, m.bare())
		ids[i] = m.ID
	}
	require.True(t, slices.IsSortedFunc(ms, func(a, b *Member) int { return strings.Compare(a.Family, b.Family) }), "family by family")
	_, ok := c.Resolve(shared)
	require.False(t, ok, "a bare name is no reference")
	_, err := c.ResolveOne(shared)
	require.EqualError(t, err, `"`+shared+`" is the bare name of `+strconv.Itoa(len(ms))+` members, `+strings.Join(ids, ", ")+`: name one by its id or registered name`)
	_, err = c.Between(shared, ms[0].ID)
	require.ErrorContains(t, err, "is the bare name of", "a question of one member refuses a shared bare name")

	one, err := c.ResolveOne(alone)
	require.NoError(t, err)
	require.Equal(t, alone, one.bare())

	require.Empty(t, c.ResolveBare("ZzNoSuchMember"))
	_, err = c.ResolveOne("ZzNoSuchMember")
	require.ErrorContains(t, err, `"ZzNoSuchMember" names no corpus member`)
}

// Every member knows where it was registered, and the file is in its
// own family's directory.
func TestMembersCarryTheirSource(t *testing.T) {
	c := load(t)
	for _, m := range c.Members {
		require.NotEmpty(t, m.Source, "%s has no source position", m.ID)
		f := c.byFamily[m.Family]
		require.True(t, strings.HasPrefix(m.Source, f.Dir+"/"), "%s registered at %s, outside its family directory %s", m.ID, m.Source, f.Dir)
	}
}

// Every family has a gloss, read off its README's title line.
func TestFamiliesHaveGlosses(t *testing.T) {
	c := load(t)
	for _, f := range c.Families {
		require.NotEmpty(t, f.Gloss, "%s: no gloss (README title line is not '# name — gloss')", f.Name)
	}
	require.Equal(t, "sequences of reals and their limits", c.byFamily["real/real_sequences"].Gloss)
}

// A family resolves by its path and by its short name, the path's last
// element, when no other family has that short name. A short name two
// families share resolves to neither, and the refusal lists both paths,
// unless it is one family's path: the path is read first. The corpus
// has no such pair, so the pairs are hand-built.
func TestFamilyResolvesByPathAndShortName(t *testing.T) {
	c := load(t)
	for _, f := range c.Families {
		byPath, ok := c.ResolveFamily(f.Name)
		require.True(t, ok, "%s does not resolve by its path", f.Name)
		require.Same(t, f, byPath)
		short := path.Base(f.Name)
		if len(c.byShort[short]) > 1 {
			continue
		}
		byShort, ok := c.ResolveFamily(short)
		require.True(t, ok, "%s does not resolve by its short name %s", f.Name, short)
		require.Same(t, f, byShort, "%s resolves differently by path and by short name", f.Name)
	}
	_, ok := c.ResolveFamily("zz_no_family")
	require.False(t, ok)
	_, err := c.FamilyView("zz_no_family")
	require.ErrorContains(t, err, `"zz_no_family" names no family`)

	x, y := &Family{Name: "x/shared"}, &Family{Name: "y/shared"}
	pair := &Corpus{
		byFamily: map[string]*Family{x.Name: x, y.Name: y},
		byShort:  map[string][]*Family{"shared": {x, y}},
	}
	_, ok = pair.ResolveFamily("shared")
	require.False(t, ok, "a short name two families share names neither")
	got, ok := pair.ResolveFamily("y/shared")
	require.True(t, ok)
	require.Same(t, y, got)
	_, err = pair.FamilyView("shared")
	require.EqualError(t, err, `"shared" is the short name of 2 families, x/shared, y/shared: name one by its path`)

	flat, nested := &Family{Name: "shared"}, &Family{Name: "x/shared"}
	withFlat := &Corpus{
		byFamily: map[string]*Family{flat.Name: flat, nested.Name: nested},
		byShort:  map[string][]*Family{"shared": {flat, nested}},
	}
	got, ok = withFlat.ResolveFamily("shared")
	require.True(t, ok, "a flat family's path is its short name, and the path is read first")
	require.Same(t, flat, got)
}

// The reverse edges and the family graph are the Deps, read backwards
// and projected.
func TestEdgesAreTheDeps(t *testing.T) {
	c := load(t)
	for _, m := range c.Members {
		for _, id := range m.Deps {
			dep := c.byID[id]
			require.Contains(t, dep.Dependents, m.ID, "%s cites %s, which does not list it", m.ID, id)
			if dep.Family != m.Family {
				require.Contains(t, c.byFamily[m.Family].Imports, dep.Family)
				require.Contains(t, c.byFamily[dep.Family].Importers, m.Family)
			}
		}
	}
	for _, f := range c.Families {
		require.NotContains(t, f.Imports, f.Name, "%s imports itself", f.Name)
	}
}

// Every constant a chapter mints is indexed once, under the member
// whose door minted it.
func TestDefinitionsAreTheMints(t *testing.T) {
	c := load(t)
	minted := 0
	for _, e := range registry.All() {
		for _, name := range e.Defines() {
			minted++
			d, ok := c.byConst[name]
			require.True(t, ok, "%s mints %s, which is not indexed", e.Name, name)
			require.Equal(t, MemberID(e), d.Member)
		}
	}
	registry.GetConstMetaManager().RangeMintSources(func(name core.TermName, source string) bool {
		_, ok := c.byConst[string(name)]
		require.True(t, ok, "%s is minted at %s through no define door", name, source)
		return true
	})
	require.Equal(t, minted, len(c.Definitions))
	d, err := c.DefinitionView("int_gcd")
	require.NoError(t, err)
	require.Equal(t, "int_num/int_divides", d.Definition.Family)
	require.NotEmpty(t, d.Mentions)
	gcd, err := c.DefinitionView("nat_gcd")
	require.NoError(t, err)
	require.Equal(t, "nat_num/nat_gcd", gcd.Definition.Family)
	require.Equal(t, "nat_num/nat_gcd.GcdDef", gcd.Definition.Member)
	_, err = c.DefinitionView("no_such_constant")
	require.Error(t, err)
}

// Several constants are answered at once, each in the order named: a
// defined one by its DefinitionView, any other name by the refusal
// DefinitionView gives it — a type's naming its minting member, a
// declared word's the constants it spells.
func TestConstantsViewAnswersEachName(t *testing.T) {
	c := load(t)
	v := c.ConstantsView([]string{"nat_gcd", "ring_ops", "int_gcd", "div", "no_such_constant"})
	var defined []string
	for _, d := range v.Definitions {
		defined = append(defined, d.Definition.Const)
	}
	require.Equal(t, []string{"nat_gcd", "int_gcd"}, defined)
	gcd, err := c.DefinitionView("int_gcd")
	require.NoError(t, err)
	require.Equal(t, gcd, v.Definitions[1])
	require.Len(t, v.Undefined, 3)
	require.Equal(t, "ring_ops", v.Undefined[0].Name)
	require.Contains(t, v.Undefined[0].Reason, "is a type, minted by algebra/module/module_record.")
	require.Equal(t, "div", v.Undefined[1].Name)
	require.Contains(t, v.Undefined[1].Reason, "is a word, spelling int_div, nat_div")
	require.Equal(t, "no_such_constant", v.Undefined[2].Name)
	require.Contains(t, v.Undefined[2].Reason, "is defined by no chapter")
}

// The overview is the totals and one line per family, and inlines
// nothing another question serves.
func TestOverview(t *testing.T) {
	c := load(t)
	o := c.Overview()
	encoded, err := json.Marshal(o)
	require.NoError(t, err)
	require.NotContains(t, string(encoded), `"imports"`, "the overview inlines the families' imports")
	require.Equal(t, len(c.Families), func() (n int) {
		for _, d := range o.Domains {
			n += len(d.Families)
		}
		return
	}())
	require.Equal(t, c.Totals(), o.Totals)
}

// The three strata partition every family; a family stands strictly
// above every family it imports; a card's depth exceeds each card it
// cites; the frontier splits the cards exactly; the domain edges weigh
// the cross-domain family imports.
func TestStrataHeightsAndFrontier(t *testing.T) {
	c := load(t)
	for _, f := range c.Families {
		require.Equal(t, f.Counts.Members, f.Counts.Proved+f.Counts.OnCards+f.Counts.Cards+f.Counts.Postulates, "%s: the strata do not partition the members", f.Name)
		for _, imp := range f.Imports {
			require.Greater(t, f.Height, c.byFamily[imp].Height, "%s imports %s but is not above it", f.Name, imp)
		}
		if len(f.Imports) == 0 {
			require.Equal(t, 0, f.Height, "%s imports nothing and has a height", f.Name)
		}
	}
	cards := 0
	for _, m := range c.Members {
		if !m.Card {
			require.Equal(t, 0, m.Depth, "%s is no card and has a depth", m.ID)
			continue
		}
		cards++
		require.GreaterOrEqual(t, m.Depth, 1)
		for _, id := range m.Deps {
			if dep := c.byID[id]; dep.Card {
				require.Greater(t, m.Depth, dep.Depth, "%s cites the card %s but is not deeper", m.ID, id)
			}
		}
	}
	v, err := c.CardsView()
	require.NoError(t, err)
	require.Equal(t, cards, len(v.Cards))
	axioms := c.AxiomsView()
	require.Equal(t, v.Cards, axioms.Cards, "the axioms view lists the cards in the cards view's order")
	require.Len(t, axioms.Postulates, 1, "the registry admits one postulate")
	require.Equal(t, "nat_num/peano.Infinity", axioms.Postulates[0].Member.ID)
	require.Equal(t, c.byID["nat_num/peano.Infinity"].Dependents, axioms.Postulates[0].CitedBy)
	require.Equal(t, cards, len(v.Leaves)+len(v.OnCards), "leaves and on_cards do not partition the cards")
	for _, card := range v.Leaves {
		require.Equal(t, []string{card.Member.ID}, c.byID[card.Member.ID].Cards, "%s is listed a leaf but stands on a card", card.Member.ID)
	}
	for _, card := range v.OnCards {
		require.NotEmpty(t, card.On)
		require.NotContains(t, card.On, card.Member.ID)
	}
	for _, h := range v.Heads {
		require.Empty(t, c.byID[h.Member.ID].Dependents, "%s is listed a head but is cited", h.Member.ID)
		require.Equal(t, len(c.byID[h.Member.ID].Cards)-1, h.Under)
	}
	o := c.Overview()
	cross := 0
	for _, f := range c.Families {
		for _, imp := range f.Imports {
			if c.byFamily[imp].Domain != f.Domain {
				cross++
			}
		}
	}
	weighed := 0
	for _, e := range o.DomainEdges {
		require.NotEqual(t, e.From, e.To)
		weighed += e.Weight
	}
	require.Equal(t, cross, weighed, "the domain edges do not weigh every cross-domain import")
}

// The cards of some families are the corpus's cards of those families:
// in its fill order, split and headed as there, with the families'
// members standing on a card. A family is named as FamilyView names
// one, and a name naming none refuses the view. Spell fills the typed
// spelling of every card in every list.
func TestCardsViewOfFamilies(t *testing.T) {
	c := load(t)
	all, err := c.CardsView()
	require.NoError(t, err)
	var picked []*Family
	for _, f := range c.Families {
		if f.Counts.Cards > 0 && len(picked) < 2 {
			picked = append(picked, f)
		}
	}
	require.Len(t, picked, 2, "the corpus has two families holding cards")
	kept := map[string]bool{picked[0].Name: true, picked[1].Name: true}
	v, err := c.CardsView(path.Base(picked[0].Name), picked[1].Name)
	require.NoError(t, err)

	ids := func(cards []Card) []string {
		var out []string
		for _, card := range cards {
			out = append(out, card.Member.ID)
		}
		return out
	}
	keptIDs := func(cards []Card) []string {
		var out []string
		for _, card := range cards {
			if kept[card.Member.Family] {
				out = append(out, card.Member.ID)
			}
		}
		return out
	}
	require.Len(t, v.Cards, picked[0].Counts.Cards+picked[1].Counts.Cards)
	require.Equal(t, keptIDs(all.Cards), ids(v.Cards), "the families' cards in the corpus's fill order")
	require.Equal(t, keptIDs(all.Leaves), ids(v.Leaves))
	var allOn []CardOnCards
	for _, x := range all.OnCards {
		if kept[x.Member.Family] {
			allOn = append(allOn, x)
		}
	}
	require.Equal(t, allOn, v.OnCards)
	var allHeads []Head
	for _, h := range all.Heads {
		if kept[h.Member.Family] {
			allHeads = append(allHeads, h)
		}
	}
	require.Equal(t, allHeads, v.Heads)
	var allStanding []Standing
	for _, s := range all.Standing {
		if kept[s.Member.Family] {
			allStanding = append(allStanding, s)
		}
	}
	require.Equal(t, allStanding, v.Standing)

	_, err = c.CardsView(picked[0].Name, "zz_no_family")
	_, refusal := c.FamilyView("zz_no_family")
	require.EqualError(t, err, refusal.Error(), "a name naming no family refuses the view as it refuses the family")

	require.Empty(t, v.Cards[0].StatementTyped, "the index spells no card typed")
	v.Spell(func(entry string) string { return "typed " + entry })
	for _, card := range v.Cards {
		require.Equal(t, "typed "+card.Member.Entry, card.StatementTyped)
	}
	for _, card := range v.Leaves {
		require.Equal(t, "typed "+card.Member.Entry, card.StatementTyped)
	}
	for _, card := range v.OnCards {
		require.Equal(t, "typed "+card.Member.Entry, card.StatementTyped)
	}
}

// A statement's constants are split by where it mentions them, the two
// halves together its constants; a constant's definition view says
// who establishes it and who asks for it, by stratum, the definition
// doors establishing nothing.
func TestConstantsByRole(t *testing.T) {
	c := load(t)
	tower := c.byID["algebra/field/galois_correspondence.GaloisTower"]
	require.Contains(t, tower.ConclusionConstants, "galois_over")
	require.Contains(t, tower.HypothesisConstants, "galois_over")
	require.Contains(t, tower.HypothesisConstants, "subfield")
	require.NotContains(t, tower.ConclusionConstants, "subfield")
	def := c.byID["algebra/field/galois_correspondence.GaloisOverDef"]
	require.Contains(t, def.ConclusionConstants, "finite_extension")
	require.Empty(t, def.HypothesisConstants)
	for _, m := range c.Members {
		both := append(append([]string{}, m.ConclusionConstants...), m.HypothesisConstants...)
		for _, name := range m.Constants {
			require.Contains(t, both, name, "%s mentions %s under neither its conclusion nor its hypotheses", m.ID, name)
		}
		for _, name := range both {
			require.Contains(t, m.Constants, name, "%s lists %s by role and not among its constants", m.ID, name)
		}
	}
	d, err := c.DefinitionView("galois_over")
	require.NoError(t, err)
	var concluders, assumers []string
	for _, s := range d.ConcludedBy {
		for _, id := range s.Members {
			require.Equal(t, s.Status, c.byID[id].Status(), id)
			require.Contains(t, c.byID[id].ConclusionConstants, "galois_over", id)
			require.False(t, c.byID[id].isDoor(), id)
		}
		concluders = append(concluders, s.Members...)
	}
	for _, s := range d.AssumedBy {
		for _, id := range s.Members {
			require.Equal(t, s.Status, c.byID[id].Status(), id)
			require.Contains(t, c.byID[id].HypothesisConstants, "galois_over", id)
		}
		assumers = append(assumers, s.Members...)
	}
	require.NotContains(t, concluders, def.ID, "the definition door establishes nothing")
	require.Contains(t, concluders, tower.ID)
	require.Contains(t, assumers, tower.ID)
	require.Contains(t, assumers, "algebra/field/galois_correspondence.CorrespondenceFixed")
	require.NotContains(t, concluders, "algebra/field/galois_correspondence.CorrespondenceFixed")
	// Empty strata are written, not left out.
	encoded, err := json.Marshal(&DefinitionView{Definition: d.Definition, ConcludedBy: []StratumMembers{}, AssumedBy: []StratumMembers{}})
	require.NoError(t, err)
	require.Contains(t, string(encoded), `"concluded_by":[]`)
}

// A card's backing is read off the registry: the theorems among its
// deps and the members its note names, resolved, bare names in the
// card's own family first; a card whose note names nothing and cites
// definition doors alone shows both lists empty, written; a member
// that is no card has no backing.
func TestCardBacking(t *testing.T) {
	c := load(t)
	bareAt := slices.IndexFunc(c.Members, func(m *Member) bool {
		return m.Card && len(m.Backing.TheoremDeps) == 0 && len(m.Backing.NoteNames) == 0
	})
	require.GreaterOrEqual(t, bareAt, 0, "no card shows both lists empty")
	encoded, err := json.Marshal(c.Members[bareAt])
	require.NoError(t, err)
	require.Contains(t, string(encoded), `"theorem_deps":[]`)
	require.Contains(t, string(encoded), `"note_names":[]`)
	// The cards are taken at run time, never by name: a card exists to
	// be filled. One whose note names a member of another chapter by
	// its bare name shows that name resolved there.
	crossAt := slices.IndexFunc(c.Members, func(m *Member) bool {
		if !m.Card {
			return false
		}
		for _, n := range m.Backing.NoteNames {
			if n.Member != "" && !strings.Contains(n.Name, ".") && c.byID[n.Member].Family != m.Family {
				return true
			}
		}
		return false
	})
	require.GreaterOrEqual(t, crossAt, 0, "no card's note names a member of another chapter")
	for _, n := range c.Members[crossAt].Backing.NoteNames {
		if n.Member != "" && !strings.Contains(n.Name, ".") {
			x := c.byID[n.Member]
			require.True(t, strings.HasSuffix(x.ID, "."+n.Name), "%s resolves %s to %s", c.Members[crossAt].ID, n.Name, x.ID)
		}
	}
	for _, m := range c.Members {
		if !m.Card {
			require.Nil(t, m.Backing, "%s is no card and has a backing", m.ID)
			continue
		}
		require.NotNil(t, m.Backing, "%s is a card without a backing", m.ID)
		for _, id := range m.Backing.TheoremDeps {
			require.Contains(t, m.Deps, id)
			require.False(t, c.byID[id].isDoor(), "%s lists the door %s as a theorem dep", m.ID, id)
		}
		for _, n := range m.Backing.NoteNames {
			require.NotEqual(t, n.Member, m.ID, "%s lists itself", m.ID)
			if !strings.Contains(n.Name, ".") && !camelCase(n.Name) {
				require.NotEmpty(t, n.Member, "%s lists the one-hump prose word %s", m.ID, n.Name)
				require.Equal(t, m.Family, c.byID[n.Member].Family, "%s lists the one-hump word %s from another chapter", m.ID, n.Name)
			}
			if n.Member != "" {
				_, ok := c.byID[n.Member]
				require.True(t, ok, "%s resolves %s to %s, which is no member", m.ID, n.Name, n.Member)
				require.Empty(t, n.Candidates)
			}
			for _, id := range n.Candidates {
				_, ok := c.byID[id]
				require.True(t, ok)
			}
		}
		for _, id := range m.Backing.NoteNamesNotCited {
			require.NotContains(t, m.Deps, id)
		}
	}
}

// A member's chapter file read as text yields its gloss, the doc
// comment with the `Name — ` left off, and its outline: the narration
// steps in source order, each with its label, its claim where the verb
// takes one, the members its proof cites and the names it uses. Every
// member is declared in its file at its registered line; every cite an
// outline lists is among the member's recorded deps; a card has no
// outline.
func TestGlossAndOutline(t *testing.T) {
	c := load(t)
	tower, err := c.MemberView("algebra/field/field_extension.TowerLaw")
	require.NoError(t, err)
	require.True(t, strings.HasPrefix(tower.Gloss, "degrees multiply in a tower"), tower.Gloss)
	steps, err := c.Outline(tower)
	require.NoError(t, err)
	require.NotEmpty(t, steps)
	first := steps[0]
	require.Equal(t, "ObtainAs", first.Verb)
	require.Equal(t, "M has a finite basis B over K", first.Label)
	require.True(t, strings.HasPrefix(first.Claim, "∃B:set(A). finite(B)"), first.Claim)
	require.Equal(t, []string{"algebra/field/field_extension.FiniteExtensionDef", "algebra/module/module_dimension.FiniteDimensionalDef"}, first.Cites)
	require.Equal(t, []string{"tower"}, first.Uses)
	require.Equal(t, 0, first.Depth)
	var verbs, cites []string
	for _, s := range steps {
		verbs = append(verbs, s.Verb)
		cites = append(cites, s.Cites...)
		require.Positive(t, s.Line)
		require.LessOrEqual(t, s.Depth, 0, "TowerLaw's argument opens no closure")
	}
	require.Contains(t, verbs, "Have")
	require.Contains(t, verbs, "Show")
	require.Contains(t, cites, "algebra/field/field_extension.TowerBasis")
	require.Contains(t, cites, "algebra/field/field_extension.BasisDegree")
	var card *Member
	for _, m := range c.Members {
		if m.Card {
			card = m
			break
		}
	}
	require.NotNil(t, card, "the corpus holds no card")
	steps, err = c.Outline(card)
	require.NoError(t, err)
	require.Empty(t, steps)
	// Every member is found in its file; every cite names a member.
	// That what a proof names is among what its replay recorded is the
	// gates' lint (TestLintProofNamesRecordedDeps).
	nested := false
	for _, f := range c.Families {
		require.NoError(t, c.readGlosses(f), f.Name)
		for _, m := range f.Members {
			steps, err := c.Outline(m)
			require.NoError(t, err, m.ID)
			if m.Card || m.isDoor() {
				require.Empty(t, steps, "%s has no Go argument and an outline", m.ID)
			}
			for _, s := range steps {
				require.NotEmpty(t, s.Verb)
				require.Positive(t, s.Line)
				if s.Depth > 0 {
					nested = true
				}
				for _, id := range s.Cites {
					_, ok := c.byID[id]
					require.True(t, ok, "%s cites %s, which is no member", m.ID, id)
				}
			}
		}
	}
	require.True(t, nested, "no proof in the corpus opens a closure")
	// A local bound to a citation carries it: the step passing
	// `counted`, bound to cardinality.HasSizeDef.At(…), cites HasSizeDef.
	steps, err = c.Outline(tower)
	require.NoError(t, err)
	aliased := false
	for _, s := range steps {
		if slices.Contains(s.Uses, "counted") {
			require.Contains(t, s.Cites, "sets/cardinality.HasSizeDef", "line %d", s.Line)
			aliased = true
		}
	}
	require.True(t, aliased, "no step of TowerLaw passes counted")
	// A member a stale file declares nothing at the line of is refused.
	moved := *tower
	moved.Source = strings.TrimSuffix(tower.Source, tower.Source[strings.LastIndex(tower.Source, ":"):]) + ":1"
	_, err = c.Outline(&moved)
	require.ErrorContains(t, err, "the binary and the tree differ")
	// A door minting several members from one declaration gives each
	// the declaration's comment and no outline.
	rules, ok := c.Resolve("algebra/group/free_group.wordEquivRules")
	require.True(t, ok)
	require.NoError(t, c.readGloss(rules))
	require.True(t, strings.HasPrefix(rules.Gloss, "the equivalence of words"), rules.Gloss)
}

// The dossier reads a member in the round: the constants it spells
// with their definitions, its stratum and plan, the suppliers of its
// hypotheses' predicates, its citation at the statement's witnesses.
func TestDossier(t *testing.T) {
	c := load(t)
	d, err := c.Dossier("topology/real_valued.Urysohn")
	require.NoError(t, err)
	require.Equal(t, "proved", d.Status)
	spelled := map[string]bool{}
	for _, sp := range d.Spells {
		spelled[sp.Const] = true
		require.NotEmpty(t, sp.Statement)
	}
	require.True(t, spelled["normal_space"] && spelled["closed_in"] && spelled["continuous_map"], "the spelled constants: %v", spelled)
	require.NotEmpty(t, d.Narrative, "the README speaks of Urysohn")
	require.Equal(t, []string{"T", "s", "t"}, d.Cite.Witnesses)
	require.Equal(t, "real_valued.Urysohn.At(T, s, t)", d.Cite.Go)
	require.Equal(t, "", d.Cite.Law, "Urysohn carries is_topology as a hypothesis, not as a law")
	suppliers := map[string][]string{}
	for _, sup := range d.Supplies {
		for _, m := range sup.Members {
			suppliers[sup.Const] = append(suppliers[sup.Const], m.ID)
		}
	}
	require.Contains(t, suppliers["normal_space"], "topology/real_valued.MetricNormal")
	require.Contains(t, suppliers["normal_space"], "topology/separation.CompactHausdorffNormal")
	require.NotContains(t, suppliers, "set_member", "the set language supplies nothing")
	variants := map[string]bool{}
	for _, v := range d.Variants {
		variants[v.ID] = true
	}
	require.True(t, variants["topology/real_valued.Tietze"] || variants["topology/real_valued.UrysohnIff"], "%v", variants)
	// A law reads its structure; a proved member has no plan and no fill order.
	law, err := c.Dossier("topology/compact.CompactClosed")
	require.NoError(t, err)
	require.Equal(t, "is_topology", law.Cite.Law)
	require.Equal(t, "proved", law.Status)
	require.Equal(t, 0, law.FillOrder)
	require.Equal(t, []string{"T", "k"}, law.Cite.Witnesses)
	require.Equal(t, "closed_in", c.byID["topology/compact.CompactClosed"].Concludes)
	require.Equal(t, "normal_space", c.byID["topology/real_valued.MetricNormal"].Concludes)
	_, err = c.Dossier("no/such.Member")
	require.Error(t, err)
}

// A card's dossier says it is one: its stratum, the note saying what
// its proof must establish, its depth in its plan and its place in the
// fill order. The card is the first the index lists, whichever that is:
// a card named here would be a proved member the day its proof landed.
func TestDossierOfACard(t *testing.T) {
	c := load(t)
	var card *Member
	for _, m := range c.Members {
		if m.Card {
			card = m
			break
		}
	}
	if card == nil {
		t.Skip("the corpus has no card")
	}
	d, err := c.Dossier(card.ID)
	require.NoError(t, err)
	require.Equal(t, "card", d.Status, card.ID)
	require.NotEmpty(t, d.Note, card.ID)
	require.Positive(t, d.Depth, card.ID)
	require.Positive(t, d.FillOrder, card.ID)
	for _, under := range d.Plan {
		require.NotEqual(t, card.ID, under.ID, "a card's plan leaves the card itself out")
	}
}

// Neighbors walks the declared edges level by level; Between finds the
// chain the levels imply.
func TestNeighborsAndBetween(t *testing.T) {
	c := load(t)
	m, ok := c.Resolve("nat_num/nat_prime.PrimesInfinite")
	require.True(t, ok)
	n, err := c.Neighbors(m.ID, Deps, 1)
	require.NoError(t, err)
	require.Len(t, n.Levels, 1)
	require.Equal(t, len(m.Deps), len(n.Levels[0].Members))
	whole, err := c.Neighbors(m.ID, Deps, 0)
	require.NoError(t, err)
	require.GreaterOrEqual(t, len(whole.Levels), len(n.Levels))
	deepest := whole.Levels[len(whole.Levels)-1].Members[0]
	p, err := c.Between(m.ID, deepest.ID)
	require.NoError(t, err)
	require.True(t, p.Found)
	require.Equal(t, "from cites to", p.Direction)
	require.Equal(t, len(whole.Levels)+1, len(p.Path), "a shortest chain to the deepest level is as long as the level count")
	require.Equal(t, m.ID, p.Path[0].ID)
	require.Equal(t, deepest.ID, p.Path[len(p.Path)-1].ID)
	_, err = c.Neighbors(m.ID, Direction("sideways"), 1)
	require.Error(t, err)
}

// The family graph has two edge sources: a member citing another
// family's member, and a member STATING a constant another family
// minted — the edge a card leaves, having no proof to cite the
// definition through, and a theorem may only unfold the constant.
// Every constant a statement mentions whose minting family is another
// is an import of the member's family; field_automorphism's
// AutomorphismOrderFacts, which states ℕ's `∣` and cites nothing in
// nat_divides, is the pinned instance of an edge only the statement
// makes.
func TestFamilyGraphReadsStatementConstants(t *testing.T) {
	c := load(t)
	imports := map[string]map[string]bool{}
	for _, f := range c.Families {
		imports[f.Name] = map[string]bool{}
		for _, imp := range f.Imports {
			imports[f.Name][imp] = true
		}
	}
	for _, m := range c.Members {
		for _, name := range m.Constants {
			d := c.byConst[name]
			if d == nil || d.Family == m.Family {
				continue
			}
			require.True(t, imports[m.Family][d.Family], "%s states %s, minted by %s, so %s must import %s", m.ID, name, d.Member, m.Family, d.Family)
		}
	}
	require.True(t, imports["algebra/field/field_automorphism"]["nat_num/nat_divides"], "the edge a statement alone makes")
	w := c.importWitness["algebra/field/field_automorphism"]["nat_num/nat_divides"]
	require.Equal(t, "algebra/field/field_automorphism.AutomorphismOrderFacts", w.Member)
	require.Contains(t, w.Reason, "states `nat_divides`")
}

// A cycle in the family graph is refused at Load, named edge by edge
// with the member that made each edge and how. The corpus has none;
// the finder and the message are exercised on a hand-built graph.
func TestFamilyCycleIsFoundAndNamed(t *testing.T) {
	require.Nil(t, familyCycles(map[string]*Family{
		"a": {Name: "a", Imports: []string{"b"}}, "b": {Name: "b", Imports: []string{"c"}}, "c": {Name: "c"},
	}))
	byFamily := map[string]*Family{
		"a": {Name: "a", Imports: []string{"b"}},
		"b": {Name: "b", Imports: []string{"c", "d"}},
		"c": {Name: "c", Imports: []string{"a"}},
		"d": {Name: "d", Imports: []string{"b"}},
	}
	cycles := familyCycles(byFamily)
	require.Equal(t, [][]string{{"a", "b", "c", "a"}, {"b", "d", "b"}}, cycles)
	c := &Corpus{byFamily: byFamily, importWitness: map[string]map[string]importWitness{
		"a": {"b": {Member: "a.X", Reason: "states `c_b`, minted by b.Def"}},
		"b": {"c": {Member: "b.Y", Reason: "cites c.Z"}, "d": {Member: "b.Y", Reason: "cites d.W"}},
		"c": {"a": {Member: "c.Z", Reason: "cites a.X"}},
		"d": {"b": {Member: "d.W", Reason: "states `c_b`, minted by b.Def"}},
	}}
	err := c.cycleError(cycles)
	require.Error(t, err)
	require.Contains(t, err.Error(), "a → b  (a.X states `c_b`, minted by b.Def)")
	require.Contains(t, err.Error(), "c → a  (c.Z cites a.X)")
	require.Contains(t, err.Error(), "d → b  (d.W states `c_b`, minted by b.Def)")
	require.Contains(t, err.Error(), "has 2 cycles")
}

// A projection law — one whose body states another structure — lists
// the laws of that structure, read through it
// (registry.ReadableDirectlyThrough), each with what the reading states
// over this law's structure; a law among them that is itself a
// projection carries the structure it states, and the reading
// continues under that law, which lists its own. Nothing a chain
// reaches past the first level is listed: `retrieve` matches it by
// goal. A law that is no projection lists nothing, and the dossier
// carries the same.
func TestProjectionLawListsWhatItMakesReadable(t *testing.T) {
	c := load(t)
	hom, ok := c.Resolve("algebra/ring/ring_homomorphism.AdditiveHomomorphism")
	require.True(t, ok)
	require.Equal(t, "group_homomorphism", hom.Projection)
	// A readable law as a reader sees it: the JSON encoding spells the body.
	type shown struct {
		Law        string `json:"law"`
		Projection string `json:"projection,omitempty"`
		Body       string `json:"body"`
	}
	listed := func(m *Member) map[string]shown {
		byLaw := map[string]shown{}
		for _, r := range m.Readable.Laws() {
			encoded, err := json.Marshal(r)
			require.NoError(t, err)
			var row shown
			require.NoError(t, json.Unmarshal(encoded, &row))
			require.Equal(t, r.Body(), row.Body)
			_, twice := byLaw[r.Law]
			require.False(t, twice, "%s lists %s twice", m.ID, r.Law)
			byLaw[r.Law] = row
		}
		return byLaw
	}
	byLaw := listed(hom)
	require.Equal(t, shown{Law: "algebra/group/group_homomorphism.MapOne", Body: "f(R.zero) = S.zero"},
		byLaw["algebra/group/group_homomorphism.MapOne"],
		"a ring homomorphism keeps zero: the group law's body at the additive groups' components, in the ring chapter's spelling")
	require.Equal(t, shown{Law: "algebra/group/group_homomorphism.Source", Projection: "group_on", Body: "group_on(additive_group(R))"},
		byLaw["algebra/group/group_homomorphism.Source"],
		"the source group is a projection of the homomorphism: the group's laws are read under it")
	require.NotContains(t, byLaw, "algebra/group/group.AssocOn", "the group's laws are a chain further, under Source and Target")

	// The same at a structure's projection to another structure on its
	// carrier: the additive group's laws are listed, its projection to
	// its monoid is marked, and the monoid's laws are read under that.
	addGroup, _ := c.Resolve("algebra/ring/comm_ring.AddGroup")
	byLaw = listed(addGroup)
	require.Equal(t, shown{Law: "algebra/group/abelian_group.Comm", Body: "∀x y:A. x + y = y + x"}, byLaw["algebra/group/abelian_group.Comm"])
	require.Equal(t, shown{Law: "algebra/group/abelian_group.Monoid", Projection: "comm_monoid", Body: "comm_monoid(R.add, R.zero)"}, byLaw["algebra/group/abelian_group.Monoid"])
	require.NotContains(t, byLaw, "algebra/group/comm_monoid.Monoidal", "the monoid's laws are read under abelian_group.Monoid")

	mapOne, _ := c.Resolve("algebra/ring/ring_homomorphism.MapOne")
	require.Empty(t, mapOne.Projection, "a law whose body is no structure projects nothing")
	require.Nil(t, mapOne.Readable)
	require.Nil(t, mapOne.Readable.Laws())

	d, err := c.Dossier(hom.ID)
	require.NoError(t, err)
	require.Equal(t, hom.Projection, d.Projection)
	require.Same(t, hom.Readable, d.Readable)

}

// Two layouts of one constant may share components: in
// short_exact_modules the inclusion's homomorphism layout and the
// projection's both fill the ring and the middle module. A served text
// folds both, the later at the first of its slots the earlier left, and
// the folded text reads back to the member's own key.
func TestServedTextFoldsLayoutsSharingComponents(t *testing.T) {
	servedTextContains(t, load(t), map[string]string{
		"simplicial/simplicial_module.DegreewiseShortExactComplexes": "(∀n:num. short_exact_modules(i(n), p(n)))",
	})
}

// A definition's equation states its structure: its definiendum and
// the body conjuncts stating its layouts are served spelled in full,
// where a theorem under the structure restates a layout by the
// bundle's name (dsl's astApp.stated).
func TestServedDefinitionStatesItsLayoutsInFull(t *testing.T) {
	servedTextContains(t, load(t), map[string]string{
		"algebra/module/chain_complex.ChainComplex":       "chain_complex(R, P) ⇔ (∀n:num. module_on(R, complex_module(P, n))) ∧ (∀n:num. module_homomorphism(R, complex_module(P, n + 1), complex_module(P, n), P.d(n + 1))) ∧",
		"algebra/module/chain_complex.ComplexBoundaryHom": "∀P:chain_complex(A, B). ∀n:num. module_homomorphism(P.d(n + 1))",
		"algebra/module/module_extension.ModuleExtension": "module_extension(R, M, N, E) ⇔ short_exact_modules(R, N, E.module, M, E.inclusion, E.projection)",
		"algebra/ring/comm_ring.CommRingOn":               "comm_ring_on(R) ⇔ abelian_group_on(additive_group(R)) ∧ comm_monoid_on(R.carrier, R.mul, R.one) ∧",
		"algebra/group/comm_monoid.CommMonoidOn":          "comm_monoid_on(c, op, e) ⇔ e ∈ c ∧",
		"simplicial/kan_fibration.KanFibration":           "kan_fibration(X, Y, p) ⇔ simplicial_map(X, Y, p) ∧",
	})
}

// servedTextContains checks that each member's served statement
// contains the text given and reads back to the member's own key.
func servedTextContains(t *testing.T, c *Corpus, texts map[string]string) {
	t.Helper()
	for id, text := range texts {
		m, ok := c.Resolve(id)
		require.True(t, ok, id)
		require.Contains(t, m.Statement, text, id)
		var entry *registry.ProofEntry
		for _, e := range registry.All() {
			if e.Name == m.Entry {
				entry = e
			}
		}
		require.NotNil(t, entry, id)
		key, err := entry.KeyOfText(m.Statement)
		require.NoError(t, err)
		require.Equal(t, string(entry.Statement().Key()), key, "%s: the served text reads back to its own key", id)
	}
}

// Load derives no readable law: a projection member's laws are derived
// when first read, so a question that prints none of them — `xugo
// query` reads the corpus once per question — reads no law at a
// projection. The JSON encoding derives them, and carries the field
// only where a law is readable.
func TestReadableLawsAreDerivedWhenRead(t *testing.T) {
	c, err := read(corpusRoot)
	require.NoError(t, err)
	projections := 0
	for _, m := range c.Members {
		if m.Projection == "" {
			require.Nil(t, m.Readable, "%s projects nothing", m.ID)
			continue
		}
		projections++
		require.NotNil(t, m.Readable, m.ID)
		require.Nil(t, m.Readable.laws, "%s: Load derived the readable laws", m.ID)
	}
	require.Positive(t, projections)

	hom, _ := c.Resolve("algebra/ring/ring_homomorphism.AdditiveHomomorphism")
	encoded, err := json.Marshal(hom)
	require.NoError(t, err)
	var fields map[string]json.RawMessage
	require.NoError(t, json.Unmarshal(encoded, &fields))
	require.Contains(t, fields, "readable")
	require.NotNil(t, hom.Readable.laws, "the encoding derived the laws")
	var laws []struct{ Law, Body string }
	require.NoError(t, json.Unmarshal(fields["readable"], &laws))
	require.Len(t, laws, len(hom.Readable.Laws()))
	require.Equal(t, hom.Readable.Laws()[0].Law, laws[0].Law)
	require.Equal(t, hom.Readable.Laws()[0].Body(), laws[0].Body)

	mapOne, _ := c.Resolve("algebra/ring/ring_homomorphism.MapOne")
	encoded, err = json.Marshal(mapOne)
	require.NoError(t, err)
	require.NotContains(t, string(encoded), `"readable"`)
	// A projection through which no law is readable encodes no field either.
	encoded, err = json.Marshal(struct {
		Readable *ReadableLaws `json:"readable,omitzero"`
	}{&ReadableLaws{}})
	require.NoError(t, err)
	require.Equal(t, "{}", string(encoded))
}
