package index

// The dossier: one member read the way a reader — a person or an agent
// about to cite or to prove it — wants it read, assembled from what
// the index already holds. The statement and how to read it (the
// definitions it spells, each with its own reading); where it stands
// (its stratum, the plan under it, who stands on it, its family's
// height, the chapter's narrative where it speaks of the member); what
// it applies to (the members supplying each of its hypotheses'
// predicates); how it is cited (the Go wrapper's witnesses, which are
// the session's); and its nearest relatives by the constants they
// share. Nothing here is new data:
// the dossier is a reading of the corpus a query assembles.

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/utils"
)

// Dossier is one member in the round.
type Dossier struct {
	Member MemberRef `json:"member"`
	Kind   string    `json:"kind"`
	// Status is the member's stratum: proved, on_cards or card.
	Status string `json:"status"`
	// Reading is the member's own reading, when one is written.
	Reading string `json:"reading,omitempty"`
	// Note is a card's note — the route its proof is to take.
	Note string `json:"note,omitempty"`
	// Gloss is the chapter's doc comment on the member; Outline the
	// narration of its proof, step by step as written (outline.go),
	// empty for a member with no Go argument.
	Gloss   string        `json:"gloss,omitempty"`
	Outline []OutlineStep `json:"outline,omitempty"`
	// Depth is a card's depth in its plan; FillOrder its position, from
	// 1, in registry.CardFillOrder — the cheap order to fill the cards
	// in, not a queue. Both 0 for a proved member.
	Depth     int `json:"depth,omitempty"`
	FillOrder int `json:"fill_order,omitempty"`

	// Spells lists the minted constants the statement mentions, each
	// with its definition and reading — what a reader expands first.
	Spells []Spelled `json:"spells,omitempty"`

	Family FamilyPlace `json:"family"`
	// Narrative is what the chapter's README says where it names the
	// member: the prose paragraphs mentioning it, tables left out.
	Narrative []string `json:"narrative,omitempty"`

	// Plan is the cards the member stands on — for a card, the cards
	// under it, itself left out; for a proved member, its frontier.
	Plan []MemberRef `json:"plan,omitempty"`
	// Deps and Dependents are the member's citations, each with its
	// statement.
	Deps       []MemberRef `json:"deps,omitempty"`
	Dependents []MemberRef `json:"dependents,omitempty"`
	// UsedBy are the members whose statement spells a constant the
	// member mints and that do not depend on it (Corpus.UsedBy): empty
	// for a member that mints no constant.
	UsedBy []Use `json:"used_by,omitempty"`
	// Supplies lists, per predicate the hypotheses apply, the members
	// whose conclusion is that predicate — what the member applies to.
	Supplies []Supplier `json:"supplies,omitempty"`
	// Projection and Readable are a projection law's: the structure its
	// body states and the laws readable through it (Member.Readable).
	Projection string        `json:"projection,omitempty"`
	Readable   *ReadableLaws `json:"readable,omitzero"`
	// Variants are the family's other members nearest by the constants
	// they share with this one.
	Variants []MemberRef `json:"variants,omitempty"`

	Cite Citation `json:"cite"`
}

// Spelled is a minted constant a statement mentions.
type Spelled struct {
	Const     string `json:"const"`
	Member    string `json:"member"`
	Family    string `json:"family"`
	Statement string `json:"statement"`
	Reading   string `json:"reading,omitempty"`
}

// FamilyPlace is where the member's family stands.
type FamilyPlace struct {
	Family string `json:"family"`
	Gloss  string `json:"gloss,omitempty"`
	Height int    `json:"height"`
	Counts Counts `json:"counts"`
}

// Supplier is a predicate one of the member's hypotheses applies and
// the members that conclude it — the instances the member applies
// to. More counts the suppliers past the ones listed.
type Supplier struct {
	Const   string      `json:"const"`
	Members []MemberRef `json:"members"`
	More    int         `json:"more,omitempty"`
}

// Citation is how the member is cited on both surfaces.
type Citation struct {
	// Witnesses are the statement's ∀-bound variables in stated order,
	// antecedents passed through — the arguments of the typed Go
	// wrapper's At and the witness list a session `cite` takes.
	Witnesses []string `json:"witnesses,omitempty"`
	// Go is the typed cite as a Go expression at those witnesses.
	Go string `json:"go"`
	// Law names the structure predicate the statement is a law of —
	// its first antecedent, at the leading binders — when it is one;
	// such a member is read at an instance (Read) as well as cited.
	Law string `json:"law,omitempty"`
}

// suppliersShown caps a predicate's supplier list.
const suppliersShown = 12

// Dossier assembles the member's dossier.
func (c *Corpus) Dossier(ref string) (*Dossier, error) {
	m, err := c.ResolveOne(ref)
	if err != nil {
		return nil, err
	}
	e, ok := registry.ByName(m.Entry)
	if !ok {
		panic(fmt.Sprintf("index dossier: the index names %s, which the registry does not hold", m.Entry))
	}
	st := e.Statement().Prop
	f := c.byFamily[m.Family]
	d := &Dossier{
		Member:  m.ref(),
		Kind:    m.Kind,
		Status:  m.Status(),
		Reading: m.Reading,
		Note:    m.Note,
		Depth:   m.Depth,
		Family:  FamilyPlace{Family: f.Name, Gloss: f.Gloss, Height: f.Height, Counts: f.Counts},
	}
	if d.Status == "card" {
		for i, name := range registry.CardFillOrder() {
			if name == m.Entry {
				d.FillOrder = i + 1
				break
			}
		}
	}
	for _, name := range m.Constants {
		if numeralConstant(name) {
			continue
		}
		if def := c.byConst[name]; def != nil {
			d.Spells = append(d.Spells, Spelled{Const: name, Member: def.Member, Family: def.Family, Statement: def.Statement, Reading: c.byID[def.Member].Reading})
		}
	}
	d.Narrative = c.narrative(f, e.BareName())
	for _, id := range m.Cards {
		if id != m.ID {
			d.Plan = append(d.Plan, c.byID[id].ref())
		}
	}
	for _, id := range m.Deps {
		d.Deps = append(d.Deps, c.byID[id].ref())
	}
	for _, id := range m.Dependents {
		d.Dependents = append(d.Dependents, c.byID[id].ref())
	}
	d.UsedBy = c.UsedBy(m)
	binders, hyps, _ := statementShape(st.Conclusion())
	d.Supplies = c.suppliers(m, hyps)
	d.Projection, d.Readable = m.Projection, m.Readable
	if err := c.readGloss(m); err != nil {
		return nil, err
	}
	d.Gloss = m.Gloss
	if d.Outline, err = c.Outline(m); err != nil {
		return nil, err
	}
	d.Variants = c.variants(m)
	d.Cite = c.citation(m, binders, hyps)
	return d, nil
}

// numeralConstant says a constant is the numeral machinery a literal
// lowers to — `0`, the binary digits, the lift of a numeral into a
// number domain — which a reader does not expand.
func numeralConstant(name string) bool {
	switch name {
	case "_0", "bit0", "bit1", "numeral", "real_of_num", "int_of_num":
		return true
	}
	return false
}

// statementShape splits a statement into its ∀-bound variables in
// stated order (antecedents passed through), its antecedents, and
// its conclusion: ∀x. P ⇒ ∀y. Q ⇒ R yields [x y], [P Q], R.
func statementShape(t core.Term) (binders []string, hyps []core.Term, conclusion core.Term) {
	for {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			binders = append(binders, string(abs.Var().Name()))
			t = abs.Body()
			continue
		}
		if ante, conseq, ok := ext.MatchesIMPLY(t); ok {
			hyps = append(hyps, ante)
			t = conseq
			continue
		}
		return binders, hyps, t
	}
}

// concludesOf is the constant at the head of a statement's conclusion,
// past binders and antecedents, and through an equation or an
// equivalence to the left side; "" when the head is a variable.
func concludesOf(p core.Prop) string {
	_, _, conclusion := statementShape(p.Conclusion())
	return headConst(conclusion)
}

func headConst(t core.Term) string {
	if lhs, _, ok := ext.MatchesIFF(t); ok {
		return headConst(lhs)
	}
	if lhs, _, ok := core.MatchesEQ(t); ok {
		return headConst(lhs)
	}
	fun, _ := ext.MatchesApply(t)
	if fun == nil {
		fun = t
	}
	if c, ok := fun.AsConst(); ok {
		name := string(c.Name())
		switch name {
		case utils.EqStr, utils.NegStr, utils.AndStr, utils.OrStr, utils.ForAllStr, utils.ExistsStr, utils.ImplyStr:
			return ""
		}
		return name
	}
	return ""
}

// readmeText reads a family README relative to the corpus root.
func readmeText(root, readme string) (string, error) {
	b, err := os.ReadFile(filepath.Join(root, filepath.FromSlash(readme)))
	return string(b), err
}

// narrative is the README's prose where it names the member: the
// blank-line-separated blocks mentioning the bare name as a word,
// tables and headings left out, at most three.
func (c *Corpus) narrative(f *Family, bare string) []string {
	text, err := readmeText(c.Root, f.Readme)
	if err != nil {
		return nil
	}
	word := regexp.MustCompile(`(^|[^A-Za-z0-9_])` + regexp.QuoteMeta(bare) + `([^A-Za-z0-9_]|$)`)
	var out []string
	for _, block := range strings.Split(text, "\n\n") {
		block = strings.TrimSpace(block)
		if block == "" || strings.HasPrefix(block, "|") || strings.HasPrefix(block, "#") || !word.MatchString(block) {
			continue
		}
		out = append(out, strings.Join(strings.Fields(block), " "))
		if len(out) == 3 {
			break
		}
	}
	return out
}

// suppliers lists, for each predicate the hypotheses apply that some
// other member concludes, those members — proved first, then cards —
// the ones minted by the set language left out, since every member
// concludes a membership.
func (c *Corpus) suppliers(m *Member, hyps []core.Term) []Supplier {
	found := map[core.TermKey]ext.ConstTerm{}
	for _, h := range hyps {
		ext.CollectConstTerms(h, found)
	}
	var names []string
	for _, ct := range found {
		name := string(ct.Name())
		def := c.byConst[name]
		if def == nil || def.Family == "sets/set_basic" || !isPredicateType(ct.Type()) {
			continue
		}
		names = append(names, name)
	}
	sort.Strings(names)
	var out []Supplier
	for _, name := range names {
		var members []*Member
		for _, x := range c.Members {
			if x.Concludes == name && x.ID != m.ID && x.Kind != "definition" && x.Kind != "structure" {
				members = append(members, x)
			}
		}
		if len(members) == 0 {
			continue
		}
		sort.SliceStable(members, func(i, j int) bool {
			if members[i].Card != members[j].Card {
				return !members[i].Card
			}
			return members[i].ID < members[j].ID
		})
		sup := Supplier{Const: name}
		for i, x := range members {
			if i == suppliersShown {
				sup.More = len(members) - suppliersShown
				break
			}
			sup.Members = append(sup.Members, x.ref())
		}
		out = append(out, sup)
	}
	return out
}

// isPredicateType says a constant's type ends in bool.
func isPredicateType(t core.HolType) bool {
	for {
		ct, ok := t.(core.CompositeType)
		if !ok {
			return false
		}
		if ct.Meta().Equals(core.MetaTypeBool()) {
			return true
		}
		if !ct.Meta().Equals(core.MetaTypeFun()) {
			return false
		}
		t = ct.SubType(1)
	}
}

// variants are the family's other members ranked by the minted
// constants they share with m, the set language's left out; at least
// two shared, at most six listed.
func (c *Corpus) variants(m *Member) []MemberRef {
	mine := map[string]bool{}
	for _, name := range m.Constants {
		if def := c.byConst[name]; def != nil && def.Family != "sets/set_basic" {
			mine[name] = true
		}
	}
	type scored struct {
		m     *Member
		score int
	}
	var ranked []scored
	for _, x := range c.byFamily[m.Family].Members {
		if x.ID == m.ID || x.Kind == "definition" || x.Kind == "structure" || x.Kind == "type" {
			continue
		}
		n := 0
		for _, name := range x.Constants {
			if mine[name] {
				n++
			}
		}
		if n >= 2 {
			ranked = append(ranked, scored{x, n})
		}
	}
	sort.SliceStable(ranked, func(i, j int) bool {
		if ranked[i].score != ranked[j].score {
			return ranked[i].score > ranked[j].score
		}
		return ranked[i].m.ID < ranked[j].m.ID
	})
	var out []MemberRef
	for i, r := range ranked {
		if i == 6 {
			break
		}
		out = append(out, r.m.ref())
	}
	return out
}

// citation renders the member's cite: the typed wrapper's At at the
// statement's witnesses, and the structure the statement is a law of.
func (c *Corpus) citation(m *Member, binders []string, hyps []core.Term) Citation {
	cite := Citation{Witnesses: binders}
	if len(binders) == 0 {
		cite.Go = m.Entry
	} else {
		cite.Go = fmt.Sprintf("%s.At(%s)", m.Entry, strings.Join(binders, ", "))
	}
	if len(hyps) > 0 {
		if name := headConst(hyps[0]); name != "" && registry.IsStructurePredicate(name) {
			cite.Law = name
		}
	}
	return cite
}
