// Package index is the corpus read as one object: the views
// `xugo query` (engine/cmd/xugo) answers an agent in JSON, computed
// from the proof registry, so they cannot drift from the corpus. The
// gate suite holds the corpus to what the index refuses, a cycle in the
// family graph (TestFamilyGraphAcyclic). The corpus drawn and browsed —
// the family graph, a member's proof, a search of the theorems — is
// library/visualize, which reads this package (`xugo browse`).
//
// # What the index knows
//
// Everything is read off library/registry after the corpus has
// registered (importing library/proofs does that): every family and its
// members in registration order, each member's statement, its declared
// Deps, the cards it stands on, the constants its statement mentions,
// the constants and types its definition door minted, and the chapter
// file and line it is registered at. Two things are derived: the
// reverse edges (who cites a member), and the family graph — one family
// imports another when a member of the first cites a member of the
// second, or STATES a constant a member of the second minted. The
// second source is what a citation cannot carry: a card has no proof
// to cite the definition through, and a theorem may only unfold the
// constant, which is no dependency (constitution §Entries and
// dependencies) — so without it a card stated over another chapter's
// constant left no edge anywhere, the statement parsing lazily after
// every family's init. The graph must be acyclic — a citation is a Go
// import, compiler-checked; a stated constant is checked here — and
// Load refuses a corpus whose graph is not, naming the cycle member by
// member. No Go-level tool is consulted: the registry's Deps are the
// citation graph, declared by the author and compiler-checked, and
// gopls would only see text.
//
// A member's identity in the index is "<family>.<bare name>" —
// "real/real_sequences.CauchyConverges" — the registered name with the
// family's full path in place of its basename, so two chapters with one
// basename never collide. A query
// takes that id, the registered name a session cites
// ("real_sequences.CauchyConverges"), or the member's own key.
//
// Internal lemmas — the unexported entries a chapter keeps for itself —
// are indexed like every other member and marked `internal`; nothing is
// hidden, because reading a proof means reading the lemmas it cites and
// a lemma that recurs across chapters is found only by seeing all of
// them.
//
// # The three zoom levels
//
// Overview answers "what is in here" in one call sized for a context
// window: the domains and one line per family (gloss, height, counts)
// — under 80 KB, and nothing another view serves. FamilyView is one
// chapter: its members with statements and glosses. MemberView is one
// member in full, and Outline its proof's narration as the chapter
// writes it — the two things read off the chapter file as text, when
// asked (outline.go). Around them sit the graph questions — Neighbors
// (deps / dependents to a depth), Between (a citation path) — and the
// definition and cards views.
//
// # The gloss
//
// A family's one-line gloss is the title line of its README
// ("# real_sequences — sequences of reals and their limits"), read by
// registry.ChapterGloss — the reader the family generator takes the
// package's doc comment from, so the index's line and the line
// pkg.go.dev prints beside the package are one text. The README is the
// chapter's narrative and stays the source; the index reads the title
// and never copies the body. Reading it needs the corpus directory on
// disk, so Load takes the library/proofs path.
package index

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path"
	"path/filepath"
	"runtime"
	"slices"
	"sort"
	"strings"
	"sync"
	"unicode"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
)

// Corpus is the registry read whole. Families and Members are in
// name order; a family's own Members are in registration order, which
// is the order the chapter's files state them in.
type Corpus struct {
	// Root is the library/proofs directory the glosses were read from.
	Root string `json:"-"`

	Domains     []*Domain     `json:"domains"`
	Families    []*Family     `json:"-"`
	Members     []*Member     `json:"-"`
	Definitions []*Definition `json:"definitions"`
	Types       []*TypeDef    `json:"types"`
	// Doors are the door calls that registered several members, in
	// family order, then registration order.
	Doors []*Door `json:"-"`

	byFamily map[string]*Family
	// byShort is the families under each short name, the last element
	// of the family's name — its package name, and the prefix of its
	// members' registered names — in name order.
	byShort map[string][]*Family
	// byDoor is the door calls by id.
	byDoor  map[string]*Door
	byID    map[string]*Member
	byEntry map[string]*Member
	byKey   map[string]*Member
	// byBare is the members under each bare name, the name after the
	// family's in the registered name: what a card's note calls one.
	byBare  map[string][]*Member
	byConst map[string]*Definition
	// sources are the chapter files read as text, by corpus-relative
	// path, each once (outline.go).
	sourcesMu sync.Mutex
	sources   map[string]*sourceFile
	// readmes are the families' READMEs read for their member rows, by
	// family name, each once (readme.go).
	readmesMu sync.Mutex
	readmes   map[string]*_ReadmeRows
	// importWitness is, per edge of the family graph (from → to), the
	// first member that made it and how — what a refused cycle is
	// explained by.
	importWitness map[string]map[string]importWitness
	// openedBy is, per definition member, the ids of the members whose
	// proofs open a constant it defines (Member.Unfolds), in id order.
	openedBy map[string][]string
}

// importWitness is one reason a family imports another: Member is the
// importing member's id, Reason "cites <id>" or "states `<constant>`,
// minted by <id>".
type importWitness struct {
	Member, Reason string
}

// Domain is a top-level directory of the corpus (nat_num, real, sets…)
// with its families in name order.
type Domain struct {
	Name     string    `json:"domain"`
	Counts   Counts    `json:"counts"`
	Families []*Family `json:"families"`
}

// Family is one chapter.
type Family struct {
	// Name is the registry family name, the corpus-relative package
	// path ("real/real_sequences", "real/tower/eudoxus_slope").
	Name string `json:"family"`
	// Domain is the first segment of Name.
	Domain string `json:"domain"`
	// Dir is the package directory relative to library/proofs; it
	// differs from Name only for the tower group's internal packages.
	Dir string `json:"dir"`
	// Gloss is the README title's tail after the dash.
	Gloss string `json:"gloss,omitempty"`
	// Readme is the README's path relative to library/proofs.
	Readme string `json:"readme,omitempty"`
	// Imports are the families this one depends on — whose members its
	// members cite, or whose constants its statements spell; Importers
	// the families depending on this one. Both in name order.
	Imports   []string `json:"imports,omitempty"`
	Importers []string `json:"importers,omitempty"`
	// Height is the family's level in the dependency graph: the length
	// of the longest chain of imports below it, 0 for a family that
	// imports nothing. The strata table on the front page is the
	// families by height.
	Height int    `json:"height"`
	Counts Counts `json:"counts"`
	// Abbrev is the chapter's own abbreviation table (registry.Family
	// .WithAbbrev): the names every statement of the chapter and every
	// text of its proofs may spell as «Name», each with the term it
	// stands for. Empty for a chapter declaring none. AbbrevOuter names
	// the chapters whose tables this one reads under (WithOuterAbbrev),
	// in order: their entries are in scope for every text of the
	// chapter too, and are listed on their own pages.
	Abbrev      dsl.Abbrev `json:"abbreviations,omitempty"`
	AbbrevOuter []string   `json:"abbreviations_under,omitempty"`
	Members     []*Member  `json:"members"`
}

// Counts sizes a family, a domain or the corpus. Definitions counts
// the constants minted there, by a door or at the vocabulary. The
// four strata partition Members: Proved, the members the corpus
// proves outright; OnCards, the proved members whose deps reach a
// card, which the corpus proves only relative to it; Cards, the
// members stated without a proof — axioms until their proofs land;
// and Postulates, the members assumed outright and for good — the
// axiom of infinity, the registry admitting one.
type Counts struct {
	Members     int `json:"members"`
	Internal    int `json:"internal"`
	Definitions int `json:"definitions"`
	Proved      int `json:"proved"`
	OnCards     int `json:"on_cards"`
	Cards       int `json:"cards"`
	Postulates  int `json:"postulates"`
}

func (c *Counts) add(o Counts) {
	c.Members += o.Members
	c.Internal += o.Internal
	c.Definitions += o.Definitions
	c.Proved += o.Proved
	c.OnCards += o.OnCards
	c.Cards += o.Cards
	c.Postulates += o.Postulates
}

// Member is one registered entry.
type Member struct {
	// ID is "<family>.<bare name>"; Entry the registered name a session
	// cites; Key the statement's own normalized key.
	ID     string `json:"id"`
	Entry  string `json:"entry"`
	Family string `json:"family"`
	Key    string `json:"key"`
	// Kind is theorem, definition, structure or type; Shape, for a
	// definition door's entry, the shape it served
	// (proof.DefinitionShape).
	Kind  string `json:"kind"`
	Shape string `json:"shape,omitempty"`
	// Internal marks an unexported entry — a lemma the chapter keeps
	// for itself, refactored freely.
	Internal bool `json:"internal,omitempty"`
	// Statement is the member's statement as the chapter states it
	// (registry.ProofEntry.StatementText): the headline text its
	// constructor parses, in the chapter's own
	// spelling — binder types, declared notation, implicit arguments
	// left out. A statement a definition door computed has no authored
	// text and is printed in that spelling instead.
	Statement string `json:"statement"`
	// Abbreviations are the names Statement spells as «Name» and the
	// entries those stand on, each with the term it stands for, the
	// member's own and the chapter's alike, in table order
	// (registry.ProofEntry.Abbreviations); what the proof spells beyond
	// the statement is not here.
	Abbreviations dsl.Abbrev `json:"abbreviations,omitempty"`
	// Source is the chapter file and line the member is registered at,
	// relative to library/proofs.
	Source string `json:"source,omitempty"`
	// Deps are the ids of the members this one stands on — the entries
	// its proof reads and the definitions it opens — in declaration
	// order; Dependents the ids of the members standing on it, in id
	// order.
	Deps       []string `json:"deps,omitempty"`
	Dependents []string `json:"dependents,omitempty"`
	// Unfolds are the ids, among Deps, of the definitions the member's
	// proof opens (Unfold, Unfolded), as the family's blob records them
	// (registry Family.RecordedUnfolds), in id order.
	Unfolds []string `json:"unfolds,omitempty"`
	// Card says the member is stated without a proof (registry
	// ProofEntry.IsCard) — an axiom until its proof lands — and Note is
	// then why it is a member and what its proof must establish. Cards
	// is the member's card frontier: the ids of every card it stands
	// on through its dependencies, itself included when it is one; empty for a
	// member the corpus proves outright.
	Card  bool     `json:"card,omitempty"`
	Note  string   `json:"note,omitempty"`
	Cards []string `json:"cards,omitempty"`
	// Backing is a card's recorded support — the theorems among its
	// deps and the members its note names, resolved (CardBacking,
	// backing.go). Nil for a member that is not a card.
	Backing *CardBacking `json:"backing,omitempty"`
	// Postulate says the member is the corpus's postulate (registry
	// ProofEntry.IsPostulate): assumed outright, no card and no debt.
	Postulate bool `json:"postulate,omitempty"`
	// Depth is a card's place in the plan its dependencies describe: 1 for a
	// card citing no card, 1 more than the deepest card it cites
	// otherwise. 0 for a member that is not a card.
	Depth int `json:"depth,omitempty"`
	// Reading is the statement read in this encoding, as its author or
	// a referee wrote it (registry.ProofEntry.Reading); empty for most
	// members.
	Reading string `json:"reading,omitempty"`
	// Gloss is the doc comment above the member in its chapter file, as
	// one line (outline.go): what the chapter says the member is, read
	// from the text when a member or a family is asked for.
	Gloss string `json:"gloss,omitempty"`
	// Concludes is the constant at the head of the statement's
	// conclusion, past its binders and antecedents and through an
	// equation or an equivalence to the left side — what the member
	// supplies (a `normal_space(…)` conclusion supplies normality).
	// Empty when the conclusion has no constant head.
	Concludes string `json:"concludes,omitempty"`
	// Constants are the non-builtin constants the statement mentions.
	Constants []string `json:"constants,omitempty"`
	// ConclusionConstants and HypothesisConstants split Constants by
	// where the statement mentions them: under its conclusion, past
	// the binders and antecedents, or under an antecedent. A member
	// establishes what its conclusion mentions and asks for what its
	// hypotheses mention; a constant under both is listed in both.
	ConclusionConstants []string `json:"conclusion_constants,omitempty"`
	HypothesisConstants []string `json:"hypothesis_constants,omitempty"`
	// Defines lists the constants the member's definition door minted,
	// DefinesType the type it minted.
	Defines     []string `json:"defines,omitempty"`
	DefinesType string   `json:"defines_type,omitempty"`
	ServesAs    string   `json:"serves_as,omitempty"`
	// Projection is set for a PROJECTION law — a law of one structure
	// whose body states another (registry.ProjectionOf): the predicate
	// the body states. Read at a fact of the law's structure, the law
	// is an instance of that one, and Readable lists the laws that are
	// then values at it.
	Projection string `json:"projection,omitempty"`
	// Readable lists the laws of the structure a projection law states,
	// read through it (registry.ReadableDirectlyThrough), each with what
	// it states over this law's structure; one that is itself a
	// projection carries the structure it states, and the reading
	// continues under that law, where its own readable laws are listed.
	// Cited where it is used, `Law.Read(this.Read(fact))`, and no member
	// (constitution §Readings); a longer chain is matched by goal
	// (`retrieve`). Nil for every other member, and the field is encoded
	// only where a law is readable.
	Readable *ReadableLaws `json:"readable,omitzero"`
	// Door is the id of the door call that registered the member
	// together with others (Door); empty for a member registered alone.
	Door string `json:"door,omitempty"`
}

// Door is a definition door's call that registered several members
// from one literal (registry.DoorCall): a datatype with its principles
// and its record's parts, a type definition, a quotient, an inductive
// definition. Its ID is "<family>.<Name>" and Entry "<family's short
// name>.<Name>", Name the literal's; Door is the door and Type the type
// the call minted, empty for an inductive definition. A graph draws a
// call as one node in place of its parts (library/visualize).
type Door struct {
	ID     string `json:"id"`
	Entry  string `json:"entry"`
	Family string `json:"family"`
	Name   string `json:"name"`
	Door   string `json:"door"`
	Type   string `json:"type,omitempty"`
	// Internal marks a call under an unexported name, as a member's.
	Internal bool `json:"internal,omitempty"`
	// Parts are the members the call registered, in registration
	// order.
	Parts []DoorPart `json:"parts"`
}

// DoorPart is a member a door call registered, and for a record's part
// the word a text writes after the dot of a value of the record (Field)
// and the operator symbol it carries (registry.DataField).
type DoorPart struct {
	Member string `json:"member"`
	Field  string `json:"field,omitempty"`
	Symbol string `json:"symbol,omitempty"`
}

// ReadableLaws lists the laws readable directly through a projection
// law, derived when first read — by Laws, or by the JSON encoding — and
// not at Load: deriving them reads the structure's laws at the
// projection through the kernel, and a question shows those of the
// members it prints.
type ReadableLaws struct {
	law  *registry.ProofEntry
	once sync.Once
	laws []ReadableLaw
}

// Laws lists the readable laws in the order the structure registers
// them; nil for a member that is no projection.
func (r *ReadableLaws) Laws() []ReadableLaw {
	if r == nil {
		return nil
	}
	r.once.Do(func() {
		for _, reading := range registry.ReadableDirectlyThrough(r.law) {
			law := ReadableLaw{Law: MemberID(reading.Law), body: &spelledBody{reading: reading}}
			if p, ok := registry.ProjectionOf(reading.Law); ok {
				law.Projection = p.To
			}
			r.laws = append(r.laws, law)
		}
	})
	return r.laws
}

// IsZero reports that no law is readable, which leaves the field out
// of the JSON encoding (omitzero).
func (r *ReadableLaws) IsZero() bool { return len(r.Laws()) == 0 }

// MarshalJSON encodes the laws, each with its body spelled.
func (r *ReadableLaws) MarshalJSON() ([]byte, error) { return json.Marshal(r.Laws()) }

// ReadableLaw is one law readable through a projection law: Law its
// id; Projection, for a law that is itself a projection, the structure
// it states, under which the reading continues; Body what the reading
// states past the projection's hypothesis — the law's body at the
// projection's components, in the projection's chapter spelling. The
// body is spelled when first asked for, by Body or by the JSON
// encoding, not at Load: spelling a statement folds and parses it
// back, and the corpus has thousands of readable laws a query that
// shows none of them need not spell.
type ReadableLaw struct {
	Law        string `json:"law"`
	Projection string `json:"projection,omitempty"`
	body       *spelledBody
}

// spelledBody spells a derived statement's body once, in its root
// chapter's spelling.
type spelledBody struct {
	once    sync.Once
	reading registry.Readable
	text    string
}

// Body is what the reading states past the projection's hypothesis.
func (r ReadableLaw) Body() string {
	r.body.once.Do(func() { r.body.text = r.body.reading.BodyText() })
	return r.body.text
}

// MarshalJSON encodes the law, the structure it states when it is a
// projection, and the body, spelled.
func (r ReadableLaw) MarshalJSON() ([]byte, error) {
	return json.Marshal(struct {
		Law        string `json:"law"`
		Projection string `json:"projection,omitempty"`
		Body       string `json:"body"`
	}{r.Law, r.Projection, r.Body()})
}

// Definition is a minted constant and the member whose definition door
// minted it.
type Definition struct {
	Const  string `json:"const"`
	Member string `json:"member"`
	Family string `json:"family"`
	Shape  string `json:"shape"`
	// Statement is the defining member's statement — the
	// characterizing equation(s).
	Statement string `json:"statement"`
	// Source is the chapter file and line of the mint.
	Source string `json:"source,omitempty"`
	// Notation is the surface spelling the chapter declared for the
	// constant: a notation pattern, a big-operator symbol or an
	// overloaded word. Empty when the constant is spelled by name.
	Notation string `json:"notation,omitempty"`
}

// TypeDef is a minted type and the member whose door minted it (a
// DefineType registers two members, a DefineData one per principle;
// Member is the first in registration order).
type TypeDef struct {
	Type   string `json:"type"`
	Member string `json:"member"`
	Family string `json:"family"`
}

// MemberRef names a member in a graph answer.
type MemberRef struct {
	ID            string     `json:"id"`
	Entry         string     `json:"entry"`
	Family        string     `json:"family"`
	Statement     string     `json:"statement"`
	Abbreviations dsl.Abbrev `json:"abbreviations,omitempty"`
}

func (m *Member) ref() MemberRef {
	return MemberRef{ID: m.ID, Entry: m.Entry, Family: m.Family, Statement: m.Statement, Abbreviations: m.Abbreviations}
}

var (
	loadMu  sync.Mutex
	loaded  = map[string]*Corpus{}
	loadErr = map[string]error{}
)

// Load reads the registered corpus once per root and returns it. root
// is the library/proofs directory, where the chapter READMEs are; a
// root that does not hold the corpus is an error, never a corpus with
// empty glosses. The laws a member makes readable are listed as a cite
// of the reading hands them over, so Load installs the corpus's record
// equations (serve.InstallRecordNormal) before it reads them.
func Load(root string) (*Corpus, error) {
	serve.InstallRecordNormal()
	loadMu.Lock()
	defer loadMu.Unlock()
	if c, ok := loaded[root]; ok {
		return c, nil
	}
	if err, ok := loadErr[root]; ok {
		return nil, err
	}
	c, err := read(root)
	if err != nil {
		loadErr[root] = err
		return nil, err
	}
	loaded[root] = c
	return c, nil
}

// MemberID is the index identity of a registered entry.
func MemberID(e *registry.ProofEntry) string {
	return e.Family().Name + "." + e.BareName()
}

func read(root string) (*Corpus, error) {
	if len(registry.Families()) == 0 {
		return nil, fmt.Errorf("index: no family is registered — import library/proofs")
	}
	if st, err := os.Stat(filepath.Join(root, "README.md")); err != nil || st.IsDir() {
		return nil, fmt.Errorf("index: %s is not the corpus directory (no README.md there)", root)
	}
	c := &Corpus{
		Root:     root,
		byFamily: map[string]*Family{},
		byShort:  map[string][]*Family{},
		byDoor:   map[string]*Door{},
		byID:     map[string]*Member{},
		byEntry:  map[string]*Member{},
		byKey:    map[string]*Member{},
		byBare:   map[string][]*Member{},
		byConst:  map[string]*Definition{},
		sources:  map[string]*sourceFile{},
		readmes:  map[string]*_ReadmeRows{},
	}
	spellStatements(registry.All())
	frontiers := registry.NewCardFrontiers()
	for _, rf := range registry.Families() {
		f, err := c.readFamily(rf, frontiers)
		if err != nil {
			return nil, err
		}
		c.Families = append(c.Families, f)
		c.byFamily[f.Name] = f
	}
	sort.Slice(c.Families, func(i, j int) bool { return c.Families[i].Name < c.Families[j].Name })
	byEntry := map[*registry.ProofEntry]*Member{}
	for _, f := range c.Families {
		c.byShort[path.Base(f.Name)] = append(c.byShort[path.Base(f.Name)], f)
		for _, m := range f.Members {
			c.Members = append(c.Members, m)
			c.byID[m.ID] = m
			c.byEntry[m.Entry] = m
			c.byKey[m.Key] = m
			c.byBare[m.bare()] = append(c.byBare[m.bare()], m)
		}
	}
	for _, e := range registry.All() {
		byEntry[e] = c.byID[MemberID(e)]
	}
	sort.Slice(c.Members, func(i, j int) bool { return c.Members[i].ID < c.Members[j].ID })

	// The door calls, each with the members it registered. A call's id
	// and entry name no member: the graph draws the call under them.
	for _, f := range c.Families {
		for _, m := range f.Members {
			if m.Door == "" {
				continue
			}
			e, _ := registry.ByName(m.Entry)
			call, _ := e.Door()
			d := c.byDoor[m.Door]
			if d == nil {
				d = &Door{ID: m.Door, Entry: path.Base(f.Name) + "." + call.Name, Family: f.Name, Name: call.Name, Door: call.Door, Type: call.Type,
					Internal: unicode.IsLower([]rune(call.Name)[0])}
				for _, clash := range []*Member{c.byID[d.ID], c.byEntry[d.Entry]} {
					if clash != nil {
						return nil, fmt.Errorf("index: the %s call %s is named as the member %s", d.Door, d.ID, clash.ID)
					}
				}
				c.Doors = append(c.Doors, d)
				c.byDoor[d.ID] = d
			}
			part := DoorPart{Member: m.ID}
			for _, field := range call.Fields {
				if field.Name == m.bare() {
					part.Field, part.Symbol = field.Field, field.Symbol
				}
			}
			d.Parts = append(d.Parts, part)
		}
	}

	// Definitions and types, in registration order per family, then
	// by constant name.
	for _, f := range c.Families {
		for _, m := range f.Members {
			for _, name := range m.Defines {
				if prev, dup := c.byConst[name]; dup {
					return nil, fmt.Errorf("index: constant %s is defined by %s and by %s", name, prev.Member, m.ID)
				}
				e, _ := registry.ByName(m.Entry)
				d := &Definition{Const: name, Member: m.ID, Family: m.Family, Shape: m.Shape,
					Statement: m.Statement, Source: m.Source, Notation: e.Notation(name)}
				c.Definitions = append(c.Definitions, d)
				c.byConst[name] = d
			}
		}
	}
	// Every chapter mint is a door's: the constant manager records
	// where each chapter-minted meta was stored from, and a mint no
	// door entry claims is refused here as it is by the gate
	// (TestEveryMintIsADoor) — the index never lists a definition it
	// cannot attribute to a member.
	var strayErr error
	registry.GetConstMetaManager().RangeMintSources(func(name core.TermName, source string) bool {
		if _, byDoor := c.byConst[string(name)]; !byDoor {
			strayErr = fmt.Errorf("index: constant %s is minted at %s through no define door", name, source)
			return false
		}
		return true
	})
	if strayErr != nil {
		return nil, strayErr
	}
	sort.Slice(c.Definitions, func(i, j int) bool { return c.Definitions[i].Const < c.Definitions[j].Const })
	for _, d := range c.Definitions {
		c.byFamily[d.Family].Counts.Definitions++
	}
	// Edges: deps by id, the reverse edges, and the family graph — a
	// family depends on the families its members cite and on the
	// families whose constants its statements spell (the definitions
	// are read first, so a constant's minting family is known here).
	imports := map[string]map[string]bool{}
	c.importWitness = map[string]map[string]importWitness{}
	edge := func(m *Member, to string, reason string) {
		if to == m.Family {
			return
		}
		if imports[m.Family] == nil {
			imports[m.Family] = map[string]bool{}
			c.importWitness[m.Family] = map[string]importWitness{}
		}
		if !imports[m.Family][to] {
			imports[m.Family][to] = true
			c.importWitness[m.Family][to] = importWitness{Member: m.ID, Reason: reason}
		}
	}
	c.openedBy = map[string][]string{}
	for _, e := range registry.All() {
		m := byEntry[e]
		opened := map[*registry.ProofEntry]bool{}
		for _, name := range e.Family().RecordedUnfolds()[e.Name] {
			if d, ok := registry.ByName(name); ok {
				opened[d] = true
				m.Unfolds = append(m.Unfolds, byEntry[d].ID)
				c.openedBy[byEntry[d].ID] = append(c.openedBy[byEntry[d].ID], m.ID)
			}
		}
		sort.Strings(m.Unfolds)
		read := map[*registry.ProofEntry]bool{}
		for _, d := range e.ServedDeps() {
			read[d] = true
		}
		for _, d := range e.DepEntries() {
			dm := byEntry[d]
			m.Deps = append(m.Deps, dm.ID)
			dm.Dependents = append(dm.Dependents, m.ID)
			if opened[d] && !read[d] {
				edge(m, dm.Family, "opens the definition "+dm.ID)
			} else {
				edge(m, dm.Family, "cites "+dm.ID)
			}
		}
	}
	for _, ids := range c.openedBy {
		sort.Strings(ids)
	}
	for _, m := range c.Members {
		for _, name := range m.Constants {
			if d := c.byConst[name]; d != nil {
				edge(m, d.Family, "states `"+name+"`, minted by "+d.Member)
			}
		}
	}
	for _, m := range c.Members {
		sort.Strings(m.Dependents)
	}
	for _, f := range c.Families {
		for imported := range imports[f.Name] {
			f.Imports = append(f.Imports, imported)
			c.byFamily[imported].Importers = append(c.byFamily[imported].Importers, f.Name)
		}
		sort.Strings(f.Imports)
	}
	for _, f := range c.Families {
		sort.Strings(f.Importers)
	}
	if cycles := familyCycles(c.byFamily); cycles != nil {
		return nil, c.cycleError(cycles)
	}
	c.settle()
	for _, m := range c.Members {
		if m.Card {
			m.Backing = c.backing(m)
		}
	}

	seenType := map[string]bool{}
	for _, f := range c.Families {
		for _, m := range f.Members {
			if m.DefinesType == "" || seenType[m.DefinesType] {
				continue
			}
			seenType[m.DefinesType] = true
			c.Types = append(c.Types, &TypeDef{Type: m.DefinesType, Member: m.ID, Family: m.Family})
		}
	}
	sort.Slice(c.Types, func(i, j int) bool { return c.Types[i].Type < c.Types[j].Type })

	// Domains.
	byDomain := map[string]*Domain{}
	for _, f := range c.Families {
		d := byDomain[f.Domain]
		if d == nil {
			d = &Domain{Name: f.Domain}
			byDomain[f.Domain] = d
			c.Domains = append(c.Domains, d)
		}
		d.Families = append(d.Families, f)
		d.Counts.add(f.Counts)
	}
	sort.Slice(c.Domains, func(i, j int) bool { return c.Domains[i].Name < c.Domains[j].Name })
	return c, nil
}

// readFamily reads one family: its gloss off the chapter README and
// its members, each member's cards read off frontiers.
func (c *Corpus) readFamily(rf *registry.Family, frontiers *registry.CardFrontiers) (*Family, error) {
	dir := rf.Dir
	if dir == "" {
		dir = rf.Name
	}
	f := &Family{Name: rf.Name, Domain: strings.SplitN(rf.Name, "/", 2)[0], Dir: dir}
	gloss, err := registry.ChapterGloss(filepath.Join(c.Root, filepath.FromSlash(dir)))
	if err != nil {
		return nil, fmt.Errorf("index: family %s: %v", rf.Name, err)
	}
	f.Readme = path.Join(dir, "README.md")
	f.Gloss = gloss
	f.Abbrev = rf.AbbrevOwn()
	f.AbbrevOuter = rf.AbbrevOuter()
	for _, e := range rf.Entries() {
		m := readMember(e, frontiers)
		f.Members = append(f.Members, m)
		f.Counts.Members++
		if m.Internal {
			f.Counts.Internal++
		}
		if m.Card {
			f.Counts.Cards++
		}
		if m.Postulate {
			f.Counts.Postulates++
		}
	}
	return f, nil
}

// spellStatements spells every member's served text on every
// processor. A text folds the chapter's notation and parses the fold
// back to the member's key, most of what reading the corpus costs;
// each is spelled once behind its own lock, and readMember then reads
// it spelled.
func spellStatements(entries []*registry.ProofEntry) {
	next := make(chan *registry.ProofEntry)
	var wg sync.WaitGroup
	for range runtime.GOMAXPROCS(0) {
		wg.Go(func() {
			for e := range next {
				e.StatementText()
			}
		})
	}
	for _, e := range entries {
		next <- e
	}
	close(next)
	wg.Wait()
}

// settle computes what the deps decide once they are read: each
// family's Proved / OnCards census, each card's Depth, and each
// family's Height.
func (c *Corpus) settle() {
	for _, f := range c.Families {
		for _, m := range f.Members {
			switch {
			case m.Card, m.Postulate:
			case len(m.Cards) > 0:
				f.Counts.OnCards++
			default:
				f.Counts.Proved++
			}
		}
	}
	depth := map[*Member]int{}
	var depthOf func(m *Member) int
	depthOf = func(m *Member) int {
		if d, ok := depth[m]; ok {
			return d
		}
		depth[m] = 1 // the registry refuses a cycle through Deps; this is the guard
		d := 1
		for _, id := range m.Deps {
			if dep := c.byID[id]; dep.Card {
				if x := depthOf(dep) + 1; x > d {
					d = x
				}
			}
		}
		depth[m] = d
		return d
	}
	for _, m := range c.Members {
		if m.Card {
			m.Depth = depthOf(m)
		}
	}
	height := map[string]int{}
	var heightOf func(f *Family) int
	heightOf = func(f *Family) int {
		if h, ok := height[f.Name]; ok {
			return h
		}
		height[f.Name] = 0
		h := 0
		for _, imp := range f.Imports {
			if x := heightOf(c.byFamily[imp]) + 1; x > h {
				h = x
			}
		}
		height[f.Name] = h
		return h
	}
	for _, f := range c.Families {
		f.Height = heightOf(f)
	}
}

// statementAbbreviations is the entries the member's statement spells
// and what those stand on, from the table every text of the member
// reads (Member.Abbreviations).
func statementAbbreviations(e *registry.ProofEntry) dsl.Abbrev {
	return e.AbbreviationTable().Needed(dsl.AbbreviationNames(e.StatementText()))
}

// readMember reads one member off its registered entry. The cards it
// stands on come from frontiers, the one table a reading of the corpus
// shares across its members.
func readMember(e *registry.ProofEntry, frontiers *registry.CardFrontiers) *Member {
	st := e.Statement()
	m := &Member{
		ID:            MemberID(e),
		Entry:         e.Name,
		Family:        e.Family().Name,
		Key:           e.Key,
		Statement:     e.StatementText(),
		Abbreviations: statementAbbreviations(e),
		Source:        e.Source(),
		Constants:     constantsOf(st.Prop),
		Defines:       e.Defines(),
		DefinesType:   e.DefinesType(),
		ServesAs:      e.ServesAs,
		Reading:       e.Reading,
		Concludes:     concludesOf(st.Prop),
	}
	m.ConclusionConstants, m.HypothesisConstants = constantsByRole(st.Prop)
	bare := e.BareName()
	m.Internal = bare != "" && unicode.IsLower([]rune(bare)[0])
	switch {
	case m.DefinesType != "":
		m.Kind = "type"
	case len(m.Defines) > 0 && registry.IsStructurePredicate(m.Defines[0]):
		m.Kind = "structure"
	case e.Definition != proof.NotADefinition:
		m.Kind = "definition"
	case e.IsCard():
		m.Kind = "card"
	case e.IsPostulate():
		m.Kind = "postulate"
	default:
		m.Kind = "theorem"
	}
	if e.Definition != proof.NotADefinition {
		m.Shape = e.Definition.String()
	}
	m.Card, m.Note = e.IsCard(), e.CardNote()
	m.Postulate = e.IsPostulate()
	for _, name := range frontiers.Of(e) {
		card, _ := registry.ByName(name)
		m.Cards = append(m.Cards, MemberID(card))
	}
	if p, ok := registry.ProjectionOf(e); ok {
		m.Projection = p.To
		m.Readable = &ReadableLaws{law: e}
	}
	if call, ok := e.Door(); ok {
		m.Door = e.Family().Name + "." + call.Name
	}
	return m
}

// constantsOf lists the non-builtin constants a statement mentions,
// sorted.
func constantsOf(p core.Prop) []string {
	found := map[core.TermKey]ext.ConstTerm{}
	ext.CollectConstTerms(p.Conclusion(), found)
	for _, h := range p.Hyps() {
		ext.CollectConstTerms(h, found)
	}
	return constNames(found)
}

// constantsByRole lists the constants a statement mentions under its
// conclusion and under its hypotheses, each sorted: ∀x. P ⇒ Q yields
// Q's as the conclusion's and P's as the hypotheses'. The sequent
// hypotheses count among the hypotheses, as constantsOf counts them.
func constantsByRole(p core.Prop) (conclusion, hypotheses []string) {
	_, hyps, concl := statementShape(p.Conclusion())
	found := map[core.TermKey]ext.ConstTerm{}
	ext.CollectConstTerms(concl, found)
	conclusion = constNames(found)
	found = map[core.TermKey]ext.ConstTerm{}
	for _, h := range hyps {
		ext.CollectConstTerms(h, found)
	}
	for _, h := range p.Hyps() {
		ext.CollectConstTerms(h, found)
	}
	return conclusion, constNames(found)
}

// constNames is the names of the constants collected, sorted; nil for
// none.
func constNames(found map[core.TermKey]ext.ConstTerm) []string {
	if len(found) == 0 {
		return nil
	}
	names := make([]string, 0, len(found))
	for _, c := range found {
		names = append(names, string(c.Name()))
	}
	sort.Strings(names)
	return names
}

// familyCycles finds the cycles of the family graph — each a sequence
// of families importing the next, closed by the first family repeated
// at the end — one per back edge of a depth-first walk in name order,
// so every chapter standing on a chapter that stands on it is named in
// one run; nil for an acyclic graph.
func familyCycles(byFamily map[string]*Family) [][]string {
	names := make([]string, 0, len(byFamily))
	for name := range byFamily {
		names = append(names, name)
	}
	sort.Strings(names)
	const (
		unseen = iota
		open
		done
	)
	state := map[string]int{}
	var stack []string
	var found [][]string
	var visit func(name string)
	visit = func(name string) {
		state[name] = open
		stack = append(stack, name)
		for _, imp := range byFamily[name].Imports {
			switch state[imp] {
			case open:
				start := 0
				for stack[start] != imp {
					start++
				}
				found = append(found, append(append([]string(nil), stack[start:]...), imp))
			case unseen:
				visit(imp)
			}
		}
		stack = stack[:len(stack)-1]
		state[name] = done
	}
	for _, name := range names {
		if state[name] == unseen {
			visit(name)
		}
	}
	return found
}

// cycleError names every cycle of the family graph edge by edge, each
// edge with the member that made it and how: the finding is a chapter
// citing, or stating a constant of, a chapter that stands on it.
func (c *Corpus) cycleError(cycles [][]string) error {
	var b strings.Builder
	fmt.Fprintf(&b, "index: the family graph has %s — a chapter depends on a chapter that stands on it:", plural(len(cycles), "cycle", "cycles"))
	for _, cycle := range cycles {
		b.WriteString("\n ")
		for i := 0; i+1 < len(cycle); i++ {
			w := c.importWitness[cycle[i]][cycle[i+1]]
			fmt.Fprintf(&b, "\n  %s → %s  (%s %s)", cycle[i], cycle[i+1], w.Member, w.Reason)
		}
	}
	return errors.New(b.String())
}

// DefinitionOf is the definition that minted the constant, nil for a
// constant no chapter minted (an engine built-in).
func (c *Corpus) DefinitionOf(constName string) *Definition { return c.byConst[constName] }

// ResolveFamily finds a family by its name, the corpus-relative
// package path, and failing that by its short name, the path's last
// element alone, when no other family has that short name.
func (c *Corpus) ResolveFamily(name string) (*Family, bool) {
	if f, ok := c.byFamily[name]; ok {
		return f, true
	}
	if fs := c.byShort[name]; len(fs) == 1 {
		return fs[0], true
	}
	return nil, false
}

func (c *Corpus) family(name string) (*Family, error) {
	f, ok := c.ResolveFamily(name)
	if ok {
		return f, nil
	}
	if fs := c.byShort[name]; len(fs) > 1 {
		paths := make([]string, len(fs))
		for i, x := range fs {
			paths[i] = x.Name
		}
		return nil, fmt.Errorf("%q is the short name of %d families, %s: name one by its path", name, len(fs), strings.Join(paths, ", "))
	}
	return nil, fmt.Errorf("%q names no family (the corpus-relative package path, e.g. real/real_sequences, or its last element alone, real_sequences)", name)
}

// Resolve finds a member by a reference: its index id, registered name
// or own key.
func (c *Corpus) Resolve(ref string) (*Member, bool) {
	if m, ok := c.byID[ref]; ok {
		return m, true
	}
	if m, ok := c.byEntry[ref]; ok {
		return m, true
	}
	if m, ok := c.byKey[ref]; ok {
		return m, true
	}
	return nil, false
}

// ResolveBare finds every member under a bare name, the name after the
// family's in its registered name, family by family. A bare name is no
// reference: several chapters each state their own AddAssoc.
func (c *Corpus) ResolveBare(name string) []*Member {
	return slices.Clone(c.byBare[name])
}

// ResolveOne finds the one member a name names: a reference Resolve
// finds, or a bare name one member alone has. A bare name several
// members have refuses, listing them, since the question asked of it
// is asked of one member.
func (c *Corpus) ResolveOne(ref string) (*Member, error) {
	if m, ok := c.Resolve(ref); ok {
		return m, nil
	}
	switch ms := c.byBare[ref]; len(ms) {
	case 0:
		return nil, fmt.Errorf("%q names no corpus member (an index id <family>.<Name>, a registered name, an entry's own key, or a bare name <Name>)", ref)
	case 1:
		return ms[0], nil
	default:
		ids := make([]string, len(ms))
		for i, m := range ms {
			ids[i] = m.ID
		}
		return nil, fmt.Errorf("%q is the bare name of %d members, %s: name one by its id or registered name", ref, len(ms), strings.Join(ids, ", "))
	}
}

// Totals sizes the whole corpus.
func (c *Corpus) Totals() Counts {
	var t Counts
	for _, f := range c.Families {
		t.add(f.Counts)
	}
	return t
}

// ---------------------------------------------------------------------------
// Views
// ---------------------------------------------------------------------------

// Overview is the corpus in one reading: totals and the domains with
// one line per family. It is the panorama a reader opens before
// choosing a family — what each chapter is about and how much of it is
// proved — and so carries nothing another question serves: a family's
// imports are in `query family`, the cards and the heads of their
// plans in `query cards`.
type Overview struct {
	Totals  Counts       `json:"totals"`
	Domains []DomainLine `json:"domains"`
	// DomainEdges is the family graph read at the domains: one edge
	// per ordered pair of domains some family of the first imports a
	// family of the second, weighted by how many such family imports
	// there are. The drawable global graph — a dozen nodes where the
	// family graph has a hundred.
	DomainEdges []DomainEdge `json:"domain_edges,omitempty"`
}

// DomainEdge is one weighted edge of the domain graph.
type DomainEdge struct {
	From   string `json:"from"`
	To     string `json:"to"`
	Weight int    `json:"weight"`
}

// DomainLine is a domain's row in the overview.
type DomainLine struct {
	Domain   string       `json:"domain"`
	Counts   Counts       `json:"counts"`
	Families []FamilyLine `json:"families"`
}

// FamilyLine is a family's row in the overview.
type FamilyLine struct {
	Family string `json:"family"`
	Gloss  string `json:"gloss,omitempty"`
	Height int    `json:"height"`
	Counts Counts `json:"counts"`
}

func (f *Family) line() FamilyLine {
	return FamilyLine{Family: f.Name, Gloss: f.Gloss, Height: f.Height, Counts: f.Counts}
}

// Overview computes the overview.
func (c *Corpus) Overview() *Overview {
	o := &Overview{Totals: c.Totals()}
	for _, d := range c.Domains {
		dl := DomainLine{Domain: d.Name, Counts: d.Counts}
		for _, f := range d.Families {
			dl.Families = append(dl.Families, f.line())
		}
		o.Domains = append(o.Domains, dl)
	}
	o.DomainEdges = c.DomainEdges()
	return o
}

// DomainEdges is the family graph at the domains, weighted: see
// Overview.DomainEdges. Sorted by from, then to.
func (c *Corpus) DomainEdges() []DomainEdge {
	weight := map[[2]string]int{}
	for _, f := range c.Families {
		for _, imp := range f.Imports {
			to := c.byFamily[imp].Domain
			if to != f.Domain {
				weight[[2]string{f.Domain, to}]++
			}
		}
	}
	var edges []DomainEdge
	for k, w := range weight {
		edges = append(edges, DomainEdge{From: k[0], To: k[1], Weight: w})
	}
	sort.Slice(edges, func(i, j int) bool {
		if edges[i].From != edges[j].From {
			return edges[i].From < edges[j].From
		}
		return edges[i].To < edges[j].To
	})
	return edges
}

// FamilyView is one chapter: the Family with its members, in
// registration order, each marked internal or not, its projection
// laws' readables derived and spelled on every processor
// (spellReadables), since the encoding reads every one of them.
func (c *Corpus) FamilyView(name string) (*Family, error) {
	f, err := c.family(name)
	if err != nil {
		return nil, err
	}
	c.spellReadables(f.Members)
	if err := c.readGlosses(f); err != nil {
		return nil, err
	}
	return f, nil
}

// MemberView is one member in full.
func (c *Corpus) MemberView(ref string) (*Member, error) {
	m, err := c.ResolveOne(ref)
	if err != nil {
		return nil, err
	}
	if err := c.readGloss(m); err != nil {
		return nil, err
	}
	return m, nil
}

// Direction of a graph walk.
type Direction string

const (
	// Deps walks what a member cites.
	Deps Direction = "deps"
	// Dependents walks what cites a member.
	Dependents Direction = "dependents"
)

// Neighbors is a member's citation neighborhood to a depth.
type Neighbors struct {
	Member    MemberRef     `json:"member"`
	Direction Direction     `json:"direction"`
	Depth     int           `json:"depth"`
	Levels    []Level       `json:"levels"`
	Families  []FamilyCount `json:"families,omitempty"`
	// UsedBy, in a Dependents answer, are the members whose statement
	// spells a constant the member mints and that do not depend on it
	// (Corpus.UsedBy): a statement reads no entry, so a definition with
	// no dependent may still be used.
	UsedBy []Use `json:"used_by,omitempty"`
}

// Level is one distance from the member.
type Level struct {
	Depth   int         `json:"depth"`
	Members []MemberRef `json:"members"`
}

// FamilyCount counts the members of one family in an answer.
type FamilyCount struct {
	Family string `json:"family"`
	Count  int    `json:"count"`
}

// Neighbors walks the citation graph from a member: direction Deps
// follows what it cites, Dependents what cites it. depth 1 is the
// direct edges; depth 0 is the whole transitive reach. Each level lists
// the members first reached at that distance, in id order. A
// Dependents answer lists beside them the members that use the member
// and cite it nowhere (UsedBy).
func (c *Corpus) Neighbors(ref string, dir Direction, depth int) (*Neighbors, error) {
	m, err := c.ResolveOne(ref)
	if err != nil {
		return nil, err
	}
	if dir != Deps && dir != Dependents {
		return nil, fmt.Errorf("direction must be %q or %q, not %q", Deps, Dependents, dir)
	}
	if depth < 0 {
		return nil, fmt.Errorf("depth must be 0 (the whole reach) or positive, not %d", depth)
	}
	n := &Neighbors{Member: m.ref(), Direction: dir, Depth: depth}
	if dir == Dependents {
		n.UsedBy = c.UsedBy(m)
	}
	seen := map[string]bool{m.ID: true}
	frontier := []*Member{m}
	perFamily := map[string]int{}
	for d := 1; len(frontier) > 0 && (depth == 0 || d <= depth); d++ {
		var next []*Member
		for _, cur := range frontier {
			edges := cur.Deps
			if dir == Dependents {
				edges = cur.Dependents
			}
			for _, id := range edges {
				if seen[id] {
					continue
				}
				seen[id] = true
				next = append(next, c.byID[id])
			}
		}
		if len(next) == 0 {
			break
		}
		sort.Slice(next, func(i, j int) bool { return next[i].ID < next[j].ID })
		level := Level{Depth: d}
		for _, x := range next {
			level.Members = append(level.Members, x.ref())
			perFamily[x.Family]++
		}
		n.Levels = append(n.Levels, level)
		frontier = next
	}
	for fam, count := range perFamily {
		n.Families = append(n.Families, FamilyCount{Family: fam, Count: count})
	}
	sort.Slice(n.Families, func(i, j int) bool { return n.Families[i].Family < n.Families[j].Family })
	return n, nil
}

// Path is a citation chain between two members.
type Path struct {
	From MemberRef `json:"from"`
	To   MemberRef `json:"to"`
	// Found is false when neither member reaches the other.
	Found bool `json:"found"`
	// Direction says which way the chain runs: "from cites to" or "to
	// cites from".
	Direction string `json:"direction,omitempty"`
	// Path is the chain, first member to last, each citing the next.
	Path []MemberRef `json:"path,omitempty"`
}

// Between finds a shortest citation chain from one member to another,
// in either direction.
func (c *Corpus) Between(fromRef, toRef string) (*Path, error) {
	from, err := c.ResolveOne(fromRef)
	if err != nil {
		return nil, err
	}
	to, err := c.ResolveOne(toRef)
	if err != nil {
		return nil, err
	}
	p := &Path{From: from.ref(), To: to.ref()}
	if chain := c.shortestChain(from, to); chain != nil {
		p.Found, p.Direction, p.Path = true, "from cites to", chain
	} else if chain := c.shortestChain(to, from); chain != nil {
		p.Found, p.Direction, p.Path = true, "to cites from", chain
	}
	return p, nil
}

// shortestChain is a breadth-first search over Deps from a to b; nil
// when a does not reach b.
func (c *Corpus) shortestChain(a, b *Member) []MemberRef {
	prev := map[string]string{a.ID: ""}
	queue := []*Member{a}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if cur == b {
			var chain []MemberRef
			for id := b.ID; id != ""; id = prev[id] {
				chain = append([]MemberRef{c.byID[id].ref()}, chain...)
			}
			return chain
		}
		for _, id := range cur.Deps {
			if _, visited := prev[id]; visited {
				continue
			}
			prev[id] = cur.ID
			queue = append(queue, c.byID[id])
		}
	}
	return nil
}

// DefinitionView is a constant: who defines it, who speaks of it, who
// establishes it and who asks for it.
type DefinitionView struct {
	Definition Definition `json:"definition"`
	// Mentions lists, per family, the members whose statement mentions
	// the constant.
	Mentions []FamilyMembers `json:"mentions,omitempty"`
	// ConcludedBy lists, by stratum, the members whose conclusion
	// mentions the constant — what establishes it — the definition
	// doors left out, since a definition unfolds its constant and
	// establishes nothing; AssumedBy, by stratum, the members whose
	// hypotheses mention it. Both are written when empty: an empty
	// ConcludedBy says the corpus states the constant and never
	// establishes it.
	ConcludedBy []StratumMembers `json:"concluded_by"`
	AssumedBy   []StratumMembers `json:"assumed_by"`
	// CitedBy lists the members that stand on the defining entry: the
	// ones that cite it and the ones that open its constant.
	CitedBy []string `json:"cited_by,omitempty"`
	// UnfoldedBy lists, among CitedBy, the members whose proofs open a
	// constant of the defining entry (Member.Unfolds), in id order.
	UnfoldedBy []string `json:"unfolded_by,omitempty"`
}

// FamilyMembers is a family's members in an answer.
type FamilyMembers struct {
	Family  string   `json:"family"`
	Members []string `json:"members"`
}

// StratumMembers is one stratum's members in an answer, in id order;
// Status is proved, on_cards, card or postulate.
type StratumMembers struct {
	Status  string   `json:"status"`
	Members []string `json:"members"`
}

// strataOrder is the order the strata are listed in.
var strataOrder = []string{"proved", "on_cards", "card", "postulate"}

// byRole lists, by stratum, the members whose conclusion mentions a
// constant and the members whose hypotheses do, the definition doors
// left out of the first.
func (c *Corpus) byRole(constName string) (concluded, assumed []StratumMembers) {
	conclude, assume := map[string][]string{}, map[string][]string{}
	for _, m := range c.Members {
		if slices.Contains(m.ConclusionConstants, constName) && !m.isDoor() {
			conclude[m.Status()] = append(conclude[m.Status()], m.ID)
		}
		if slices.Contains(m.HypothesisConstants, constName) {
			assume[m.Status()] = append(assume[m.Status()], m.ID)
		}
	}
	strata := func(by map[string][]string) []StratumMembers {
		out := []StratumMembers{}
		for _, status := range strataOrder {
			if ids := by[status]; len(ids) > 0 {
				out = append(out, StratumMembers{Status: status, Members: ids})
			}
		}
		return out
	}
	return strata(conclude), strata(assume)
}

// isDoor says the member is a definition door's entry — a definition,
// a structure or a type — which mints and establishes nothing.
func (m *Member) isDoor() bool {
	switch m.Kind {
	case "definition", "structure", "type":
		return true
	}
	return false
}

// bare is the member's bare name, the registered name's after the
// family's: what a chapter's prose calls it.
func (m *Member) bare() string {
	return m.ID[strings.LastIndex(m.ID, ".")+1:]
}

// Status is a member's stratum: "postulate", "card", "on_cards" (proved
// relative to the cards it stands on) or "proved" (outright).
func (m *Member) Status() string {
	switch {
	case m.Postulate:
		return "postulate"
	case m.Card:
		return "card"
	case len(m.Cards) > 0:
		return "on_cards"
	}
	return "proved"
}

// DefinitionView answers for a constant by name. A name no chapter
// defines is refused: a type's name naming the member that minted the
// type, a declared word naming the constants it spells.
func (c *Corpus) DefinitionView(constName string) (*DefinitionView, error) {
	d, ok := c.byConst[constName]
	if !ok {
		for _, t := range c.Types {
			if t.Type == constName {
				return nil, fmt.Errorf("%q is a type, minted by %s, and no constant", constName, t.Member)
			}
		}
		var spelled []string
		for _, d := range c.Definitions {
			if d.Notation == constName {
				spelled = append(spelled, d.Const)
			}
		}
		if len(spelled) > 0 {
			return nil, fmt.Errorf("%q is a word, spelling %s; a definition is asked for by the constant's name",
				constName, strings.Join(spelled, ", "))
		}
		return nil, fmt.Errorf("%q is defined by no chapter (an engine built-in, or not a constant's name)", constName)
	}
	v := &DefinitionView{
		Definition: *d, CitedBy: c.byID[d.Member].Dependents, UnfoldedBy: c.openedBy[d.Member],
	}
	v.ConcludedBy, v.AssumedBy = c.byRole(constName)
	perFamily := map[string][]string{}
	for _, m := range c.Members {
		for _, name := range m.Constants {
			if name == constName {
				perFamily[m.Family] = append(perFamily[m.Family], m.ID)
				break
			}
		}
	}
	for _, f := range c.Families {
		if ids := perFamily[f.Name]; len(ids) > 0 {
			v.Mentions = append(v.Mentions, FamilyMembers{Family: f.Name, Members: ids})
		}
	}
	return v, nil
}

// ConstantsView answers for several constants named at once: the
// DefinitionView of each the corpus defines and the refusal of each it
// does not, both in the order the names were given.
type ConstantsView struct {
	Definitions []*DefinitionView `json:"definitions"`
	Undefined   []UndefinedName   `json:"undefined,omitempty"`
}

// UndefinedName is a name a ConstantsView asked for and no chapter
// defines as a constant, with DefinitionView's refusal.
type UndefinedName struct {
	Name   string `json:"name"`
	Reason string `json:"reason"`
}

// ConstantsView answers for constants by name, one answer per name.
func (c *Corpus) ConstantsView(names []string) *ConstantsView {
	v := &ConstantsView{Definitions: []*DefinitionView{}}
	for _, name := range names {
		d, err := c.DefinitionView(name)
		if err != nil {
			v.Undefined = append(v.Undefined, UndefinedName{Name: name, Reason: err.Error()})
			continue
		}
		v.Definitions = append(v.Definitions, d)
	}
	return v
}

// DefinitionsView lists every minted constant and type.
type DefinitionsView struct {
	Definitions []*Definition `json:"definitions"`
	Types       []*TypeDef    `json:"types"`
}

// DefinitionsView lists every minted constant and type.
func (c *Corpus) DefinitionsView() *DefinitionsView {
	return &DefinitionsView{Definitions: c.Definitions, Types: c.Types}
}

// Card is a member stated without a proof, with who stands on it.
type Card struct {
	Member MemberRef `json:"member"`
	Note   string    `json:"note,omitempty"`
	// StatementTyped is the card's parse-faithful spelling, paste-ready
	// for `add-goal {text}`; empty until CardsView.Spell fills it, and
	// where the print does not round-trip.
	StatementTyped string `json:"statement_typed,omitempty"`
	// CitedBy are the ids of the members whose Deps name the card.
	CitedBy []string `json:"cited_by,omitempty"`
}

// CardsView lists the cards of the corpus, or of some of its families,
// leaves first (registry.CardFillOrder: a card after every card it stands on, then
// by how many members stand on each, then by name), the same cards
// split by what a proof of each would stand on — Leaves, OnCards —
// the Heads of the plan, and the members standing on cards. Every
// card can be filled now and in any order: a proof cites the cards
// under it as the axioms they are, and leaves first is only the order
// that re-proves least when a card is found false.
type CardsView struct {
	Cards []Card `json:"cards"`
	// Leaves are the cards citing no card: their plans stand on proved
	// members alone, so a proof of one is proved outright. In fill
	// order.
	Leaves []Card `json:"leaves,omitempty"`
	// OnCards are the cards citing cards, each with the cards its plan
	// stands on (its frontier less itself): a proof of one is proved on
	// those cards until they are filled too. In fill order.
	OnCards []CardOnCards `json:"on_cards,omitempty"`
	// Heads are the cards no member cites — the tops of the plans.
	// Largest plan first, then deepest, then by name.
	Heads []Head `json:"heads,omitempty"`
	// Standing lists the proved members whose Deps reach a card, with
	// their frontier — what the corpus proves only relative to a card.
	Standing []Standing `json:"standing,omitempty"`
}

// CardOnCards is a card and the cards its plan stands on.
type CardOnCards struct {
	Card
	On []string `json:"on"`
}

// Head is a card no member cites: its plan's size (the cards under
// it) and depth.
type Head struct {
	Member MemberRef `json:"member"`
	Under  int       `json:"under"`
	Depth  int       `json:"depth"`
}

// Standing is a proved member and the cards it stands on.
type Standing struct {
	Member MemberRef `json:"member"`
	Cards  []string  `json:"cards"`
}

// CardsView lists the cards of the named families, of every family
// when none is named, and the members of those families standing on a
// card. A name resolves as FamilyView's does, and one that names no
// family refuses the question.
func (c *Corpus) CardsView(families ...string) (*CardsView, error) {
	kept := map[string]bool{}
	for _, name := range families {
		f, err := c.family(name)
		if err != nil {
			return nil, err
		}
		kept[f.Name] = true
	}
	return c.cards(kept), nil
}

// Spell fills every card's StatementTyped with typed's spelling of its
// registered entry. The engine spells a statement typed, and the index
// does not read the engine, so the reader holding both spells the view.
func (v *CardsView) Spell(typed func(entry string) string) {
	for i := range v.Cards {
		v.Cards[i].StatementTyped = typed(v.Cards[i].Member.Entry)
	}
	for i := range v.Leaves {
		v.Leaves[i].StatementTyped = typed(v.Leaves[i].Member.Entry)
	}
	for i := range v.OnCards {
		v.OnCards[i].StatementTyped = typed(v.OnCards[i].Member.Entry)
	}
}

// cards is CardsView of the families kept, of every family when kept
// is empty.
func (c *Corpus) cards(kept map[string]bool) *CardsView {
	keeps := func(m *Member) bool { return len(kept) == 0 || kept[m.Family] }
	v := &CardsView{Cards: []Card{}}
	for _, name := range registry.CardFillOrder() {
		m := c.byEntry[name]
		if !keeps(m) {
			continue
		}
		card := Card{Member: m.ref(), Note: m.Note}
		for _, id := range m.Dependents {
			card.CitedBy = append(card.CitedBy, id)
		}
		v.Cards = append(v.Cards, card)
		var on []string
		for _, id := range m.Cards {
			if id != m.ID {
				on = append(on, id)
			}
		}
		if len(on) == 0 {
			v.Leaves = append(v.Leaves, card)
		} else {
			v.OnCards = append(v.OnCards, CardOnCards{Card: card, On: on})
		}
		if len(m.Dependents) == 0 {
			v.Heads = append(v.Heads, Head{Member: m.ref(), Under: len(m.Cards) - 1, Depth: m.Depth})
		}
	}
	sort.Slice(v.Heads, func(i, j int) bool {
		a, b := v.Heads[i], v.Heads[j]
		if a.Under != b.Under {
			return a.Under > b.Under
		}
		if a.Depth != b.Depth {
			return a.Depth > b.Depth
		}
		return a.Member.ID < b.Member.ID
	})
	for _, m := range c.Members {
		if !m.Card && len(m.Cards) > 0 && keeps(m) {
			v.Standing = append(v.Standing, Standing{Member: m.ref(), Cards: m.Cards})
		}
	}
	return v
}

// AxiomsView lists every member the corpus serves as an axiom: the
// postulate, assumed outright and for good, and the cards, stated
// without a proof and axioms until their proofs land, in CardsView's
// fill order. A cite of either is a cite of an axiom; nothing else in
// the corpus is one (core/README.md, "The logic and what it assumes":
// the rules η and choice besides).
type AxiomsView struct {
	Postulates []Postulate `json:"postulates"`
	Cards      []Card      `json:"cards"`
}

// Postulate is a member assumed outright, with the members whose Deps
// name it.
type Postulate struct {
	Member  MemberRef `json:"member"`
	CitedBy []string  `json:"cited_by,omitempty"`
}

// AxiomsView lists the postulate and the cards.
func (c *Corpus) AxiomsView() *AxiomsView {
	v := &AxiomsView{Postulates: []Postulate{}, Cards: c.cards(nil).Cards}
	for _, m := range c.Members {
		if m.Postulate {
			v.Postulates = append(v.Postulates, Postulate{Member: m.ref(), CitedBy: m.Dependents})
		}
	}
	return v
}

// spellReadables derives the laws readable through the projection
// laws among members and spells each one's body, on every processor:
// first the projections, each one's laws derived once behind its own
// sync.Once (ReadableLaws.Laws), then the bodies, each spelled once
// the same way. Deriving and spelling them is most of what encoding a
// family with its projections costs; the encoding then reads the laws
// derived and the bodies spelled.
func (c *Corpus) spellReadables(members []*Member) {
	var projections []*Member
	for _, m := range members {
		if m.Readable != nil {
			projections = append(projections, m)
		}
	}
	onEveryProcessor(len(projections), func(i int) { projections[i].Readable.Laws() })
	var laws []ReadableLaw
	for _, m := range projections {
		laws = append(laws, m.Readable.Laws()...)
	}
	onEveryProcessor(len(laws), func(i int) { laws[i].Body() })
}

// onEveryProcessor runs do(i) for each i below n, the calls spread
// over every processor.
func onEveryProcessor(n int, do func(i int)) {
	next := make(chan int)
	var wg sync.WaitGroup
	for range runtime.GOMAXPROCS(0) {
		wg.Go(func() {
			for i := range next {
				do(i)
			}
		})
	}
	for i := range n {
		next <- i
	}
	close(next)
	wg.Wait()
}

// plural is a count with its noun, the noun in the number the count asks.
func plural(n int, one, many string) string {
	if n == 1 {
		return fmt.Sprintf("%d %s", n, one)
	}
	return fmt.Sprintf("%d %s", n, many)
}
