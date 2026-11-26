package index

import "regexp"

// CardBacking is what a card's plan stands on as recorded, read off the
// registry and never off the note's sense: the theorems among its deps
// and the members its note names. A card whose note names no member
// and whose deps are definition doors alone is a bare assertion, and
// its lists are then empty — written, not left out, so the absence is
// read.
type CardBacking struct {
	// TheoremDeps are the deps that are no definition door: the members
	// the plan cites as steps. The doors among the deps spell the
	// statement's constants and prove nothing.
	TheoremDeps []string `json:"theorem_deps"`
	// NoteNames are the member names the note mentions, each once in
	// the note's order, resolved against the registry (NoteName).
	NoteNames []NoteName `json:"note_names"`
	// NoteNamesNotCited are the members the note names and the deps do
	// not list: steps the plan speaks of and does not record.
	NoteNamesNotCited []string `json:"note_names_not_cited"`
}

// NoteName is one member name a card's note mentions. Member is the id
// it resolves to; Candidates, when the bare name is registered in more
// than one chapter and none is the card's own, the ids it could mean;
// neither when the name resolves to nothing.
type NoteName struct {
	Name       string   `json:"name"`
	Member     string   `json:"member,omitempty"`
	Candidates []string `json:"candidates,omitempty"`
}

// noteNamePattern finds the names a note may call a member by: a
// capitalized word, alone or after a chapter's basename and a dot
// (`RootBound`, `trace_dual.MonogenicCodifferent`). A name broken by
// an underscore, `Aut_K`, is no member's.
var noteNamePattern = regexp.MustCompile(`\b(?:([a-z][a-z0-9_]*)\.)?([A-Z][A-Za-z0-9]*)\b`)

// backing reads a card's recorded support: the deps that are theorems
// and the names its note mentions, resolved.
func (c *Corpus) backing(m *Member) *CardBacking {
	b := &CardBacking{TheoremDeps: []string{}, NoteNames: []NoteName{}, NoteNamesNotCited: []string{}}
	cited := map[string]bool{}
	for _, id := range m.Deps {
		cited[id] = true
		if !c.byID[id].isDoor() {
			b.TheoremDeps = append(b.TheoremDeps, id)
		}
	}
	seen := map[string]bool{}
	for _, match := range noteNamePattern.FindAllStringSubmatch(m.Note, -1) {
		family, bare := match[1], match[2]
		name := match[0]
		if seen[name] {
			continue
		}
		seen[name] = true
		n, listed := c.resolveNoteName(m, cited, family, bare)
		if !listed || n.Member == m.ID {
			continue
		}
		b.NoteNames = append(b.NoteNames, n)
		if n.Member != "" && !cited[n.Member] {
			b.NoteNamesNotCited = append(b.NoteNamesNotCited, n.Member)
		}
	}
	return b
}

// resolveNoteName reads one name a card's note mentions, and says
// whether it is listed. A qualified name, `polynomial.RootBound`, is a
// registered name and resolves by it or not at all. A bare name in
// camel case — a second capital after a lowercase letter, `RootBound`
// — is a member's: the card's own family's when it registers one,
// else the one the deps cite (cited) when the chapters registering it
// include exactly one the plan records, else the one chapter's
// registering it, else the candidates. A bare name of one hump,
// `Dedekind` or `Choose`, is a member's only when the card's family
// registers it, and otherwise a word of the prose, not listed.
func (c *Corpus) resolveNoteName(m *Member, cited map[string]bool, family, bare string) (NoteName, bool) {
	if family != "" {
		n := NoteName{Name: family + "." + bare}
		if x, ok := c.byEntry[n.Name]; ok {
			n.Member = x.ID
		}
		return n, true
	}
	n := NoteName{Name: bare}
	var elsewhere, recorded []string
	for _, x := range c.byBare[bare] {
		if x.Family == m.Family {
			n.Member = x.ID
			return n, true
		}
		elsewhere = append(elsewhere, x.ID)
		if cited[x.ID] {
			recorded = append(recorded, x.ID)
		}
	}
	if !camelCase(bare) {
		return n, false
	}
	switch {
	case len(recorded) == 1:
		n.Member = recorded[0]
	case len(elsewhere) == 1:
		n.Member = elsewhere[0]
	case len(elsewhere) > 1:
		n.Candidates = elsewhere
	}
	return n, true
}

// camelCase says a name has a second capital after a lowercase letter,
// `RootBound`: the shape a member's bare name has and a word of the
// prose, `Choose` or `GCD`, has not.
func camelCase(name string) bool {
	lower := false
	for i, r := range name {
		switch {
		case 'a' <= r && r <= 'z':
			lower = true
		case i > 0 && 'A' <= r && r <= 'Z' && lower:
			return true
		}
	}
	return false
}
