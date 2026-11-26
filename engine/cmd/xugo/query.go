package main

// `query` — the corpus asked as a whole (library/index). One door, one
// body, several questions: the overview an agent reads first, a
// family, a member, a member's dossier, a member's citation
// neighborhood — each of one name or of several — a citation path
// between two members, a constant's definition and uses (or several
// constants' at once), every definition, every card (or some
// families' cards), every axiom, and the corpus drawn
// (library/visualize): its families, or a member's proof. The generated pages under library/index render the index's
// views, so what this answers and what a reader browses are one thing.

import (
	"fmt"
	"path/filepath"
	"runtime/debug"
	"strconv"
	"strings"

	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/library/index"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/visualize"
)

// QueryRPCInput is the body `query` takes. `what` picks the question;
// the other fields are the question's arguments, and a field a question
// does not take is refused by name. `root` is the library/proofs
// directory (default: under the go.mod above the working directory).
type QueryRPCInput struct {
	What   string `json:"what"`
	Family string `json:"family,omitempty"`
	// Families names several families for one `family` answer, in place
	// of Family.
	Families []string `json:"families,omitempty"`
	Member   string   `json:"member,omitempty"`
	// Members names several members for one `member`, `dossier`, `deps`
	// or `dependents` answer, in place of Member.
	Members []string `json:"members,omitempty"`
	From    string   `json:"from,omitempty"`
	To      string   `json:"to,omitempty"`
	Const   string   `json:"const,omitempty"`
	// Consts names several constants for one `definition` answer, in
	// place of Const.
	Consts []string `json:"consts,omitempty"`
	// Depth bounds a deps / dependents walk: absent is 1 (the direct
	// edges), 0 is the whole reach.
	Depth *int `json:"depth,omitempty"`
	// Scope picks the graph drawn (graphScopes): the corpus's families,
	// or the proof of Member.
	Scope string `json:"scope,omitempty"`
	Root  string `json:"root,omitempty"`
}

// queryWhats lists the questions, for the error a wrong `what` gets.
const queryWhats = "overview | family | member | dossier | deps | dependents | between | definition | definitions | cards | axioms | graph"

// graphScopes lists the graphs `query graph` draws, and graphUsage is
// its grammar, each for the error a wrong scope gets.
const (
	graphScopes = "families | proof"
	graphUsage  = "families, proof <member>"
)

// QueryMemberOutput is `query member`, the door that shows a member:
// the index member plus its statement's spelling that reads with
// nothing declared (statementTyped), when the print round-trips.
type QueryMemberOutput struct {
	*index.Member
	StatementTyped string `json:"statement_typed,omitempty"`
	// Outline is the proof's narration step by step as the chapter
	// writes it (index.OutlineStep); empty for a member with no Go
	// argument.
	Outline []index.OutlineStep `json:"outline,omitempty"`
	// UsedBy are the members whose statement spells a constant the
	// member mints and that do not depend on it (index.Corpus.UsedBy),
	// beside the Dependents the member carries; empty for a member
	// that mints no constant.
	UsedBy []index.Use `json:"used_by,omitempty"`
}

// QueryDossierOutput is `query dossier`: the index dossier plus the
// same spelling of the statement, paste-ready for a session.
type QueryDossierOutput struct {
	*index.Dossier
	StatementTyped string `json:"statement_typed,omitempty"`
}

// QueryMembersOutput is `query member` asked of several members: one
// answer per member, and the names that name no member, each list in
// the order given. The members are read in one process, which reads the
// corpus once.
type QueryMembersOutput struct {
	Members []*QueryMemberOutput `json:"members"`
	Unknown []UnknownName        `json:"unknown,omitempty"`
}

// QueryDossiersOutput is `query dossier` asked of several members, as
// QueryMembersOutput is `query member`.
type QueryDossiersOutput struct {
	Dossiers []*QueryDossierOutput `json:"dossiers"`
	Unknown  []UnknownName         `json:"unknown,omitempty"`
}

// QueryFamiliesOutput is `query family` asked of several families, as
// QueryMembersOutput is `query member`.
type QueryFamiliesOutput struct {
	Families []*index.Family `json:"families"`
	Unknown  []UnknownName   `json:"unknown,omitempty"`
}

// QueryNeighborhoodsOutput is `query deps` or `query dependents` asked
// of several members: each member's neighborhood, as
// QueryMembersOutput is `query member`.
type QueryNeighborhoodsOutput struct {
	Neighborhoods []*index.Neighbors `json:"neighborhoods"`
	Unknown       []UnknownName      `json:"unknown,omitempty"`
}

// UnknownName is a name a question of several asked for and nothing of
// the corpus carries — no member, no family — with the refusal the
// question of one gives it.
type UnknownName struct {
	Name   string `json:"name"`
	Reason string `json:"reason"`
}

// statementTyped is the member's statement in the spelling that reads
// at its family's statement door — its authored text where that reads
// there, the typed print otherwise (engine.EntryStatementTyped) — ""
// when the door reads neither.
func statementTyped(m *index.Member) string {
	entry, ok := registry.ByName(m.Entry)
	if !ok {
		panic(fmt.Sprintf("query: the index names %s, which the registry does not hold", m.Entry))
	}
	return engine.EntryStatementTyped(entry)
}

// cardStatementTyped is a card's typed spelling, by its registered
// name: what `query cards` spells its view with.
func cardStatementTyped(entry string) string {
	e, ok := registry.ByName(entry)
	if !ok {
		panic(fmt.Sprintf("query: the index names %s, which the registry does not hold", entry))
	}
	return engine.CardStatementTyped(e)
}

// oneOrSeveralMembers checks the fields of a question asked of one
// member (`member`) or of several (`members`), with the optional
// fields it takes beside, and reports which.
func (in QueryRPCInput) oneOrSeveralMembers(optional ...string) (several bool, err error) {
	if len(in.Members) == 0 {
		return false, in.takes([]string{"member"}, optional...)
	}
	if in.Member != "" {
		return false, fmt.Errorf("query %s takes `member` or `members`, not both", in.What)
	}
	return true, in.takes([]string{"members"}, optional...)
}

// memberRefs reads the members a question of one or several is asked
// of: a reference (an index id, a registered name, an own key) stands
// for its member, a bare name for every member under it
// (index.Corpus.ResolveBare), and a name naming neither stays, for the
// answer to refuse. The answer is a list when the question is asked of
// several or of a bare name, however many members that holds.
func (in QueryRPCInput) memberRefs(corpus *index.Corpus, several bool) (refs []string, list bool) {
	names := in.Members
	if !several {
		names = []string{in.Member}
	}
	list = several
	for _, name := range names {
		if _, ok := corpus.Resolve(name); ok {
			refs = append(refs, name)
			continue
		}
		bare := corpus.ResolveBare(name)
		if len(bare) == 0 {
			refs = append(refs, name)
			continue
		}
		list = true
		for _, m := range bare {
			refs = append(refs, m.ID)
		}
	}
	return refs, list
}

// eachName asks answer of each name in turn. A name nothing carries
// (known) is listed with answer's refusal and the rest are still
// asked; any other failure is the question's.
func eachName(names []string, known func(name string) bool, answer func(name string) error) ([]UnknownName, error) {
	var unknown []UnknownName
	for _, name := range names {
		err := answer(name)
		if err == nil {
			continue
		}
		if known(name) {
			return nil, err
		}
		unknown = append(unknown, UnknownName{Name: name, Reason: err.Error()})
	}
	return unknown, nil
}

// eachMember is eachName over the names of members.
func eachMember(corpus *index.Corpus, refs []string, answer func(ref string) error) ([]UnknownName, error) {
	return eachName(refs, func(ref string) bool { _, ok := corpus.Resolve(ref); return ok }, answer)
}

// memberOutput is `query member` of one member.
func memberOutput(corpus *index.Corpus, ref string) (*QueryMemberOutput, error) {
	m, err := corpus.MemberView(ref)
	if err != nil {
		return nil, err
	}
	outline, err := corpus.Outline(m)
	if err != nil {
		return nil, err
	}
	return &QueryMemberOutput{
		Member: m, StatementTyped: statementTyped(m), Outline: outline, UsedBy: corpus.UsedBy(m),
	}, nil
}

// dossierOutput is `query dossier` of one member.
func dossierOutput(corpus *index.Corpus, ref string) (*QueryDossierOutput, error) {
	d, err := corpus.Dossier(ref)
	if err != nil {
		return nil, err
	}
	m, _ := corpus.Resolve(ref)
	return &QueryDossierOutput{Dossier: d, StatementTyped: statementTyped(m)}, nil
}

func rpcQuery(body []byte) (any, error) {
	var in QueryRPCInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	return runQuery(in)
}

// takes checks the question's arguments: every required field is
// set, and no field outside required and optional is — a misplaced
// field is refused by name, never silently ignored.
func (in QueryRPCInput) takes(required []string, optional ...string) error {
	allowed := map[string]bool{}
	for _, f := range required {
		allowed[f] = true
	}
	for _, f := range optional {
		allowed[f] = true
	}
	set := map[string]bool{
		"family": in.Family != "", "families": len(in.Families) > 0, "member": in.Member != "",
		"members": len(in.Members) > 0, "from": in.From != "",
		"to": in.To != "", "const": in.Const != "", "consts": len(in.Consts) > 0, "depth": in.Depth != nil,
		"scope": in.Scope != "",
	}
	what := in.What
	if in.What == "graph" && in.Scope != "" {
		what = "graph " + in.Scope
	}
	for _, name := range []string{"scope", "family", "families", "member", "members", "from", "to", "const", "consts", "depth"} {
		if set[name] && !allowed[name] {
			return fmt.Errorf("query %s takes no `%s`", what, name)
		}
	}
	for _, f := range required {
		if !set[f] {
			return fmt.Errorf("query %s requires `%s`", what, f)
		}
	}
	return nil
}

// graph answers `query graph`: the scope's fields are checked by name,
// then the graph is drawn — the corpus's families (visualize.Families)
// or a member's proof (visualize.Proof) — and stamped with the revision
// this binary was built from.
func (in QueryRPCInput) graph(corpus *index.Corpus) (any, error) {
	switch in.Scope {
	case "families":
		if err := in.takes([]string{"scope"}); err != nil {
			return nil, err
		}
		g, err := visualize.Families(corpus)
		if err != nil {
			return nil, err
		}
		g.Revision = buildRevision()
		return g, nil
	case "proof":
		if err := in.takes([]string{"scope", "member"}); err != nil {
			return nil, err
		}
		g, err := visualize.Proof(corpus, in.Member)
		if err != nil {
			return nil, err
		}
		g.Revision = buildRevision()
		return g, nil
	case "":
		return nil, fmt.Errorf("query graph requires `scope` (%s)", graphScopes)
	}
	return nil, fmt.Errorf("query graph: unknown scope %q (%s)", in.Scope, graphScopes)
}

// buildRevision names the commit this binary was built from, and so
// the corpus it links: the revision's first nine digits, with a + when
// the tree held changes past it. Empty for a binary built with no
// version-control stamp, as `go run` and `go test` build theirs.
func buildRevision() string {
	info, ok := debug.ReadBuildInfo()
	if !ok {
		return ""
	}
	revision, modified := "", false
	for _, s := range info.Settings {
		switch s.Key {
		case "vcs.revision":
			revision = s.Value
		case "vcs.modified":
			modified = s.Value == "true"
		}
	}
	if len(revision) > 9 {
		revision = revision[:9]
	}
	if revision != "" && modified {
		revision += "+"
	}
	return revision
}

func runQuery(in QueryRPCInput) (any, error) {
	root := in.Root
	if root == "" {
		mod, err := moduleRoot()
		if err != nil {
			return nil, fmt.Errorf("query: %v (pass `root`, the library/proofs directory)", err)
		}
		root = filepath.Join(mod, "library", "proofs")
	}
	corpus, err := index.Load(root)
	if err != nil {
		return nil, err
	}
	switch in.What {
	case "overview":
		if err := in.takes(nil); err != nil {
			return nil, err
		}
		return corpus.Overview(), nil
	case "family":
		if len(in.Families) == 0 {
			if err := in.takes([]string{"family"}); err != nil {
				return nil, err
			}
			return corpus.FamilyView(in.Family)
		}
		if in.Family != "" {
			return nil, fmt.Errorf("query family takes `family` or `families`, not both")
		}
		if err := in.takes([]string{"families"}); err != nil {
			return nil, err
		}
		out := &QueryFamiliesOutput{Families: []*index.Family{}}
		known := func(name string) bool { _, ok := corpus.ResolveFamily(name); return ok }
		unknown, err := eachName(in.Families, known, func(name string) error {
			f, err := corpus.FamilyView(name)
			if err == nil {
				out.Families = append(out.Families, f)
			}
			return err
		})
		if err != nil {
			return nil, err
		}
		out.Unknown = unknown
		return out, nil
	case "member":
		several, err := in.oneOrSeveralMembers()
		if err != nil {
			return nil, err
		}
		refs, list := in.memberRefs(corpus, several)
		if !list {
			return memberOutput(corpus, refs[0])
		}
		out := &QueryMembersOutput{Members: []*QueryMemberOutput{}}
		out.Unknown, err = eachMember(corpus, refs, func(ref string) error {
			m, err := memberOutput(corpus, ref)
			if err == nil {
				out.Members = append(out.Members, m)
			}
			return err
		})
		if err != nil {
			return nil, err
		}
		return out, nil
	case "dossier":
		several, err := in.oneOrSeveralMembers()
		if err != nil {
			return nil, err
		}
		refs, list := in.memberRefs(corpus, several)
		if !list {
			return dossierOutput(corpus, refs[0])
		}
		out := &QueryDossiersOutput{Dossiers: []*QueryDossierOutput{}}
		out.Unknown, err = eachMember(corpus, refs, func(ref string) error {
			d, err := dossierOutput(corpus, ref)
			if err == nil {
				out.Dossiers = append(out.Dossiers, d)
			}
			return err
		})
		if err != nil {
			return nil, err
		}
		return out, nil
	case "deps", "dependents":
		several, err := in.oneOrSeveralMembers("depth")
		if err != nil {
			return nil, err
		}
		depth := 1
		if in.Depth != nil {
			depth = *in.Depth
		}
		refs, list := in.memberRefs(corpus, several)
		if !list {
			return corpus.Neighbors(refs[0], index.Direction(in.What), depth)
		}
		out := &QueryNeighborhoodsOutput{Neighborhoods: []*index.Neighbors{}}
		out.Unknown, err = eachMember(corpus, refs, func(ref string) error {
			n, err := corpus.Neighbors(ref, index.Direction(in.What), depth)
			if err == nil {
				out.Neighborhoods = append(out.Neighborhoods, n)
			}
			return err
		})
		if err != nil {
			return nil, err
		}
		return out, nil
	case "between":
		if err := in.takes([]string{"from", "to"}); err != nil {
			return nil, err
		}
		return corpus.Between(in.From, in.To)
	case "definition":
		if len(in.Consts) > 0 {
			if in.Const != "" {
				return nil, fmt.Errorf("query definition takes `const` or `consts`, not both")
			}
			if err := in.takes([]string{"consts"}); err != nil {
				return nil, err
			}
			return corpus.ConstantsView(in.Consts), nil
		}
		if err := in.takes([]string{"const"}); err != nil {
			return nil, err
		}
		return corpus.DefinitionView(in.Const)
	case "definitions":
		if err := in.takes(nil); err != nil {
			return nil, err
		}
		return corpus.DefinitionsView(), nil
	case "cards":
		if in.Family != "" && len(in.Families) > 0 {
			return nil, fmt.Errorf("query cards takes `family` or `families`, not both")
		}
		if err := in.takes(nil, "family", "families"); err != nil {
			return nil, err
		}
		names := in.Families
		if in.Family != "" {
			names = []string{in.Family}
		}
		v, err := corpus.CardsView(names...)
		if err != nil {
			return nil, err
		}
		v.Spell(cardStatementTyped)
		return v, nil
	case "axioms":
		if err := in.takes(nil); err != nil {
			return nil, err
		}
		return corpus.AxiomsView(), nil
	case "graph":
		return in.graph(corpus)
	case "":
		return nil, fmt.Errorf("query requires `what` (%s)", queryWhats)
	default:
		return nil, fmt.Errorf("query: unknown question %q (%s)", in.What, queryWhats)
	}
}

// cmdQuery is the CLI face of the same door:
//
//	xugo query overview
//	xugo query family real/real_sequences
//	xugo query member real/real_sequences.CauchyConverges
//	xugo query dossier <member>                 (the member in the round: reading, place, plan, use, cite)
//	xugo query deps <member> [--depth N]        (--depth 0: the whole reach)
//	xugo query dependents <member> [--depth N]
//	xugo query family|member|dossier|deps|dependents <name> <name> …
//	                                            (two or more: one answer — `families`, `members`,
//	                                            `dossiers`, `neighborhoods` — and `unknown`)
//	xugo query between <member> <member>
//	xugo query definition <constant> …          (two or more: one answer, `definitions` and `undefined`)
//	xugo query definitions | cards | axioms
//	xugo query graph families                   (every family by height, with the imports between them)
//	xugo query graph proof <member>             (a theorem's proof as the results it stands on, at three grains; a definition as what it is built from and who uses it)
//
// A graph prints as JSON, laid out; the pages drawing the graphs are
// `xugo browse`'s. --root DIR names the library/proofs directory when
// the working directory is not under the module.
func cmdQuery(args []string) {
	var in QueryRPCInput
	var positional []string
	for i := 0; i < len(args); i++ {
		switch {
		case args[i] == "--depth" && i+1 < len(args):
			in.setDepth(args[i+1])
			i++
		case strings.HasPrefix(args[i], "--depth="):
			in.setDepth(strings.TrimPrefix(args[i], "--depth="))
		case args[i] == "--root" && i+1 < len(args):
			in.Root = args[i+1]
			i++
		case strings.HasPrefix(args[i], "--root="):
			in.Root = strings.TrimPrefix(args[i], "--root=")
		case strings.HasPrefix(args[i], "--"):
			fatal("query: unknown flag %s (flags: --depth N, --root DIR)", args[i])
		default:
			positional = append(positional, args[i])
		}
	}
	if len(positional) == 0 {
		fatal("query requires a question: xugo query <%s> …", queryWhats)
	}
	in.What = positional[0]
	rest := positional[1:]
	arity := func(n int, usage string) {
		if len(rest) != n {
			fatal("query %s takes %s", in.What, usage)
		}
	}
	switch in.What {
	case "family":
		switch len(rest) {
		case 0:
			fatal("query family takes one or more family names (a path, e.g. real/real_sequences, or its short name, real_sequences)")
		case 1:
			in.Family = rest[0]
		default:
			in.Families = rest
		}
	case "member", "dossier", "deps", "dependents":
		switch len(rest) {
		case 0:
			fatal("query %s takes one or more members (each an index id <family>.<Name>, a registered name, an own key, or a bare name <Name>, which asks of every member under it)", in.What)
		case 1:
			in.Member = rest[0]
		default:
			in.Members = rest
		}
	case "between":
		arity(2, "two members")
		in.From, in.To = rest[0], rest[1]
	case "definition":
		switch len(rest) {
		case 0:
			fatal("query definition takes one or more constant names")
		case 1:
			in.Const = rest[0]
		default:
			in.Consts = rest
		}
	case "cards":
		in.Families = rest
	case "graph":
		in.graphArgs(rest)
	default:
		arity(0, "no argument")
	}
	out, err := runQuery(in)
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(out)
}

// graphArgs reads a graph's scope words into the input's fields.
func (in *QueryRPCInput) graphArgs(words []string) {
	if len(words) == 0 {
		fatal("query graph takes a scope: %s", graphUsage)
	}
	in.Scope = words[0]
	args := words[1:]
	switch in.Scope {
	case "families":
		if len(args) != 0 {
			fatal("query graph families takes no argument")
		}
	case "proof":
		if len(args) != 1 {
			fatal("query graph proof takes one member (an index id <family>.<Name>, a registered name, an own key, or a bare name one member alone has)")
		}
		in.Member = args[0]
	default:
		fatal("query graph: unknown scope %q (%s)", in.Scope, graphUsage)
	}
}

func (in *QueryRPCInput) setDepth(s string) {
	n, err := strconv.Atoi(s)
	if err != nil || n < 0 {
		fatal("query: --depth takes 0 (the whole reach) or a positive integer, not %q", s)
	}
	in.Depth = &n
}
