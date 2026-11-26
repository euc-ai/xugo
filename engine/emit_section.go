// Package engine — emit_section.go: render a closed session section as a
// family member.
//
// Everything the renderer needs is in memory: each section's root
// GoalStackNode carries its DetailedProofProto, and env.ProofService
// carries the CNF certificates the session recorded. EmitSection hands
// the recorded sections to emit.EmitMember with the session's resolvers
// (external statements, typed deps, the family vocabulary) and returns
// the member source, plus the certificates its replay would read — the
// author's in-session key oracle (emit.CollectCNFCache).
//
// The output is the member's mechanical translation — ministeps as Step
// verbs, deps as typed entries, statements in the chapter's spelling.
// The argument structure (Case labels, role names, a.Have facts) is the
// author's pass over it. See library/chapter_constitution.md §"Argument
// structure" and §"The session".

package engine

import (
	"errors"
	"fmt"
	"maps"
	"path"
	"slices"
	"sort"
	"strings"
	"unicode"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/emit"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// EmitSectionResult carries the family member rendered from a closed
// session section (plus the earlier proved sections the request
// included) and the CNF certificates its replay would read.
type EmitSectionResult struct {
	// SectionID echoes the caller's requested target slice index.
	SectionID int `json:"section_id"`

	// FuncName is the member name the source is rendered under
	// (Build_<Name>; the Build_ prefix is dropped in the entry var).
	// Defaults to "Build_Draft" when the caller passed empty.
	FuncName string `json:"func_name"`

	// SectionsIncluded lists the session slice indices that ended up
	// in the member, in the member's order: each after the sections it
	// cites, the last always SectionID (the target) — relevant when
	// IncludePrior was left as the default and the caller wants to see
	// which sections the target's cites brought along.
	SectionsIncluded []int `json:"sections_included"`

	// Go is the member source for the family's package: the package
	// clause from the family path's last segment, the imports, the
	// goal-text const and the family.Add entry var (a proved member
	// spells no Deps: the landing's recording observes what it reads),
	// each card the member cites rendered as an entry of its own before
	// it. One section renders a family.Theorem closure whose parameters
	// are the strips the proof opens with (library/emit/emit_signature.go)
	// — or, for a `define` section, the definition door its composite
	// records, for a structure instance proved conjunct by conjunct,
	// family.Instance, and for a law of a structure in a family stating
	// members through its door, the structure's Law; several render
	// family.Sections — each earlier section a ctx.Lemma the later ones
	// cite, the target last.
	Go string `json:"go"`

	// Capabilities is the dependency-capability list emit computed from
	// the recorded steps — what the family recorder will observe the
	// landed member using. Informational: nothing declares it.
	Capabilities []string `json:"capabilities,omitempty"`

	// DepNames lists every named theorem the member cites or reads by
	// name (sorted, deduplicated): the entries the landing's recording
	// will observe it reading. A name no landed entry proves is rendered
	// as a TODO in the entry. Informational: nothing declares it.
	DepNames []string `json:"dep_names,omitempty"`
	// UnfoldNames lists the entries defining the constants the member
	// opens (Unfold, Unfolded), by registered name: the definitions the
	// family recorder will record the landed member standing on.
	UnfoldNames []string `json:"unfold_names,omitempty"`

	// CNFCache is the marshalled *proof.CNFCache of every certificate
	// and conditioning plan the included sections' replay reads — empty
	// (the field absent) when no leaf reached the refuter. Its reader is
	// the author: a non-empty cache means some leaf will cost a recorded
	// key, which a session close alone does not show. It is never
	// installed — the family CNF recorder records a landed member's keys
	// into the family blob.
	CNFCache []byte `json:"cnf_cache,omitempty"`
}

// EmitSectionRequest bundles the parameters for EmitSection.
//
// IncludePrior is the tri-state that controls which other proved
// sections render with the target (as the member's lemmas, so the
// target's cites of them resolve). Whichever it selects, the member
// orders them itself (emit.SectionOrder): each after the sections it
// cites, ties in slice order, the target last. Semantics:
//
//   - nil (default, JSON field omitted or null): the proved sections
//     the target cites, directly or through another section — opened
//     before the target or after it.
//   - empty slice ([]): no other section — the member has only the
//     target section. A cite of a sibling from the target then renders
//     as an unresolved TODO, which is often what the author wants to
//     confirm the target closes without pulling scratch along; a
//     `cite-node`, whose record holds the sibling's proof under its
//     claim, renders that proof inline.
//   - non-empty ([k, l, m]): exactly these sections, each proved and
//     not the target, each reached by the target's cites (a section
//     nothing cites would render as a local nothing reads), none a
//     definition, and the target not one.
//
// A definition section is never a lemma: the default leaves every one
// out, and a theorem's use of it cites the definition's family entry.
//
// Family is the family's registered PATH (registry.Family.Name — e.g.
// "real/real_field"): every segment a Go package identifier, the last
// one the emitted package clause. A member spelling
// (`cardinality.FiniteFunspace`) is refused. Empty means the family
// the session is bound to; a session bound to none must name one. The
// member's texts are written for this family — its instance bindings
// and numeric domain — whatever family the session works.
type EmitSectionRequest struct {
	SessionID    string
	Section      int
	FuncName     string
	IncludePrior []int
	Family       string
}

// EmitSection renders one closed session section — with the proved
// sections IncludePrior selects — as a member of the request's family,
// and collects the CNF certificates its replay would read.
//
// Errors: unknown session, section index out of range, section not
// proved, an IncludePrior entry that is the target or out of range /
// unproved / duplicated, a selected section the target's cites do not
// reach, sections that cite one another round a cycle, no family
// (neither requested nor bound), a family value that is not a family
// path, an emit-side rendering error,
// a CNF collection error (typically a MISS on a refute the strict walk
// re-runs — the session closed a refute whose certificate is not under
// the key replay computes). A collection error comes with the result:
// the member rendered, its CNFCache empty.
func (e *Engine) EmitSection(req *EmitSectionRequest) (*EmitSectionResult, error) {
	if req == nil {
		return nil, fmt.Errorf("emit-section: nil request")
	}
	s, err := e.getSession(req.SessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()

	sectionIdx := req.Section
	if sectionIdx < 0 || sectionIdx >= len(s.sections) {
		return nil, fmt.Errorf("section %d out of range (session has %d sections)", sectionIdx, len(s.sections))
	}
	target := s.sections[sectionIdx]
	if !target.root.Proved() {
		return nil, fmt.Errorf("section %d is not proved — emit-section requires a closed section", sectionIdx)
	}

	family := strings.TrimSpace(req.Family)
	if family == "" && s.family != nil {
		family = s.family.Name
	}
	if family == "" {
		return nil, fmt.Errorf(
			"emit-section: no family — pass the family's registered path (e.g. %q), "+
				"or bind the session to its family at session-create",
			"iterate/real/real_sum")
	}
	if err := validateFamilyPath(family); err != nil {
		return nil, err
	}
	// The member's texts are read by the family it lands in, under that
	// family's instance bindings and numeric domain, whichever family the
	// session proved it under. A family this process has not registered
	// declares neither, as it declares no vocabulary (familyVocabForEmit).
	var implicit map[string]core.Term
	var domain core.HolType
	if dest, ok := registry.FamilyByName(family); ok {
		implicit, domain = dest.ImplicitBindings(), dest.CoerceDomain()
	}

	funcName := req.FuncName
	if funcName == "" {
		funcName = "Build_Draft"
	}

	// The sections the member may take: every other proved one by
	// default, else exactly the caller's, in slice order.
	var candidates []int
	if req.IncludePrior == nil {
		for i, sec := range s.sections {
			if i != sectionIdx && sec.root.Proved() {
				candidates = append(candidates, i)
			}
		}
	} else {
		seen := make(map[int]bool, len(req.IncludePrior))
		for _, i := range req.IncludePrior {
			if i == sectionIdx {
				return nil, fmt.Errorf(
					"include_prior: %d is the target section (Section %d) — "+
						"the target is included automatically, do not list it in include_prior",
					i, sectionIdx)
			}
			if i < 0 || i >= len(s.sections) {
				return nil, fmt.Errorf(
					"include_prior: %d out of range (session has %d sections)",
					i, len(s.sections))
			}
			if seen[i] {
				return nil, fmt.Errorf("include_prior: duplicate section %d", i)
			}
			if !s.sections[i].root.Proved() {
				return nil, fmt.Errorf(
					"include_prior: %d is not proved — every included section "+
						"must be closed",
					i)
			}
			seen[i] = true
			candidates = append(candidates, i)
		}
		sort.Ints(candidates)
	}

	// unreachable collects the entries the rendering cites that the
	// family's package cannot name in Go; any refuses the export.
	unreachable := map[string]*registry.ProofEntry{}
	// render is the member over the given session sections, the target
	// last: the recorded sections and the options their rendering reads.
	render := func(indices []int) ([]*proof.DetailedProofProto, []*sectionState, emit.EmitOptions, error) {
		recorded := make([]*proof.DetailedProofProto, 0, len(indices))
		included := make([]*sectionState, 0, len(indices))
		for _, i := range indices {
			sec := s.sections[i]
			detailed := sec.root.DetailedProofProto()
			if detailed == nil {
				return nil, nil, emit.EmitOptions{}, fmt.Errorf(
					"section %d reports Proved but DetailedProofProto is nil "+
						"(engine invariant break)",
					i)
			}
			recorded = append(recorded, detailed)
			included = append(included, sec)
		}
		opts := emit.EmitOptions{
			Family:   family,
			FuncName: funcName,
			// The entry literal's Key is the statement's own.
			EntryKey:      entryOwnKey(target),
			ExtraDepNames: sessionInductionPrincipleDeps(s, family, recorded),
			// A session's external references are `lemma {key}` cites; the
			// resolver classifies each lazily at render time — exactly the
			// keys emit needs.
			ResolveExternalLeaf: sessionDefineLeafResolver(s, family,
				e.polymorphicSourceLeafResolver(included,
					sessionCardLeafResolver(s, e.resolveExternalLeafForEmit))),
			FamilyDepEntry: e.familyDepEntryForEmit(family, unreachable),
			DefinitionOf:   e.definitionForEmit(s, family, unreachable),
			Structure:      e.structureForEmit(family, unreachable),
			LawStatement:   lawStatementForEmit,
			// The Law door is the family's where its entries state through
			// it; elsewhere a law-shaped statement binds its bundle as one
			// typed fact (emit_signature.go).
			StructureDoorInUse: structureDoorInUse(family),
			FamilyVocab:        familyVocabForEmit(family),
			// A landed entry stating the member's statement — the card the
			// session fills — keeps its authored text as the headline.
			StatementText:  statedText(target),
			StatementParts: statedParts(target),
			// The abbreviations the rendered sections' texts were read
			// under — the chapter's, and the session reads every
			// section's text under the tables of all its sections, so a
			// later section spells an earlier one's names — and what the
			// member declares of them beyond the chapter's
			// (emit.EmitOptions.Abbreviations, FamilyVocab.Abbrev).
			Abbreviations: s.abbreviationTableOf(included).Entries(),
			// The cards the session minted that no entry states: rendered
			// as card entries beside the member where the member cites
			// them (emit.EmitOptions.Cards).
			Cards: cardsForEmit(s),
			// A session-defined constant's definition renders in the
			// author's own spelling (the define RPC's texts).
			DefinitionText: s.definitionText,
			// The chapter's spelling for every rendered text: implicit
			// structure arguments the destination family binds are dropped.
			ImplicitBindings: implicit,
			// And the destination's reading of an unanchored `&`.
			CoerceDomain: domain,
		}
		return recorded, included, opts, nil
	}

	offered := append(append([]int(nil), candidates...), sectionIdx)
	recorded, _, opts, err := render(offered)
	if err != nil {
		return nil, err
	}
	order, err := emit.SectionOrder(recorded, e.env.ProofService.LoadConstMeta, opts, req.IncludePrior == nil)
	if err != nil {
		var refused *emit.SectionOrderError
		if errors.As(err, &refused) {
			return nil, sectionOrderRefusal(refused, offered)
		}
		return nil, fmt.Errorf("emit: %w", err)
	}
	sectionsIncluded := make([]int, len(order))
	for k, i := range order {
		sectionsIncluded[k] = offered[i]
	}
	recorded, _, opts, err = render(sectionsIncluded)
	if err != nil {
		return nil, err
	}
	// Only the member's own rendering is held to its family's reach.
	clear(unreachable)
	member, err := emit.EmitMember(recorded, e.env.ProofService.LoadConstMeta, opts)
	if err != nil {
		return nil, fmt.Errorf("emit: %w", err)
	}
	if err := unreachableCitesRefusal(family, unreachable); err != nil {
		return nil, err
	}
	result := &EmitSectionResult{
		SectionID:        sectionIdx,
		FuncName:         funcName,
		SectionsIncluded: sectionsIncluded,
		Go:               member.Source,
		Capabilities:     member.Capabilities,
		DepNames:         member.DepNames,
		UnfoldNames:      member.UnfoldNames,
	}
	// The rendering reads none of the certificates, so a collection that
	// fails returns the member beside its error: the Go is read while
	// the MISS is diagnosed.
	cnfProto, err := emit.CollectCNFCache(e.env, recorded)
	if err != nil {
		return result, fmt.Errorf("collect CNF cache: %w", err)
	}
	if !cnfProto.IsEmpty() {
		b, mErr := proto.Marshal(cnfProto)
		if mErr != nil {
			return result, fmt.Errorf("marshal CNF cache: %w", mErr)
		}
		result.CNFCache = b
	}
	return result, nil
}

// sectionOrderRefusal spells emit.SectionOrder's refusal in session
// section indices: offered maps the indices SectionOrder read to them.
func sectionOrderRefusal(refused *emit.SectionOrderError, offered []int) error {
	sessionIndices := func(indices []int) []int {
		out := make([]int, len(indices))
		for k, i := range indices {
			out[k] = offered[i]
		}
		return out
	}
	if definitions := refused.Definitions; len(definitions) > 0 {
		if last := len(offered) - 1; definitions[len(definitions)-1] == last {
			return fmt.Errorf("include_prior: section %d is a definition, a member of its own — "+
				"emit it with include_prior omitted or []", offered[last])
		}
		return fmt.Errorf("include_prior: sections %v are definitions — a definition is a member of "+
			"its own, and a theorem that uses one cites its family entry; leave them out",
			sessionIndices(definitions))
	}
	if len(refused.Cycle) > 0 {
		return fmt.Errorf("emit-section: sections %v cite one another round a cycle — "+
			"leave one out with include_prior", sessionIndices(refused.Cycle))
	}
	return fmt.Errorf("include_prior: sections %v are cited by no section the target reaches — "+
		"each would render as a local nothing reads; leave them out", sessionIndices(refused.Uncited))
}

// familyDepEntryForEmit resolves a theorem's registered name, service
// name or key to its Go expression and package import. Datatype theorems
// are fields of their registered handle; ordinary entries are variables.
// An unregistered same-family name is a session-defined sibling and keeps
// its bare name. Other misses remain untyped dependencies in the scaffold.
// An entry the family's package cannot name in Go
// (registry.ProofEntry.UnreachableFrom) resolves to nothing and is
// entered in unreachable under its name: the export refuses the member
// (EmitSection) rather than print a reference that does not compile.
func (e *Engine) familyDepEntryForEmit(family string, unreachable map[string]*registry.ProofEntry) func(name string, key core.PropKey) (emit.FamilyDepRef, bool) {
	dir := familyPackageDir(family)
	return func(name string, key core.PropKey) (emit.FamilyDepRef, bool) {
		entry, ok := registry.ByName(name)
		if !ok {
			entry, ok = registry.ByServesAs(name)
		}
		if !ok && key != "" {
			entry, ok = entryByKey(string(key))
		}
		if !ok || entry.Family() == nil {
			if short := path.Base(family) + "."; family != "" && strings.HasPrefix(name, short) {
				return emit.FamilyDepRef{Expr: strings.TrimPrefix(name, short)}, true
			}
			return emit.FamilyDepRef{}, false
		}
		if entry.UnreachableFrom(dir) != "" {
			unreachable[entry.Name] = entry
			return emit.FamilyDepRef{}, false
		}
		fam := entry.Family()
		if fam.Name == family {
			// Same family: the expression needs no package qualifier.
			return emit.FamilyDepRef{
				Expr:      entry.GoRef(),
				BareEntry: entry.GoRef() != entry.BareName(),
			}, true
		}
		// The registry supplies the Go expression: a member variable or
		// a field of its datatype handle, qualified by the package.
		return emit.FamilyDepRef{
			Expr:       path.Base(fam.Name) + "." + entry.GoRef(),
			ImportPath: "github.com/euc-ai/xugo/library/proofs/" + fam.PackageDir(),
			BareEntry:  entry.GoRef() != entry.BareName(),
		}, true
	}
}

// definitionForEmit resolves a constant a recorded step opens to its
// definition as the member's package names it
// (emit.EmitOptions.DefinitionOf): the landed entry whose door minted
// the constant, or, for a constant the session defined, the entry its
// define will land under (sessionDefineEntryName), a sibling of the
// member. A constant neither defines has no definition to name.
func (e *Engine) definitionForEmit(s *Session, family string, unreachable map[string]*registry.ProofEntry) func(string) (emit.FamilyDepRef, string, bool) {
	resolve := e.familyDepEntryForEmit(family, unreachable)
	return func(constant string) (emit.FamilyDepRef, string, bool) {
		name := ""
		if definer := registry.Definer(constant); definer != nil {
			name = definer.Name
		} else if _, defined := s.defineTexts[constant]; defined {
			name = sessionDefineEntryName(family, constant, "")
		}
		if name == "" {
			return emit.FamilyDepRef{}, "", false
		}
		ref, ok := resolve(name, "")
		return ref, name, ok
	}
}

// familyPackageDir is the package directory under library/proofs of the
// family a member is emitted into, and "" for a family no package
// registers yet: its name does not say where its package will lie
// (registry.NewFamilyIn), so registry.ProofEntry.UnreachableFrom reads
// it as not yet placed.
func familyPackageDir(family string) string {
	if fam, ok := registry.FamilyByName(family); ok {
		return fam.PackageDir()
	}
	return ""
}

// unreachableCitesRefusal is the export's refusal of a member citing
// entries its family's package cannot name in Go (familyDepEntryForEmit),
// one line per entry in name order; nil when it cites none.
func unreachableCitesRefusal(family string, unreachable map[string]*registry.ProofEntry) error {
	if len(unreachable) == 0 {
		return nil
	}
	dir := familyPackageDir(family)
	lines := make([]string, 0, len(unreachable))
	for _, name := range slices.Sorted(maps.Keys(unreachable)) {
		lines = append(lines, unreachableCite(unreachable[name], dir, family))
	}
	return fmt.Errorf("emit-section: the member's Go would not compile:\n  %s", strings.Join(lines, "\n  "))
}

// structureForEmit is the structure resolver of the Instance door's
// rendering (emit.EmitOptions.Structure): a predicate a chapter made a
// structure through DefineStructure resolves to that structure's var,
// which is its definition entry's var, spelled from the member's
// family as a dep is (familyDepEntryForEmit). A structure a chapter
// named over a plain definition (StructureOf) has no entry of its own
// and does not resolve.
func (e *Engine) structureForEmit(family string, unreachable map[string]*registry.ProofEntry) func(predicate string) (emit.FamilyDepRef, bool) {
	depEntry := e.familyDepEntryForEmit(family, unreachable)
	return func(predicate string) (emit.FamilyDepRef, bool) {
		structure, ok := registry.StructureByPredicate(predicate)
		if !ok || structure.ProofEntry == nil {
			return emit.FamilyDepRef{}, false
		}
		return depEntry(structure.ProofEntry.Name, core.PropKey(structure.ProofEntry.Key))
	}
}

// lawStatementForEmit is a structure law's statement at body
// (registry.Structure.Statement) for the emitter's Law door; false
// where the predicate names no structure with a definition entry.
func lawStatementForEmit(predicate, body string) (string, bool) {
	structure, ok := registry.StructureByPredicate(predicate)
	if !ok || structure.ProofEntry == nil {
		return "", false
	}
	return lawStatementText(structure, body)
}

// lawStatementText is the text of the door's statement at body; false
// where the door refuses the body (one not in the standard form).
func lawStatementText(structure *registry.Structure, body string) (text string, ok bool) {
	defer func() {
		if recover() != nil {
			text, ok = "", false
		}
	}()
	text, err := structure.Statement(body).Text()
	return text, err == nil
}

// structureDoorInUse reports, for the emitter's Law door
// (emit.EmitOptions.StructureDoorInUse), whether the family states a
// member through the structure's door — a law `S.Law(body, …)` or an
// axiom: an entry whose constructor declared the structure's
// definition its dep (registry.BuildSpec.Deps, what Law sets) and
// whose headline opens as the door's statement does (registry.Structure.
// Statement at ⊤, dsl.Statement.AfterPrefix — what tells it from an
// instance). A family.Theorem whose headline spells the same text — a
// record structure's components are what a chapter writes by hand,
// `∀R:ring_ops(A). ∀M:module_ops(A, B). module_on(R, M) ⇒ …` — declares
// no such dep. A family stating none so binds a law-shaped statement's
// bundle as one typed fact instead.
func structureDoorInUse(family string) func(predicate string) bool {
	return func(predicate string) bool {
		structure, ok := registry.StructureByPredicate(predicate)
		if !ok || structure.ProofEntry == nil {
			return false
		}
		fam, ok := registry.FamilyByName(family)
		if !ok {
			return false
		}
		opening, ok := lawStatementText(structure, "⊤")
		if !ok {
			return false
		}
		prefix, ok := dsl.SplitStatement(opening)
		if !ok {
			return false
		}
		for _, entry := range fam.Entries() {
			if !slices.ContainsFunc(entry.Build.Deps, func(dep registry.EntryLike) bool {
				return dep != nil && dep.Entry() == structure.ProofEntry
			}) {
				continue
			}
			if headline, ok := dsl.SplitStatement(entry.Build.Headline); ok {
				if _, opens := headline.AfterPrefix(prefix); opens {
					return true
				}
			}
		}
		return false
	}
}

// statedText is the authored text of the landed entry stating a
// section's statement — the card a session fills, whose landing keeps
// the text as written — and "" where no entry states it.
func statedText(sec *sectionState) string {
	if stated, ok := registry.ByKey(string(entryOwnKey(sec))); ok && stated != nil {
		return stated.StatementText()
	}
	return ""
}

// statedParts is the landed entry's statement in parts, where its
// author wrote it so (dsl.Statement) — the literal the member keeps;
// nil otherwise.
func statedParts(sec *sectionState) *dsl.Statement {
	if stated, ok := registry.ByKey(string(entryOwnKey(sec))); ok && stated != nil {
		return stated.StatementParts()
	}
	return nil
}

// familyVocabForEmit reads the target family's declared vocabulary
// (registry.VocabSpec rows) into the name sets emit prunes
// registration-only declarations against (emit.EmitOptions.FamilyVocab):
// every constant a term / spelled / defined / poly / declare row names
// is installed into a member's ParseScope by the family before the
// headline parses, and every free row's variable is registered there,
// so a body line that only re-registers such a name is redundant. A
// family with no spec (or none registered under that name — a session
// emitting for a chapter not yet in the tree) prunes nothing.
func familyVocabForEmit(family string) *emit.FamilyVocab {
	// Every member scope resolves a chapter-minted constant through the
	// process's inventory before its texts parse, so a name the
	// inventory serves — the family's own definitions, another
	// chapter's (`empty_set`) — needs no registration line whether or not
	// the family carries a VocabSpec; the rows below add the names a
	// spec registers beyond those.
	mgr := registry.GetConstMetaManager()
	vocab := &emit.FamilyVocab{Consts: map[string]bool{}, Vars: map[string]bool{}, Abbrev: map[string]bool{},
		Resolves: func(name string) bool {
			_, ok := mgr.LoadConstMeta(core.TermName(name))
			return ok
		}}
	fam, ok := registry.FamilyByName(family)
	if !ok {
		return vocab
	}
	for _, a := range fam.Abbrev() {
		vocab.Abbrev[a.Name] = true
	}
	if fam.VocabSpec() == nil {
		return vocab
	}
	for _, row := range fam.VocabSpec().RowInfos() {
		switch row.Kind {
		case "term", "spelled", "defined", "poly":
			vocab.Consts[row.Name] = true
		case "declare":
			for _, n := range row.Names {
				vocab.Consts[n] = true
			}
		case "free":
			vocab.Vars[row.Name] = true
		}
	}
	return vocab
}

// resolveExternalLeafForEmit classifies a cited statement no included
// section proves (the EmitOptions.ResolveExternalLeaf hook):
//
//  1. Const-def index hit → LeafConstDef / LeafTypeDefAxiom (the leaf
//     IS a const's def equation or a type definition's axiom).
//  2. A registry entry's own statement → LeafLibraryThm under the
//     entry's registered name (a cite reads the entry's theorem by that
//     name, so the by-name lookup is exactly the replay contract).
//  3. Anything else → a miss; emit falls through to its
//     const-def-by-name tier and finally the TODO placeholder.
func (e *Engine) resolveExternalLeafForEmit(key core.PropKey) (emit.ExternalLeaf, bool) {
	if ref, ok := e.constDefIndex()[key]; ok {
		if leaf, ok := emit.ExternalLeafFromConstDefRef(key, ref); ok {
			return leaf, true
		}
	}
	return registryLeafForEmit(key)
}

// constDefIndex is the reverse index from a constant's definitional
// theorem (its normalized key) to the constant, over every constant
// the process knows — the engine's built-ins and the chapters' mints
// (registry.GetConstMetaManager). Built once per engine.
func (e *Engine) constDefIndex() registry.ConstDefIndex {
	e.constDefIdxOnce.Do(func() {
		e.constDefIdx = registry.BuildConstDefIndex(registry.GetConstMetaManager().Range)
	})
	return e.constDefIdx
}

// registryEntryLeaf is the leaf a registry entry renders as: a library
// theorem under its REGISTERED name — the replay contract, since the
// harness serves a member's deps by their registered names —
// carrying the statement that name serves, for the type-instance and
// Simp-marker renderings that must know what ctx.Dep(name) delivers.
func registryEntryLeaf(key core.PropKey, entry *registry.ProofEntry) emit.ExternalLeaf {
	return emit.ExternalLeaf{
		Key:     key,
		Kind:    emit.LeafLibraryThm,
		ThmName: entry.Name,
		Stated:  entry.Statement().Prop,
	}
}

// polymorphicSourceLeafResolver wraps an external-leaf resolver with
// the SESSION-INSTANCE tier: a cite whose recorded payload is the
// type-adapted session form of a polymorphic registry entry — a
// `simp_with` rule with a type_specialize, an auto-match close through
// the sourceKey channel — has no entry at the payload's own key. The
// entry it came from is stamped on the in-memory ministep at apply time
// (GoalStackNode.PolymorphicSourceKeys, parallel to the proto's steps;
// the proto itself does not carry it), so the leaf resolves through
// THAT key and keeps the payload's key as its identity — the emitter's
// lookup key. Two instances of one entry resolve to one dep. A by
// premise's entry is stamped on its By step the same way
// (GoalStackNode.ByPremiseSourceKeys). Without this tier every such cite would render as
// a TODO placeholder.
func (e *Engine) polymorphicSourceLeafResolver(
	sections []*sectionState,
	fallback func(core.PropKey) (emit.ExternalLeaf, bool),
) func(core.PropKey) (emit.ExternalLeaf, bool) {
	// source is a stamped source: its key, and — when the step carries
	// it — the polymorphic statement the session served (a TypeInst
	// close's source), which stands in for ExternalLeaf.Stated when the
	// resolved leaf does not say what it serves.
	type source struct {
		key    core.PropKey
		stated core.Prop
	}
	sources := map[core.PropKey]source{}
	for _, sec := range sections {
		detailed := sec.root.DetailedProofProto()
		keys := sec.root.PolymorphicSourceKeys()
		if detailed == nil || len(keys) == 0 {
			continue
		}
		r := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
		for i, step := range detailed.Steps {
			if i >= len(keys) || keys[i] == "" {
				continue
			}
			var payload, closed, stated core.Prop
			switch st := step.Step.(type) {
			case *proof.StepProto_Lemma:
				payload, _ = r.Prop(st.Lemma)
			case *proof.StepProto_LeanRw:
				payload, _ = r.Prop(st.LeanRw)
			case *proof.StepProto_LemmaPreserve:
				payload, _ = r.Prop(st.LemmaPreserve)
			case *proof.StepProto_TypeInst:
				payload, _ = r.Prop(st.TypeInst)
				closed, _ = r.Prop(step.Goal)
				stated = payload
			case *proof.StepProto_KnownThm:
				src := st.KnownThm.GetEquivalentThm()
				if src == nil {
					src = st.KnownThm.GetStrongerGoal()
				}
				payload, _ = r.Prop(src)
				closed, _ = r.Prop(step.Goal)
			}
			// A close's GOAL is the obligation the emitter looks up too:
			// a fused Simp cites the rule child's statement, which is
			// the TypeInst/KnownThm step's goal, not its payload.
			for _, p := range []core.Prop{payload, closed} {
				if p == nil {
					continue
				}
				sources[p.AlphaKey()] = source{keys[i], stated}
				if normalized, _ := prop.Normalize(p); normalized != nil {
					sources[normalized.AlphaKey()] = source{keys[i], stated}
				}
			}
		}
	}
	// A by premise is cited at its recorded install, and an explicit type
	// instance of a key premise (a term_specialize prefix pinning every
	// type variable) has no entry at the install's own key. The session
	// stamped the entry each key premise was loaded from on the
	// in-memory step (GoalStackNode.ByPremiseSourceKeys, parallel to the
	// proto's steps and to each By's premises): the install resolves
	// through it, at both keys the emitter looks it up by. An install
	// that resolves on its own, here or through the fallback, is cited
	// as before.
	for _, sec := range sections {
		detailed := sec.root.DetailedProofProto()
		premiseKeys := sec.root.ByPremiseSourceKeys()
		if detailed == nil {
			continue
		}
		r := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
		for i, step := range detailed.Steps {
			by, ok := step.Step.(*proof.StepProto_By)
			if !ok {
				continue
			}
			for j, premise := range by.By.GetPremises() {
				key := premiseKeys[i][j]
				if key == "" {
					continue
				}
				install, _ := r.Prop(premise.GetInstall())
				normalized, _ := prop.Normalize(install)
				keys := []core.PropKey{install.AlphaKey(), normalized.AlphaKey()}
				resolved := false
				for _, k := range keys {
					_, mapped := sources[k]
					_, found := fallback(k)
					resolved = resolved || mapped || found
				}
				if resolved {
					continue
				}
				for _, k := range keys {
					sources[k] = source{key: key}
				}
			}
		}
	}
	if len(sources) == 0 {
		return fallback
	}
	return func(key core.PropKey) (emit.ExternalLeaf, bool) {
		if src, ok := sources[key]; ok && src.key != key {
			if leaf, ok := fallback(src.key); ok {
				leaf.Key = key
				if leaf.Stated == nil {
					leaf.Stated = src.stated
				}
				return leaf, true
			}
		}
		return fallback(key)
	}
}

// sessionDefineLeafResolver wraps the engine's external-leaf resolver
// with a SESSION-DEFINE tier: a leaf whose key is a `define`-installed
// characterizing theorem (the session's simp set tracks them — one
// entry per define, statement + section promise) resolves as a
// LibraryThm cite of the definition's FUTURE entry, named by
// convention `<family-base>.<ExportedConst>` (zz_fam + zz_sumto →
// "zz_fam.ZzSumto"). The emitted member then declares that DepName and
// cites it like any named theorem — landable Go whose replay preloads
// the define entry once it lands, the ordinary forward-dep story; the
// name is changed at landing exactly as with FuncName. Without this
// tier a simp fire against a define-installed equation rendered as an
// unresolvable external-leaf TODO.
//
// A type definition's two theorems name their future entries the same
// way (`<fam>.<ExportedType>Retraction` / `…Membership`), and so does
// the inhabitation the author proved before the define
// (`<fam>.<ExportedType>Inhabited`) — unless a landed entry already
// states it, which the registry tier answers first: the inhabitation
// is the author's own theorem and may have landed under its own name.
// A completed WF or spec definition's characterizing theorem, which
// the simp set does not carry, names its entry `<fam>.<ExportedConst>`
// (a spec group's first constant) — the cite a later member makes of
// it (cite-node records a known-theorem leaf for a definition).
func sessionDefineLeafResolver(
	s *Session, family string,
	fallback func(core.PropKey) (emit.ExternalLeaf, bool),
) func(core.PropKey) (emit.ExternalLeaf, bool) {
	type defRule struct {
		keys   []core.PropKey
		name   string
		stated core.Prop
	}
	// Caller contract: EmitSection holds s.mu while building the emit
	// options, so the snapshot below reads under that lock — taking it
	// here would self-deadlock.
	var rules []defRule
	claimed := map[core.PropKey]bool{}
	// Datatype defines first: their INJ/DISTINCT rules also sit in
	// simpRules, but their entry names follow the datatype convention
	// (<Type>Inj / <Type>Distinct), not the clause-head one.
	for _, ddef := range s.dataDefines {
		for _, kindRule := range []struct {
			stmt   core.Prop
			suffix string
		}{{ddef.inj, "Inj"}, {ddef.distinct, "Distinct"}} {
			if kindRule.stmt == nil {
				continue
			}
			keys := []core.PropKey{kindRule.stmt.AlphaKey()}
			if normalized, _ := prop.Normalize(kindRule.stmt); normalized != nil {
				keys = append(keys, normalized.AlphaKey())
			}
			for _, k := range keys {
				claimed[k] = true
			}
			rules = append(rules, defRule{
				keys: keys, name: sessionDefineEntryName(family, ddef.typeName, kindRule.suffix)})
		}
	}
	statementKeys := func(stmt core.Prop) []core.PropKey {
		keys := []core.PropKey{stmt.AlphaKey()}
		if normalized, _ := prop.Normalize(stmt); normalized != nil {
			keys = append(keys, normalized.AlphaKey())
		}
		return keys
	}
	var landedFirst []defRule
	for _, tdef := range s.typedefDefines {
		for _, kindRule := range []struct {
			stmt   core.Prop
			suffix string
		}{{tdef.retraction, "Retraction"}, {tdef.membership, "Membership"}} {
			keys := statementKeys(kindRule.stmt)
			for _, k := range keys {
				claimed[k] = true
			}
			rules = append(rules, defRule{
				keys: keys, name: sessionDefineEntryName(family, tdef.typeName, kindRule.suffix)})
		}
		if tdef.existence != nil {
			landedFirst = append(landedFirst, defRule{
				keys: statementKeys(tdef.existence),
				name: sessionDefineEntryName(family, tdef.typeName, "Inhabited")})
		}
	}
	for _, qdef := range s.quotientDefines {
		for _, k := range proof.QuotientTheoremKinds {
			keys := statementKeys(qdef.stmts[k])
			for _, key := range keys {
				claimed[key] = true
			}
			rules = append(rules, defRule{
				keys: keys, name: sessionDefineEntryName(family, qdef.typeName, k.String())})
		}
		landedFirst = append(landedFirst, defRule{
			keys: statementKeys(qdef.equivalence),
			name: sessionDefineEntryName(family, quotientRelationName(qdef), "Equivalence")})
	}
	for _, idef := range s.inductiveDefines {
		for _, kindRule := range []struct {
			stmt   core.Prop
			suffix string
		}{{idef.rules, "Rules"}, {idef.induct, "Induct"}, {idef.cases, "Cases"}} {
			keys := statementKeys(kindRule.stmt)
			for _, k := range keys {
				claimed[k] = true
			}
			rules = append(rules, defRule{
				keys: keys, name: sessionDefineEntryName(family, idef.constName, kindRule.suffix)})
		}
	}
	for _, odef := range s.obligationDefines {
		keys := statementKeys(odef.characterizing)
		for _, k := range keys {
			claimed[k] = true
		}
		rules = append(rules, defRule{keys: keys, name: sessionDefineEntryName(family, odef.constName, "")})
	}
	for _, r := range s.simpRules {
		keys := []core.PropKey{r.rule.AlphaKey()}
		if normalized, _ := prop.Normalize(r.rule); normalized != nil {
			keys = append(keys, normalized.AlphaKey())
		}
		if claimed[keys[0]] {
			continue
		}
		name := defineEntryDepName(family, r.rule)
		var stated core.Prop
		if r.entry != nil {
			// A rule the family binding imported cites the registered
			// definition it was derived from (familyDepEntryForEmit
			// renders the typed dep). A WF reading cites the definition
			// too — as a session define's reading names its future
			// entry — and its derivation from the equation is the
			// author's.
			name = r.entry.Name
			stated = r.entry.Statement().Prop
		}
		rules = append(rules, defRule{keys: keys, name: name, stated: stated})
	}
	if len(rules) == 0 && len(landedFirst) == 0 {
		return fallback
	}
	return func(key core.PropKey) (emit.ExternalLeaf, bool) {
		for _, r := range landedFirst {
			for _, k := range r.keys {
				if k != key {
					continue
				}
				if leaf, ok := fallback(key); ok {
					return leaf, true
				}
				return emit.ExternalLeaf{Key: key, Kind: emit.LeafLibraryThm, ThmName: r.name}, true
			}
		}
		for _, r := range rules {
			if r.name == "" {
				continue
			}
			for _, k := range r.keys {
				if k == key {
					return emit.ExternalLeaf{
						Key:     key,
						Kind:    emit.LeafLibraryThm,
						ThmName: r.name,
						Stated:  r.stated,
					}, true
				}
			}
		}
		return fallback(key)
	}
}

// quotientRelationName is the base name the equivalence of a session
// quotient's relation is named by: the relation's constant when the
// relation is one (nadd_eq → NaddEqEquivalence), else the type's.
func quotientRelationName(qdef sessionQuotientDefine) string {
	head, _ := ext.MatchesApply(qdef.relation)
	if head != nil {
		if c, ok := head.AsConst(); ok {
			return string(c.Name())
		}
	}
	if c, ok := qdef.relation.AsConst(); ok {
		return string(c.Name())
	}
	return qdef.typeName
}

// sessionDefineEntryName derives the conventional registered name of a
// session define's future entry: family short name + the exported base
// name + a kind suffix (zz_fam + zz_btree_b + "Inj" →
// "zz_fam.ZzBtreeBInj"; zz_fam + zz_nat_sqrt + "" → "zz_fam.ZzNatSqrt")
// — the convention the chapter doors register under, so the emitted
// member's dep resolves once the entry lands (the define forward-dep
// story).
func sessionDefineEntryName(family, typeName, suffix string) string {
	name := exportedIdent(typeName)
	if name == "" {
		return ""
	}
	name += suffix
	if family != "" {
		return path.Base(family) + "." + name
	}
	return name
}

// sessionInductionPrincipleDeps scans the included sections' recorded
// ministeps for induction over a session-defined datatype and returns
// the conventional Induct-entry dep names the emitted member reads:
// the induction ministep re-resolves its principle BY NAME at replay
// (Script.Induct reads <T>_INDUCT, which the Induct entry serves), so
// the member stands on that entry though no leaf cite carries it. The
// emit reports the names and marks one no landed entry proves.
func sessionInductionPrincipleDeps(s *Session, family string, sections []*proof.DetailedProofProto) []string {
	if len(s.dataDefines) == 0 && len(s.quotientDefines) == 0 {
		return nil
	}
	inductTypes := make([]string, 0, len(s.dataDefines)+len(s.quotientDefines))
	for _, dd := range s.dataDefines {
		inductTypes = append(inductTypes, dd.typeName)
	}
	for _, qd := range s.quotientDefines {
		inductTypes = append(inductTypes, qd.typeName)
	}
	loadConstMeta := func(name core.TermName) (core.ConstTermMeta, bool) { return core.ConstTermMeta{}, false }
	if s.env.ProofService != nil && s.env.ProofService.LoadConstMeta != nil {
		loadConstMeta = s.env.ProofService.LoadConstMeta
	}
	seen := map[string]bool{}
	var out []string
	for _, detailed := range sections {
		if detailed == nil {
			continue
		}
		reader := ext.NewPoolReader(detailed.Pool, loadConstMeta)
		for _, step := range detailed.Steps {
			ind, ok := step.Step.(*proof.StepProto_Induction)
			if !ok {
				continue
			}
			v := reader.Term(ind.Induction)
			if v == nil {
				continue
			}
			ct, isComposite := v.Type().(core.CompositeType)
			if !isComposite {
				continue
			}
			for _, typeName := range inductTypes {
				if string(ct.Meta().Name()) != typeName {
					continue
				}
				name := sessionDefineEntryName(family, typeName, "Induct")
				if name != "" && !seen[name] {
					seen[name] = true
					out = append(out, name)
				}
			}
		}
	}
	return out
}

// defineEntryDepName derives the conventional registered name of a
// define's entry from its characterizing statement: the family
// short name + the minted constant's exported spelling. The constant is
// read off the statement's first clause head (the define shapes
// guarantee it).
func defineEntryDepName(family string, rule core.Prop) string {
	clauses := ext.DecomposesAND(rule.Conclusion())
	if len(clauses) == 0 {
		return ""
	}
	_, matrix := ext.DecomposesFORALL(clauses[0])
	l, _, ok := core.MatchesEQ(matrix)
	if !ok {
		return ""
	}
	head, _ := ext.MatchesApply(l)
	c, ok := head.AsConst()
	if !ok {
		return ""
	}
	name := exportedIdent(string(c.Name()))
	if name == "" {
		return ""
	}
	if family != "" {
		return path.Base(family) + "." + name
	}
	return name
}

// exportedIdent converts a constant name to an exported Go identifier
// (zz_sumto_a → ZzSumtoA). Non-identifier runes separate words.
func exportedIdent(name string) string {
	var b strings.Builder
	up := true
	for _, r := range name {
		switch {
		case r == '_' || r == '-' || r == ' ':
			up = true
		case up:
			b.WriteRune(unicode.ToUpper(r))
			up = false
		default:
			b.WriteRune(r)
		}
	}
	return b.String()
}

// registryLeafForEmit is resolveExternalLeafForEmit's registry tier: a
// key that is a registry entry's own key — a member stated by a chapter
// (see registry_lemmas.go). Rendering it as LeafLibraryThm under the
// REGISTERED name is exactly the replay contract: the harness preloads
// the declared entry under that name, so `ctx.Dep(X)` + the typed
// Deps entry round-trips.
//
// The key is also read as a registry NAME: the session's `by` and
// `simp_with` stamp a key-loaded entry's claim children with the
// spelling the agent cited — so the polymorphic-source tier hands a
// name here for every member cited at a type instance or through
// term_specialize.
func registryLeafForEmit(key core.PropKey) (emit.ExternalLeaf, bool) {
	entry, ok := registryEntry(string(key))
	if !ok {
		return emit.ExternalLeaf{}, false
	}
	return registryEntryLeaf(key, entry), true
}

// entryOwnKey is the Key a family entry literal spells: the statement's
// own normalized key, exactly what the harness recomputes from the
// headline (registry.Statement.Key).
func entryOwnKey(sec *sectionState) core.PropKey {
	return registry.KeyOf(sec.root.Goal)
}

// validateFamilyPath refuses a `family` value that is not a family
// PATH — a member spelling (`cardinality.FiniteFunspace`), a registered
// name, anything whose last segment is not a Go package identifier —
// before it becomes a package clause that does not compile and an
// import of the member's own family.
func validateFamilyPath(family string) error {
	for _, seg := range strings.Split(family, "/") {
		if !isPackageIdent(seg) {
			return fmt.Errorf(
				"family %q: pass the family's registered PATH (registry.Family.Name, e.g. %q) — "+
					"its last segment is the emitted package clause, and every segment must be a Go "+
					"package identifier; the member is named by func_name",
				family, "iterate/real/real_sum")
		}
	}
	return nil
}

// isPackageIdent reports whether s is a lower-case Go package identifier.
func isPackageIdent(s string) bool {
	if s == "" {
		return false
	}
	for i, r := range s {
		switch {
		case r == '_', unicode.IsLower(r):
		case unicode.IsDigit(r) && i > 0:
		default:
			return false
		}
	}
	return true
}

// cardsForEmit lists the session's minted cards no entry states — the
// card entries emit renders beside the member where the member, or a
// card it renders, names them: the bare name the entry var is declared
// as, the registered name the cite spells, the statement's own key,
// the statement in its paste-ready spelling (the display print when
// the print does not round-trip), the note, and the deps by registered
// name.
func cardsForEmit(s *Session) []emit.EmitCard {
	var out []emit.EmitCard
	for _, c := range s.cards {
		if stated, ok := registry.ByKey(string(c.key)); ok && stated != nil {
			continue
		}
		v := c.view(0, s.Spelling())
		stmt := v.StatementTyped
		if stmt == "" {
			stmt = strings.TrimPrefix(v.Statement, "⊢ ")
		}
		out = append(out, emit.EmitCard{Name: c.name, Entry: c.entry, Key: c.key, Statement: stmt, Note: c.note, Deps: slices.Clone(c.deps)})
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Name < out[j].Name })
	return out
}

// sessionCardLeafResolver is the SESSION-CARD tier of the external-leaf
// resolver: a cite whose recorded statement is a card this session
// minted (defer.go) renders as a library theorem under the card's
// registered name — the name the card entry lands as beside the
// member — carrying the card's statement. Looked up by the leaf's key
// in both its stated and its normalized form, as a registry entry is.
func sessionCardLeafResolver(
	s *Session,
	fallback func(core.PropKey) (emit.ExternalLeaf, bool),
) func(core.PropKey) (emit.ExternalLeaf, bool) {
	byKey := map[core.PropKey]*sessionCard{}
	for _, c := range s.cards {
		byKey[c.key] = c
		byKey[core.PropKey(c.entry)] = c
		byKey[c.statement.AlphaKey()] = c
	}
	return func(key core.PropKey) (emit.ExternalLeaf, bool) {
		if leaf, ok := fallback(key); ok {
			return leaf, true
		}
		if c, ok := byKey[key]; ok {
			return emit.ExternalLeaf{Key: key, Kind: emit.LeafLibraryThm, ThmName: c.entry, Stated: c.statement}, true
		}
		return emit.ExternalLeaf{}, false
	}
}
