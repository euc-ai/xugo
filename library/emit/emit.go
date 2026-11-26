// Package emit renders closed session sections as a family member: the
// Go a chapter file carries for one theorem (family.Theorem /
// family.Sections, or family.Instance for a structure's instance) or
// one definition (the family door its `define` step records).
//
// The input is the session's recorded ministep trees
// (DetailedProofProto); the output replays those same ministeps when
// the family's replay harness runs the member, so every rendering
// choice here is a faithfulness choice first and a readability choice
// second. Term-level rendering (HOL connectives, multi-binder ∀/∃,
// multi-arg application, special-const aliases, Type printing) lives
// in ext/render.go's GoTermPrinter; this file owns the member
// scaffold, the symbol table, reference resolution (earlier sections;
// classified external statements, external_leaf.go) and the step
// renderers. The `by` composite renders in emit_by.go.
package emit

import (
	"errors"
	"fmt"
	"go/format"
	"go/parser"
	"go/token"
	"maps"
	"os"
	"path"
	"regexp"
	"slices"
	"sort"
	"strings"
	"unicode"

	"golang.org/x/text/unicode/norm"
	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/aliasgen"
	"github.com/euc-ai/xugo/library/registry/typedgen"
	"github.com/euc-ai/xugo/library/xugofmt"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
)

// EmitOptions controls the rendering of one family member.
type EmitOptions struct {
	// Family is the registered family name of the chapter the member
	// lands in (registry.Family.Name — e.g. "real/real_field"). Required:
	// every rendered file is a family member, and the package clause is
	// the family path's last segment.
	Family string
	// FuncName names the member — "Build_<Name>" or "<Name>". Required.
	FuncName string
	// EntryKey is the entry literal's Key: the statement's own normalized
	// key, the one the replay harness recomputes from the headline.
	// Empty renders no Key field.
	EntryKey core.PropKey
	// ImplicitBindings are the family's instance bindings for implicit
	// structure arguments (registry.Family.ImplicitBindings): under
	// them a rendered statement or claim text drops the components the
	// chapter's scope reads back (ext/dsl/implicit.go), so the emitted
	// text is the chapter's own spelling. nil renders every argument.
	ImplicitBindings map[string]core.Term
	// CoerceDomain is the family's declared numeric domain
	// (registry.Family.CoerceDomain), nil when it declares none. A
	// rendered text is validated under it and under the guard on an
	// unanchored `&`, as the chapter's doors will read it: a text whose
	// `&` nothing anchors, in a chapter declaring no domain, does not
	// take the text form.
	CoerceDomain core.HolType
	// ExtraDepNames are dep names the caller knows the member reads
	// beyond what leaf rendering discovers — the session emit's
	// induction-principle deps: an `induction` ministep over a
	// session-defined datatype re-resolves its principle by NAME at
	// replay (Script.InductStep), so the member reads the datatype's
	// Induct entry though no leaf cites it. Reported in the result's
	// DepNames, and rendered as a TODO when no landed entry proves the
	// name; the landing's recording observes the read.
	ExtraDepNames []string
	// ResolveExternalLeaf classifies the key of a cited statement that
	// no section of this member proves: a registry entry (rendered as
	// the entry var, or `ctx.Dep(<var>.Name)` in a cert-typed slot,
	// with the statement it serves in ExternalLeaf.Stated), a const's
	// definition, a type definition's axiom, the axiom of infinity. The
	// engine wires it to the const-def index and the registry
	// (engine.resolveExternalLeafForEmit);
	// resolution is tried at the payload's raw key and then its
	// normalized key. A miss renders a TODO placeholder that does not
	// compile — loud, never a wrong reference.
	ResolveExternalLeaf func(key core.PropKey) (ExternalLeaf, bool)
	// FamilyDepEntry resolves a rendered dep NAME (plus the leaf key it
	// was recorded at) to a LANDED entry var — the import the member's
	// file needs, and a definition door's typed Deps list. A miss
	// renders as a TODO: the name has no entry yet, and a dep is an
	// entry. Emit stays registry-agnostic: the engine
	// owns the lookup.
	FamilyDepEntry func(name string, key core.PropKey) (FamilyDepRef, bool)
	// DefinitionOf resolves a constant a recorded step opens to its
	// definition: the entry var an Unfold or an Unfolded names, and the
	// registered name of that entry — a landed definition's, or the one
	// a session define's entry will land under. A miss renders the
	// constant's quoted name, which neither verb takes: the definition
	// is landed first.
	DefinitionOf func(constant string) (ref FamilyDepRef, entry string, ok bool)
	// Cards are the cards the member cites that no entry states yet —
	// the lemmas a session's `defer` minted (engine/defer.go). Each the
	// member cites, or a rendered card's Deps name, is rendered as its
	// own family.Add entry built by family.Card, before the member, so
	// the landed file carries the member and the cards it stands on,
	// and the member's proof cites them.
	Cards []EmitCard
	// DefinitionText, when non-nil, answers the AUTHOR'S spelling of a
	// session-defined constant — the `define` RPC's type, equations,
	// measure and spec texts, kept on the session record — so the
	// family.Define / family.DefineSpec literal carries the text the
	// author wrote, not the printer's. Each text is re-parsed before
	// use; one that no longer reads falls back to the printed form.
	DefinitionText func(constName core.TermName) (DefinitionText, bool)
	// Structure resolves a STRUCTURE predicate's name (`equivalence`,
	// `comm_ring`) to the var of the structure its chapter defined
	// (registry.Family.DefineStructure) — the value the Instance door
	// takes — spelled from the member's own package as FamilyDepEntry
	// spells an entry. A member whose statement applies such a
	// predicate, and whose proof unfolds it and closes one branch per
	// conjunct, renders through family.Instance (readInstanceDoor). A miss
	// — the name is no structure's predicate, or the structure is one a
	// chapter NAMED over a plain definition (StructureOf), whose var no
	// entry carries — leaves the member a family.Theorem. nil resolves
	// nothing.
	Structure func(predicate string) (FamilyDepRef, bool)
	// LawStatement is the statement of a law of the structure whose
	// predicate is named — `∀<components>. <predicate>(<components>) ⇒
	// <body>`, registry.Structure.Statement — for the Law door
	// (readLawDoor); false where Structure resolves no structure. nil
	// renders no Law door.
	LawStatement func(predicate, body string) (string, bool)
	// StructureDoorInUse reports whether the family states a member
	// through the named structure's door — a law, an axiom. The Law door
	// renders a law-shaped section, and a law-shaped card renders at
	// `S.Statement`, only there; elsewhere the statement's bundle binds
	// as one typed fact of a family.Theorem closure, the form a chapter
	// stating its bundles in the text lands (emit_signature.go). nil
	// leaves the door open.
	StructureDoorInUse func(predicate string) bool
	// FamilyVocab is the chapter's declared statement vocabulary
	// (registry.VocabSpec rows): the constant NAMES the family installs
	// into every member's ParseScope before the headline parses, and
	// the free-variable names it registers. A declaration the body would
	// carry ONLY to register such a name is not rendered — the family
	// already made it. A name the body references as a Go expression
	// keeps its binding at the instance the step needs. nil prunes
	// nothing.
	FamilyVocab *FamilyVocab
	// StatementText is the member statement's authored text where a
	// landed entry states it — a card the session fills, whose landing
	// keeps the card's text as written (`∀S:(num → set(I))` where the
	// printer spells the arrow). It is the headline where it reads back
	// as the statement; "" prints the statement.
	StatementText string
	// StatementParts is StatementText in parts where the landed entry's
	// author wrote it so (dsl.Statement): the literal the member keeps,
	// rendered as written where StatementText is the headline, the
	// entries its proof spells beyond the author's table appended. nil
	// renders the headline from its text — in parts where it has a
	// premise or the member spells an abbreviation (dsl.SplitStatement),
	// as one string otherwise.
	StatementParts *dsl.Statement
	// Abbreviations is the table the member's section was stated with
	// (dsl.Statement.Abbrev): every text the member renders is
	// read back under it, a term an entry names is spelled «Name», and
	// the member declares the entries its texts spell.
	Abbreviations dsl.Abbrev
}

// FamilyVocab is the name set of a chapter's vocabulary as emit needs
// it (EmitOptions.FamilyVocab): the engine reads the registry's
// VocabSpec rows and hands emit the names, so emit stays
// registry-agnostic.
type FamilyVocab struct {
	// Consts are the constant names the family declares (term,
	// spelled, defined, poly and declare rows).
	Consts map[string]bool
	// Vars are the free-variable names the family registers (free rows).
	Vars map[string]bool
	// Abbrev are the names the chapter's abbreviation table declares
	// (registry.Family.WithAbbrev): in scope for every text of the
	// chapter, so a member declares none of them (ownEntries).
	Abbrev map[string]bool
	// Resolves reports whether the process's constant inventory serves
	// the name — a chapter-minted constant (the family's own or any
	// other chapter's, `convex`, `empty_set`), which every member scope
	// reads through the inventory before its texts parse. A
	// registration-only `ctx.Const` line for such a name is dead; the
	// engine sets this to the inventory's lookup, and nil resolves
	// nothing (the emit unit tests' control).
	Resolves func(name string) bool
}

// familyDeclaresConst / familyDeclaresVar report whether the target
// family's vocabulary already registers the name — the case where a
// registration-only declaration in the member body is redundant.
func (e *_Emitter) familyDeclaresConst(name string) bool {
	v := e.opts.FamilyVocab
	if v == nil {
		return false
	}
	return v.Consts[name] || (v.Resolves != nil && v.Resolves(name))
}

func (e *_Emitter) familyDeclaresVar(name string) bool {
	return e.opts.FamilyVocab != nil && e.opts.FamilyVocab.Vars[name]
}

// DefinitionText is the author's own spelling of one definition, as
// the `define` RPC received it (EmitOptions.DefinitionText): the
// constant's type, its equations (the recursive/direct door), the WF
// measure, and — for a specification constant — the spec statement.
// Fields the door does not take stay empty.
type DefinitionText struct {
	Type      string
	Equations []string
	Measure   string
	Spec      string
}

// EmitCard is one card the family profile renders as a card entry
// before the member — see EmitOptions.Cards: the bare entry name the
// var is declared as, the registered name the member's cites spell
// (rendered only when the member cites it or a rendered card's Deps
// name it), the statement's own key,
// the statement in its paste-ready spelling, the note the card was
// deferred with, and the registered names of the members it says it
// stands on, rendered as its Deps.
type EmitCard struct {
	Name      string
	Entry     string
	Key       core.PropKey
	Statement string
	Note      string
	Deps      []string
}

// FamilyDepRef is one resolved typed dep for the family.Add block
// (EmitOptions.FamilyDepEntry).
type FamilyDepRef struct {
	// Expr names the entry from the member's own package: a member
	// variable or a field of a datatype handle, qualified for a
	// cross-family reference ("real_ring.NegNeg" or
	// "list.ListData.Induct").
	Expr string
	// ImportPath is the cross-family package import the Expr needs;
	// empty for a same-family ref.
	ImportPath string
	// BareEntry means Expr is a registry entry without generated wrapper
	// methods, such as a theorem field of a datatype handle.
	BareEntry bool
}

// registryImportPath is the one import every family member file
// carries (the registry.ProofEntry literal in its family.Add block).
const registryImportPath = "github.com/euc-ai/xugo/library/registry"

// authoringImportPath is the package a proof file dot-imports for the
// bare-name surface (Cite, Argument, MakeFun, …).
const authoringImportPath = "github.com/euc-ai/xugo/library/authoring"

// EmitResult carries the emitted Go source and the metadata callers need
// without re-parsing it.
type EmitResult struct {
	Source string
	// Capabilities is the dependency-capability list the recorded steps
	// use — what the family recorder will observe the landed member
	// using. Informational: nothing declares it.
	Capabilities []string
	// DepNames lists every named theorem the emitted source cites
	// (rendered as the entry var, or `<var>.Name` inside a cert-typed
	// call), sorted + deduplicated —
	// the names whose entries the member declares (typed where the
	// registry knows them, a TODO where it does not).
	DepNames []string
	// UnfoldNames lists the entries defining the constants the emitted
	// source opens (Unfold, Unfolded), by registered name, sorted +
	// deduplicated — what the family recorder will observe the landed
	// member opening.
	UnfoldNames []string
}

// EmitMember renders closed session sections as one family member.
// The LAST section is the member's statement; the earlier ones are the
// lemmas it cites, each after the sections it cites (SectionOrder
// decides that order); a section cites only sections before it. One
// section renders as
// `family.Theorem` — or the definition door its `define` step records,
// or `family.Instance` for a structure instance proved conjunct by
// conjunct; several render as `family.Sections`, each earlier section a
// `ctx.Lemma` whose node the later bodies cite by closure capture.
func EmitMember(
	sections []*proof.DetailedProofProto,
	loadConstMeta ext.LoadConstMeta,
	opts EmitOptions,
) (EmitResult, error) {
	return emitMemberWithReservedImports(sections, loadConstMeta, opts, nil, nil)
}

// SectionOrder decides which of the given sections a member renders,
// and in what order: indices into sections, the last section — the
// member's statement — last, and every other after each section it
// cites, ties in the given order. A cite resolves by statement, so the
// order is read off one rendering in which every section may cite every
// other (citableSectionsFor); EmitMember in that order resolves the same
// cites, each to a section declared before it. With citedOnly the
// member keeps the sections its statement reaches through its cites,
// directly or through another section; without it every section is kept,
// and one the statement does not reach is refused, since it would render
// as a local nothing reads. Sections that cite one another round a cycle
// are refused. A definition is a member of its own (validateFamilyProfile)
// and never a lemma: a theorem that uses one cites its family entry. With
// citedOnly the definitions are left out — a definition statement keeps
// no other section — and without it a definition beside other sections
// is refused. A refusal is a *SectionOrderError.
func SectionOrder(sections []*proof.DetailedProofProto, loadConstMeta ext.LoadConstMeta, opts EmitOptions, citedOnly bool) ([]int, error) {
	if len(sections) == 0 {
		return nil, fmt.Errorf("empty section list")
	}
	last := len(sections) - 1
	if last == 0 {
		return []int{0}, nil
	}
	e, err := newEmitter(loadConstMeta, opts, nil, nil)
	if err != nil {
		return nil, err
	}
	e.observing = true
	if err := e.decodeSections(sections); err != nil {
		return nil, err
	}
	var definitions, theorems []int
	for i, s := range e.sections {
		if e.isDefinitionSection(s) {
			definitions = append(definitions, i)
		} else {
			theorems = append(theorems, i)
		}
	}
	switch {
	case len(definitions) == 0:
	case !citedOnly:
		return nil, &SectionOrderError{Definitions: definitions}
	case definitions[len(definitions)-1] == last:
		return []int{last}, nil
	default:
		return theoremOrder(sections, theorems, loadConstMeta, opts)
	}
	e.planSectionCites()
	e.planByInductions()
	e.planHypothesisVerbs()
	e.collectSymbols()
	e.computeRegisterableVarNames()
	e.decideSectionForms()
	e.caps = e.dependencyCapabilities()
	// The rendering is read for its cites alone: what the member's own
	// rendering refuses (validateFamilyProfile, a text that does not read
	// back) it refuses of the sections it keeps.
	e.familyGoalText = e.sectionTextForm[last]
	e.render()

	reads := e.sectionReads
	reached := map[int]bool{}
	var reach func(int)
	reach = func(i int) {
		for j := range reads[i] {
			if !reached[j] {
				reached[j] = true
				reach(j)
			}
		}
	}
	reach(last)
	var kept, uncited []int
	for i := 0; i < last; i++ {
		switch {
		case reached[i]:
			kept = append(kept, i)
		case citedOnly:
		default:
			uncited = append(uncited, i)
		}
	}
	if len(uncited) > 0 {
		return nil, &SectionOrderError{Uncited: uncited}
	}
	placed := map[int]bool{}
	order := make([]int, 0, len(kept)+1)
	ready := func(i int) bool {
		for j := range reads[i] {
			if !placed[j] {
				return false
			}
		}
		return true
	}
	for len(order) < len(kept) {
		next := -1
		for _, i := range kept {
			if !placed[i] && ready(i) {
				next = i
				break
			}
		}
		if next < 0 {
			return nil, &SectionOrderError{Cycle: sectionCycle(reads, placed, kept)}
		}
		placed[next] = true
		order = append(order, next)
	}
	return append(order, last), nil
}

// theoremOrder is SectionOrder with citedOnly over the sections at
// theorems — indices into sections, in order, the member's statement
// last — in indices into sections.
func theoremOrder(sections []*proof.DetailedProofProto, theorems []int, loadConstMeta ext.LoadConstMeta, opts EmitOptions) ([]int, error) {
	picked := make([]*proof.DetailedProofProto, len(theorems))
	for k, i := range theorems {
		picked[k] = sections[i]
	}
	back := func(indices []int) []int {
		out := make([]int, len(indices))
		for k, i := range indices {
			out[k] = theorems[i]
		}
		return out
	}
	order, err := SectionOrder(picked, loadConstMeta, opts, true)
	var refused *SectionOrderError
	if errors.As(err, &refused) {
		return nil, &SectionOrderError{Cycle: back(refused.Cycle)}
	}
	if err != nil {
		return nil, err
	}
	return back(order), nil
}

// sectionCycle walks unplaced cites from the first unplaced kept section
// until a section repeats, and returns the sections round that cycle.
func sectionCycle(reads map[int]map[int]bool, placed map[int]bool, kept []int) []int {
	at := -1
	for _, i := range kept {
		if !placed[i] {
			at = i
			break
		}
	}
	seen := map[int]int{}
	var path []int
	for {
		if k, again := seen[at]; again {
			return path[k:]
		}
		seen[at] = len(path)
		path = append(path, at)
		next := -1
		for j := range reads[at] {
			if !placed[j] && (next < 0 || j < next) {
				next = j
			}
		}
		at = next
	}
}

// SectionOrderError is SectionOrder's refusal, each section named by its
// index into the sections SectionOrder was handed: Definitions the
// definition sections handed beside other sections, the member's
// statement among them where it is one; Cycle the sections that cite
// one another round a cycle, in cite order; Uncited the sections the
// member's statement does not reach through its cites.
type SectionOrderError struct {
	Definitions []int
	Cycle       []int
	Uncited     []int
}

func (err *SectionOrderError) Error() string {
	switch {
	case len(err.Definitions) > 0:
		return fmt.Sprintf("sections %v are definitions, each a member of its own", err.Definitions)
	case len(err.Cycle) > 0:
		return fmt.Sprintf("sections %v cite one another round a cycle", err.Cycle)
	}
	return fmt.Sprintf("sections %v are cited by no section the member's statement reaches", err.Uncited)
}

// emitMemberWithReservedImports renders the member, its symbols kept off
// importIdents and its texts checked beside the declared variables
// declaredSeed names (_Emitter.declaredSeed).
func emitMemberWithReservedImports(
	sections []*proof.DetailedProofProto,
	loadConstMeta ext.LoadConstMeta,
	opts EmitOptions,
	importIdents map[string]bool,
	declaredSeed map[string]core.HolType,
) (EmitResult, error) {
	if opts.Family == "" {
		return EmitResult{}, fmt.Errorf("EmitOptions.Family is required — every rendered file is a family member")
	}
	if opts.FuncName == "" {
		return EmitResult{}, fmt.Errorf("EmitOptions.FuncName is required")
	}
	if len(sections) == 0 {
		return EmitResult{}, fmt.Errorf("empty section list")
	}
	e, err := newEmitter(loadConstMeta, opts, importIdents, declaredSeed)
	if err != nil {
		return EmitResult{}, err
	}
	if err := e.decodeSections(sections); err != nil {
		return EmitResult{}, err
	}
	e.planSectionCites()
	e.planByInductions()
	e.planHypothesisVerbs()
	e.collectSymbols()
	e.computeRegisterableVarNames()
	e.decideSectionForms()
	e.caps = e.dependencyCapabilities()
	if err := e.validateFamilyProfile(); err != nil {
		return EmitResult{}, err
	}
	src := e.render() // render() populates depNames as leaves resolve
	if e.textErr != nil {
		return EmitResult{}, e.textErr
	}
	// A text parsed after the member's declarations is parsed beside all
	// of them at replay. The texts were chosen beside the Skolems their
	// closure's boundary declares and the variables the last rendering
	// declared (none on the first); one that does not read back beside
	// this rendering's has the member rendered again, its texts chosen
	// beside them — once: a text that still does not read back is
	// refused.
	if declared, err := e.verifyTextsAtReplayScope(); err != nil {
		if declaredSeed != nil {
			return EmitResult{}, err
		}
		return emitMemberWithReservedImports(sections, loadConstMeta, opts, importIdents, declared)
	}
	for step, facts := range e.branchFacts {
		if !e.branchFactOpened[step] {
			return EmitResult{}, fmt.Errorf("emit: the subtree that binds %s is rendered by no step renderer that opens it — "+
				"its uses name a fact the member never declares", facts[0].ident)
		}
	}
	// Rendering discovers the dependency imports. If a symbol took one
	// of their package names, allocate the symbols again with those
	// names reserved; the dependency expressions retain their qualifiers.
	file, err := parser.ParseFile(token.NewFileSet(), "member.go", src, parser.ImportsOnly)
	if err != nil {
		return EmitResult{}, fmt.Errorf("emit: parse rendered imports: %w", err)
	}
	reserved := map[string]bool{}
	for name := range importIdents {
		reserved[name] = true
	}
	collision := false
	for _, spec := range file.Imports {
		name := path.Base(strings.Trim(spec.Path.Value, `"`))
		reserved[name] = true
		if !e.constMeta[name].IsZero() || !e.varDecl[name].IsZero() {
			collision = true
		}
	}
	if collision {
		return emitMemberWithReservedImports(sections, loadConstMeta, opts, reserved, declaredSeed)
	}
	src, err = importAuthoring(src)
	if err != nil {
		return EmitResult{}, err
	}
	// The member is laid out as a chapter file is, so it lands as
	// rendered (xugofmt).
	formatted, err := xugofmt.Source([]byte(src))
	if err != nil {
		return EmitResult{}, fmt.Errorf("emit: the rendered file does not format (an emitter defect): %w\n--- source: ---\n%s", err, src)
	}
	return EmitResult{Source: string(formatted), Capabilities: e.caps, DepNames: e.sortedDepNames(), UnfoldNames: e.sortedUnfoldNames()}, nil
}

// newEmitter is an emitter for one rendering under opts, its symbols
// kept off importIdents and its texts checked beside declaredSeed.
func newEmitter(loadConstMeta ext.LoadConstMeta, opts EmitOptions, importIdents map[string]bool, declaredSeed map[string]core.HolType) (*_Emitter, error) {
	abbrevTable, err := dsl.ParseAbbreviations(opts.Abbreviations)
	if err != nil {
		return nil, fmt.Errorf("EmitOptions.Abbreviations: %v", err)
	}
	e := &_Emitter{
		opts:            opts,
		importIdents:    importIdents,
		loadConstMeta:   loadConstMeta,
		abbrevTable:     abbrevTable,
		abbrevUsed:      map[string]bool{},
		constIdent:      map[_ConstKey]string{},
		constMeta:       map[string]core.ConstTermMeta{},
		constInstType:   map[string]core.HolType{},
		varIdent:        map[_VarKey]string{},
		varDecl:         map[string]core.VarTerm{},
		pendingVars:     map[_VarKey]core.VarTerm{},
		sectionTextForm: map[int]string{},
		sectionTextErr:  map[int]error{},
		goUsedConst:     map[string]bool{},
		goUsedVar:       map[string]bool{},
		declaredSeed:    declaredSeed,
	}
	e.printer = &ext.GoTermPrinter{
		VarIdent:         e.lookupVarIdent,
		WrapperlessIdent: e.signatureBoundVar,
		ConstIdent:       e.lookupConstIdent,
		ConstAtType:      e.constAtType,
		// Bare mode: the body uses MakeFun / TypeBool / Var / Const /
		// ForAll / … without the `core.` / `ext.` qualifier — the names
		// of library/authoring, which the rendered file dot-imports
		// (importAuthoring).
		BareNames: true,
		// Fail loud at emit time on an unresolved const instead of
		// emitting a WrapTerm(nil) that nil-derefs at replay.
		StrictConsts: true,
	}
	return e, nil
}

// _HypUse identifies a recorded hypothesis use by its step or resident
// premise. Exactly one pointer is set; identity is the record's address.
type _HypUse struct {
	step    *proof.StepProto
	premise *proof.ByPremiseProto
	// rule is a simp step's rule that is a resident hypothesis, by
	// position plus one; 0 for a use of the step's target.
	rule int
}

// _PlacedUse is a hypothesis use with where it is in the rendering: the
// nodes from the root of the stretch it was found in down to its own,
// and whether it rewrites the hypothesis in place (a Simp at it, after
// which the handle names the rewritten hypothesis from the Simp's
// residual down, and nowhere else — HypHandle.Simp rebinds it there).
type _PlacedUse struct {
	use     _HypUse
	path    []*msNode
	rewrite bool
}

// _BranchFact is the fact a subtree binds of its own: the Go ident, and
// the hypothesis as it stands at the subtree's root.
type _BranchFact struct {
	ident   string
	content core.Term
}

type _Emitter struct {
	opts          EmitOptions
	importIdents  map[string]bool
	loadConstMeta ext.LoadConstMeta

	// abbrevTable is EmitOptions.Abbreviations parsed, nil for none;
	// abbrevUsed the names the member's rendered texts spell — its
	// headline's, its sections' and its proof's, a card's beside it not
	// among them — so the headline declares those entries and what they
	// stand on (usedAbbreviations, headlineArg).
	abbrevTable *dsl.AbbreviationTable
	abbrevUsed  map[string]bool

	// reader is the pool reader for the section currently being emitted,
	// set at each section's entry. Every goal / term / prop ref in that
	// section's steps indexes into this pool.
	reader *ext.PoolReader

	printer *ext.GoTermPrinter

	sections []*_SectionEmit

	// hypHandleByUse maps a recorded use of a hypothesis — a
	// hyp-addressing ministep (Rw / Subst / CongrArg / a simp at a
	// hypothesis, keyed by its *proof.StepProto) or a resident premise
	// of a `by` (keyed by its *proof.ByPremiseProto) — to the Go ident
	// of the Fact that names the hypothesis: the `a.Have` that
	// introduced it, when a Derive block bound one (haveHandleIdents),
	// or a Given closure's parameter (renderGivenBranch). A step then
	// renders in the handle form (`fact1.Rw()`) instead of the
	// positional index the chapter lint bans, and a premise as the
	// handle (`By(fact1)`) instead of the hypothesis's statement.
	// factHandleCount numbers the idents across the file.
	hypHandleByUse  map[_HypUse]string
	factHandleCount int

	// branchFacts maps the root of a subtree that binds facts of its
	// own — Haves' facts rewritten in place inside the subtree and used
	// again after it (haveHandleIdents) — to those facts, one per Have:
	// the subtree renders as a Derive block opening with a
	// `local := c.Hyp(<stmt>)` for each (renderBranchFact), so each
	// rewrite moves its local's handle and the Have's stays where it was
	// bound. branchFactOpened marks the roots rendered so far.
	branchFacts      map[*proof.StepProto][]_BranchFact
	branchFactOpened map[*proof.StepProto]bool

	// simpRulesKeptByStep maps a recorded simp_with step to the rules
	// the rendering keeps (simpRulesKept), noted for the symbol walk
	// before any step renders (noteSimpRulesKept); a step not noted
	// prints every rule.
	simpRulesKeptByStep map[*proof.StepProto][]bool

	// byInductions maps the first assert of a recorded induction by a
	// cited principle — the obligations asserted one each, the by that
	// closes on them — to the verb it renders as (planByInductions,
	// byInductionFusion); byInductionAsserts marks every assert of
	// such a chain, whose claim no text prints.
	byInductions       map[*proof.StepProto]*byInductionFusion
	byInductionAsserts map[*proof.StepProto]bool

	// obtained maps an assert of a Derive block whose continuation opens
	// the asserted ∃ — `strip_quant {hyp_index}` at the hypothesis the
	// assert added — to that strip's node: the pair is one Obtain
	// (obtainStrip), and the strip renders nothing of its own.
	obtained map[*proof.StepProto]*msNode

	// unfolded and conjuncts are the records of the Argument verbs that
	// read one resident fact (planHypothesisVerbs,
	// emit_hypothesis_verbs.go): an assert a.Unfolded made, by the fact
	// it opened, and every assert of a run a.Conjuncts made, by its run.
	unfolded  map[*proof.StepProto]_UnfoldedFact
	conjuncts map[*proof.StepProto]*_ConjunctsRun

	// lawHypothesis is the structure hypothesis a Law door's closure
	// receives as lawHandle (renderFamilyLawFile): a resident premise or
	// a reading under that statement renders as the handle.
	lawHypothesis core.Prop
	lawHandle     string
	lawHandleUsed bool

	// The lifted boundary (emit_signature.go). Of the closure rendering
	// now: boundHyps are the antecedents its Fact parameters bind,
	// surfaceSkolems the Skolems a claim text spells under their binders'
	// names, closureReceiver its Argument (`a`, or `arg` where a binder
	// is named a). Of the member, every section's signature among them:
	// boundNames the Go names a signature binds, boundVars the variables
	// a boundary fixes — each Skolem and the binder name it is aliased
	// by, which no registration-only ctx.Var repeats — and extraImports
	// the packages the signatures and the cards spell.
	boundHyps       []*boundHyp
	boundNames      map[string]bool
	boundVars       map[string]bool
	surfaceSkolems  []boundSkolem
	closureReceiver string
	extraImports    map[string]bool
	// splitSkolems are the Skolems of a member of several sections that
	// some closure binds as a parameter and some section mentions
	// outside it (planSectionLifts); closureIdents names each by the
	// parameter of the closure being read (readUnderLift), where the
	// member's table (varIdent) holds its declaration.
	splitSkolems  map[_VarKey]bool
	closureIdents map[_VarKey]string
	// goalFrees are the variables free in a goal some rendered step of
	// the member sees (planSectionLifts): the proof's own variables, as
	// against the binders of the terms its steps carry.
	goalFrees map[_VarKey]bool
	// unfoldNames is the entries defining the constants the rendered
	// source opens (definitionExpr), by registered name.
	unfoldNames map[string]bool

	// sectionLifts holds each section's lift, by section index
	// (planSectionLifts): the parameters its closure binds and the node
	// its body renders from.
	sectionLifts []*sectionBinding

	// declaredSeed is the variables a previous rendering of the member
	// registers at script scope (replayScopeVars), read into the check
	// of every text parsed after the declarations; nil on the first
	// rendering. checkedTexts are those texts, as chosen, re-read in the
	// scope the replay gives them once the rendering knows it
	// (verifyTextsAtReplayScope).
	declaredSeed map[string]core.HolType
	checkedTexts []_CheckedText

	// typedefsInScope is the typedef metatypes whose phantom the family
	// the member lands in has in scope (phantomInScope), read once;
	// lettersInScope the statement letters it has a phantom for.
	typedefsInScope map[string]bool
	lettersInScope  map[string]bool

	// closureArgumentRead is set when a rendered step calls a method of
	// the Argument its enclosing closure binds (witnessExpr's
	// `a.TermAs`): a Case of the Instance door, which has no closure of
	// its own, then takes one (renderInstanceCaseBody).
	closureArgumentRead bool

	// textScopeVars are the free-variable NAMES some rendered text
	// payload (miniStepPropExpr's MakePropText form) mentions — the
	// names whose ParseScope registration a body text actually reads.
	// A member renders its bodies before its declarations, so a
	// registration-only `ctx.Var` is emitted only for a name in this
	// set: a Skolem the goal carries but no text spells needs no line
	// (see renderVarDecls).
	textScopeVars map[string]bool

	// (const meta name, instantiated type key) → Go identifier.
	// Polymorphic re-uses at distinct types get distinct idents
	// (`set_comprehension` for the first instance, `set_comprehension_2` for the second, …)
	// so each (name, instType) pair has exactly one ctx.Const(...)
	// declaration and Go-expr bodies reference it by bare ident.
	constIdent map[_ConstKey]string
	// Go identifier → meta + the type used at the declaration site.
	constMeta     map[string]core.ConstTermMeta
	constInstType map[string]core.HolType

	// Free vars. Identified by (name, typeKey) — distinct types under
	// the same name get distinct Go idents.
	varIdent map[_VarKey]string
	varDecl  map[string]core.VarTerm

	// pendingVars holds every (varKey, VarTerm) seen during collectSymbols'
	// walk BEFORE ident allocation runs. assignVarIdents (called at the end
	// of collectSymbols) drains this into varIdent / varDecl: names with a
	// single type instance get a bare base ident; names with multiple type
	// instances get a symmetric `<base>_<TypeName>` suffix for EVERY variant
	// (falling back to `_N` numeric only for composite types with no natural
	// short suffix).
	pendingVars map[_VarKey]core.VarTerm

	// observing says the rendering is SectionOrder's, in which a section
	// may cite every other (citableSections); sectionReads records, per
	// section index, the sections its rendering cites (citeSection).
	observing    bool
	sectionReads map[int]map[int]bool

	// sectionCites holds, per `assert` step whose claim an earlier
	// section of the member proves, how the assert renders as a cite of
	// that section's node (planSectionCites); sectionCitedSteps are the
	// steps of those claims' recorded proofs, which the cite stands for
	// and no rendering prints.
	sectionCites      map[*proof.StepProto]sectionCite
	sectionCitedSteps map[*proof.StepProto]bool

	// sectionTextForm[i] holds section i's statement as parser text
	// (every member section is spelled as text — family.Theorem,
	// family.Sections and ctx.Lemma all parse their statement), in the
	// chapter's surface form (surfaceText); sectionTextErr[i] is why
	// section i has none — its surface print did not read back.
	// goUsedConst / goUsedVar track which declared idents are referenced
	// as Go identifiers; renderDecls binds `<ident> :=` only for those.
	sectionTextForm map[int]string
	sectionTextErr  map[int]error
	goUsedConst     map[string]bool
	goUsedVar       map[string]bool

	// textErr is the first claim text that did not read back
	// (failText). The body renders to the end regardless; EmitMember
	// returns the error in place of the member.
	textErr error

	// depNames collects the named theorems rendered as dep references
	// during render(); surfaced (sorted) as EmitResult.DepNames. Lazily
	// initialized by markDepName.
	depNames map[string]bool
	// depKeys records the leaf key each dep name was first rendered at —
	// the lookup handle FamilyDepEntry resolves typed entry vars by
	// (names alias across renames; the statement key doesn't).
	depKeys map[string]core.PropKey

	// familyGoalText is the member statement's text — set by
	// validateFamilyProfile, rendered as the goal-text const the entry's
	// constructor parses at replay.
	familyGoalText string

	// deriveDepth is the current Derive nesting level, naming the
	// Argument receiver (`a`, then `b`, `c` for sub-arguments — the
	// chartered spelling for genuine nesting).
	deriveDepth int

	// registerableVarNames is the set of free-var NAMES emit may declare
	// via ctx.Var (collected at exactly one type). Computed once after
	// assignVarIdents; read by textDoorScope, varOverrideEntries and
	// renderDecls.
	registerableVarNames map[string]bool

	// caps is the dependency-capability list computed once by
	// dependencyCapabilities, returned as EmitResult.Capabilities.
	caps []string
}

// _VarKey identifies one free variable by (name, type): distinct types
// under one name are distinct kernel variables and get distinct idents.
type _VarKey struct {
	name core.TermName
	tkey core.TypeKey
}

// _ConstKey identifies one polymorphic instance of a const. Two
// occurrences of the same const name at different instantiated types
// get distinct Go idents (`set_comprehension` vs `set_comprehension_2`), so each instance's
// ctx.Const(...) declaration is emitted once and Go-expr bodies can
// reference it directly instead of rebuilding the full type expression
// at every use site.
type _ConstKey struct {
	name core.TermName
	tkey core.TypeKey
}

// _SectionEmit is one member section: its recorded ministep tree and
// the Go ident an earlier section's node is bound to ("lemma1",
// "lemma2", …; the member's own statement is "goal").
type _SectionEmit struct {
	// index is the section's position in the member: a section cites
	// only sections before it (citableSections).
	index   int
	varName string
	goal    core.Prop
	// outKey and normKey are the statement's α-key, raw and up to
	// Normalize: a payload stating either renders as a cite of the
	// section.
	outKey, normKey core.PropKey
	// reader is the pool reader for this section's steps; every Goal /
	// term / prop ref in detailedSteps indexes into it. The emit passes
	// set e.reader = s.reader on entry.
	reader        *ext.PoolReader
	detailedSteps []*proof.StepProto
}

func (e *_Emitter) lookupVarIdent(v core.VarTerm) (string, bool) {
	return e.identOfVar(_VarKey{v.Name(), v.Type().Key()})
}

// identOfVar is the Go identifier a variable is named by where the
// emitter is reading: the parameter of the closure being read for a
// split Skolem it binds (closureIdents), the member's identifier
// otherwise.
func (e *_Emitter) identOfVar(k _VarKey) (string, bool) {
	if id, bound := e.closureIdents[k]; bound {
		return id, true
	}
	id, ok := e.varIdent[k]
	return id, ok
}

// signatureBoundVar reports that v's ident is a parameter of the
// closure's signature: a typed wrapper or a core Term, not the
// *TermWrapper a ctx.Var declares.
func (e *_Emitter) signatureBoundVar(v core.VarTerm) bool {
	id, ok := e.lookupVarIdent(v)
	return ok && e.boundNames[id]
}

func (e *_Emitter) lookupConstIdent(c core.ConstTerm) (string, core.HolType, bool) {
	id, ok := e.constIdent[_ConstKey{c.Meta().Name(), c.Type().Key()}]
	if !ok {
		return "", nil, false
	}
	return id, e.constInstType[id], true
}

// constAtType renders a const at a type no declared ident carries — the
// printer's fallback for an off-type occurrence.
func (e *_Emitter) constAtType(c core.ConstTerm) string {
	return fmt.Sprintf("ctx.Const(%q, %s)", string(c.Meta().Name()), e.printer.PrintType(c.Type()))
}

// decodeSections binds each recorded ministep tree to a section, the
// last one being the member's own statement.
func (e *_Emitter) decodeSections(sections []*proof.DetailedProofProto) error {
	e.sections = make([]*_SectionEmit, 0, len(sections))
	for i, d := range sections {
		if d == nil || len(d.Steps) == 0 {
			return fmt.Errorf("section %d has no recorded steps", i)
		}
		s := &_SectionEmit{
			index:         i,
			reader:        ext.NewPoolReader(d.Pool, e.loadConstMeta),
			detailedSteps: d.Steps,
			varName:       fmt.Sprintf("lemma%d", i+1),
		}
		if i == len(sections)-1 {
			s.varName = "goal"
		}
		e.reader = s.reader
		s.goal, _ = e.reader.Prop(d.Steps[0].Goal)
		normalized, _ := proof.Normalize(s.goal)
		s.outKey, s.normKey = s.goal.AlphaKey(), normalized.AlphaKey()
		e.sections = append(e.sections, s)
	}
	return nil
}

// citableSections are the sections the section e.reader belongs to may
// cite (citableSectionsFor); none when it belongs to none.
func (e *_Emitter) citableSections() []*_SectionEmit {
	if s := e.readingSection(); s != nil {
		return e.citableSectionsFor(s)
	}
	return nil
}

// citableSectionsFor are the sections s may cite, in member order: those
// before it — every other while SectionOrder observes the cites — less
// the member's statement, which no section cites, a section stating s's
// own statement, whose payload of that statement is the external
// theorem s restates, and a section stating what a section before it
// states, which the first one serves; a statement is the same one up to
// α. A payload
// stating one of them renders as its node; every pass that asks whether
// a payload renders by reference asks here, so the symbol walk and the
// Go-used marking judge a cite as the rendering does, and no closure
// binds a local its body never reads.
func (e *_Emitter) citableSectionsFor(s *_SectionEmit) []*_SectionEmit {
	last := len(e.sections) - 1
	var citable []*_SectionEmit
	served := map[core.PropKey]bool{}
	for i, c := range e.sections {
		restates := served[c.outKey]
		served[c.outKey] = true
		if c == s || i == last || (!e.observing && i > s.index) || restates || c.outKey == s.outKey {
			continue
		}
		citable = append(citable, c)
	}
	return citable
}

// citeSection is the Go node a cite of section c spells, the cite
// recorded against the section being read (sectionReads).
func (e *_Emitter) citeSection(c *_SectionEmit) string {
	if s := e.readingSection(); s != nil {
		if e.sectionReads == nil {
			e.sectionReads = map[int]map[int]bool{}
		}
		if e.sectionReads[s.index] == nil {
			e.sectionReads[s.index] = map[int]bool{}
		}
		e.sectionReads[s.index][c.index] = true
	}
	return c.varName
}

// readingSection is the section whose steps the emitter is reading, the
// one e.reader belongs to; nil when it belongs to none.
func (e *_Emitter) readingSection() *_SectionEmit {
	for _, s := range e.sections {
		if s.reader == e.reader {
			return s
		}
	}
	return nil
}

func (e *_Emitter) collectSymbols() {
	for _, s := range e.sections {
		e.reader = s.reader
		e.noteSimpRulesKept(buildMSTree(s.detailedSteps))
		// A section's statement is spelled as the pre-Normalize goal the
		// recorded steps actually saw (sectionInitGoal); walk that exact
		// prop so the consts/vars its text reads get declared.
		e.walkProp(e.sectionInitGoal(s))
		for _, step := range s.detailedSteps {
			e.walkMiniStep(step)
		}
	}
	// All (varKey, VarTerm) pairs are now in e.pendingVars — drain into
	// varIdent / varDecl with symmetric multi-type disambiguation.
	e.assignVarIdents()
}

// assignVarIdents allocates a Go identifier for every (name, type) pair
// pending in e.pendingVars. Same-HOL-name-different-type variables (which
// are truly distinct in the kernel — var identity is name × type) get a
// symmetric `<base>_<TypeName>` suffix on EVERY variant when the type is a
// bare type var (`A`, `B`) or a 0-arity CompositeType (`bool`, `ind`), so
// a reader seeing `y_A` immediately knows `y_B` also exists in the file.
// Composite types with no natural short suffix (`A → bool`, `prod(A, B)`,
// …) fall back to freshIdent's numeric `_N`.
//
// Single-type-instance names get the bare base ident with no suffix.
//
// Iteration is over pendingVars keys in a stable order (sort by name then
// typeKey) so emit output is deterministic across runs.
func (e *_Emitter) assignVarIdents() {
	byName := map[core.TermName][]_VarKey{}
	for k := range e.pendingVars {
		byName[k.name] = append(byName[k.name], k)
	}
	names := make([]core.TermName, 0, len(byName))
	for n := range byName {
		names = append(names, n)
	}
	sort.Slice(names, func(i, j int) bool { return names[i] < names[j] })
	for _, name := range names {
		keys := byName[name]
		base := sanitizeIdent(string(name))
		if len(keys) == 1 {
			ident := e.freshIdent(base, e.declSet())
			k := keys[0]
			e.varIdent[k] = ident
			e.varDecl[ident] = e.pendingVars[k]
			continue
		}
		// Multi-type name — symmetric suffix.
		sort.Slice(keys, func(i, j int) bool { return keys[i].tkey < keys[j].tkey })
		for _, k := range keys {
			t := e.pendingVars[k]
			var cand string
			if suffix := typeSuffixForIdent(t.Type()); suffix != "" {
				cand = base + suffix
			} else {
				cand = base
			}
			ident := e.freshIdent(cand, e.declSet())
			e.varIdent[k] = ident
			e.varDecl[ident] = t
		}
	}
	// Release pendingVars — subsequent walks (if any) should not populate
	// it; walkTerm's re-entry short-circuits on already-allocated varIdent.
	e.pendingVars = nil
}

// walkMiniStep registers any constants / free variables referenced by
// a ministep's payload: only payloads that introduce identifiers the
// emit body will reference (witness terms, case-split terms, …) — and
// only when the rendering prints them, never a payload rendered by
// reference.
//
// A payload rendered by reference (an earlier section, a classified
// external statement) is skipped: walking it would register vars/consts
// that no emit site references, and a closure-local binding nothing
// uses breaks Go's "declared and not used" check.
func (e *_Emitter) walkMiniStep(step *proof.StepProto) {
	if e.sectionCitedSteps[step] {
		return
	}
	switch s := step.Step.(type) {
	case *proof.StepProto_AxiomDef:
		if s.AxiomDef != nil {
			if ct := e.constAt(s.AxiomDef.GetConst()); !ct.IsZero() {
				e.recordConst(ct)
			}
		}
	case *proof.StepProto_ExistentialConstDef:
		{
			ct := e.constAt(s.ExistentialConstDef)
			e.recordConst(ct)
		}
	case *proof.StepProto_DefExpand:
		// def_expand composite (proto tag 51) renders as
		// `Unfold(<definition>)`, which names the definition's entry
		// instead of referencing a declared term — nothing to register
		// (see emitMiniStep's DefExpand arm).
	case *proof.StepProto_Witness:
		{
			e.walkTerm(e.reader.Term(s.Witness))
		}
	case *proof.StepProto_Specialize:
		// specialize composite (proto tag 52): every witness term of every
		// per-hyp entry becomes a Go reference at the call site.
		if s.Specialize != nil {
			for _, h := range s.Specialize.GetHyps() {
				for _, ref := range h.GetWitnesses() {
					e.walkTerm(e.reader.Term(ref))
				}
			}
		}
	case *proof.StepProto_Trans:
		{
			e.walkTerm(e.reader.Term(s.Trans))
		}
	case *proof.StepProto_Denote:
		if ref := s.Denote.GetTerm(); ref != 0 {
			e.walkTerm(e.reader.Term(ref))
		}
	case *proof.StepProto_ByCase:
		{
			e.walkTerm(e.reader.Term(s.ByCase))
		}
	case *proof.StepProto_CongrArg:
		// The supplied function term becomes a Go reference at the call site.
		if s.CongrArg != nil {
			e.walkTerm(e.reader.Term(s.CongrArg.GetFunction()))
		}
	case *proof.StepProto_CongrFun:
		// The supplied argument term becomes a Go reference at the call site.
		if s.CongrFun != nil {
			e.walkTerm(e.reader.Term(s.CongrFun.GetArgument()))
		}
	case *proof.StepProto_Induction:
		{
			e.walkTerm(e.reader.Term(s.Induction))
		}
	case *proof.StepProto_Lemma:
		// A `Lemma` ministep that isn't a Cite fusion renders inline as
		// Lemma(MakeProp(<concl>), ...) — its conclusion's consts / free
		// vars become Go references, so walk them here (mirrors Assert).
		// Only the conclusion is rendered (LemmaTactic lemmas are
		// hyp-free standalone claims), so only the conclusion is walked.
		if s.Lemma != nil {
			l, _ := e.reader.Prop(s.Lemma)
			e.walkTerm(l.Conclusion())
		}
	case *proof.StepProto_LemmaPreserve:
		// Same rationale as Lemma above — a non-fused `lemma_preserve`
		// renders inline as LemmaPreserve(MakeProp(<concl>)).
		if s.LemmaPreserve != nil {
			l, _ := e.reader.Prop(s.LemmaPreserve)
			e.walkTerm(l.Conclusion())
		}
	case *proof.StepProto_LeanRw:
		// A LeanRw's rewrite rule normally resolves to a reference (an
		// earlier section, an external statement) and needs no symbol
		// walking. But when the rule is proven inline by LeanRw's own
		// obligation subtree (child[0]) rather than cited — e.g. a
		// binder-reordered variant of the goal — leanRwLemmaExpr falls
		// back to rendering it as MakeProp(<concl>), whose consts / free
		// vars must be registered.
		//
		// Only the inline rendering references the payload: a rule that
		// resolves to a reference (leanRwRuleTarget) prints nothing of
		// it, and walking it anyway declares the rule's whole vocabulary
		// at the session's inferred instances — the const wall a family
		// member then carries for a statement its Dep cite already
		// serves. The gate is the same predicate the Go-used marking
		// pass reads (leanRwRendersMakeProp), so registration and
		// rendering agree.
		if s.LeanRw != nil {
			l, _ := e.reader.Prop(s.LeanRw)
			if e.leanRwRendersMakeProp(l) {
				e.walkTerm(l.Conclusion())
			}
		}
	case *proof.StepProto_TypeInst:
		// typeInstSourceExpr's viaNormalize arm renders the recorded
		// source prop inline (TypeInstSourceExact(ref, <prop payload>)),
		// so its consts / free vars must be registered — the recorded
		// form is only normalize-equivalent to the resolved section's
		// goal, so that section's walkProp pass does NOT cover it (its
		// const instances can differ). The exact-ref path and the
		// AtTypes / Simp fusions print none of the source, so its
		// vocabulary is registered only when the inline rendering will
		// reference it (typeInstRendersProp — the predicate the Go-used
		// marking pass reads): a polymorphic source walked
		// unconditionally declared the row's generic instance beside
		// the goal's own, plus the source's η-binder as a var
		// (`ctx.Var("ẋ", A)`), for a cite rendered as
		// `ctx.AtTypes(ctx.Dep(name), τ…)`.
		if s.TypeInst != nil {
			l, _ := e.reader.Prop(s.TypeInst)
			if l != nil && e.typeInstRendersProp(l) {
				e.walkTerm(l.Conclusion())
			}
		}
	case *proof.StepProto_Assert:
		// _AssertStep introduces a fresh hyp-free sub-claim (NOT a lemma
		// reference — distinct from Lemma/LeanRw/KnownThm), so we
		// walk its terms here. The claim is rendered at the call site as
		// its text (claimExpr), which is read in a scope holding the
		// consts / free vars the claim mentions. An assert rendered whole
		// as a cite of an earlier section prints no claim.
		if s.Assert != nil && !e.sectionCites[step].installs {
			claim, _ := e.reader.Prop(s.Assert)
			e.walkProp(claim)
		}
		// An a.Unfolded prints the fact it opens where no Go value names it.
		e.walkUnfoldedFact(step)
	case *proof.StepProto_KnownThm:
		// A cite of a reading prints the hypothesis the reading is under
		// (readingExpr); any other close resolves to a reference.
		if under := e.readingHypothesis(s.KnownThm.GetReading()); under != nil {
			e.walkProp(under)
		}
	case *proof.StepProto_SimpWith:
		// Each rule the rendering keeps renders through the LeanRw
		// payload resolver; when a rule falls back to the inline
		// MakeProp literal its conclusion's consts / free vars become Go
		// references — same rationale as the LeanRw arm above, per rule,
		// without that arm's resolving gate: resolving a rule marks its
		// dep (leanRwRuleTarget), which only a rendered rule may. A rule
		// the Simp fusion prunes — a named rule with no obligation child
		// (simpRulesKept) — prints nothing and is walked not at all: the
		// copies the session's type adaptation records beside a rule are
		// such, and walking them held a name at an instance the member
		// never spells, one every text then passed as a scope override.
		// A reading prints its entries and the hypothesis it is under,
		// never its derived statement.
		if s.SimpWith != nil {
			kept := e.simpRulesKeptByStep[step]
			for i, ref := range s.SimpWith.GetRules() {
				if reading := simpRuleReading(s.SimpWith, i); reading != nil {
					if under := e.readingHypothesis(reading); under != nil {
						e.walkProp(under)
					}
					continue
				}
				if kept != nil && !kept[i] {
					continue
				}
				l, _ := e.reader.Prop(ref)
				e.walkTerm(l.Conclusion())
			}
		}
	case *proof.StepProto_Elementarity:
		// An `elementarity` composite renders its resident source and facts
		// as ResidentHyp(<stmt>) and its parameters as Go expressions;
		// their consts and free variables are references at the call
		// site. Its entries render by registered name.
		if t := s.Elementarity; t != nil {
			if family := t.GetFamily(); family != nil {
				l, _ := e.reader.Prop(family)
				e.walkTerm(l.Conclusion())
			}
			for _, ref := range t.GetFacts() {
				l, _ := e.reader.Prop(ref)
				e.walkTerm(l.Conclusion())
			}
			for _, ref := range t.GetParams() {
				e.walkTerm(e.reader.Term(ref))
			}
		}
	case *proof.StepProto_By:
		// A `by` composite renders every premise's install prop
		// (ResidentHyp(<stmt>) for resident/derived; the lemmaRef
		// resolver's inline-MakeProp fallback for named premises — same
		// rationale as the Lemma/LeanRw arms), every `term_specialize`
		// witness (`At(base, w…)`), each scaled coefficient, and the shape's explicit denote term
		// (`DenotedAs(name, <term>)`). All of those are Go references at
		// the call site, so walk them; a witness-only const (e.g. `_0`
		// from a numeral witness on a statement with no numeral of its
		// own) has no other channel into the symbol table.
		if s.By != nil {
			if sh := s.By.GetShape(); sh != nil && sh.GetDenoteTerm() != 0 {
				e.walkTerm(e.reader.Term(sh.GetDenoteTerm()))
			}
			for _, pr := range s.By.GetPremises() {
				// NOTE: PoolReader.Prop's second return is the proto's
				// ClaimProved bit, NOT a success flag — By premise installs
				// are claims the composite certifies itself (ClaimProved
				// false), so gating the walk on it skips exactly the props
				// this arm exists to walk. Ignore it, like the sibling
				// LeanRw / SimpWith / Assert arms do: an install's consts
				// are registered whether or not the claim is proved, or a
				// ResidentHyp text whose const only occurs mid-proof — at
				// the statement's own type var — re-parses at replay
				// against the GENERIC global meta and misses the hyp.
				//
				// A NAMED premise that resolves to a reference prints
				// nothing of its install (`ctx.Dep(name)`, the entry at
				// its instance, the registered name string), so its
				// statement's vocabulary is registered only when the
				// rendering will spell the install (byPremiseInstallPrinted)
				// — otherwise every dep a `by` names dragged its whole
				// statement's consts into the member's declarations.
				if install, _ := e.reader.Prop(pr.GetInstall()); install != nil && e.byPremiseInstallPrinted(pr, install) {
					e.walkProp(install)
				}
				if under := e.readingHypothesis(pr.GetReading()); under != nil {
					// A reading under a hypothesis prints that hypothesis.
					e.walkProp(under)
				}
				if pr.GetScaled() {
					e.walkTerm(e.reader.Term(pr.GetCoefficient()))
				}
				for _, w := range pr.GetWitnesses() {
					e.walkTerm(e.reader.Term(w))
				}
				for _, nw := range pr.GetNamed() {
					e.walkTerm(e.reader.Term(nw.GetTerm()))
				}
			}
		}
	}
}

func (e *_Emitter) walkProp(p core.Prop) {
	for i := range p.NumHyps() {
		e.walkTerm(p.Hyp(i))
	}
	e.walkTerm(p.Conclusion())
}

func (e *_Emitter) walkTerm(t core.Term) {
	switch t := t.Core().(type) {
	case core.VarTerm:
		k := _VarKey{t.Name(), t.Type().Key()}
		// Already-allocated (walk called after assignVarIdents drained
		// pendingVars) — nothing to do.
		if _, ok := e.varIdent[k]; ok {
			return
		}
		if e.pendingVars == nil {
			// Post-drain walk: allocate immediately with the
			// symmetric-suffix logic (via freshVarIdent, which respects
			// the same rules for single-name-multi-type disambiguation).
			ident := e.freshVarIdent(sanitizeIdent(string(t.Name())), t.Type())
			e.varIdent[k] = ident
			e.varDecl[ident] = t
			return
		}
		if _, ok := e.pendingVars[k]; ok {
			return
		}
		// Defer ident allocation to assignVarIdents (called at the end
		// of collectSymbols) so we know the complete set of (name, type)
		// instances for each HOL name. That lets multi-type names get
		// symmetric type-suffixed idents (all `_A` / `_B`) instead of
		// asymmetric first-wins-bare-second-suffixed.
		e.pendingVars[k] = t
	case core.ConstTerm:
		e.recordConst(t)
	case core.AppliedTerm:
		e.walkTerm(t.Fun())
		e.walkTerm(t.Arg())
	case core.AbsTerm:
		// HOL identifies binders by VarTerm pointer; the var instance
		// in Body() is the same as the lambda's var. Registering it
		// here gives the emitted x.To(body) a Go-scope x to refer to.
		// Distinct VarTerm pointers happening to share (name, type)
		// collapse to the same Go ident — fine for Go and rare in
		// practice (deserialized terms are alpha-renamed).
		e.walkTerm(t.Var())
		e.walkTerm(t.Body())
	}
}

func (e *_Emitter) recordConst(c core.ConstTerm) {
	if _, ok := isSpecialConst(c); ok {
		// Special consts use ext-package globals via specialConstGoAlias
		// in ext/render.go; no top-level declaration emitted here.
		return
	}
	key := _ConstKey{c.Meta().Name(), c.Type().Key()}
	if _, seen := e.constIdent[key]; seen {
		return
	}
	ident := e.freshIdent(sanitizeIdent(string(key.name)), e.declSet())
	e.constIdent[key] = ident
	e.constMeta[ident] = c.Meta()
	e.constInstType[ident] = c.Type()
}

// declSet returns the union of currently-claimed identifiers (consts +
// vars). Used by freshIdent to avoid collisions in the member's scope.
func (e *_Emitter) declSet() map[string]bool {
	out := map[string]bool{}
	for _, id := range e.constIdent {
		out[id] = true
	}
	for id := range e.varDecl {
		out[id] = true
	}
	return out
}

// isSpecialConst is the local mirror of the ext/render.go logic that
// renders a const without going through the lookupConstIdent path. Two
// shapes contribute:
//
// - specialConstGoAlias rewrites bare `⊤ / ⊥ / ¬ / ∧ / ∨ / ⇒ / ∀ /
// ∃ / ∃! / COND` to `WrapTerm(T) / WrapTerm(F) / …` directly.
// - printApp pattern-matches `App(=, …)`, `App(ε, λx.body)`,
// `App(∀, …)`, `App(∃, …)`, `App(∃!, …)`, the boolean connectives,
// and COND, rendering them via term-level forms (`l.Eq(r)`,
// `x.SuchThat(body)`, multi-binder ∀/∃, etc.) that never spell out
// the head const's identifier.
//
// In both cases, declaring a top-level `<name> := ctx.Const(...)` would
// produce a "declared and not used" compile error. Skip recording so
// the symbol-collection pass leaves it out. The full alias rendering
// lives in ext/render.go; this list must stay in lock-step.
// isSpecialConst reports whether the const needs NO ctx.Const
// declaration from the symbol-collection pass. Two sub-classes, both
// handled inside printConstRef without a registered ident:
// - print-aliased connectives (⊤⊥¬∧∨⇒∀∃∃!COND) — specialConstGoAlias
// renders a fixed ext-package global;
// - kernel primitives `=` / `ε` — full applications render via
// tryPrintConnective (.Eq / .SuchThat); leaf/PARTIAL applications
// (e.g. the eta-contracted operands `=(c) = =(COND(…))` that the
// def_expand of a constant c defined by a conditional leaves) are
// rebuilt kernel-direct as `Const(MetaEq, <type>)` — they are kernel
// primitives, not managed constants, so a ctx.Const decl would panic at
// replay.
func isSpecialConst(c core.ConstTerm) (string, bool) {
	switch string(c.Meta().Name()) {
	case "⊤", "⊥", "¬", "∧", "∨", "⇒", "∀", "∃", "∃!", "COND", "=", "ε":
		return string(c.Meta().Name()), true
	}
	return "", false
}

// ---------------------------------------------------------------------------
// Rendering the member file
// ---------------------------------------------------------------------------

// render writes the member file: a definition door when the single
// section records one, family.Theorem for one theorem section, and
// family.Sections when earlier sections tag along as the lemmas the
// statement cites.
func (e *_Emitter) render() string {
	if len(e.sections) > 1 {
		return e.renderFamilySectionsFile()
	}
	return e.renderFamilyFile()
}

// validateFamilyProfile is the admission gate, run before any source is
// rendered: every section must be a theorem whose statement reads back
// from its TEXT (family.Theorem, family.Sections and ctx.Lemma all
// parse their statement — decideSectionForms printed it), no statement
// may normalize to ⊤ (a section that Qed's a tautology cannot claim
// it), and a definition door is a member of its own — never one lemma
// among several. It declines loudly: a
// wrong scaffold pasted into a family package fails later and worse
// than an emit error does. On success it pins the member statement's
// text.
func (e *_Emitter) validateFamilyProfile() error {
	for i, s := range e.sections {
		e.reader = s.reader
		goal := e.sectionInitGoal(s)
		if normalized, _ := prop.Normalize(goal); normalized.Conclusion().Equals(ext.T) {
			return fmt.Errorf(
				"emit: section %q's statement normalizes to ⊤ — a member cannot Qed a "+
					"tautology; drop the section, or state what it was meant to establish", s.varName)
		}
		if len(e.sections) > 1 && e.isDefinitionSection(s) {
			return fmt.Errorf(
				"emit: section %q records a definition door — a definition is a member of its "+
					"own: emit it alone, and a theorem that uses it cites its entry", s.varName)
		}
		if err := e.sectionTextErr[i]; err != nil {
			return err
		}
		if _, ok := e.sectionTextForm[i]; !ok {
			return fmt.Errorf(
				"emit: section %q's statement does not round-trip through the parser — a "+
					"member statement is parsed from its text", s.varName)
		}
	}
	e.familyGoalText = e.sectionTextForm[len(e.sections)-1]
	return nil
}

// isDefinitionSection reports whether the section records one of the
// definition doors (define / define_data / define_spec / define_type)
// the single-section renderer spells as a family door call.
func (e *_Emitter) isDefinitionSection(s *_SectionEmit) bool {
	if c, _ := e.familyDefineConst(s); !c.IsZero() {
		return true
	}
	if mk, _ := e.familyDefineDataConsts(s); !mk.IsZero() {
		return true
	}
	if consts := e.familyDefineSpecConsts(s); consts != nil {
		return true
	}
	if c, _, _ := e.familyDefineInductive(s); !c.IsZero() {
		return true
	}
	if !e.familyDefineQuotientMk(s).IsZero() {
		return true
	}
	return !e.familyDefineTypeAbs(s).IsZero()
}

// familyDefineConst detects a DEFINITION section — one whose recorded
// ministep tree is the define composite at the root — and returns the
// minted const plus, for the WF shape, the measure term. The direct
// and primrec shapes are exactly one step (their obligations close
// inside the composite); the WF shape (measure set) carries the
// author's termination proof as the composite's recorded child steps,
// rendered into the DefEntry's Termination field. Nil for every other
// section.
func (e *_Emitter) familyDefineConst(s *_SectionEmit) (core.ConstTerm, core.Term) {
	if len(s.detailedSteps) == 0 {
		return core.ConstTerm{}, nil
	}
	d, ok := s.detailedSteps[0].Step.(*proof.StepProto_Define)
	if !ok || d.Define == nil {
		return core.ConstTerm{}, nil
	}
	c, _ := s.reader.Term(d.Define.GetConst()).AsConst()
	if c.IsZero() {
		return core.ConstTerm{}, nil
	}
	var measure core.Term
	if d.Define.Measure != nil {
		measure = s.reader.Term(d.Define.GetMeasure())
	}
	if measure == nil && len(s.detailedSteps) != 1 && !proof.IsQuotientLiftConst(c, managerResolver()) {
		// Only the WF and lift shapes record body steps (their
		// obligation proofs).
		return core.ConstTerm{}, nil
	}
	return c, measure
}

// managerResolver is the process-global constant registry as the
// resolver shape the definition spines read constants through.
func managerResolver() func(core.TermName) core.ConstTermMeta {
	return func(name core.TermName) core.ConstTermMeta {
		if meta, ok := registry.GetConstMetaManager().LoadConstMeta(name); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}
}

// renderFamilyDefineFile is renderFamilyFile for a definition section:
// the whole member is ONE family.Define(registry.DefEntry{…}) call —
// the equation literal serving both roles (pre-mint definition text,
// post-mint characterizing headline), the record/emit/replay principle
// at entry granularity. No Build var, no binder-closure body. Its Key
// is the characterizing statement's own (EmitOptions.EntryKey), as a
// theorem entry's is. Deps are the entries the shape reads at replay:
// the recursion schema of a corpus carrier, the WF rows, the
// termination proof's cites.
func (e *_Emitter) renderFamilyDefineFile(s *_SectionEmit, c core.ConstTerm, measure core.Term) string {
	name := strings.TrimPrefix(e.opts.FuncName, "Build_")
	if name == "" {
		name = e.opts.FuncName
	}
	// WF and lift shapes: render the obligation proof (the composite's
	// recorded child steps) FIRST — resolving its cite leaves is what
	// marks the dep names the DefEntry must declare (the
	// renderFamilyFile body-first discipline). The WF rows the
	// existence compile discharges from are deps of the same standing;
	// a lift's quotient laws are declared by family.Define itself.
	isLift := measure == nil && proof.IsQuotientLiftConst(c, managerResolver())
	var obligation string
	if measure != nil || isLift {
		root := buildMSTree(s.detailedSteps)
		var tb strings.Builder
		for _, ch := range root.children {
			e.renderStepExpr(&tb, s, ch, "\t\t")
		}
		obligation = tb.String()
	}
	if measure != nil {
		e.markDepName(proof.WFRecName, "")
		e.markDepName(proof.WFMeasureName, "")
	}
	// The DefEntry's Type field must round-trip through the type
	// parser (family.Define re-parses it at registration). Verified
	// here so a non-round-tripping type is an emit error, not a landed
	// file that panics at package init.
	// The author's own texts, when the session kept them: the type as
	// written, the equations as written. Each is re-parsed here; a text
	// that no longer reads leaves the printed form in place.
	author, hasAuthor := e.definitionText(c.Name())
	typeText := ext.FormatType(c.Type())
	if hasAuthor && author.Type != "" {
		if parsed, err := dsl.ParseTypeText(author.Type); err == nil && parsed.Equals(c.Type()) {
			typeText = author.Type
		}
	}
	if parsed, err := dsl.ParseTypeText(typeText); err != nil || !parsed.Equals(c.Type()) {
		panic(fmt.Sprintf("emit: define const %s's type %q does not round-trip "+
			"through dsl.ParseTypeText (err=%v)", c.Name(), typeText, err))
	}

	// One equation string per top-level conjunct of the characterizing
	// statement — the DefEntry's author-form list (a recursive define
	// records the ∧ of its clauses; a direct one is a single conjunct).
	// A conjunct that fails to round-trip alone falls the whole list
	// back to the single joined text. The author's equations, when kept
	// and still readable at the definition door, are the list itself.
	eqTexts := []string{e.familyGoalText}
	if conjuncts := ext.DecomposesAND(e.sectionInitGoal(s).Conclusion()); len(conjuncts) > 1 {
		split := make([]string, 0, len(conjuncts))
		for _, cj := range conjuncts {
			text, ok := e.tryTextForm(core.MakeProp(cj), false)
			if !ok {
				split = nil
				break
			}
			split = append(split, text)
		}
		if split != nil {
			eqTexts = split
		}
	}
	if hasAuthor && len(author.Equations) > 0 && definitionEquationsReparse(author.Equations, c, typeText) {
		eqTexts = author.Equations
	}
	typed, untyped := e.familyDeps()
	// A direct or recursive definition names only its own family's
	// entries in Deps (registry's checkOwnFamilyDeps): its build reads
	// nothing the door does not find itself — the recursive shape's
	// schema included — and its edge to another family's mint is read
	// off the equation. A WF or lift definition's obligation proof reads
	// what it cites, so its Deps keep every cite.
	if measure == nil && !isLift {
		own := typed[:0:0]
		for _, ref := range typed {
			if ref.ImportPath == "" {
				own = append(own, ref)
			}
		}
		typed = own
	}

	var b strings.Builder
	fmt.Fprintf(&b, "package %s\n\n", path.Base(e.opts.Family))
	renderTypedImports(&b, typed)

	fmt.Fprintf(&b, "// The defining equation(s) — also the characterizing statement once\n")
	fmt.Fprintf(&b, "// the constant is minted (family.Define reads them in both roles).\n")
	fmt.Fprintf(&b, "var %s = family.Define(registry.DefEntry{\n", name)
	fmt.Fprintf(&b, "\tName:  %q,\n", name)
	if key := e.opts.EntryKey; key != "" {
		fmt.Fprintf(&b, "\tKey:   %q,\n", string(key))
	}
	fmt.Fprintf(&b, "\tConst: %q,\n", string(c.Name()))
	fmt.Fprintf(&b, "\tType:  %q,\n", typeText)
	fmt.Fprintf(&b, "\tEquations: []string{\n")
	for _, t := range eqTexts {
		fmt.Fprintf(&b, "\t\t%q,\n", t)
	}
	fmt.Fprintf(&b, "\t},\n")
	if measure != nil {
		// The measure text re-parses at registration with no expected
		// type, so the binder annotation must be SPELLED — the printer
		// elides it as recoverable, which it only is in context. Hand-
		// compose λ<binder>:<type>. <body> and verify the round-trip
		// here (an emit error, not a landed file that panics at init).
		mAbs, okAbs := measure.AsAbsTerm()
		if !okAbs {
			panic(fmt.Sprintf("emit: WF measure %s is not a λ", ext.PrintTerm(measure)))
		}
		measureText := fmt.Sprintf("λ%s:%s. %s", mAbs.Var().Name(),
			ext.FormatType(mAbs.Var().Type()), ext.PrintTerm(mAbs.Body()))
		measureScope := &dsl.ParseScope{
			ConstResolver: func(name string) core.ConstTermMeta {
				if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(name)); ok {
					return meta
				}
				return core.ConstTermMeta{}
			},
			StrictResolution:   true,
			FreshenMetaLetters: true,
		}
		if hasAuthor && author.Measure != "" {
			aRes := dsl.ParseTermTextInScope(author.Measure, nil, measureScope, nil)
			if len(aRes.Errors) == 0 && aRes.Term.AlphaEquals(measure) {
				measureText = author.Measure
			}
		}
		mRes := dsl.ParseTermTextInScope(measureText, nil, measureScope, nil)
		if len(mRes.Errors) > 0 || !mRes.Term.AlphaEquals(measure) {
			panic(fmt.Sprintf("emit: WF measure %q does not round-trip (errors=%v)",
				measureText, mRes.Errors))
		}
		fmt.Fprintf(&b, "\tMeasure: %q,\n", measureText)
		fmt.Fprintf(&b, "\tTermination: []Action{\n%s\t},\n", obligation)
	}
	if isLift {
		fmt.Fprintf(&b, "\tRespects: []Action{\n%s\t},\n", obligation)
	}
	if deps, ok := depsFieldValue(typed, untyped); ok {
		fmt.Fprintf(&b, "\tDeps: %s,\n", deps)
	}
	fmt.Fprintf(&b, "})\n")
	return b.String()
}

// definitionText answers EmitOptions.DefinitionText for a constant, or
// ok=false when the caller kept no author texts.
func (e *_Emitter) definitionText(name core.TermName) (DefinitionText, bool) {
	if e.opts.DefinitionText == nil {
		return DefinitionText{}, false
	}
	return e.opts.DefinitionText(name)
}

// definitionEquationsReparse reports whether every author equation
// still reads at the definition door the way family.Define will read
// it at registration — the constant masked from the resolver, the
// definiendum declared at typeText. A text that does not read is not
// emitted: the printed form stands.
func definitionEquationsReparse(texts []string, c core.ConstTerm, typeText string) bool {
	base := &dsl.ParseScope{ConstResolver: func(n string) core.ConstTermMeta {
		if n == string(c.Name()) {
			return core.ConstTermMeta{}
		}
		if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(n)); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}, Syntax: registry.GetConstMetaManager()}
	for _, text := range texts {
		if _, _, err := proof.ParseDefinitionEquation(text, string(c.Name()), typeText, base); err != nil {
			return false
		}
	}
	return true
}

// familyDefineDataConsts detects a DATATYPE-DEFINITION section — one
// whose recorded ministep tree is exactly the define-data composite
// (StepProto_DefineData: one step, zero children) — and returns the
// minted mk const plus the ordered constructor consts. Nils for every
// other section.
func (e *_Emitter) familyDefineDataConsts(s *_SectionEmit) (core.ConstTerm, []core.ConstTerm) {
	if len(s.detailedSteps) != 1 {
		return core.ConstTerm{}, nil
	}
	d, ok := s.detailedSteps[0].Step.(*proof.StepProto_DefineData)
	if !ok || d.DefineData == nil {
		return core.ConstTerm{}, nil
	}
	mk, _ := s.reader.Term(d.DefineData.Mk).AsConst()
	ctors := make([]core.ConstTerm, 0, len(d.DefineData.Ctors))
	for _, ref := range d.DefineData.Ctors {
		c, okC := s.reader.Term(ref).AsConst()
		if !okC {
			return core.ConstTerm{}, nil
		}
		ctors = append(ctors, c)
	}
	if mk.IsZero() || len(ctors) == 0 {
		return core.ConstTerm{}, nil
	}
	return mk, ctors
}

// renderFamilyDefineDataFile is renderFamilyFile for a datatype
// definition section: the whole datatype is ONE
// family.DefineData(registry.DataEntry{…}) call, whose registration
// re-mints the type and re-registers the four derived-theorem entries
// — the record/emit/replay principle at entry granularity. The
// payload (name, params, constructors) is recovered from the minted
// consts' metas, the same recovery the composite's replay runs, so
// the rendered call and the recorded section cannot drift. Any of the
// datatype's four sections renders the SAME call — the chapter keeps
// one copy.
func (e *_Emitter) renderFamilyDefineDataFile(mk core.ConstTerm, ctors []core.ConstTerm) string {
	md, err := proof.RecoverMintedDatatype(mk, ctors)
	if err != nil {
		panic(fmt.Sprintf("emit: define-data section does not recover from its minted "+
			"consts: %v", err))
	}
	dd := md.Def
	name := strings.TrimPrefix(e.opts.FuncName, "Build_")
	if name == "" {
		name = e.opts.FuncName
	}

	var b strings.Builder
	fmt.Fprintf(&b, "package %s\n\n", path.Base(e.opts.Family))
	// The derived theorems' Builds read the recspace rows, the pair
	// projections and the two Peano facts off env.LibraryThms; the entry
	// declares the entries serving those names (family.DefineData gives
	// each derived entry the subset its derivation consumes).
	for _, n := range dataDefinitionLibraryNames {
		e.markDepName(n, "")
	}
	typed, untyped := e.familyDeps()
	renderTypedImports(&b, typed, "github.com/euc-ai/xugo/prover/proof")

	fmt.Fprintf(&b, "// The datatype declaration — registration re-mints the type and\n")
	fmt.Fprintf(&b, "// constructors and registers the INDUCT/RECURSION/INJ/DISTINCT entries\n")
	fmt.Fprintf(&b, "// (family.DefineData re-derives each through the define-data composite).\n")
	fmt.Fprintf(&b, "var %s = family.DefineData(registry.DataEntry{\n", name)
	fmt.Fprintf(&b, "	Name: %q,\n", name)
	fmt.Fprintf(&b, "	Type: %q,\n", string(dd.TypeName))
	if len(dd.Params) > 0 {
		fmt.Fprintf(&b, "	Params: []string{")
		for i, p := range dd.Params {
			if i > 0 {
				fmt.Fprintf(&b, ", ")
			}
			fmt.Fprintf(&b, "%q", string(p.Name()))
		}
		fmt.Fprintf(&b, "},\n")
	}
	fmt.Fprintf(&b, "	Constructors: []proof.DataConstructorSpec{\n")
	for j := range dd.Ctors {
		c := &dd.Ctors[j]
		fmt.Fprintf(&b, "		{Name: %q", string(c.Name))
		if len(c.ArgTypes) > 0 {
			fmt.Fprintf(&b, ", Args: []string{")
			for i, at := range c.ArgTypes {
				text := authorTypeText(at)
				if parsed, perr := dsl.ParseTypeText(text); perr != nil || !parsed.Equals(at) {
					panic(fmt.Sprintf("emit: constructor %s argument type %q does not "+
						"round-trip through dsl.ParseTypeText (err=%v)", c.Name, text, perr))
				}
				if i > 0 {
					fmt.Fprintf(&b, ", ")
				}
				fmt.Fprintf(&b, "%q", text)
			}
			fmt.Fprintf(&b, "}")
		}
		fmt.Fprintf(&b, "},\n")
	}
	fmt.Fprintf(&b, "	},\n")
	// The derived entries' registered names, spelled — the door derives
	// nothing by suffix. Rendered in the session's own convention
	// (`<TypeName><Induct|Recursion|Inj|Distinct>`, the names its
	// emitted members already cite before the file lands); the author
	// renames them to the chapter's words at landing, and the
	// re-export vars carry the same words (entry lint E0).
	anyArgs, ctorCount := false, len(dd.Ctors)
	for j := range dd.Ctors {
		if len(dd.Ctors[j].ArgTypes) > 0 {
			anyArgs = true
		}
	}
	base := exportedIdent(string(dd.TypeName))
	fmt.Fprintf(&b, "	Principles: registry.DataPrinciples{\n")
	fmt.Fprintf(&b, "		Induction: %q,\n", base+"Induct")
	fmt.Fprintf(&b, "		Recursion: %q,\n", base+"Recursion")
	if anyArgs {
		fmt.Fprintf(&b, "		Injective: %q,\n", base+"Inj")
	}
	if ctorCount >= 2 {
		fmt.Fprintf(&b, "		Distinct:  %q,\n", base+"Distinct")
	}
	fmt.Fprintf(&b, "	},\n")
	if deps, ok := depsFieldValue(typed, untyped); ok {
		fmt.Fprintf(&b, "	Deps: %s,\n", deps)
	}
	fmt.Fprintf(&b, "})\n")
	return b.String()
}

// exportedIdent is a minted name as an exported Go identifier
// (`zz_btree_b` → `ZzBtreeB`) — the session's convention for a
// define's entry name (engine.sessionDefineEntryName), reproduced here
// so the emitted DataEntry spells the principle names the session's
// other emitted members already cite.
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

// familyDefineInductive detects an INDUCTIVE-DEFINITION section — one
// whose recorded ministep tree is exactly the define-inductive
// composite (StepProto_DefineInductive: one step, zero children) — and
// returns the minted constant, the parameter variables and the rules
// as recorded. Nils for every other section.
func (e *_Emitter) familyDefineInductive(s *_SectionEmit) (core.ConstTerm, []core.VarTerm, []core.Term) {
	if len(s.detailedSteps) != 1 {
		return core.ConstTerm{}, nil, nil
	}
	d, ok := s.detailedSteps[0].Step.(*proof.StepProto_DefineInductive)
	if !ok || d.DefineInductive == nil {
		return core.ConstTerm{}, nil, nil
	}
	c, _ := s.reader.Term(d.DefineInductive.Const).AsConst()
	params := make([]core.VarTerm, 0, len(d.DefineInductive.Params))
	for _, ref := range d.DefineInductive.Params {
		v, okV := s.reader.Term(ref).AsVar()
		if !okV {
			return core.ConstTerm{}, nil, nil
		}
		params = append(params, v)
	}
	rules := make([]core.Term, 0, len(d.DefineInductive.Rules))
	for _, ref := range d.DefineInductive.Rules {
		rules = append(rules, s.reader.Term(ref))
	}
	if c.IsZero() || len(rules) == 0 {
		return core.ConstTerm{}, nil, nil
	}
	return c, params, rules
}

// renderFamilyDefineInductiveFile is renderFamilyFile for an inductive
// definition section: the whole definition is ONE
// family.DefineInductive(registry.InductiveEntry{…}) call, whose
// registration re-mints the relation and re-registers its entries,
// under the keys the literal spells — the record/emit/replay principle
// at entry granularity.
// The payload (the constant, the parameters, the rules) is the
// record's own, re-analyzed here exactly as the composite's replay
// re-analyzes it; any of the definition's three sections renders the
// SAME call, and the chapter keeps one copy. The rules render in the
// author's spelling when the session kept it and it still reads,
// else in the printer's, each verified to re-parse at the definition
// door to the recorded rule.
func (e *_Emitter) renderFamilyDefineInductiveFile(c core.ConstTerm, params []core.VarTerm, rules []core.Term) string {
	d, err := proof.RecoverInductiveDefinition(c, params, rules)
	if err != nil {
		panic(fmt.Sprintf("emit: define-inductive section does not recover from its record: %v", err))
	}
	name := strings.TrimPrefix(e.opts.FuncName, "Build_")
	if name == "" {
		name = e.opts.FuncName
	}
	author, hasAuthor := e.definitionText(c.Name())
	typeText := ext.FormatType(c.Type())
	if hasAuthor && author.Type != "" {
		if parsed, perr := dsl.ParseTypeText(author.Type); perr == nil && parsed.Equals(c.Type()) {
			typeText = author.Type
		}
	}
	if parsed, perr := dsl.ParseTypeText(typeText); perr != nil || !parsed.Equals(c.Type()) {
		panic(fmt.Sprintf("emit: inductive const %s's type %q does not round-trip "+
			"through dsl.ParseTypeText (err=%v)", c.Name(), typeText, perr))
	}
	paramNames := make([]string, len(params))
	for i, p := range params {
		paramNames[i] = string(p.Name())
	}
	// The rule texts re-parse at the definition door with the
	// definiendum a VARIABLE: the resolver hides the minted constant.
	ruleScope := &dsl.ParseScope{
		ConstResolver: func(n string) core.ConstTermMeta {
			if n == string(c.Name()) {
				return core.ConstTermMeta{}
			}
			if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(n)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
	}
	reparses := func(texts []string) bool {
		if len(texts) != len(rules) {
			return false
		}
		for i, text := range texts {
			r, _, _, perr := proof.ParseInductiveRule(text, string(c.Name()), typeText, paramNames, ruleScope)
			if perr != nil || !r.Conclusion().AlphaEquals(rules[i]) {
				return false
			}
		}
		return true
	}
	ruleTexts := make([]string, len(rules))
	for i, r := range rules {
		ruleTexts[i] = ext.PrintTermWithPolyBinders(r)
	}
	if hasAuthor && reparses(author.Equations) {
		ruleTexts = author.Equations
	} else if !reparses(ruleTexts) {
		panic(fmt.Sprintf("emit: the rules of %s do not round-trip through the definition door: %q",
			c.Name(), ruleTexts))
	}
	typed, untyped := e.familyDeps()

	var b strings.Builder
	fmt.Fprintf(&b, "package %s\n\n", path.Base(e.opts.Family))
	renderTypedImports(&b, typed)

	fmt.Fprintf(&b, "// The introduction rules — registration re-mints %s as the smallest\n", c.Name())
	fmt.Fprintf(&b, "// relation closed under them and registers the Rules / Induct / Cases\n")
	fmt.Fprintf(&b, "// entries (family.DefineInductive re-derives each through the composite).\n")
	fmt.Fprintf(&b, "var %s = family.DefineInductive(registry.InductiveEntry{\n", name)
	fmt.Fprintf(&b, "\tName:  %q,\n", name)
	// The keys of the entries the call registers, each its statement's
	// own: the door reads them and normalizes nothing
	// (registry.InductiveKeys).
	fmt.Fprintf(&b, "\tKeys: registry.InductiveKeys{\n")
	for _, kind := range d.Kinds() {
		normalized, _ := prop.Normalize(d.Stmt(c, kind))
		fmt.Fprintf(&b, "\t\t%s: %q,\n", kind.EntrySuffix(), string(normalized.AlphaKey()))
	}
	fmt.Fprintf(&b, "\t},\n")
	fmt.Fprintf(&b, "\tConst: %q,\n", string(c.Name()))
	fmt.Fprintf(&b, "\tType:  %q,\n", typeText)
	if len(paramNames) > 0 {
		fmt.Fprintf(&b, "\tParams: []string{")
		for i, p := range paramNames {
			if i > 0 {
				fmt.Fprintf(&b, ", ")
			}
			fmt.Fprintf(&b, "%q", p)
		}
		fmt.Fprintf(&b, "},\n")
	}
	fmt.Fprintf(&b, "\tRules: []string{\n")
	for _, t := range ruleTexts {
		fmt.Fprintf(&b, "\t\t%q,\n", t)
	}
	fmt.Fprintf(&b, "\t},\n")
	if deps, ok := depsFieldValue(typed, untyped); ok {
		fmt.Fprintf(&b, "\tDeps: %s,\n", deps)
	}
	fmt.Fprintf(&b, "})\n")
	return b.String()
}

// dataDefinitionLibraryNames are the library names a datatype's derived
// theorems read at replay (prover/proof define_data): the recspace
// encoding rows, the pair projections and Peano's two constructor
// facts. Every DefineData declares the entries serving them.
var dataDefinitionLibraryNames = []string{
	"recspace_recursion", "recspace_node_injective", "family_cons_definition", "suc_not_zero", "suc_injective", "pair_injective",
	proof.SpecFstName, proof.SpecSndName,
}

// familyDefineSpecConsts detects a SPEC-DEFINITION section — one whose
// recorded ministep tree is the define-spec composite at the root
// (StepProto_DefineSpec) — and returns the spec constants in
// definition order. The composite's recorded child steps are the
// author's pointwise-existence proof (the obligation is ALWAYS the
// author's — the spec shape is the WF branch's degenerate form),
// rendered into the SpecEntry's Existence field. Nil for every other
// section.
func (e *_Emitter) familyDefineSpecConsts(s *_SectionEmit) []core.ConstTerm {
	if len(s.detailedSteps) == 0 {
		return nil
	}
	d, ok := s.detailedSteps[0].Step.(*proof.StepProto_DefineSpec)
	if !ok || d.DefineSpec == nil {
		return nil
	}
	consts := make([]core.ConstTerm, 0, len(d.DefineSpec.Consts))
	for _, ref := range d.DefineSpec.Consts {
		c, okC := s.reader.Term(ref).AsConst()
		if !okC {
			return nil
		}
		consts = append(consts, c)
	}
	if len(consts) == 0 {
		return nil
	}
	return consts
}

// renderFamilyDefineSpecFile is renderFamilyFile for a spec definition
// section: the whole member is ONE family.DefineSpec(registry.
// SpecEntry{…}) call — the Spec literal serving both roles (pre-mint
// specification text, post-mint characterizing headline), the
// Existence actions the author's recorded obligation proof, and the
// entry's Key the characterizing statement's own
// (EmitOptions.EntryKey). The emitted entry serves BOTH provenances by
// construction: in a clean process registration re-mints the
// constants (FRESH); in a process where they are already registered —
// this one's replay included — it claims them (CLAIM).
func (e *_Emitter) renderFamilyDefineSpecFile(s *_SectionEmit, consts []core.ConstTerm) string {
	name := strings.TrimPrefix(e.opts.FuncName, "Build_")
	if name == "" {
		name = e.opts.FuncName
	}
	// The existence proof (the composite's recorded child steps)
	// renders FIRST — resolving its cite leaves is what marks the dep
	// names the SpecEntry must declare (the renderFamilyFile
	// body-first discipline; the WF Termination path). It renders into
	// the ctx-hosted ExistenceBody form: the SpecEntry value list is a
	// struct-literal position with no Script in scope, and a real
	// existence proof references declared consts/vars and env-bound
	// constructors.
	root := buildMSTree(s.detailedSteps)
	var eb strings.Builder
	for _, ch := range root.children {
		e.renderStepExpr(&eb, s, ch, "\t\t\t")
	}
	existence := eb.String()
	// The declarations the body references (ctx.Const registration +
	// var bindings) — the renderFamilyBody prelude, re-hosted at the
	// closure's depth.
	var decls strings.Builder
	e.renderDecls(&decls)
	declText := indentLines(decls.String(), "\t")

	// Per-constant name/type texts; each type must round-trip through
	// the type parser (family.DefineSpec re-parses it at registration).
	masked := make(map[string]bool, len(consts))
	names := make([]string, len(consts))
	typeTexts := make([]string, len(consts))
	// The author's spec text, when the session kept it (recorded per
	// constant; one statement for the group).
	var authorSpec string
	for i, c := range consts {
		names[i] = string(c.Name())
		masked[names[i]] = true
		typeTexts[i] = ext.FormatType(c.Type())
		if author, ok := e.definitionText(c.Name()); ok {
			if parsed, err := dsl.ParseTypeText(author.Type); author.Type != "" && err == nil && parsed.Equals(c.Type()) {
				typeTexts[i] = author.Type
			}
			if author.Spec != "" {
				authorSpec = author.Spec
			}
		}
		if parsed, err := dsl.ParseTypeText(typeTexts[i]); err != nil || !parsed.Equals(c.Type()) {
			panic(fmt.Sprintf("emit: spec const %s's type %q does not round-trip "+
				"through dsl.ParseTypeText (err=%v)", c.Name(), typeTexts[i], err))
		}
	}

	// The Spec literal must round-trip through the FRESH parse: the
	// emitted entry registers in a clean process by re-minting, while
	// this process's own parse (validateFamilyProfile's) ran with the
	// constants registered. Mask them from the resolver and verify the
	// definiendum-variable parse maps back onto the recorded goal
	// under defVar ↦ const substitution — an emit error, not a landed
	// file that panics at package init. The author's text is preferred
	// when it passes the same check; the printed form must pass it.
	goal := e.sectionInitGoal(s)
	freshBase := &dsl.ParseScope{ConstResolver: func(n string) core.ConstTermMeta {
		if masked[n] {
			return core.ConstTermMeta{}
		}
		if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(n)); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}}
	specReparses := func(text string) error {
		stmt, defVars, err := proof.ParseSpecStatement(text, names, typeTexts, freshBase)
		if err != nil {
			return fmt.Errorf("spec statement %q does not re-parse in the fresh "+
				"(definiendum-variable) form: %v", text, err)
		}
		reconstructed := stmt.Conclusion()
		for i, dv := range defVars {
			reconstructed = reconstructed.Substitute(core.MakeTermSubst(dv, consts[i]))
		}
		if !reconstructed.AlphaEquals(goal.Conclusion()) {
			return fmt.Errorf("spec statement %q re-parses but does not map back "+
				"onto the recorded characterizing goal under the definiendum "+
				"substitution\n  reparsed: %s\n  goal:     %s",
				text, ext.PrintTerm(reconstructed), ext.PrintTerm(goal.Conclusion()))
		}
		return nil
	}
	specText := e.familyGoalText
	if authorSpec != "" && specReparses(authorSpec) == nil {
		specText = authorSpec
	} else if err := specReparses(specText); err != nil {
		panic("emit: " + err.Error())
	}
	// A specification applying a constant at a pair literal compiles
	// through the served fst/snd rows: the entry declares the entries
	// serving them.
	if sd, err := proof.AnalyzeSpecGoal(goal, consts); err == nil && specAppliesAtPairLiteral(sd) {
		e.markDepName(proof.SpecFstName, "")
		e.markDepName(proof.SpecSndName, "")
	}
	typed, untyped := e.familyDeps()

	var b strings.Builder
	fmt.Fprintf(&b, "package %s\n\n", path.Base(e.opts.Family))
	renderTypedImports(&b, typed)

	fmt.Fprintf(&b, "// The specification — also the characterizing statement once the\n")
	fmt.Fprintf(&b, "// constants are minted (family.DefineSpec reads it in both roles);\n")
	fmt.Fprintf(&b, "// the Existence actions close the pointwise obligation, the author's\n")
	fmt.Fprintf(&b, "// mathematics.\n")
	fmt.Fprintf(&b, "var %s = family.DefineSpec(registry.SpecEntry{\n", name)
	fmt.Fprintf(&b, "\tName: %q,\n", name)
	if key := e.opts.EntryKey; key != "" {
		fmt.Fprintf(&b, "\tKey:  %q,\n", string(key))
	}
	fmt.Fprintf(&b, "\tConsts: []registry.SpecConst{\n")
	for i := range consts {
		fmt.Fprintf(&b, "\t\t{Const: %q, Type: %q},\n", names[i], typeTexts[i])
	}
	fmt.Fprintf(&b, "\t},\n")
	fmt.Fprintf(&b, "\tSpec: %q,\n", specText)
	fmt.Fprintf(&b, "\tExistenceBody: func(ctx *Script) []Action {\n")
	b.WriteString(declText)
	fmt.Fprintf(&b, "\t\treturn []Action{\n%s\t\t}\n", existence)
	fmt.Fprintf(&b, "\t},\n")
	if deps, ok := depsFieldValue(typed, untyped); ok {
		fmt.Fprintf(&b, "\tDeps: %s,\n", deps)
	}
	fmt.Fprintf(&b, "})\n")
	return b.String()
}

// specAppliesAtPairLiteral reports whether any constant of the spec is
// applied at a pair literal — the shapes whose compile reads the served
// fst/snd rows.
func specAppliesAtPairLiteral(sd *proof.SpecDefinition) bool {
	for _, args := range sd.AppArgs {
		for _, a := range args {
			head, hargs := ext.MatchesApply(a)
			if hc, ok := head.AsConst(); ok && len(hargs) == 2 && hc.Name() == ext.CommaConstMeta.Name() {
				return true
			}
		}
	}
	return false
}

// authorTypeText renders a type in the author's spelling: FormatType's
// canonical text with single-letter type variables written bare (the
// DSL's convenience form — `A`, not `var:A`). Multi-letter variable
// names keep the var: prefix, which the parser requires for them.
func authorTypeText(t core.HolType) string {
	return singleLetterVarRe.ReplaceAllString(ext.FormatType(t), "$1")
}

var singleLetterVarRe = regexp.MustCompile(`var:([A-Z])\b`)

// familyDefineTypeAbs detects a TYPE-DEFINITION section — one whose
// recorded ministep tree is the define-type composite at the root
// (StepProto_DefineType) — and returns the minted abs const. Nil for
// every other section.
func (e *_Emitter) familyDefineTypeAbs(s *_SectionEmit) core.ConstTerm {
	if len(s.detailedSteps) == 0 {
		return core.ConstTerm{}
	}
	d, ok := s.detailedSteps[0].Step.(*proof.StepProto_DefineType)
	if !ok || d.DefineType == nil {
		return core.ConstTerm{}
	}
	abs, _ := s.reader.Term(d.DefineType.Abs).AsConst()
	return abs
}

// renderFamilyDefineTypeFile is renderFamilyFile for a type-definition
// section: the whole type is ONE family.DefineType(registry.TypeEntry{…})
// call, whose registration re-mints the type with its abs/rep pair and
// re-registers the Retraction and Membership entries — the
// record/emit/replay principle at entry granularity. The payload (the
// predicate, the inhabitation's form, the witness) is recovered from
// the abs const's meta, the same recovery the composite's replay runs,
// so the rendered call and the recorded section cannot drift; either
// of the type's two sections renders the SAME call. The inhabitation —
// the composite's one child, a known-theorem cite of the statement the
// author proved before the define — renders as the Existence dep,
// named as the leaf resolves: a landed entry, else the session
// convention `<Type>Inhabited`, renamed at landing.
func (e *_Emitter) renderFamilyDefineTypeFile(s *_SectionEmit, abs core.ConstTerm) string {
	md, err := proof.RecoverMintedTypedef(abs)
	if err != nil {
		panic(fmt.Sprintf("emit: define-type section does not recover from its minted abs const: %v", err))
	}
	td := md.Def
	name := strings.TrimPrefix(e.opts.FuncName, "Build_")
	if name == "" {
		name = e.opts.FuncName
	}
	freshScope := &dsl.ParseScope{
		ConstResolver: func(n string) core.ConstTermMeta {
			if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(n)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		StrictResolution:   true,
		StrictMint:         true,
		FreshenMetaLetters: true,
	}
	// The predicate text re-parses at registration with no expected
	// type, so a λ's binder annotation must be SPELLED — the printer
	// elides it as recoverable, which it only is in context (the WF
	// measure's rule). Round-trip verified here: an emit error, not a
	// landed file that panics at package init.
	predText := ext.PrintTerm(td.Pred)
	if !td.PredAbs.IsZero() {
		binderType := ext.FormatType(td.PredAbs.Var().Type())
		if strings.Contains(binderType, "→") {
			binderType = "(" + binderType + ")"
		}
		predText = fmt.Sprintf("λ%s:%s. %s", td.PredAbs.Var().Name(), binderType, ext.PrintTerm(td.PredAbs.Body()))
	}
	pRes := dsl.ParseTermTextInScope(predText, nil, freshScope, nil)
	if len(pRes.Errors) > 0 || !pRes.Term.Core().AlphaEquals(td.Pred) {
		panic(fmt.Sprintf("emit: type-definition predicate %q does not round-trip (errors=%v)", predText, pRes.Errors))
	}
	witnessText := ""
	if td.Witness != nil {
		witnessText = ext.PrintTerm(td.Witness)
		wRes := dsl.ParseTermTextInScope(witnessText, nil, freshScope, td.Rho)
		if len(wRes.Errors) > 0 || !wRes.Term.Core().AlphaEquals(td.Witness) {
			panic(fmt.Sprintf("emit: type-definition witness %q does not round-trip (errors=%v)", witnessText, wRes.Errors))
		}
	}

	// The inhabitation dep: the composite's one child, resolved as the
	// leaf it is (a landed entry by key, else the session-define tier's
	// conventional name) — marked so it is a declared dep, and spelled
	// as the Existence field.
	existenceExpr := ""
	if !td.Trivial {
		root := buildMSTree(s.detailedSteps)
		if root == nil || len(root.children) != 1 {
			panic("emit: a type-definition section with a proved inhabitation records exactly one child")
		}
		known, ok := root.children[0].step.Step.(*proof.StepProto_KnownThm)
		if !ok || known.KnownThm == nil {
			panic("emit: the type definition's inhabitation child is not a known-theorem cite")
		}
		stronger, _ := s.reader.Prop(known.KnownThm.GetStrongerGoal())
		leaf, resolved := e.resolveExternalLeafProp(stronger)
		switch {
		case resolved && leaf.Kind == LeafLibraryThm && leaf.ThmName != "":
			e.markDepName(leaf.ThmName, leaf.Key)
			if e.opts.FamilyDepEntry != nil {
				if ref, ok := e.opts.FamilyDepEntry(leaf.ThmName, leaf.Key); ok {
					existenceExpr = ref.Expr
				}
			}
			if existenceExpr == "" {
				existenceExpr = fmt.Sprintf("/* TODO: no entry proves %s — land the inhabitation first */ nil", leaf.ThmName)
			}
		default:
			existenceExpr = fmt.Sprintf("/* TODO: the inhabitation %s is not a landed entry — land it first */ nil",
				ext.PrintTerm(stronger.Conclusion()))
		}
	}
	typed, untyped := e.familyDeps()
	// The door adds Existence to the entries' deps itself; the Deps
	// field lists the rest.
	rest := make([]FamilyDepRef, 0, len(typed))
	for _, ref := range typed {
		if ref.Expr != existenceExpr {
			rest = append(rest, ref)
		}
	}

	var b strings.Builder
	fmt.Fprintf(&b, "package %s\n\n", path.Base(e.opts.Family))
	renderTypedImports(&b, typed)

	fmt.Fprintf(&b, "// The type declaration — registration re-mints the type with its\n")
	fmt.Fprintf(&b, "// abs/rep pair and registers the Retraction/Membership entries\n")
	fmt.Fprintf(&b, "// (family.DefineType re-derives each through the define-type composite).\n")
	fmt.Fprintf(&b, "var %s = family.DefineType(registry.TypeEntry{\n", name)
	fmt.Fprintf(&b, "\tName: %q,\n", exportedTypeName(string(md.Meta.Name())))
	fmt.Fprintf(&b, "\tType: %q,\n", string(md.Meta.Name()))
	fmt.Fprintf(&b, "\tAbs:  %q,\n", string(md.Abs.Name()))
	fmt.Fprintf(&b, "\tRep:  %q,\n", string(md.Rep.Name()))
	fmt.Fprintf(&b, "\tPred: %q,\n", predText)
	if existenceExpr != "" {
		fmt.Fprintf(&b, "\tExistence: %s,\n", existenceExpr)
	}
	if witnessText != "" {
		fmt.Fprintf(&b, "\tWitness: %q,\n", witnessText)
	}
	if deps, ok := depsFieldValue(rest, untyped); ok {
		fmt.Fprintf(&b, "\tDeps: %s,\n", deps)
	}
	fmt.Fprintf(&b, "})\n")
	return b.String()
}

// exportedTypeName is the entry base name a type definition registers
// under: the type name in exported CamelCase (zz_pos_t → ZzPosT) — the
// convention the chapters follow (int → Int, prod → Prod).
func exportedTypeName(typeName string) string {
	var b strings.Builder
	up := true
	for _, r := range typeName {
		switch {
		case r == '_':
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

// familyDefineQuotientMk detects a QUOTIENT-DEFINITION section — one
// whose recorded ministep tree is the define-quotient composite at the
// root (StepProto_DefineQuotient) — and returns the minted class map.
// Nil for every other section.
func (e *_Emitter) familyDefineQuotientMk(s *_SectionEmit) core.ConstTerm {
	if len(s.detailedSteps) == 0 {
		return core.ConstTerm{}
	}
	d, ok := s.detailedSteps[0].Step.(*proof.StepProto_DefineQuotient)
	if !ok || d.DefineQuotient == nil {
		return core.ConstTerm{}
	}
	mk, _ := s.reader.Term(d.DefineQuotient.Mk).AsConst()
	return mk
}

// renderFamilyDefineQuotientFile is renderFamilyFile for a quotient
// definition section: the whole quotient is ONE
// family.DefineQuotient(registry.QuotientEntry{…}) call, whose
// registration re-mints the type with its class map and abs/rep pair
// and re-registers the seven entries — the record/emit/replay
// principle at entry granularity. The payload (the relation, the
// carrier) is recovered from the class map's meta, the same recovery
// the composite's replay runs, so the rendered call and the recorded
// section cannot drift; any of the seven sections renders the SAME
// call. The equivalence — the composite's one child, a known-theorem
// cite of the statement the author proved before the define — renders
// as the Equivalence dep, named as the leaf resolves: a landed entry,
// else the session convention `<Relation>Equivalence`, renamed at
// landing.
func (e *_Emitter) renderFamilyDefineQuotientFile(s *_SectionEmit, mk core.ConstTerm) string {
	mq, err := proof.RecoverMintedQuotient(mk, managerResolver())
	if err != nil {
		panic(fmt.Sprintf("emit: define-quotient section does not recover from its minted class map: %v", err))
	}
	name := strings.TrimPrefix(e.opts.FuncName, "Build_")
	if name == "" {
		name = e.opts.FuncName
	}
	freshScope := &dsl.ParseScope{
		ConstResolver: func(n string) core.ConstTermMeta {
			if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(n)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		Syntax:             registry.GetConstMetaManager(),
		StrictResolution:   true,
		StrictMint:         true,
		FreshenMetaLetters: true,
	}
	// The relation text re-parses at registration; round-trip verified
	// here — an emit error, not a landed file that panics at init.
	relText := ext.PrintTerm(mq.Def.Rel)
	if parsed, perr := proof.ParseQuotientRelation(relText, freshScope); perr != nil || !parsed.AlphaEquals(mq.Def.Rel) {
		panic(fmt.Sprintf("emit: quotient relation %q does not round-trip (err=%v)", relText, perr))
	}

	// The equivalence dep: the composite's one child, resolved as the
	// leaf it is (a landed entry by key, else the session-define tier's
	// conventional name) — marked so it is a declared dep, and spelled
	// as the Equivalence field.
	root := buildMSTree(s.detailedSteps)
	if root == nil || len(root.children) != 1 {
		panic("emit: a quotient-definition section records exactly one child, the equivalence")
	}
	known, ok := root.children[0].step.Step.(*proof.StepProto_KnownThm)
	if !ok || known.KnownThm == nil {
		panic("emit: the quotient definition's equivalence child is not a known-theorem cite")
	}
	stronger, _ := s.reader.Prop(known.KnownThm.GetStrongerGoal())
	leaf, resolved := e.resolveExternalLeafProp(stronger)
	equivalenceExpr := ""
	switch {
	case resolved && leaf.Kind == LeafLibraryThm && leaf.ThmName != "":
		e.markDepName(leaf.ThmName, leaf.Key)
		if e.opts.FamilyDepEntry != nil {
			if ref, ok := e.opts.FamilyDepEntry(leaf.ThmName, leaf.Key); ok {
				equivalenceExpr = ref.Expr
			}
		}
		if equivalenceExpr == "" {
			equivalenceExpr = fmt.Sprintf("/* TODO: no entry proves %s — land the equivalence first */ nil", leaf.ThmName)
		}
	default:
		equivalenceExpr = fmt.Sprintf("/* TODO: the equivalence %s is not a landed entry — land it first */ nil",
			ext.PrintTerm(stronger.Conclusion()))
	}
	typed, untyped := e.familyDeps()
	// The door adds Equivalence to the entries' deps itself; the Deps
	// field lists the rest.
	rest := make([]FamilyDepRef, 0, len(typed))
	for _, ref := range typed {
		if ref.Expr != equivalenceExpr {
			rest = append(rest, ref)
		}
	}

	var b strings.Builder
	fmt.Fprintf(&b, "package %s\n\n", path.Base(e.opts.Family))
	renderTypedImports(&b, typed)

	fmt.Fprintf(&b, "// The quotient declaration — registration re-mints the type with its\n")
	fmt.Fprintf(&b, "// class map and abs/rep pair and registers the seven entries\n")
	fmt.Fprintf(&b, "// (family.DefineQuotient re-derives each through the define-quotient composite).\n")
	fmt.Fprintf(&b, "var %s = family.DefineQuotient(registry.QuotientEntry{\n", name)
	fmt.Fprintf(&b, "\tName:     %q,\n", exportedTypeName(string(mq.Meta.Name())))
	fmt.Fprintf(&b, "\tType:     %q,\n", string(mq.Meta.Name()))
	fmt.Fprintf(&b, "\tMk:       %q,\n", string(mq.Mk.Name()))
	fmt.Fprintf(&b, "\tAbs:      %q,\n", string(mq.Abs.Name()))
	fmt.Fprintf(&b, "\tRep:      %q,\n", string(mq.Rep.Name()))
	fmt.Fprintf(&b, "\tRelation: %q,\n", relText)
	fmt.Fprintf(&b, "\tEquivalence: %s,\n", equivalenceExpr)
	if deps, ok := depsFieldValue(rest, untyped); ok {
		fmt.Fprintf(&b, "\tDeps: %s,\n", deps)
	}
	fmt.Fprintf(&b, "})\n")
	return b.String()
}

// definitionDoorCall names the chapter door call a definition
// composite renders as, for the routing message above.
func definitionDoorCall(step *proof.StepProto) string {
	switch step.Step.(type) {
	case *proof.StepProto_Define:
		return "family.Define(registry.DefEntry{…})"
	case *proof.StepProto_DefineData:
		return "family.DefineData(registry.DataEntry{…})"
	case *proof.StepProto_DefineSpec:
		return "family.DefineSpec(registry.SpecEntry{…})"
	case *proof.StepProto_DefineType:
		return "family.DefineType(registry.TypeEntry{…})"
	case *proof.StepProto_DefineInductive:
		return "family.DefineInductive(registry.InductiveEntry{…})"
	case *proof.StepProto_DefineQuotient:
		return "family.DefineQuotient(registry.QuotientEntry{…})"
	}
	return "a family door"
}

// renderFamilyFile renders a single-section member: the definition
// door its `define` step records, the Instance door for a structure
// instance proved conjunct by conjunct (readInstanceDoor), or the
// family.Add entry var with a family.Theorem binder closure.
func (e *_Emitter) renderFamilyFile() string {
	s := e.sections[0]
	e.reader = s.reader
	if c, measure := e.familyDefineConst(s); !c.IsZero() {
		return e.renderFamilyDefineFile(s, c, measure)
	}
	if mk, ctors := e.familyDefineDataConsts(s); !mk.IsZero() {
		return e.renderFamilyDefineDataFile(mk, ctors)
	}
	if consts := e.familyDefineSpecConsts(s); consts != nil {
		return e.renderFamilyDefineSpecFile(s, consts)
	}
	if abs := e.familyDefineTypeAbs(s); !abs.IsZero() {
		return e.renderFamilyDefineTypeFile(s, abs)
	}
	if c, params, rules := e.familyDefineInductive(s); !c.IsZero() {
		return e.renderFamilyDefineInductiveFile(c, params, rules)
	}
	if mk := e.familyDefineQuotientMk(s); !mk.IsZero() {
		return e.renderFamilyDefineQuotientFile(s, mk)
	}
	if door, ok := e.readInstanceDoor(s); ok {
		return e.renderFamilyInstanceFile(s, door)
	}
	if door, ok := e.readLawDoor(s); ok {
		return e.renderFamilyLawFile(s, door)
	}
	name := e.memberName()

	// The opening strips are the closure's parameters (emit_signature.go):
	// the body renders from the first step after them, the Skolems
	// they minted the parameters' names.
	binding := e.sectionLifts[0]
	if binding.bound() {
		e.installBinding(binding)
	}

	// The body renders FIRST, into a scratch buffer: resolving its
	// external leaves is what populates depNames/depKeys, and the
	// family.Add block ABOVE the body lists exactly those deps.
	var body strings.Builder
	e.renderFamilyBodyFrom(&body, s, binding.rest)
	typed, untyped := e.entryDeps()

	cards := e.renderCardEntries()
	var b strings.Builder
	e.renderFamilyPrelude(&b, typed, s)
	b.WriteString(cards)
	// The Build constructor call is the entry literal's LAST field,
	// inline: one declaration per entry (chapter_constitution.md
	// §"Entries and dependencies"; the entry lint rejects a separate
	// Build_<N> var the literal references by name). The statement is
	// its first argument, inline too: a hoisted `<name>GoalText` const
	// is for a text several sites must agree on character for
	// character, and the statement has one site.
	var build strings.Builder
	fmt.Fprintf(&build, "family.Theorem(%s,\n", e.headlineArg("\t"))
	if opening, ok := openingBody(s, body.String()); ok && !binding.bound() {
		fmt.Fprintf(&build, "\t\t%s)", opening)
		e.renderFamilyEntry(&b, name, untyped, "", build.String())
		return b.String()
	}
	fmt.Fprintf(&build, "\t\tfunc(%s *Argument%s) {\n", e.deriveReceiver(0), e.boundSignature(binding))
	build.WriteString(indentLines(body.String(), "\t"))
	fmt.Fprintf(&build, "\t\t})")
	var binderComment strings.Builder
	if !binding.bound() {
		e.renderFamilyBinderComment(&binderComment, s)
	}
	e.renderFamilyEntry(&b, name, untyped, indentLines(binderComment.String(), "\t"), build.String())
	return b.String()
}

// boundSignature is a lift's parameter list as the closure declares it
// after its receiver, a Fact parameter nothing names written `_`.
func (e *_Emitter) boundSignature(binding *sectionBinding) string {
	if !binding.bound() {
		return ""
	}
	for _, h := range binding.hyps {
		if h.used {
			continue
		}
		for _, p := range binding.params {
			for i, name := range p.names {
				if !p.term && name == h.handle {
					p.names[i] = "_"
				}
			}
		}
	}
	return binding.signature()
}

// openingBody reads a single-section body as the Opening door: a root
// that unfolds one definition and an unfolded goal one action closes is
// the statement read through that definition, which a chapter writes
// `Opening(Unfold(…), <close>)` — the opening runs on the section root
// and the one-Action body closes what it leaves (proof.Opening), the
// same recorded steps as the a.Do the closure form renders. body is
// what renderFamilyBody wrote; the door has no closure, so a body that
// declares anything or reads ctx keeps the closure form.
func openingBody(s *_SectionEmit, body string) (string, bool) {
	if len(s.detailedSteps) == 0 {
		return "", false
	}
	if _, unfolds := s.detailedSteps[0].Step.(*proof.StepProto_DefExpand); !unfolds {
		return "", false
	}
	const open, close = "\t\ta.Do(\n", "\t\t)\n"
	if !strings.HasPrefix(body, open) || !strings.HasSuffix(body, close) || strings.Contains(body, "ctx.") {
		return "", false
	}
	items := topLevelItems(strings.TrimSuffix(strings.TrimPrefix(body, open), close), "\t\t\t")
	if len(items) != 2 || strings.Contains(items[0], "\n") || !strings.HasPrefix(items[0], "Unfold(") {
		return "", false
	}
	unfold := strings.TrimSuffix(items[0], ",")
	closing := strings.TrimSuffix(items[1], ",")
	if !strings.Contains(closing, "\n") {
		return fmt.Sprintf("Opening(%s, %s)", unfold, closing), true
	}
	return fmt.Sprintf("Opening(%s,\n%s\t\t)", unfold, indentLines(closing+",\n", "\t\t\t")), true
}

// topLevelItems splits a rendered action list — one action per item,
// each item's first line at indent and its continuation lines deeper —
// into its items, the indent stripped from every line of each.
func topLevelItems(list, indent string) []string {
	var items []string
	for _, line := range strings.SplitAfter(list, "\n") {
		if line == "" {
			continue
		}
		if !strings.HasPrefix(line, indent) {
			return nil
		}
		rest := strings.TrimPrefix(line, indent)
		if !strings.HasPrefix(rest, "\t") && !strings.HasPrefix(rest, ")") && !strings.HasPrefix(rest, "//") || len(items) == 0 {
			items = append(items, strings.TrimSuffix(rest, "\n"))
			continue
		}
		items[len(items)-1] += "\n" + strings.TrimSuffix(rest, "\n")
	}
	return items
}

// lawDoor is a single-section member read as a LAW of a structure
// (registry.Structure.Law): the structure's var, the law's body text,
// the structure hypothesis, and the node the body's proof starts at.
type lawDoor struct {
	structure  FamilyDepRef
	bodyText   string
	hypothesis core.Prop
	rest       *msNode
	// body is the law's body as the statement spells it, the components
	// replaced by the variables the strip minted — what the body's own
	// leading binders are read against (readSectionBinding).
	body core.Term
	// components maps each component's minted variable, by name, to
	// the component's binder in the statement.
	components map[string]string
}

// readLawDoor reports whether section s is a law the Law door states,
// and reads it. The door binds the structure's components and its
// hypothesis before the body runs — the components minted as a
// strip-all mints them — so s qualifies when
//
//   - its goal is hypothesis-free and reads `∀<components>.
//     <predicate>(<components>) ⇒ <body>`: the leading binders are
//     exactly the predicate's arguments, in order, and the predicate is
//     a structure's (EmitOptions.Structure) whose door the family
//     states members through (EmitOptions.StructureDoorInUse);
//   - its first recorded steps are the strip of those binders and of
//     the antecedent (StripQuant, StripImp), which the door's binding
//     takes the place of; and
//   - its headline, the statement in the standard form, opens as the
//     door's statement does — the body is what follows (lawBody) — and
//     the door's statement at that body is the member: it reads back to
//     the statement's key (EmitOptions.LawStatement).
func (e *_Emitter) readLawDoor(s *_SectionEmit) (lawDoor, bool) {
	if e.opts.Structure == nil || e.opts.LawStatement == nil {
		return lawDoor{}, false
	}
	goal := e.sectionInitGoal(s)
	if goal == nil || goal.NumHyps() != 0 {
		return lawDoor{}, false
	}
	var binders []core.Term
	t := goal.Conclusion()
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		binders = append(binders, abs.Var())
		t = abs.Body()
	}
	ante, _, ok := ext.MatchesIMPLY(t)
	if !ok || len(binders) == 0 {
		return lawDoor{}, false
	}
	head, args := ext.MatchesApply(ante)
	pred, isConst := head.AsConst()
	if !isConst || len(args) != len(binders) {
		return lawDoor{}, false
	}
	for i, arg := range args {
		if !arg.AlphaEquals(binders[i]) {
			return lawDoor{}, false
		}
	}
	structure, ok := e.opts.Structure(string(pred.Name()))
	if !ok || e.opts.StructureDoorInUse != nil && !e.opts.StructureDoorInUse(string(pred.Name())) {
		return lawDoor{}, false
	}
	root := e.foldFinallyTails(buildMSTree(s.detailedSteps))
	sq, isStrip := root.step.Step.(*proof.StepProto_StripQuant)
	if !isStrip || (sq.StripQuant != nil && sq.StripQuant.HypIndex != nil) || len(root.children) != 1 {
		return lawDoor{}, false
	}
	imp := root.children[0]
	if _, isImp := imp.step.Step.(*proof.StepProto_StripImp); !isImp || len(imp.children) != 1 {
		return lawDoor{}, false
	}
	stripped, _ := e.reader.Prop(imp.step.Goal)
	if stripped == nil {
		return lawDoor{}, false
	}
	hypAnte, _, ok := ext.MatchesIMPLY(stripped.Conclusion())
	if !ok {
		return lawDoor{}, false
	}
	body, ok := e.lawBody(string(pred.Name()), e.familyGoalText)
	if !ok {
		return lawDoor{}, false
	}
	statement, ok := e.opts.LawStatement(string(pred.Name()), body)
	if !ok {
		return lawDoor{}, false
	}
	scope := e.textDoorScope(goal)
	if read := dsl.ParsePropTextAtDoor(statement, scope); len(read.Errors) > 0 || registry.KeyOf(read.Prop) != registry.KeyOf(goal) {
		return lawDoor{}, false
	}
	components := map[string]string{}
	var substs []core.TermSubst
	if _, minted := ext.MatchesApply(hypAnte); len(minted) == len(binders) {
		for i, arg := range minted {
			v, isVar := arg.AsVar()
			binder, isBinder := binders[i].AsVar()
			if isVar && isBinder {
				components[string(v.Name())] = string(binder.Name())
				substs = append(substs, core.MakeTermSubst(binder, v))
			}
		}
	}
	_, lawBody, _ := ext.MatchesIMPLY(t)
	return lawDoor{structure: structure, bodyText: body, hypothesis: core.MakeProp(hypAnte), rest: imp.children[0],
		body: lawBody.Substitute(substs...), components: components}, true
}

// lawBody is the body of statement — a member's statement in the
// standard form — as a law of the structure predicate names: what
// follows the door's opening, the door's statement at ⊤
// (EmitOptions.LawStatement), where the statement opens as it does
// (dsl.Statement.AfterPrefix) — its first binders the components, its
// first hypothesis the predicate at them where the bundle syntax does
// not fold it into the binder; false where it does not.
func (e *_Emitter) lawBody(predicate, statement string) (string, bool) {
	opening, ok := e.opts.LawStatement(predicate, "⊤")
	if !ok {
		return "", false
	}
	prefix, ok := dsl.SplitStatement(opening)
	if !ok {
		return "", false
	}
	parts, ok := dsl.SplitStatement(statement)
	if !ok {
		return "", false
	}
	body, ok := parts.AfterPrefix(prefix)
	if !ok {
		return "", false
	}
	text, err := body.Text()
	return text, err == nil
}

// renderFamilyLawFile renders a member read as a structure's law
// (readLawDoor) through the door: `<Structure>.Law(<body>, …)`, the
// proof a closure receiving the structure hypothesis as a Fact — a
// premise that is the hypothesis, resident or read under, is that Fact
// — or, where the body is one action that names no hypothesis and
// needs no declaration, that action.
func (e *_Emitter) renderFamilyLawFile(s *_SectionEmit, door lawDoor) string {
	name := e.memberName()
	taken := e.declSet()
	e.lawHypothesis, e.lawHandle = door.hypothesis, e.freshIdent("h", taken)
	defer func() { e.lawHypothesis, e.lawHandle = nil, "" }()
	e.lawHandleUsed = false
	// The hypothesis is the structure's typed fact where its carriers
	// are components the `on` vocabulary has letters for; the body's own
	// leading binders are the closure's further parameters
	// (emit_signature.go).
	hypType := "Fact"
	if typed, home, ok := e.structureFactType(door.hypothesis.Conclusion(), door.components); ok {
		hypType = typed
		if home != "" {
			e.addImport(home)
		}
		e.addImport(onImportPath)
	}
	taken[e.lawHandle] = true
	binding := e.readSectionBinding(door.rest, door.body, taken)
	if binding.bound() {
		e.installBinding(binding)
	}
	// The door fixes the components under their own names: a claim
	// spells them so.
	e.reserveBoundName(e.lawHandle)
	_, components := ext.MatchesApply(door.hypothesis.Conclusion())
	for _, arg := range components {
		if v, isVar := arg.AsVar(); isVar && door.components[string(v.Name())] != "" {
			component := boundSkolem{binder: door.components[string(v.Name())], skolem: v}
			e.bindSurface(component)
			e.surfaceSkolems = append(e.surfaceSkolems, component)
		}
	}

	var body strings.Builder
	e.renderFamilyBodyFrom(&body, s, binding.rest)
	typed, untyped := e.entryDeps()

	cards := e.renderCardEntries()
	var b strings.Builder
	var imports []string
	if door.structure.ImportPath != "" {
		imports = append(imports, door.structure.ImportPath)
	}
	e.renderFamilyPrelude(&b, typed, s, imports...)
	b.WriteString(cards)
	var build strings.Builder
	fmt.Fprintf(&build, "%s.Law(%s,\n", door.structure.Expr, e.lawArg(door.bodyText, "\t"))
	if action, ok := soleAction(body.String()); ok && !e.lawHandleUsed && !binding.bound() {
		fmt.Fprintf(&build, "\t\t%s)", action)
	} else {
		handle := e.lawHandle
		if !e.lawHandleUsed {
			handle = "_"
		}
		fmt.Fprintf(&build, "\t\tfunc(%s *Argument, %s %s%s) {\n", e.deriveReceiver(0), handle, hypType, e.boundSignature(binding))
		build.WriteString(indentLines(body.String(), "\t"))
		fmt.Fprintf(&build, "\t\t})")
	}
	e.renderFamilyEntry(&b, name, untyped, "", build.String())
	return b.String()
}

// soleAction reads a body renderFamilyBody wrote as the one action it
// runs: `a.Do(<one action>)` with nothing declared and no ctx read.
func soleAction(body string) (string, bool) {
	const open, close = "\t\ta.Do(\n", "\t\t)\n"
	if !strings.HasPrefix(body, open) || !strings.HasSuffix(body, close) || strings.Contains(body, "ctx.") {
		return "", false
	}
	items := topLevelItems(strings.TrimSuffix(strings.TrimPrefix(body, open), close), "\t\t\t")
	if len(items) != 1 || strings.Contains(items[0], "\n") {
		return "", false
	}
	return strings.TrimSuffix(items[0], ","), true
}

// lawHandleFor is the Law door's hypothesis handle where stated is that
// hypothesis, "" elsewhere; a use marks the handle used.
func (e *_Emitter) lawHandleFor(stated core.Prop) string {
	if e.lawHypothesis == nil || stated == nil || !stated.Conclusion().AlphaEquals(e.lawHypothesis.Conclusion()) {
		return e.boundHandleFor(stated)
	}
	e.lawHandleUsed = true
	return e.lawHandle
}

// instanceDoor is a single-section member read as a structure's
// INSTANCE (registry.Family.Instance): the structure's var, and the
// recorded branch that proves each conjunct of its definition, in the
// definition's order.
type instanceDoor struct {
	structure FamilyDepRef
	conjuncts []*msNode
}

// readInstanceDoor reports whether section s is a structure instance the
// Instance door states, and reads it. The door's own proof is the
// predicate unfolded and one Case per conjunct of the definition
// (`Unfold(<predicate>)`, then SplitConjAll), so s qualifies when
//
//   - its statement is hypothesis-free and applies a structure
//     predicate whose structure EmitOptions.Structure resolves, under
//     a ∀-prefix or none;
//   - its FIRST recorded step unfolds that predicate — after the strip
//     of the whole prefix, for a parametric instance; and
//   - the unfolded goal is then split, and only split, down to the
//     definition's conjuncts — whether by one SplitConjAll or by
//     nested binary SplitConj steps, whose branches the door's single
//     n-ary split yields in the same order.
//
// The statement must also be the predicate's own application as the
// door reads it from its text. The door binds a parametric instance's
// prefix as the section's binders, one slot per binder, where a session
// records one strip of the whole prefix: the steps differ, the goal the
// unfold meets does not — the binders are minted as the strip mints
// them — and the landing records the member's own steps. A statement
// under a hypothesis has no form at the door and stays a
// family.Theorem, as does a proof that proves two conjuncts in one
// branch or runs any other step between the unfold and the split.
func (e *_Emitter) readInstanceDoor(s *_SectionEmit) (instanceDoor, bool) {
	if e.opts.Structure == nil {
		return instanceDoor{}, false
	}
	statement := e.sectionInitGoal(s)
	if statement.NumHyps() != 0 {
		return instanceDoor{}, false
	}
	// A parametric instance states the predicate under a ∀-prefix,
	// which the door binds as the section's binders — minted as the
	// session's strip-all mints them — before it unfolds.
	conclusion, parametric := statement.Conclusion(), false
	for abs := ext.MatchesFORALL(conclusion); !abs.IsZero(); abs = ext.MatchesFORALL(conclusion) {
		conclusion, parametric = abs.Body(), true
	}
	head, components := ext.MatchesApply(conclusion)
	predicate, isConst := head.AsConst()
	if !isConst || len(components) == 0 {
		return instanceDoor{}, false
	}
	root := buildMSTree(s.detailedSteps)
	if parametric {
		sq, strips := root.step.Step.(*proof.StepProto_StripQuant)
		if !strips || (sq.StripQuant != nil && sq.StripQuant.HypIndex != nil) || len(root.children) != 1 {
			return instanceDoor{}, false
		}
		root = root.children[0]
		if opened, _ := e.reader.Prop(root.step.Goal); opened == nil || opened.NumHyps() != 0 || !ext.MatchesFORALL(opened.Conclusion()).IsZero() {
			return instanceDoor{}, false
		}
		if !strings.Contains(e.familyGoalText, ". "+string(predicate.Name())+"(") {
			return instanceDoor{}, false
		}
	} else if !strings.HasPrefix(e.familyGoalText, string(predicate.Name())+"(") {
		return instanceDoor{}, false
	}
	unfold, unfolds := root.step.Step.(*proof.StepProto_DefExpand)
	if !unfolds {
		return instanceDoor{}, false
	}
	if unfolded := e.constAt(unfold.DefExpand); unfolded.IsZero() || unfolded.Name() != predicate.Name() {
		return instanceDoor{}, false
	}
	if len(root.children) != 1 {
		return instanceDoor{}, false
	}
	definition, _ := e.reader.Prop(root.children[0].step.Goal)
	if definition == nil || definition.NumHyps() != 0 {
		return instanceDoor{}, false
	}
	conjuncts := ext.DecomposesAND(definition.Conclusion())
	branches := conjunctionBranches(root.children[0])
	if len(conjuncts) < 2 || len(branches) != len(conjuncts) {
		return instanceDoor{}, false
	}
	for i, branch := range branches {
		goal, _ := e.reader.Prop(branch.step.Goal)
		if goal == nil || goal.NumHyps() != 0 || !goal.Conclusion().AlphaEquals(conjuncts[i]) {
			return instanceDoor{}, false
		}
	}
	structure, ok := e.opts.Structure(string(predicate.Name()))
	if !ok || structure.Expr == "" {
		return instanceDoor{}, false
	}
	return instanceDoor{structure: structure, conjuncts: branches}, true
}

// conjunctionBranches flattens a tree of conjunction splits — binary
// SplitConj, n-ary SplitConjAll, nested in any way — into the branches
// it ends in, left to right. A node that is no such split is one
// branch.
func conjunctionBranches(n *msNode) []*msNode {
	switch n.step.Step.(type) {
	case *proof.StepProto_SplitConj, *proof.StepProto_SplitConjAll:
		if len(n.children) >= 2 {
			var out []*msNode
			for _, c := range n.children {
				out = append(out, conjunctionBranches(c)...)
			}
			return out
		}
	}
	return []*msNode{n}
}

// renderFamilyInstanceFile is renderFamilyFile for a structure
// instance: the member is ONE family.Instance call — the structure,
// the statement, and one Case per conjunct of the structure's
// definition. The door unfolds the predicate and splits the
// conjunction itself, so neither step is rendered, and it declares the
// structure's definition entry as the member's dep, so the Deps list
// names only what the Case bodies cite.
func (e *_Emitter) renderFamilyInstanceFile(s *_SectionEmit, door instanceDoor) string {
	name := e.memberName()

	// The Case bodies render FIRST: resolving their leaves populates
	// depNames/depKeys for the family.Add block above them.
	var cases strings.Builder
	split := &proof.StepProto{Step: &proof.StepProto_SplitConjAll{}}
	for i, branch := range door.conjuncts {
		goal, _ := e.reader.Prop(branch.step.Goal)
		fmt.Fprintf(&cases, "\t\tCase(%q,\n", e.caseLabel(split, i, branch, "Case"))
		cases.WriteString(e.contextComment("\t\t\t", goal))
		cases.WriteString(e.renderInstanceCaseBody(s, branch))
		fmt.Fprintf(&cases, "\t\t),\n")
	}
	typed, untyped := e.entryDeps()

	cards := e.renderCardEntries()
	var b strings.Builder
	var imports []string
	if door.structure.ImportPath != "" {
		imports = append(imports, door.structure.ImportPath)
	}
	e.renderFamilyPrelude(&b, typed, s, imports...)
	b.WriteString(cards)
	e.requireNoAbbreviations("Instance")
	var build strings.Builder
	fmt.Fprintf(&build, "family.Instance(%s, %q,\n", door.structure.Expr, e.familyGoalText)
	build.WriteString(cases.String())
	fmt.Fprintf(&build, "\t)")
	e.renderFamilyEntry(&b, name, untyped, "", build.String())
	return b.String()
}

// renderInstanceCaseBody renders the recorded steps of one conjunct's
// branch as the body of its Case, three tabs hung. A Case of the
// Instance door is an argument of the entry literal — there is no
// closure around it for the Script handle, a declaration or the
// Argument a witness text is parsed by — so a branch that needs one of
// them carries its own: the steps run inside
// `Derive(func(a *Argument) { ctx := a.Ctx(); <declarations>; … })`,
// which records no step of its own. A branch that needs none renders
// its steps bare.
//
// What a branch needs is decided per branch: the Go-used marks and the
// text-scope names are reset and taken from this branch's steps alone,
// so a declaration binds a local only in the Case whose steps
// reference it.
func (e *_Emitter) renderInstanceCaseBody(s *_SectionEmit, branch *msNode) string {
	e.goUsedConst, e.goUsedVar, e.textScopeVars = map[string]bool{}, map[string]bool{}, nil
	var mark func(n *msNode)
	mark = func(n *msNode) {
		e.markGoUsedFromMiniStep(n.step)
		for _, c := range n.children {
			mark(c)
		}
	}
	mark(branch)
	branch = e.foldFinallyTails(branch)

	// The wrapping closure's `a` occupies Derive depth 0.
	e.deriveDepth = 1
	defer func() { e.deriveDepth = 0 }()

	chain, tail, staircase := e.tryDeriveFusion(branch)
	staircase = staircase && e.byInductions[branch.step] == nil
	var steps strings.Builder
	e.closureArgumentRead = false
	if staircase {
		e.renderDeriveStatements(&steps, s, chain, tail, "a", "\t\t\t\t")
	} else {
		e.renderStepExpr(&steps, s, branch, "\t\t\t")
	}
	var decls strings.Builder
	e.renderDecls(&decls)
	declText := indentLines(decls.String(), "\t\t\t")
	usesScript := declText != "" || strings.Contains(steps.String(), "ctx.")
	if !staircase && !usesScript && !e.closureArgumentRead {
		return steps.String()
	}
	var b strings.Builder
	fmt.Fprintf(&b, "\t\t\tDerive(func(a *Argument) {\n")
	if usesScript {
		fmt.Fprintf(&b, "\t\t\t\tctx := a.Ctx()\n")
	}
	b.WriteString(declText)
	if staircase {
		b.WriteString(steps.String())
	} else {
		fmt.Fprintf(&b, "\t\t\t\ta.Do(\n")
		b.WriteString(indentLines(steps.String(), "\t\t"))
		fmt.Fprintf(&b, "\t\t\t\t)\n")
	}
	fmt.Fprintf(&b, "\t\t\t}),\n")
	return b.String()
}

// renderCardEntries renders one family.Add block per card the member
// cites that no entry states yet (EmitOptions.Cards), and per card such
// a card's Deps name, to stand before the member: a card is a member
// stated without a proof, built by family.Card with the statement, in
// the standard form every member is written in (standardCardText), and
// the note it was deferred with, its Deps the members it says it stands
// on (cardDepsField), and the member's proof cites it as it cites any
// sibling. A card stating a law of a structure —
// `∀c:comm_ring_on(A). <body>` — takes its statement from the
// structure's door, `S.Statement(body)`, as the chapter's cards do
// (lawCardStatement). The packages the statements and the Deps spell
// are recorded for the prelude (extraImports), so the call comes
// before it.
func (e *_Emitter) renderCardEntries() string {
	rendered := e.renderedCards()
	var b strings.Builder
	for i, c := range e.opts.Cards {
		if !rendered[i] {
			continue // minted in the session, cited by no rendered section or card
		}
		text := e.standardCardText(c)
		statement := e.cardArg(text, "\t")
		if door, ok := e.lawCardStatement(c, text); ok {
			statement = door
		}
		fmt.Fprintf(&b, "// %s is a card: stated without a proof, served as an axiom until its\n", c.Name)
		fmt.Fprintf(&b, "// proof lands in place of family.Card.\n")
		fmt.Fprintf(&b, "var %s = family.Add(registry.ProofEntry{\n", c.Name)
		fmt.Fprintf(&b, "\tName: %q,\n", c.Name)
		if c.Key != "" {
			fmt.Fprintf(&b, "\tKey:  %q,\n", string(c.Key))
		}
		if deps, ok := e.cardDepsField(c); ok {
			fmt.Fprintf(&b, "\tDeps: %s,\n", deps)
		}
		fmt.Fprintf(&b, "\tBuild: family.Card(%s,\n\t\t%q),\n", statement, c.Note)
		fmt.Fprintf(&b, "})\n\n")
	}
	return b.String()
}

// renderedCards is the set, by index in EmitOptions.Cards, of the
// cards renderCardEntries renders: every card a rendered section cites
// (one with no registered name always), and every card the Deps of a
// rendered card name, transitively — a card's Deps name each as its
// var, which the file then declares.
func (e *_Emitter) renderedCards() map[int]bool {
	byEntry := map[string]int{}
	var queue []int
	for i, c := range e.opts.Cards {
		if c.Entry != "" {
			byEntry[c.Entry] = i
		}
		if c.Entry == "" || e.depNames[c.Entry] {
			queue = append(queue, i)
		}
	}
	rendered := map[int]bool{}
	for len(queue) > 0 {
		i := queue[0]
		queue = queue[1:]
		if rendered[i] {
			continue
		}
		rendered[i] = true
		for _, d := range e.opts.Cards[i].Deps {
			if j, ok := byEntry[d]; ok {
				queue = append(queue, j)
			}
		}
	}
	return rendered
}

// cardDepsField is a card's Deps literal, in the order the card names
// them: a card rendered beside it by its var, any other entry as a
// typed dep is spelled from the member's package (FamilyDepEntry: a
// sibling bare, another family's qualified, its package recorded for
// the prelude), and a name no entry serves as the TODO depsFieldValue
// writes. ok is false for a card that names no dep.
func (e *_Emitter) cardDepsField(c EmitCard) (string, bool) {
	var typed []FamilyDepRef
	var untyped []string
	for _, n := range c.Deps {
		if card, ok := e.cardByEntry(n); ok {
			typed = append(typed, FamilyDepRef{Expr: card.Name})
			continue
		}
		if e.opts.FamilyDepEntry != nil {
			if ref, ok := e.opts.FamilyDepEntry(n, ""); ok {
				if ref.ImportPath != "" {
					e.addImport(ref.ImportPath)
				}
				typed = append(typed, ref)
				continue
			}
		}
		untyped = append(untyped, n)
	}
	return depsFieldValue(typed, untyped)
}

// cardByEntry is the card of EmitOptions.Cards registered as entry.
func (e *_Emitter) cardByEntry(entry string) (EmitCard, bool) {
	for _, c := range e.opts.Cards {
		if c.Entry != "" && c.Entry == entry {
			return c, true
		}
	}
	return EmitCard{}, false
}

// standardCardText is a card's statement in the standard form a member
// is written in (dsl.StandardStatement; standardHeadline is the
// section's): the session prints the card's statement as it deferred
// the goal, its premises curried where the goal's were. The restated
// text reads back, at the member's scope, as a proposition of the
// card's own key; a card whose text the form refuses or whose
// restating reads otherwise is a defect of the session's print, and
// panics.
func (e *_Emitter) standardCardText(c EmitCard) string {
	parts, err := dsl.StandardStatement(c.Statement)
	if err != nil {
		panic(fmt.Sprintf("emit: the card %s's statement %q has no standard form: %v", c.Name, c.Statement, err))
	}
	standard, err := parts.Text()
	if err != nil {
		panic(fmt.Sprintf("emit: the standard form of the card %s's statement %q does not assemble: %v", c.Name, c.Statement, err))
	}
	if standard == c.Statement || c.Key == "" {
		return standard
	}
	scope := e.parseScopeOver()
	scope.AbbreviationBinders = leadingBinderSet(standard)
	read := dsl.ParsePropTextAtDoor(standard, scope)
	if len(read.Errors) > 0 {
		panic(fmt.Sprintf("emit: the standard form %q of the card %s's statement %q does not parse: %s", standard, c.Name, c.Statement, read.Errors[0].Message))
	}
	if registry.KeyOf(read.Prop) != c.Key {
		panic(fmt.Sprintf("emit: the standard form %q of the card %s's statement %q reads as a proposition of the key %s, not the card's %s",
			standard, c.Name, c.Statement, registry.KeyOf(read.Prop), c.Key))
	}
	return standard
}

// lawCardStatement is a card's statement through its structure's door,
// `<Structure>.Statement(<body>)` with the body as a card's statement is
// written (cardArg), where the card states a law in a
// family that states members through that door — statement, the card's
// text in the standard form, opens with the bundle binder of a
// structure the Instance and Law doors resolve, and the door's statement
// at the body (lawBody) reads back as the card's own key; ok is false
// for any other card.
func (e *_Emitter) lawCardStatement(c EmitCard, statement string) (string, bool) {
	if e.opts.Structure == nil || e.opts.LawStatement == nil || c.Key == "" {
		return "", false
	}
	rest, ok := strings.CutPrefix(statement, "∀")
	if !ok {
		return "", false
	}
	_, rest, ok = strings.Cut(rest, ":")
	if !ok {
		return "", false
	}
	predicate, _, ok := strings.Cut(rest, "(")
	if !ok {
		return "", false
	}
	body, ok := e.lawBody(predicate, statement)
	if !ok || e.opts.StructureDoorInUse != nil && !e.opts.StructureDoorInUse(predicate) {
		return "", false
	}
	structure, ok := e.opts.Structure(predicate)
	if !ok {
		return "", false
	}
	door, ok := e.opts.LawStatement(predicate, body)
	if !ok {
		return "", false
	}
	read := dsl.ParsePropTextAtDoor(door, e.parseScopeOver())
	if len(read.Errors) > 0 || registry.KeyOf(read.Prop) != c.Key {
		return "", false
	}
	if structure.ImportPath != "" {
		e.addImport(structure.ImportPath)
	}
	return fmt.Sprintf("%s.Statement(%s)", structure.Expr, e.cardArg(body, "\t")), true
}

// leadingBinderSet is the set of the names a statement text's leading
// ∀-prefix binds — what its door exempts from the abbreviation capture
// check (dsl.ParseScope.AbbreviationBinders), as the registry sets it
// for a member's headline.
func leadingBinderSet(text string) map[string]bool {
	set := map[string]bool{}
	for _, name := range dsl.LeadingBinderNames(text) {
		set[name] = true
	}
	return set
}

// renderFamilyEntry writes the member's family.Add block — the entry
// var other proofs cite. Key is the
// statement's OWN normalized key (registry.ProofEntry.Key), which is
// what the harness recomputes from the headline. An unbound session
// renders none and registration mints the unminted sentinel until the
// landing supplies it. Stmt is absent: registration derives it from the
// headline (registry.Family.Add), and so are the member's dependencies:
// they are what its proof reads, recorded when the landing records the
// family blob, and a proved member spells no Deps. A cite of a name no
// landed entry proves (untyped) is rendered as a TODO above Build — the
// replay fails on that cite until the entry lands.
//
// buildComment (may be empty) and build are the Build field: the
// liftable-signature comment rendered above it, and the constructor call
// expression — multi-line, so gofmt aligns it with nothing (a
// multi-line value closes the key/value alignment run), and the single
// space after `Build:` is the formatter's own.
func (e *_Emitter) renderFamilyEntry(b *strings.Builder, name string, untyped []string, buildComment, build string) {
	fmt.Fprintf(b, "var %s = family.Add(registry.ProofEntry{\n", name)
	if key := e.opts.EntryKey; key != "" {
		fmt.Fprintf(b, "\tName: %q,\n\tKey:  %q,\n", name, string(key))
	} else {
		fmt.Fprintf(b, "\tName: %q,\n", name)
	}
	for _, n := range untyped {
		fmt.Fprintf(b, "\t// TODO: the proof cites %s, which no entry proves — land that entry first\n", n)
	}
	if buildComment != "" {
		b.WriteString(buildComment)
		if !strings.HasSuffix(buildComment, "\n") {
			b.WriteByte('\n')
		}
	}
	fmt.Fprintf(b, "\tBuild: %s,\n", build)
	fmt.Fprintf(b, "})\n")
}

// depsFieldValue renders a Deps literal: the typed entry refs, then —
// for every name no landed entry proves — a TODO a landing cannot
// miss. A dep is an entry; there is no string channel, so a member
// citing a name with no entry cannot land until that entry does.
func depsFieldValue(typed []FamilyDepRef, untyped []string) (string, bool) {
	if len(typed) == 0 && len(untyped) == 0 {
		return "", false
	}
	exprs := make([]string, 0, len(typed))
	for _, ref := range typed {
		exprs = append(exprs, ref.Expr)
	}
	// A TODO is a comment, not an element: comma-joining two of them
	// would leave an empty element the parser refuses.
	todos := make([]string, 0, len(untyped))
	for _, n := range untyped {
		todos = append(todos, fmt.Sprintf("/* TODO: no entry proves %s — land it first; a dep is an entry */", n))
	}
	body := strings.Join(exprs, ", ")
	if len(todos) > 0 {
		if body != "" {
			body += ", "
		}
		body += strings.Join(todos, " ")
	}
	return "[]registry.EntryLike{" + body + "}", true
}

// importAuthoring adds the dot import of library/authoring to a
// rendered family file that spells a name of the bare-name surface,
// and leaves a file that spells none as it is: a dot-imported name is
// in scope only in the file that carries the import, and Go refuses an
// import a file does not use — a definition door stated in text and a
// card spell no such name, a member with a body spells several.
//
// Which it is is read off the rendered file itself — an identifier
// the file does not resolve, on the surface's roster
// (aliasgen.OnSurface) — and never off an account of what each
// renderer writes, so no renderer can spell a bare name the import
// decision does not see. The line joins the import block every
// rendered file opens with (renderTypedImports), at its sorted place.
func importAuthoring(src string) (string, error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "member.go", src, 0)
	if err != nil {
		return "", fmt.Errorf("emit: the rendered file does not parse (an emitter defect): %w\n--- source: ---\n%s", err, src)
	}
	spelled := false
	for _, ident := range file.Unresolved {
		if aliasgen.OnSurface(ident.Name) {
			spelled = true
			break
		}
	}
	if !spelled {
		return src, nil
	}
	// Before the first import whose path sorts after it; else after the
	// last. The block is one sorted group (renderTypedImports).
	at := -1
	for _, spec := range file.Imports {
		p := strings.Trim(spec.Path.Value, `"`)
		if p == authoringImportPath {
			return src, nil
		}
		offset := fset.Position(spec.Pos()).Offset
		lineStart := strings.LastIndexByte(src[:offset], '\n') + 1
		if at < 0 && p > authoringImportPath {
			at = lineStart
		}
	}
	if len(file.Imports) == 0 {
		return "", fmt.Errorf("emit: the rendered file has no import block for the dot import of %s (an emitter defect)\n--- source: ---\n%s",
			authoringImportPath, src)
	}
	if at < 0 {
		last := file.Imports[len(file.Imports)-1]
		end := fset.Position(last.End()).Offset
		at = end + strings.IndexByte(src[end:], '\n') + 1
	}
	return src[:at] + "\t. \"" + authoringImportPath + "\"\n" + src[at:], nil
}

// renderTypedImports writes a family file's import block: the registry
// (every entry literal), the extra packages the file spells, and every
// cross-family package a typed dep lives in. The dot import of
// library/authoring joins it afterwards, where the file spells a name
// of the bare-name surface (importAuthoring).
func renderTypedImports(b *strings.Builder, typed []FamilyDepRef, extra ...string) {
	imports := []string{registryImportPath}
	seen := map[string]bool{registryImportPath: true}
	for _, p := range extra {
		if !seen[p] {
			seen[p] = true
			imports = append(imports, p)
		}
	}
	for _, ref := range typed {
		if ref.ImportPath != "" && !seen[ref.ImportPath] {
			seen[ref.ImportPath] = true
			imports = append(imports, ref.ImportPath)
		}
	}
	sort.Strings(imports)
	fmt.Fprintf(b, "import (\n")
	for _, p := range imports {
		fmt.Fprintf(b, "\t%q\n", p)
	}
	fmt.Fprintf(b, ")\n\n")
}

// depIdent is the entry var a landed dep renders as, spelled from the
// member's own package (`ConvexDef` for a sibling, `vec_space.ZeroSmul`
// across families — FamilyDepEntry's resolution, the one the Deps list
// already uses), or "" when no landed entry serves the name. Every
// rendered cite goes through it: a raw `ctx.Dep("convex.ConvexDef")`
// is the string channel the authoring contract bans, beside a Deps
// list that has already resolved the very same name.
func (e *_Emitter) depIdent(name string, key core.PropKey) (string, bool) {
	if e.opts.FamilyDepEntry == nil {
		return "", false
	}
	ref, ok := e.opts.FamilyDepEntry(name, key)
	if !ok || ref.Expr == "" {
		return "", false
	}
	return ref.Expr, true
}

// depNameExpr is the argument a cert-typed call (`ctx.Dep(…)`,
// `ctx.DepNormalized(…)`) takes for a dep: the entry var when one is
// landed — the corpus spelling, `ctx.Dep(SupportDelta)` — and the
// quoted name only for a dep nothing states, which the verb refuses
// (it takes a NamedDep) as the Deps field's TODO says: a dep is an
// entry, landed first.
func (e *_Emitter) depNameExpr(name string, key core.PropKey) string {
	if id, ok := e.depIdent(name, key); ok {
		return id
	}
	return fmt.Sprintf("%q", name)
}

// familyDeps splits the rendered dep names into typed entry refs
// (FamilyDepEntry hits — landed entries) and the names no
// landed entry proves, both in sorted-name order.
// entryDeps returns the typed deps the member's body cites — their
// packages are the imports the file needs — and every dep name no
// landed entry proves, the by-name reads the caller knows of
// (ExtraDepNames) included: the TODOs a landing cannot miss. The
// by-name reads join the reported names (DepNames) here and nowhere
// else, because the body never references their entries and an import
// of their package would be unused.
func (e *_Emitter) entryDeps() (typed []FamilyDepRef, untyped []string) {
	typed, _ = e.familyDeps()
	for _, n := range e.opts.ExtraDepNames {
		e.markDepName(n, "")
	}
	_, untyped = e.familyDeps()
	return typed, untyped
}

func (e *_Emitter) familyDeps() (typed []FamilyDepRef, untyped []string) {
	for _, n := range e.sortedDepNames() {
		if e.opts.FamilyDepEntry != nil {
			if ref, ok := e.opts.FamilyDepEntry(n, e.depKeys[n]); ok {
				typed = append(typed, ref)
				continue
			}
		}
		untyped = append(untyped, n)
	}
	return typed, untyped
}

// familyBinderProbeMax bounds the leading-binder walk for the liftable
// signature comment. Far above any real statement's slot count.
const familyBinderProbeMax = 32

// renderFamilyBinderComment writes, above a closure the lift gave no
// parameter — a proof that opens with no strip, or with one the lift
// could not bind (readSectionBinding) — the binder-closure signature
// the section's leading binders bind as, read off its statement: what a
// landing can bind them with. The ∀-slot names rendered here are what
// TestLintBinderClosureNames checks a closure's parameters against.
func (e *_Emitter) renderFamilyBinderComment(b *strings.Builder, s *_SectionEmit) {
	names := proof.SectionBinderNames(e.sectionInitGoal(s), familyBinderProbeMax)
	if len(names) == 0 {
		return
	}
	signature, ok := e.familyBinderSignature(names)
	if !ok {
		return
	}
	fmt.Fprintf(b, "// The statement's leading binders, as the closure signature a landing\n")
	fmt.Fprintf(b, "// can bind them with:\n//\n")
	fmt.Fprintf(b, "//\t%s\n", signature)
}

// familyBinderSignature renders the liftable closure signature from
// SectionBinderNames' slot list, as Go a landing can paste: a named
// slot is a leading ∀ (Term parameter, the binder's own name as a
// lifted signature spells it, binderParamName — the param-name lint's
// contract), an unnamed slot a ⇒-antecedent (Fact parameter, h/h2/…,
// the first of them no binder holds). The receiver is `a`, and `arg`
// where a binder is named a, as enterLift names it. Consecutive
// same-typed parameters group Go-style ("x, y Term"). The signature
// binds the slots up to the first whose name Go does not take as a
// parameter beside the ones before it — a keyword, a second binder of
// one name — and what it leaves stays in the goal; ok=false where it
// would bind none.
func (e *_Emitter) familyBinderSignature(names []string) (string, bool) {
	taken := map[string]bool{}
	params := make([]string, 0, len(names))
	for _, name := range names {
		if name == "" {
			params = append(params, "")
			continue
		}
		param := e.binderParamName(name)
		if taken[param] || token.IsKeyword(param) || param == "_" {
			break
		}
		taken[param] = true
		params = append(params, param)
	}
	if len(params) == 0 {
		return "", false
	}
	receiver := "a"
	if taken["a"] {
		receiver = "arg"
	}
	taken[receiver] = true
	factN := 0
	factName := func() string {
		for {
			factN++
			name := "h"
			if factN > 1 {
				name = fmt.Sprintf("h%d", factN)
			}
			if !taken[name] {
				taken[name] = true
				return name
			}
		}
	}
	var b strings.Builder
	fmt.Fprintf(&b, "func(%s *Argument", receiver)
	for i := 0; i < len(params); {
		term := params[i] != ""
		group := []string{}
		for ; i < len(params) && (params[i] != "") == term; i++ {
			if term {
				group = append(group, params[i])
				continue
			}
			group = append(group, factName())
		}
		kind := "Term"
		if !term {
			kind = "Fact"
		}
		fmt.Fprintf(&b, ", %s %s", strings.Join(group, ", "), kind)
	}
	b.WriteString(")")
	return b.String(), true
}

// renderFamilyStepsFrom writes a section's recorded step chain from a
// node of its tree — the steps a lift or a door's own binding leaves to
// the body — as a closure body, two-tab hung. A body that is one whole
// assert staircase renders its Have/Show chain directly on the
// closure's own `a` — the closure IS an Argument context, and a nested
// Derive wrapper would be a driver around a driver (tree-identical
// either way: Derive records no step of its own). Anything else renders
// as one a.Do over the recorded tree, every node a bare Step expression.
func (e *_Emitter) renderFamilyStepsFrom(b *strings.Builder, s *_SectionEmit, root *msNode) {
	// The closure's own `a` occupies Derive depth 0, so nested Derive
	// blocks inside the step chain name their receivers b, c, ….
	e.deriveDepth = 1
	defer func() { e.deriveDepth = 0 }()

	recv := e.deriveReceiver(0)
	if chain, tail, ok := e.tryDeriveFusion(root); ok && e.byInductions[root.step] == nil {
		e.renderDeriveStatements(b, s, chain, tail, recv, "\t\t")
		return
	}
	fmt.Fprintf(b, "\t\t%s.Do(\n", recv)
	e.renderStepExpr(b, s, root, "\t\t\t")
	fmt.Fprintf(b, "\t\t)\n")
}

// renderFamilyBody writes a single-section member's closure body: the
// ctx handle (only when referenced), the const/var declarations as
// LOCALS, and the recorded step chain. The declarations render AFTER
// the steps: whether a const or var is bound (`X := ctx.Const(…)`) or
// only registered (`ctx.Const(…)`) is decided by what the rendered
// steps reference — for a simp rule, by whether the Simp fusion cited
// it or the pinned literal spelled it out.
func (e *_Emitter) renderFamilyBody(b *strings.Builder, s *_SectionEmit) {
	e.renderFamilyBodyFrom(b, s, e.foldFinallyTails(buildMSTree(s.detailedSteps)))
}

// renderFamilyBodyFrom is renderFamilyBody from a node of the section's
// tree (renderFamilyStepsFrom).
func (e *_Emitter) renderFamilyBodyFrom(b *strings.Builder, s *_SectionEmit, root *msNode) {
	var steps strings.Builder
	e.renderFamilyStepsFrom(&steps, s, root)
	var decls strings.Builder
	e.renderDecls(&decls)
	declText := indentLines(decls.String(), "\t")
	stepText := steps.String()
	if strings.Contains(declText, "ctx.") || strings.Contains(stepText, "ctx.") {
		fmt.Fprintf(b, "\t\tctx := %s.Ctx()\n", e.deriveReceiver(0))
	}
	b.WriteString(declText)
	b.WriteString(stepText)
}

// renderFamilySectionsFile renders a member proved through lemmas of its
// own as family.Sections: the headline is the constructor's first
// argument, each earlier section a `lemmaN := ctx.Lemma(text, …)` whose
// node a later body cites by closure capture (Cite(lemmaN), a By
// premise), and the member's own section `return ctx.Theorem(headline,
// …)`. The declarations every body needs open the constructor's
// closure, where `ctx` is the Script parameter — so no body re-derives
// it. A lemma passes scope-override args for the multi-instance consts
// its text mentions; the headline parses under the family vocabulary.
// Each section's opening strips are its closure's parameters, as a
// member of one section binds them (planSectionLifts).
func (e *_Emitter) renderFamilySectionsFile() string {
	name := e.memberName()
	last := len(e.sections) - 1

	// Every signature's names are the member's before any body renders:
	// the declarations the bodies print are kept off them.
	for i, s := range e.sections {
		e.reader = s.reader
		if lift := e.sectionLifts[i]; lift.bound() {
			e.bindLift(lift)
		}
	}
	// Bodies FIRST: resolving their leaves populates depNames/depKeys
	// and settles which declarations are bound.
	var sections strings.Builder
	for i, s := range e.sections {
		e.reader = s.reader
		lift := e.sectionLifts[i]
		e.enterLift(lift)
		var steps strings.Builder
		e.renderFamilyStepsFrom(&steps, s, lift.rest)
		closure := fmt.Sprintf("func(%s *Argument%s)", e.deriveReceiver(0), e.boundSignature(lift))
		if !lift.bound() {
			var comment strings.Builder
			e.renderFamilyBinderComment(&comment, s)
			sections.WriteString(indentLines(comment.String(), "\t\t\t"))
		}
		if i < last {
			args := joinSectionScopeArgs(e.textOverrides(e.sectionInitGoal(s)))
			fmt.Fprintf(&sections, "\t\t\t%s := ctx.Lemma(%s,\n", s.varName, e.lemmaArg(e.sectionTextForm[i], "\t\t\t"))
			fmt.Fprintf(&sections, "\t\t\t\t%s {\n", closure)
			sections.WriteString(indentLines(steps.String(), "\t\t\t"))
			fmt.Fprintf(&sections, "\t\t\t\t}%s)\n", args)
			continue
		}
		fmt.Fprintf(&sections, "\t\t\treturn ctx.Theorem(headline,\n")
		fmt.Fprintf(&sections, "\t\t\t\t%s {\n", closure)
		sections.WriteString(indentLines(steps.String(), "\t\t\t"))
		fmt.Fprintf(&sections, "\t\t\t\t})\n")
	}
	e.enterLift(nil)
	typed, untyped := e.entryDeps()

	var decls strings.Builder
	e.renderDecls(&decls)

	cards := e.renderCardEntries()
	var b strings.Builder
	e.renderFamilyPrelude(&b, typed, e.sections[last])
	b.WriteString(cards)
	var build strings.Builder
	fmt.Fprintf(&build, "family.Sections(%s,\n", e.headlineArg("\t"))
	fmt.Fprintf(&build, "\t\tfunc(ctx *Script, headline string) *GoalStackNode {\n")
	build.WriteString(indentLines(decls.String(), "\t\t"))
	build.WriteString(sections.String())
	fmt.Fprintf(&build, "\t\t})")
	e.renderFamilyEntry(&b, name, untyped, "", build.String())
	return b.String()
}

// memberName is the entry's name: FuncName without its "Build_" prefix.
func (e *_Emitter) memberName() string {
	if name := strings.TrimPrefix(e.opts.FuncName, "Build_"); name != "" {
		return name
	}
	return e.opts.FuncName
}

// renderFamilyPrelude writes what every member file opens with: the
// package clause (the family path's last segment), the imports — the
// registry (the ProofEntry literal) plus every cross-family package a
// typed dep lives in; the bare proof names (Cite, Argument, …) come
// from library/authoring, whose dot import importAuthoring adds — and,
// when the statement
// has free variables, the note that the family vocabulary must declare
// them (the constructor parses the headline before any body line
// runs).
func (e *_Emitter) renderFamilyPrelude(b *strings.Builder, typed []FamilyDepRef, top *_SectionEmit, extraImports ...string) {
	fmt.Fprintf(b, "package %s\n\n", path.Base(e.opts.Family))
	renderTypedImports(b, typed, append(e.extraImportList(), extraImports...)...)
	if top == nil {
		return
	}
	e.reader = top.reader
	if frees := e.textFreeVars(e.sectionInitGoal(top)); len(frees) > 0 {
		names := make([]string, 0, len(frees))
		for n := range frees {
			names = append(names, n)
		}
		sort.Strings(names)
		fmt.Fprintf(b, "// NOTE: the statement's free variable(s) %s must be declared by the\n",
			strings.Join(names, ", "))
		fmt.Fprintf(b, "// family vocabulary — the constructor parses the headline before this\n")
		fmt.Fprintf(b, "// file's ctx.Var lines run.\n")
	}
}

// indentLines shifts every non-empty line of text right by prefix —
// re-hosting the "\t"-hung renderers (renderDecls) at closure depth.
func indentLines(text, prefix string) string {
	if text == "" {
		return text
	}
	lines := strings.Split(text, "\n")
	var b strings.Builder
	for i, line := range lines {
		if i > 0 {
			b.WriteByte('\n')
		}
		if line != "" {
			b.WriteString(prefix)
			b.WriteString(line)
		}
	}
	return b.String()
}

// dependencyCapabilities returns the ambient proof mechanisms the
// recorded steps use (EmitResult.Capabilities) — what the family
// recorder will observe the landed member using.
func (e *_Emitter) dependencyCapabilities() []string {
	seen := map[string]bool{}
	for _, section := range e.sections {
		for _, step := range section.detailedSteps {
			_, isArith := step.Step.(*proof.StepProto_Arith)
			_, isRingNf := step.Step.(*proof.StepProto_RingNormalize)
			if isArith || isRingNf {
				p, _ := section.reader.Prop(step.Goal)
				for _, capability := range proof.ArithCapabilitiesForProp(p) {
					seen[capability] = true
				}
			}
			// A `by{arith}` composite runs its Arith INSIDE the recorded
			// node (no StepProto_Arith on the wire), so the capability
			// scan reads the closer flag off the payload. The arith'd
			// leaf is the node's goal under the premise installs — union
			// the goal's domains with each installed premise's.
			if by, ok := step.Step.(*proof.StepProto_By); ok && by.By.GetArith() {
				p, _ := section.reader.Prop(step.Goal)
				for _, capability := range proof.ArithCapabilitiesForProp(p) {
					seen[capability] = true
				}
				for _, pr := range by.By.GetPremises() {
					ip, _ := section.reader.Prop(pr.GetInstall())
					for _, capability := range proof.ArithCapabilitiesForProp(ip) {
						seen[capability] = true
					}
				}
			}
		}
	}
	out := make([]string, 0, len(seen))
	for capability := range seen {
		out = append(out, capability)
	}
	sort.Strings(out)
	return out
}

// markDepName records a named library theorem (a registry entry)
// rendered as a LibraryThm-backed leaf (see EmitResult.DepNames), plus
// the leaf key it was rendered at (the FamilyDepEntry lookup handle).
// Lazy map init so secondary emitter construction sites
// (emitTrivialTrue) need no seed.
func (e *_Emitter) markDepName(name string, key core.PropKey) {
	if e.depNames == nil {
		e.depNames = map[string]bool{}
		e.depKeys = map[string]core.PropKey{}
	}
	e.depNames[name] = true
	if _, seen := e.depKeys[name]; !seen && key != "" {
		e.depKeys[name] = key
	}
}

// sortedDepNames returns the collected dep names sorted, for
// EmitResult.DepNames. Nil when no LibraryThm leaf rendered.
func (e *_Emitter) sortedDepNames() []string {
	if len(e.depNames) == 0 {
		return nil
	}
	out := make([]string, 0, len(e.depNames))
	for n := range e.depNames {
		out = append(out, n)
	}
	sort.Strings(out)
	return out
}

// renderDecls writes the member's const and var declarations as closure
// locals. ctx.Const / ctx.Var REGISTER the name in Script.ParseScope
// (where a rendered text reads its types); a line binds a Go ident
// (`X := ctx.Const(…)`) only when a rendered Go expression references
// it, and a registration-only line is dropped when nothing needs it —
// the family vocabulary already registers the name, or (for a var) no
// rendered text mentions it.
func (e *_Emitter) renderDecls(b *strings.Builder) {
	var constLines []string
	for _, ident := range sortedValues(e.constIdent) {
		meta := e.constMeta[ident]
		typeExpr := e.printer.PrintType(e.constInstType[ident])
		if e.goUsedConst[ident] {
			constLines = append(constLines, fmt.Sprintf("\t%s := ctx.Const(%q, %s)\n",
				ident, string(meta.Name()), typeExpr))
			continue
		}
		// A registration-only declaration of a name the family's
		// vocabulary already installs is redundant (EmitOptions.
		// FamilyVocab): the member's texts parse under the family
		// scope, which carries the name before the body runs.
		if e.familyDeclaresConst(string(meta.Name())) {
			continue
		}
		constLines = append(constLines, fmt.Sprintf("\tctx.Const(%q, %s)\n",
			string(meta.Name()), typeExpr))
	}
	if len(constLines) > 0 {
		fmt.Fprintf(b, "\t// === Constants ===\n")
		for _, line := range constLines {
			b.WriteString(line)
		}
		fmt.Fprintf(b, "\n")
	}

	var varLines []string
	idents := make([]string, 0, len(e.varDecl))
	for id := range e.varDecl {
		idents = append(idents, id)
	}
	sort.Strings(idents)
	for _, id := range idents {
		v := e.varDecl[id]
		typeExpr := e.printer.PrintType(v.Type())
		if e.goUsedVar[id] {
			// A name the member holds at two types is declared without
			// registering it: Script.Var refuses a second type, and each
			// text spelling the name passes this value (textOverrides).
			declare := "ctx.Var"
			if !e.registersVar(id) {
				declare = "Var"
			}
			varLines = append(varLines, fmt.Sprintf("\t%s := %s(%q, %s)\n",
				id, declare, string(v.Name()), typeExpr))
			continue
		}
		if e.registersVar(id) {
			varLines = append(varLines, fmt.Sprintf("\tctx.Var(%q, %s)\n",
				string(v.Name()), typeExpr))
		}
	}
	if len(varLines) > 0 {
		fmt.Fprintf(b, "\t// === Variables ===\n")
		for _, line := range varLines {
			b.WriteString(line)
		}
		fmt.Fprintf(b, "\n")
	}
}

// registersVar reports whether the member's declarations register the
// variable of ident id in the script's parse scope — `ctx.Var`, where
// `Var` builds a term and registers nothing: a variable the Go body
// uses, held at one type, that is a variable of the proof — free in a
// goal some step sees (goalFrees), or read by a rendered text — or one
// only a rendered text reads (scopeOnlyVarDeclared). A variable the Go
// body uses only to build a term that binds it (`ForAll(n)(…)`, a λ's
// binder) is no name of the script's: registered, it would be the `n`
// every later text and every closure binding an `n` reads.
// renderDecls declares by it, and the replay scope a text is checked
// in (replayScopeVars) is read off it.
func (e *_Emitter) registersVar(id string) bool {
	v := e.varDecl[id]
	name := string(v.Name())
	if e.goUsedVar[id] {
		return e.registerableVarNames[name] && (e.goalFrees[_VarKey{v.Name(), v.Type().Key()}] || e.textScopeVars[name])
	}
	return e.scopeOnlyVarDeclared(name)
}

// scopeOnlyVarDeclared reports whether a var the Go body never
// references is still declared for its ParseScope entry: exactly when a
// rendered text mentions the name (textScopeVars — the bodies render
// before the declarations, so this is known) and neither the family's
// own vocabulary (EmitOptions.FamilyVocab) nor the closure's boundary
// (boundVars) already registers it.
func (e *_Emitter) scopeOnlyVarDeclared(name string) bool {
	return e.registerableVarNames[name] && !e.familyDeclaresVar(name) && e.textScopeVars[name] && !e.boundVars[name]
}

// sectionConstOverrides returns the Go expressions for the per-section
// scope overrides — the const locals corresponding to the ConstTerm
// instances actually used in the section's prop, for const NAMES that
// have multiple distinct instantiations across emit's e.constIdent.
// Single-instance consts don't need an override because the runtime
// script's only registration matches the section's use.
//
// emit-time buildParseScope used a section-specific scope built from the
// prop's own const occurrences; this list propagates the same per-section
// choice to runtime via the text call's variadic overrides (ctx.Lemma,
// MakePropText). Without it, runtime's "first Script.Const wins"
// registration resolves a polymorphic name to whichever instance
// Script.Const happened to register first — often the wrong one for this
// section.
func (e *_Emitter) sectionConstOverrides(p core.Prop) []string {
	idents := e.sectionScopeOverrideIdents(p)
	if len(idents) == 0 {
		return nil
	}
	exprs := make([]string, 0, len(idents))
	for _, ident := range idents {
		exprs = append(exprs, ident)
	}
	return exprs
}

// sectionScopeOverrideIdents returns the const idents a text for prop
// p passes as explicit scope-disambiguation args (`ctx.Lemma(text,
// body, <overrides>...)`, `MakePropText(text, <overrides>...)`): one
// per multi-instance const name actually occurring in p. These idents
// are referenced as Go expressions, so they MUST be marked goUsedConst
// (so renderDecls binds them) — decideSectionForms and
// markGoUsedFromPropPayload do that from this same list, keeping the
// "what's referenced" and "what's declared" sets in lockstep.
func (e *_Emitter) sectionScopeOverrideIdents(p core.Prop) []string {
	entries := e.sectionScopeOverrideEntries(p)
	if len(entries) == 0 {
		return nil
	}
	idents := make([]string, 0, len(entries))
	for _, en := range entries {
		idents = append(idents, en.ident)
	}
	return idents
}

// scopeOverrideEntry pairs the Go ident a text-form call passes as a
// scope override with the ConstTerm instance that ident is bound to
// at runtime. sectionScopeOverrideIdents renders the idents;
// tryTextForm replays the const terms to validate the text against
// the exact scope the runtime overlay will produce. One collector, so
// the two views can never drift.
type scopeOverrideEntry struct {
	ident string
	ct    core.ConstTerm
}

// sectionScopeOverrideEntries is the shared collector behind
// sectionScopeOverrideIdents (see its doc): one entry per
// multi-instance const name actually occurring in p, dedup'd on
// (name, type key), sorted for deterministic emit output, and
// restricted to consts e.constIdent tracks (untracked ones are not
// passed as runtime args either, so they must not participate in the
// validation overlay).
func (e *_Emitter) sectionScopeOverrideEntries(p core.Prop) []scopeOverrideEntry {
	if len(e.constIdent) == 0 {
		return nil
	}
	// Names that have more than one ident (i.e. multiple type-instances)
	// among the constants the member registers itself: a constant the
	// family's scope serves has no ctx.Const line, and the Script
	// reads it through the resolver at each occurrence's own instance
	// (parseScopeOver), so no override fixes one.
	multi := map[core.TermName]bool{}
	counts := map[core.TermName]int{}
	for k := range e.constIdent {
		if e.familyDeclaresConst(string(k.name)) {
			continue
		}
		counts[k.name]++
		if counts[k.name] > 1 {
			multi[k.name] = true
		}
	}
	if len(multi) == 0 {
		return nil
	}
	// Walk the prop and collect the section-specific (name, type.Key())
	// for each multi-instance name. Dedup so we emit each override once
	// even if the const occurs multiple times.
	type key struct {
		name core.TermName
		tkey core.TypeKey
	}
	seen := map[key]bool{}
	var found []key
	consts := map[key]core.ConstTerm{}
	var walk func(t core.Term)
	walk = func(t core.Term) {
		switch tt := t.Core().(type) {
		case core.ConstTerm:
			if multi[tt.Name()] {
				k := key{tt.Name(), tt.Type().Key()}
				if !seen[k] {
					seen[k] = true
					found = append(found, k)
					consts[k] = tt
				}
			}
		case core.AppliedTerm:
			walk(tt.Fun())
			walk(tt.Arg())
		case core.AbsTerm:
			walk(tt.Body())
		}
	}
	walk(p.Conclusion())
	for i := range p.NumHyps() {
		walk(p.Hyp(i))
	}
	if len(found) == 0 {
		return nil
	}
	// Stable order by (name, tkey) so emit output is deterministic.
	sort.Slice(found, func(i, j int) bool {
		if found[i].name != found[j].name {
			return found[i].name < found[j].name
		}
		return string(found[i].tkey) < string(found[j].tkey)
	})
	entries := make([]scopeOverrideEntry, 0, len(found))
	for _, k := range found {
		ident, ok := e.constIdent[_ConstKey{k.name, k.tkey}]
		if !ok {
			continue // const not tracked (e.g. special const) — skip
		}
		entries = append(entries, scopeOverrideEntry{ident: ident, ct: consts[k]})
	}
	return entries
}

// joinSectionScopeArgs appends the section-local scope overrides to a
// call's argument list as `", arg1, arg2"`. Empty when no overrides.
func joinSectionScopeArgs(overrides []string) string {
	if len(overrides) == 0 {
		return ""
	}
	return ", " + strings.Join(overrides, ", ")
}

// sectionInitGoal returns the prop the section was opened with at
// record time — `Steps[0].Goal` deserialized — which is the statement
// the member's text spells. The replayed section must open on an
// α-equal goal for the recorded ministeps to replay faithfully, so this
// is the PRE-Normalize form the first step saw, not a normalized
// restatement. A section with no recorded steps falls back to its
// stated goal.
func (e *_Emitter) sectionInitGoal(s *_SectionEmit) core.Prop {
	if len(s.detailedSteps) > 0 && s.detailedSteps[0].Goal != nil {
		if g, _ := e.reader.Prop(s.detailedSteps[0].Goal); g != nil {
			return g
		}
	}
	return s.goal
}

// renderStepExpr emits one tree node as bare Step expressions —
// comma-terminated `<Step-expr>,` lines for an a.Do, a Case body or
// any other Step-list context. Fusions are tried first (a fused pair
// renders as one verb), then the case-eligible / Expect block forms,
// then the plain ministep followed by its children.
func (e *_Emitter) renderStepExpr(b *strings.Builder, s *_SectionEmit, n *msNode, indent string) {
	if facts, binds := e.branchFacts[n.step]; binds && !e.branchFactOpened[n.step] {
		e.renderBranchFact(b, s, n, facts, indent)
		return
	}
	if n.finallyFold > 0 {
		fmt.Fprintf(b, "%sFinally(%s),\n", indent, reindentMiniStep(e.emitMiniStep(n.step), indent))
		return
	}

	if e.condRewriteLeftToBasic(n) {
		e.renderStepExpr(b, s, n.children[0], indent)
		return
	}

	if cite, ok := e.sectionCites[n.step]; ok && cite.installs {
		rest := n.children[1]
		if !cite.grounds {
			fmt.Fprintf(b, "%sCite(%s),\n", indent, cite.lemma)
			e.renderStepExpr(b, s, rest, indent)
			return
		}
		ground := rest.step.Step.(*proof.StepProto_Specialize).Specialize
		verb := "Cite"
		if ground.GetKeepSources() {
			verb = "CiteKeep"
		}
		args := []string{cite.lemma}
		for _, ref := range ground.GetHyps()[0].GetWitnesses() {
			args = append(args, e.witnessExpr(e.reader.Term(ref)))
		}
		fmt.Fprintf(b, "%s%s(%s),\n", indent, verb, strings.Join(args, ", "))
		for _, c := range rest.children {
			e.renderStepExpr(b, s, c, indent)
		}
		return
	}

	if len(n.children) >= 1 {
		first := n.children[0]
		if f := e.byInductions[n.step]; f != nil {
			e.renderByInduction(b, s, f, indent)
			return
		}
		if name, args, spec, ok := e.tryCiteSpecializeFusion(n); ok {
			fmt.Fprintf(b, "%s%s(%s),\n", indent, name, args)
			for _, c := range spec.children {
				e.renderStepExpr(b, s, c, indent)
			}
			return
		}
		if expr, ok := e.tryCiteFusion(n.step, first.step); ok {
			fmt.Fprintf(b, "%sCite(%s),\n", indent, expr)
			for _, c := range n.children[1:] {
				e.renderStepExpr(b, s, c, indent)
			}
			return
		}
		if dExpr, cExpr, ok := e.tryRewriteFusion(n); ok {
			fmt.Fprintf(b, "%sRewrite(%s, %s),\n", indent, dExpr, cExpr)
			for _, c := range n.children[1:] {
				e.renderStepExpr(b, s, c, indent)
			}
			return
		}
		if expr, rest, ok := e.trySimpFusion(n); ok {
			fmt.Fprintf(b, "%s%s,\n", indent, expr)
			for _, c := range rest {
				e.renderStepExpr(b, s, c, indent)
			}
			return
		}
		if expr, rest, ok := e.tryAtTypesFusion(n); ok {
			fmt.Fprintf(b, "%sCite(%s),\n", indent, expr)
			for _, c := range rest {
				e.renderStepExpr(b, s, c, indent)
			}
			return
		}
		if chain, tail, ok := e.tryDeriveFusion(n); ok {
			b.WriteString(indent)
			e.renderDeriveBlock(b, s, chain, tail, indent)
			fmt.Fprintf(b, ",\n")
			return
		}
	}

	if by, ok := n.step.Step.(*proof.StepProto_By); ok {
		// The children (premise claims) are implied by the premise list:
		// the replayed By regenerates and certifies them itself.
		fmt.Fprintf(b, "%s%s,\n", indent, e.renderByExpr(by.By))
		return
	}

	if isCaseBlockNode(n) {
		if caseEligibleStep(n.step) {
			prefix, hasArgs := e.emitMiniStepCaseHead(n.step)
			if hasArgs {
				fmt.Fprintf(b, "%s%s,\n", indent, prefix)
			} else {
				fmt.Fprintf(b, "%s%s\n", indent, prefix)
			}
		} else {
			// Expect wrap for an auto-splitting fan-out with no native Case form.
			fmt.Fprintf(b, "%sExpect(%s,\n", indent, reindentMiniStep(e.emitMiniStep(n.step), indent))
		}
		for _, i := range branchOrder(n.step, len(n.children)) {
			child := n.children[i]
			ctor := branchCtor(n.step, i, len(n.children))
			label := e.caseLabel(n.step, i, child, ctor)
			childGoal, _ := e.reader.Prop(child.step.Goal)
			fmt.Fprintf(b, "%s\t%s(%q,\n", indent, ctor, label)
			b.WriteString(e.contextComment(indent+"\t\t", childGoal))
			if cite, cited := e.sectionCites[n.step]; cited && i == 0 {
				fmt.Fprintf(b, "%s\t\tCite(%s),\n", indent, cite.lemma)
			} else if !e.renderGivenBranch(b, s, n, child, childGoal, indent+"\t\t") {
				e.renderStepExpr(b, s, child, indent+"\t\t")
			}
			fmt.Fprintf(b, "%s\t),\n", indent)
		}
		fmt.Fprintf(b, "%s),\n", indent)
		return
	}

	line := reindentMiniStep(e.emitMiniStep(n.step), indent)
	fmt.Fprintf(b, "%s%s,\n", indent, line)
	for _, c := range n.children {
		e.renderStepExpr(b, s, c, indent)
	}
}

// condRewriteLeftToBasic reports whether n is a recorded `cond_rewrite`
// that renders no line of its own: its goal holds no COND, its one
// child is a `basic` leaf, and Basic closes that goal as it stands.
// CondRewrite is the basic rewrite with the COND eliminations added,
// so on a goal with no COND it is the basic rewrite alone (what turns
// the `t = t` a rewrite left into ⊤); where Basic closes the goal
// without it, the leaf's `Basic()` stands for both, and
// `CondRewrite(), Basic()` names a step that eliminates nothing. A
// goal with a COND keeps the step, and so does a `basic` that leaves a
// residual.
func (e *_Emitter) condRewriteLeftToBasic(n *msNode) bool {
	if _, isCondRewrite := n.step.Step.(*proof.StepProto_CondRewrite); !isCondRewrite {
		return false
	}
	if len(n.children) != 1 || len(n.children[0].children) != 0 || n.children[0].finallyFold > 0 {
		return false
	}
	if _, isBasic := n.children[0].step.Step.(*proof.StepProto_Basic); !isBasic {
		return false
	}
	goal, _ := e.reader.Prop(n.step.Goal)
	if goal == nil || prop.ContainsConstName(goal, ext.COND.Name()) {
		return false
	}
	// The one line left must do what the two did: Basic is run on the
	// goal the rewrite was recorded at, and the step is dropped only
	// where that closes it.
	closed := tactic.BasicTactics(goal)
	return closed != nil && closed.Size() == 0
}

// renderGivenBranch renders a Case branch whose body rewrites with the
// ONE hypothesis the parent step introduced as the branch form that
// receives that hypothesis as a value —
//
//	Case("…",
//		Given(func(b *Argument, ih Fact) {
//			b.Show("…", Simp(…), ih.Rw(), By(…))
//		}),
//	),
//
// so the rewrite addresses the hypothesis through its handle (`ih.Rw()`,
// `ih.Subst()`, `ih.CongrArg(f)`) instead of the positional index
// (`Rw(0, false)`) the chapter lint refuses in every proof file
// (TestLintNoPositionalHypIndices). Binding is pure
// bookkeeping at replay — Given locates the hypothesis by diffing the
// parent goal against the branch's, and the handle tracks it by
// content — so the rendered tree and every recorded key are the same
// as the positional form's. The step's own goal decides: only a step
// addressing the introduced hypothesis at its UNCHANGED content (the
// same identity the handle resolves at replay) takes the handle; a
// step addressing a hyp no branch introduced keeps its positional
// spelling, which the lint then names.
//
// A step granting SEVERAL hypotheses — a constructor with two
// recursive arguments — has the closure form too (GivenEach:
// func(b *Argument, left, right Fact) / func(b *Argument, ihs []Fact),
// hypotheses in the constructor's argument order), but that order is
// the induction template's, which the recorded tree does not carry; so
// such a branch stays positional here and SAYS SO in a comment naming
// the lint and the closure to rewrite it into, instead of handing the
// author a body that fails a gate without a word.
//
// Returns false — nothing written — when the branch is not this shape;
// the caller renders the flat action list as before.
func (e *_Emitter) renderGivenBranch(b *strings.Builder, s *_SectionEmit, parent, child *msNode, childGoal core.Prop, indent string) bool {
	parentGoal, _ := e.reader.Prop(parent.step.Goal)
	if parentGoal == nil || childGoal == nil {
		return false
	}
	introduced := hypsIntroduced(parentGoal, childGoal)
	if len(introduced) == 0 {
		return false
	}
	// The hyp-addressing steps of the branch, by the introduced
	// hypothesis each addresses (at unchanged content). A step a Derive
	// block already bound to a Have handle is that handle's.
	uses := make([][]*proof.StepProto, len(introduced))
	total := 0
	var visit func(n *msNode)
	visit = func(n *msNode) {
		if n == nil || e.sectionCitedSteps[n.step] {
			return
		}
		if idx, ok := e.hypAddressedByStep(n.step); ok {
			if _, bound := e.hypHandleByUse[_HypUse{step: n.step}]; !bound {
				if goal, _ := e.reader.Prop(n.step.Goal); goal != nil && idx < goal.NumHyps() {
					for k, h := range introduced {
						if goal.Hyp(idx).AlphaEquals(h) {
							uses[k] = append(uses[k], n.step)
							total++
							break
						}
					}
				}
			}
		}
		for _, c := range n.children {
			visit(c)
		}
	}
	visit(child)
	if total == 0 {
		return false
	}
	if len(introduced) > 1 {
		fmt.Fprintf(b, "%s// NOTE: this branch rewrites with %d of the %d hypotheses the step introduced,\n", indent, total, len(introduced))
		fmt.Fprintf(b, "%s// addressed by POSITION below — TestLintNoPositionalHypIndices refuses that in a\n", indent)
		fmt.Fprintf(b, "%s// chapter file. Take them as values in the constructor's argument order:\n", indent)
		fmt.Fprintf(b, "%s// GivenEach(func(b *Argument, ihs []Fact) { b.Show(\"…\", …, ihs[k].Rw(), …) }), or\n", indent)
		fmt.Fprintf(b, "%s// func(b *Argument, left, right Fact) for a binary constructor, and address each\n", indent)
		fmt.Fprintf(b, "%s// by its handle (h.Rw() / h.RwRev() / h.Subst() / h.CongrArg(f)).\n", indent)
		return false
	}
	if e.hypHandleByUse == nil {
		e.hypHandleByUse = map[_HypUse]string{}
	}
	base := "h"
	if _, isInduct := parent.step.Step.(*proof.StepProto_Induction); isInduct {
		base = "ih"
	}
	ident := e.freshIdent(base, e.handleNamesTaken())
	for _, use := range uses[0] {
		e.hypHandleByUse[_HypUse{step: use}] = ident
	}
	recv := e.deriveReceiver(e.deriveDepth)
	e.deriveDepth++
	defer func() { e.deriveDepth-- }()
	fmt.Fprintf(b, "%sGiven(func(%s *Argument, %s Fact) {\n", indent, recv, ident)
	fmt.Fprintf(b, "%s\t%s.Show(%q,\n", indent, recv, e.conclusionLabel(childGoal))
	e.renderStepExpr(b, s, child, indent+"\t\t")
	fmt.Fprintf(b, "%s\t)\n", indent)
	fmt.Fprintf(b, "%s}),\n", indent)
	return true
}

// handleNamesTaken is every identifier a hypothesis handle is named
// apart from: the member's declarations, the handles bound so far and
// the Law door's, which the closures nested in the door's body see.
func (e *_Emitter) handleNamesTaken() map[string]bool {
	taken := e.declSet()
	for _, id := range e.hypHandleByUse {
		taken[id] = true
	}
	if e.lawHandle != "" {
		taken[e.lawHandle] = true
	}
	return taken
}

// hypsIntroduced returns the hypotheses of child that parent does not
// carry — one per occurrence, matched up to α — the hypotheses the
// step between them granted the branch.
func hypsIntroduced(parent, child core.Prop) []core.Term {
	used := make([]bool, parent.NumHyps())
	var out []core.Term
	for i := range child.NumHyps() {
		h := child.Hyp(i)
		found := false
		for j := range parent.NumHyps() {
			if !used[j] && parent.Hyp(j).AlphaEquals(h) {
				used[j] = true
				found = true
				break
			}
		}
		if !found {
			out = append(out, h)
		}
	}
	return out
}

// caseEligibleStep reports whether a ministep should be wrapped in
// labeled Case(...) args when it has ≥ 2 children. The whitelist
// covers every multi-residual branching ministep where positional
// child closing carries non-trivial role information (SplitConj /
// SplitDisj / SplitIff / SplitHypIff / SplitHypImply / ByCase /
// Induction / Lemma / Assert). Cascade ministeps (Trans / Symm /
// Congr) are intentionally excluded — their "spine + spur" pattern
// reads cleaner flat at the outer indent.
func caseEligibleStep(step *proof.StepProto) bool {
	switch step.Step.(type) {
	case *proof.StepProto_SplitConj,
		*proof.StepProto_SplitConjAll,
		*proof.StepProto_SplitDisj,
		*proof.StepProto_SplitIff,
		*proof.StepProto_SplitHypIff,
		*proof.StepProto_SplitHypImply,
		*proof.StepProto_ByCase,
		*proof.StepProto_Induction,
		*proof.StepProto_Lemma,
		*proof.StepProto_Assert,
		*proof.StepProto_ExistentialConstDef:
		return true
	}
	return false
}

// emitMiniStepCaseHead emits the case-eligible ministep's call up to
// (but NOT including) the closing ")". The second return reports
// whether the ministep carries positional args already — when true,
// a "," prefix is needed before the variadic Case args. renderStepExpr
// uses it to splice Case args into the call site without splitting
// emitMiniStep's full-string output.
func (e *_Emitter) emitMiniStepCaseHead(step *proof.StepProto) (string, bool) {
	switch s := step.Step.(type) {
	case *proof.StepProto_SplitConj:
		return "SplitConj(", false
	case *proof.StepProto_SplitConjAll:
		return "SplitConjAll(", false
	case *proof.StepProto_SplitDisj:
		if s.SplitDisj != nil && s.SplitDisj.HypIndex != nil {
			return fmt.Sprintf("SplitDisjAt(%d", *s.SplitDisj.HypIndex), true
		}
		return "SplitDisj(", false
	case *proof.StepProto_SplitIff:
		return "SplitIff(", false
	case *proof.StepProto_SplitHypIff:
		if s.SplitHypIff != nil && s.SplitHypIff.HypIndex != nil {
			return fmt.Sprintf("SplitHypIffAt(%d", *s.SplitHypIff.HypIndex), true
		}
		return "SplitHypIff(", false
	// Both render through the NAMED slots below (branchCtor), not
	// through Case — the direction is the constructor, so an emitted
	// split cannot be pasted with its two halves the wrong way round.
	case *proof.StepProto_SplitHypImply:
		if s.SplitHypImply != nil && s.SplitHypImply.HypIndex != nil {
			return fmt.Sprintf("SplitHypImplyAt(%d", *s.SplitHypImply.HypIndex), true
		}
		return "SplitHypImply(", false
	case *proof.StepProto_ByCase:
		t := e.reader.Term(s.ByCase)
		return fmt.Sprintf("ByCaseStep(%s", e.caseTermExpr(t)), true
	case *proof.StepProto_Induction:
		t := e.reader.Term(s.Induction)
		return fmt.Sprintf("ctx.InductStep(%s.Core()", e.goTermExpr(t)), true
	case *proof.StepProto_Lemma:
		// A `Lemma` ministep INTRODUCES its payload as a sub-claim:
		// LemmaTactic makes child(0) = the lemma (proved by the Case
		// bodies that follow) and child(1) = the residual. The payload
		// is the lemma's STATEMENT, not a reference to an existing Thm —
		// `Lemma(lemma Prop, cases ...Case)` takes a Prop. Render it as
		// MakeProp(<concl>), exactly like Assert below. (The
		// external-citation idiom — Lemma immediately closed by a
		// KnownThm cache hit — is intercepted earlier as a Cite fusion,
		// which is where lemmaRefExpr correctly resolves the Thm.)
		l, _ := e.reader.Prop(s.Lemma)
		return fmt.Sprintf("Lemma(%s", e.miniStepPropExpr(l)), true
	case *proof.StepProto_Assert:
		claim, _ := e.reader.Prop(s.Assert)
		return fmt.Sprintf("AssertStep(%s", e.claimExpr(claim)), true
	case *proof.StepProto_ExistentialConstDef:
		ct := e.constAt(s.ExistentialConstDef)
		return fmt.Sprintf("ExistentialConstDefStep(%s", e.printer.PrintTerm(ct)), true
	}
	// Unreachable — caller gates on caseEligibleStep.
	panic(fmt.Sprintf("emitMiniStepCaseHead: not case-eligible: %T", step.Step))
}

// caseLabel renders the label string for one branch: the conclusion
// the branch proves, in the chapter's spelling. The branch's hypotheses
// are not in it — the `// context:` comment under the label lists them
// (contextComment), and a sequent printed whole runs out of the label's
// width before it reaches its conclusion.
//
// A positional Case leads with its role tag (`left` / `claim` /
// `case_<idx>` / ...) and ": ". The tag is what marks the label as
// rendered rather than written: the chapter lint refuses every tag
// caseTag returns (TestLintNoStructuralTokenInLabel), so a pasted
// branch stays red until its label is restated as a sentence.
func (e *_Emitter) caseLabel(parent *proof.StepProto, idx int, child *msNode, ctor string) string {
	childGoal, _ := e.reader.Prop(child.step.Goal)
	if ctor != "Case" {
		// Forward / Backward, BothHold / NeitherHolds, LeftHolds /
		// RightHolds already say which branch this is, and say it in a
		// slot the compiler checks — a role tag in the text would only
		// be a second, unchecked copy.
		return e.conclusionLabel(childGoal)
	}
	return caseTag(parent, e.caseRole(parent, idx)) + ": " + e.conclusionLabel(childGoal)
}

// caseRole is the role position of the child at idx: idx itself, except
// under a ByCaseStep, whose `true` tag names the branch on which the
// case term holds — child 1 for a ¬-headed term (proof.ByCaseBranch),
// which role 1 then tags `false`.
func (e *_Emitter) caseRole(parent *proof.StepProto, idx int) int {
	byCase, ok := parent.Step.(*proof.StepProto_ByCase)
	if !ok {
		return idx
	}
	holds, _ := proof.ByCaseBranch(e.reader.Term(byCase.ByCase), true)
	if holds == 0 {
		return idx
	}
	return 1 - idx
}

// branchCtor names the constructor one branch renders through. An ⇔
// split's halves are not Cases: they are Forward / Backward (the goal
// split) or BothHold / NeitherHolds (the hyp split), typed so that
// pasted output cannot be edited into a swapped pair
// (prover/proof/iff_direction.go); a disjunctive hypothesis's branches
// are LeftHolds / RightHolds (disjunction_branches.go). Everything else
// is a plain Case.
func branchCtor(parent *proof.StepProto, idx, children int) string {
	if children != 2 {
		// None of these splits can yield another count, and a surface
		// taking named branches has nowhere to put a third: render plain
		// Cases and let the compiler refuse the paste rather than invent
		// a slot.
		return "Case"
	}
	switch parent.Step.(type) {
	case *proof.StepProto_SplitIff:
		return [2]string{"Backward", "Forward"}[idx]
	case *proof.StepProto_SplitHypIff:
		return [2]string{"BothHold", "NeitherHolds"}[idx]
	case *proof.StepProto_SplitDisj:
		return [2]string{"LeftHolds", "RightHolds"}[idx]
	}
	return "Case"
}

// branchOrder is the order a split's branches render in: the order its
// constructor takes them. SplitIff takes the ⇒ half first while the
// tactic emits the ⇐ child first (prover/proof/script.go), so its two
// children render swapped; every other split renders in child order.
func branchOrder(parent *proof.StepProto, children int) []int {
	order := make([]int, children)
	for i := range order {
		order[i] = i
	}
	if _, iff := parent.Step.(*proof.StepProto_SplitIff); iff && children == 2 {
		order[0], order[1] = 1, 0
	}
	return order
}

// caseRoleTags lists every role tag caseTag returns besides the
// numbered `case_<idx>` (TestCaseTag_ReturnsOnlyListedRoleTags). The
// chapter lint reads the list through CaseRoleTags and refuses each
// one as a label's lead.
var caseRoleTags = []string{
	"left", "right", "premise", "after", "true", "false",
	"base", "step", "claim", "residual",
}

// CaseRoleTags returns the role tags a rendered positional Case label
// can lead with, the numbered `case_<idx>` aside.
func CaseRoleTags() []string { return append([]string(nil), caseRoleTags...) }

// caseTag is the per-(ministep-type, role-position) role tag; the role
// position is the child index, read through caseRole where the two
// differ. Two-child patterns get role-naming tags; >2 children fall
// back to numeric "case_N" so the position is at least disambiguated.
func caseTag(parent *proof.StepProto, idx int) string {
	switch parent.Step.(type) {
	case *proof.StepProto_SplitConj, *proof.StepProto_SplitDisj:
		switch idx {
		case 0:
			return "left"
		case 1:
			return "right"
		}
	case *proof.StepProto_SplitHypImply:
		switch idx {
		case 0:
			return "premise"
		case 1:
			return "after"
		}
	case *proof.StepProto_ByCase:
		switch idx {
		case 0:
			return "true"
		case 1:
			return "false"
		}
	case *proof.StepProto_Induction:
		switch idx {
		case 0:
			return "base"
		case 1:
			return "step"
		}
	case *proof.StepProto_Lemma:
		switch idx {
		case 0:
			return "claim"
		case 1:
			return "residual"
		}
	case *proof.StepProto_Assert:
		switch idx {
		case 0:
			return "claim"
		case 1:
			return "after"
		}
	}
	return fmt.Sprintf("case_%d", idx)
}

// msNode is the parent → children tree rebuilt from a flat preorder
// StepProto sequence. The tree shape is implicit in the proto
// (each step's len(SubGoals) determines its child count; positional
// preorder determines who's whose parent), so buildMSTree is a pure
// structural transform with no semantic loss.
//
// The tree exists so emit can render multi-residual ministeps as
// labeled `Case` branches (Remaining tasks item 2). Step 1 of that
// rollout uses the tree to reproduce the previous flat output
// byte-for-byte; subsequent steps switch on the new render forms.
type msNode struct {
	step     *proof.StepProto
	children []*msNode

	// finallyFold, when > 0, marks a synthetic render-time node that
	// emits `Finally(<step>)` — the broadcast-terminator fold of that
	// many trailing identical closing leaves (see foldFinallyTails).
	// step holds the first folded leaf's StepProto, so walkers unaware
	// of the marker still see a well-formed closing step.
	finallyFold int
}

// buildMSTree reconstructs the proof tree from a preorder
// StepProto sequence. Algorithm:
//
// - Maintain a stack of (open parent, children-remaining) pairs.
// - Each new step is appended to the current top's children;
// decrement top.remaining. While the top is fully filled
// (remaining == 0), pop it.
// - If the new step has its own subgoals, push it as the new top.
//
// The "preorder + per-node child count" pair is sufficient to
// reconstruct the tree uniquely — same invariant the kernel's replay
// (proof.go's reconstructFromDetailedProof, line 330's
// `unsolvedLeaf(0)` lookup) relies on going the other direction.
// Returns nil for an empty input. Panics on a malformed proto where
// the step count does not match the implied tree shape.
func buildMSTree(steps []*proof.StepProto) *msNode {
	if len(steps) == 0 {
		return nil
	}
	root := &msNode{step: steps[0]}
	var stack []msTreeFrame
	if subN := len(steps[0].SubGoals); subN > 0 {
		stack = append(stack, msTreeFrame{root, subN})
	}
	for i := 1; i < len(steps); i++ {
		if len(stack) == 0 {
			panic(fmt.Sprintf("malformed DetailedProofProto: extra step at index %d after root closed (%d total steps)", i, len(steps)))
		}
		n := &msNode{step: steps[i]}
		top := len(stack) - 1
		stack[top].node.children = append(stack[top].node.children, n)
		stack[top].remaining--
		for len(stack) > 0 && stack[len(stack)-1].remaining == 0 {
			stack = stack[:len(stack)-1]
		}
		if subN := len(n.step.SubGoals); subN > 0 {
			stack = append(stack, msTreeFrame{n, subN})
		}
	}
	if len(stack) != 0 {
		open := 0
		for _, f := range stack {
			open += f.remaining
		}
		panic(fmt.Sprintf("malformed DetailedProofProto: %d open subgoal slot(s) remain after consuming all %d steps", open, len(steps)))
	}
	return root
}

type msTreeFrame struct {
	node      *msNode
	remaining int
}

// foldFinallyTails folds, per node, a trailing run of ≥2 identical
// parameterless closing leaves (whitelist: CnfRefute) into one
// synthetic Finally marker child — rendered as `Finally(CnfRefute())`,
// the broadcast terminator (proof.Finally). The fold applies only
// when at most one non-run child remains: with ≥2 substantive children
// the node renders as a Case block instead (native or Expect), where
// the trailing closers become labeled Case bodies — more structure
// than a broadcast.
//
// Case-eligible ministeps are exempt: their native labeled-Case
// rendering (fwd/bwd, base/step, …) outranks the fold.
//
// Purely a render-time tree transform: the recorded StepProto sequence
// is untouched, and Finally issues one inner Script.Do per folded leaf in
// the same leftmost-first order.
func (e *_Emitter) foldFinallyTails(n *msNode) *msNode {
	for i, c := range n.children {
		n.children[i] = e.foldFinallyTails(c)
	}
	if caseEligibleStep(n.step) {
		return n
	}
	start := len(n.children)
	for start > 0 && isFoldableClosingLeaf(n.children[start-1]) {
		start--
	}
	runLen := len(n.children) - start
	if runLen < 2 || start > 1 {
		return n
	}
	marker := &msNode{
		step:        n.children[start].step,
		finallyFold: runLen,
	}
	n.children = append(n.children[:start], marker)
	return n
}

// isFoldableClosingLeaf reports whether c is a leaf whose step is in
// the Finally-foldable whitelist. CnfRefute only for now: it is the
// corpus's trailing-terminator pattern, takes no arguments, and its
// refutation content lives in the CNF cache keyed by the leaf goal —
// the step itself carries nothing the fold could lose.
func isFoldableClosingLeaf(c *msNode) bool {
	if c.finallyFold > 0 || len(c.children) > 0 {
		return false
	}
	_, ok := c.step.Step.(*proof.StepProto_CnfRefute)
	return ok
}

// isCaseBlockNode reports whether n renders as a labeled Case block —
// native for case-eligible ministeps, Expect-wrapped otherwise. A
// trailing Finally marker means foldFinallyTails already reduced the
// node's substantive fan-out to ≤1, so it renders as a flat cascade.
func isCaseBlockNode(n *msNode) bool {
	return len(n.children) >= 2 && n.children[len(n.children)-1].finallyFold == 0
}

// sectionCite is how an `assert` whose claim an earlier section of the
// member proves renders: as a cite of that section's node. It is the
// record a session `cite-node` of a section's root leaves — an assert
// of the section's statement whose claim branch is the section's own
// proof again, under a `clear_hyps` when the citing goal carries
// hypotheses the section does not — and the member already holds that
// proof once, as the section's `ctx.Lemma`.
type sectionCite struct {
	// lemma is the earlier section's node ident.
	lemma string
	// installs says the assert and its claim branch render as ONE
	// `Cite(lemma)` on the spine: the cite verb, run on the assert's
	// goal, leaves the goal the recorded assert left
	// (citeInstallsAsAsserted). Where it would not, the assert keeps
	// its own rendering and `Cite(lemma)` closes its claim branch — the
	// claim branch's goal is the section's statement, which the cite
	// closes outright.
	installs bool
	// grounds says, with installs, that the step after the assert is
	// the one-entry specialize of the hypothesis the cite installs, so
	// the pair renders as the cite at its witnesses, `Cite(lemma, w…)`
	// (citeGroundsInstalled).
	grounds bool
}

// planSectionCites finds, in every section, the asserts whose claim an
// EARLIER section of the member proves, and decides how each renders
// (sectionCite). Rendering-only: the recorded steps are untouched, and
// the claim branch's own steps — the earlier section's proof, already
// rendered as that section's body — are set aside (sectionCitedSteps)
// so that neither the symbol walk nor the Go-used marking declares what
// only they would have printed.
func (e *_Emitter) planSectionCites() {
	e.sectionCites = map[*proof.StepProto]sectionCite{}
	e.sectionCitedSteps = map[*proof.StepProto]bool{}
	var setAside func(n *msNode)
	setAside = func(n *msNode) {
		e.sectionCitedSteps[n.step] = true
		for _, c := range n.children {
			setAside(c)
		}
	}
	for _, s := range e.sections {
		e.reader = s.reader
		var visit func(n *msNode)
		visit = func(n *msNode) {
			if cite, ok := e.sectionCiteAt(s, n); ok {
				e.sectionCites[n.step] = cite
				setAside(n.children[0])
				visit(n.children[1])
				return
			}
			for _, c := range n.children {
				visit(c)
			}
		}
		visit(buildMSTree(s.detailedSteps))
	}
}

// sectionCiteAt reports the cite node n renders as, when n is an assert
// whose claim branch proves an earlier section's statement.
func (e *_Emitter) sectionCiteAt(s *_SectionEmit, n *msNode) (sectionCite, bool) {
	if _, isAssert := n.step.Step.(*proof.StepProto_Assert); !isAssert || len(n.children) != 2 {
		return sectionCite{}, false
	}
	cited := e.sectionStatedBy(s, n.children[0])
	if cited == nil {
		return sectionCite{}, false
	}
	cite := sectionCite{lemma: e.citeSection(cited)}
	cite.installs = e.citeInstallsAsAsserted(n, cited.goal)
	cite.grounds = cite.installs && e.citeGroundsInstalled(n, cited.goal)
	return cite, true
}

// sectionStatedBy returns the section s may cite (citableSectionsFor)
// whose statement is the goal of claim — or of claim's one child when
// claim is the `clear_hyps` that weakens the citing context to the
// section's — up to α. nil when no such section states it.
func (e *_Emitter) sectionStatedBy(s *_SectionEmit, claim *msNode) *_SectionEmit {
	candidates := []*msNode{claim}
	if _, clears := claim.step.Step.(*proof.StepProto_ClearHyps); clears && len(claim.children) == 1 {
		candidates = append(candidates, claim.children[0])
	}
	for _, n := range candidates {
		goal, _ := e.reader.Prop(n.step.Goal)
		if goal == nil {
			continue
		}
		key := goal.AlphaKey()
		for _, citable := range e.citableSectionsFor(s) {
			if citable.outKey == key {
				return citable
			}
		}
	}
	return nil
}

// citeInstallsAsAsserted reports whether `Cite(<section>)`, run on the
// goal of assert n, leaves exactly the goal the recorded assert left —
// the section's statement added as a hypothesis, nothing else moved.
// The check runs the cite verb's own stages against the recorded goals
// (prover/proof/fact.go, Cite): the statement must neither close the
// goal outright nor be the goal up to Normalize, and the preserving
// install (proof.LemmaPreserveInstall, the verb's own) must return the
// statement's reproduction obligation and a residual α-equal to the
// recorded one. An install
// that chains backward on the conclusion, rewrites with the statement,
// generalizes a variable the statement leaves free, or takes the
// statement at another type instance returns something else, and is
// declined here by its result.
func (e *_Emitter) citeInstallsAsAsserted(n *msNode, statement core.Prop) bool {
	goal, _ := e.reader.Prop(n.step.Goal)
	residual, _ := e.reader.Prop(n.children[1].step.Goal)
	if goal == nil || residual == nil {
		return false
	}
	if prop.IsStronger(statement, goal) {
		return false
	}
	normalizedGoal, _ := proof.Normalize(goal)
	normalizedStatement, _ := proof.Normalize(statement)
	if normalizedGoal.AlphaKey() == normalizedStatement.AlphaKey() {
		return false
	}
	installed := proof.LemmaPreserveInstall(statement, goal)
	return installed != nil && installed.Size() == 2 &&
		prop.IsStronger(statement, installed.ChildGoal(0)) &&
		installed.ChildGoal(1).AlphaEquals(residual)
}

// citeGroundsInstalled reports whether the step after assert n — an
// assert citeInstallsAsAsserted holds for — is the grounding the cite
// verb's witness form performs: a specialize of ONE hypothesis, the one
// the cite installs (installedHypIndexStatic, the runtime locator's
// mirror), at one or more witnesses. The witness form also discharges
// the guards of the instance it leaves from the context
// (prover/proof/apply_close.go, dischargeGuards), which the recorded
// specialize did not, and types a statement with type variables by its
// witnesses before it installs it (witness_order.go), where the bare
// verb reads the goal; so an instance that is an implication, and a
// statement with type variables, keep their own Specialize after a
// bare cite.
func (e *_Emitter) citeGroundsInstalled(n *msNode, statement core.Prop) bool {
	if ext.PropHasTypeVars(statement) {
		return false
	}
	spec := n.children[1]
	sp, isSpecialize := spec.step.Step.(*proof.StepProto_Specialize)
	if !isSpecialize || len(sp.Specialize.GetHyps()) != 1 || len(spec.children) != 1 {
		return false
	}
	entry := sp.Specialize.GetHyps()[0]
	if len(entry.GetWitnesses()) == 0 {
		return false
	}
	before, _ := e.reader.Prop(n.step.Goal)
	after, _ := e.reader.Prop(spec.step.Goal)
	grounded, _ := e.reader.Prop(spec.children[0].step.Goal)
	if before == nil || after == nil || grounded == nil {
		return false
	}
	if installedHypIndexStatic(before, after, statement) != int(entry.GetHypIndex()) {
		return false
	}
	instance := hypsIntroduced(after, grounded)
	if len(instance) != 1 {
		return false
	}
	_, _, guarded := ext.MatchesIMPLY(instance[0])
	return !guarded
}

// tryCiteFusion checks whether (a, b) is the `Lemma(L) + KnownThm(L)`
// idiom — a is a lemma / lemma_preserve ministep and b a KnownThm whose
// StrongerGoal is alpha-equal to a's payload — and returns the cite
// target expression the pair renders as: `Cite(<L>)`, the consolidated
// verb, which decides install-vs-close and the install form from the
// goal state per call (prover/proof/fact.go). The two recorded
// spellings encode a plumbing fact about the RECORDING, and a member is
// not a recording: its replay re-derives the state, so it wants the verb
// that reads as mathematics.
func (e *_Emitter) tryCiteFusion(a, b *proof.StepProto) (string, bool) {
	var lemmaRef *ext.HolPropProto
	switch s := a.Step.(type) {
	case *proof.StepProto_Lemma:
		lemmaRef = s.Lemma
	case *proof.StepProto_LemmaPreserve:
		lemmaRef = s.LemmaPreserve
	default:
		return "", false
	}
	bKnown, ok := b.Step.(*proof.StepProto_KnownThm)
	if !ok {
		return "", false
	}
	propA, _ := e.reader.Prop(lemmaRef)
	propB, _ := e.reader.Prop(bKnown.KnownThm.GetStrongerGoal())
	if propA.AlphaKey() != propB.AlphaKey() {
		return "", false
	}
	if r := bKnown.KnownThm.GetReading(); r.GetLaw() != nil {
		// The install of a law read at an instance, its claim certified
		// by the reading (the session's `lemma {key, read_at}`).
		return e.readingExpr(r, e.hypHandleByUse[_HypUse{step: b}]), true
	}
	return e.lemmaRefExprCtx(propA, leafCite), true
}

// tryCiteSpecializeFusion extends tryCiteFusion one node further: when
// the residual continuation of a fused `lemma_preserve + known_thm`
// cite is a single-entry `specialize` step that grounds EXACTLY the
// hyp the cite just installed, the triple renders as ONE
// `Cite(<L>, w₁, …, wₖ)` (CiteKeep for keep_sources) — the cite-at-use
// fused form. Rendering-only: the runtime Action performs
// the same three applies the unfused sequence records (lemma_preserve,
// known_thm, composite specialize), locating the installed hyp by
// content at replay instead of by the recorded index. The recorded step
// sequence and every CNF cache key are unchanged; only the naked hyp
// index disappears from the Go surface.
//
// The "grounds exactly the installed hyp" check is static, against the
// per-step goals the proto records, and mirrors the runtime locator
// exactly (installedHypIndex): of the hyps present in the specialize
// step's input goal but absent from the lemma step's input goal, the one
// α-equal to the cited payload's conclusion is the installed one, else
// the sole net-new hyp. Fusion requires the recorded HypIndex to name
// what the locator will pick (goal hyp lists are content-sorted, so the
// index is deterministic). Any mismatch — tag-10 `lemma` install
// (different runtime semantics), multi-entry specialize, zero witnesses,
// missing recorded goals, unlocatable hyp, index drift — declines, and
// the plain two-call rendering applies.
//
// The content half of the locator is what makes ABSORPTION SITES fuse:
// a cite into a clause-shaped goal nets the lemma's hyp AND the goal's
// folded disjuncts, so a pure diff is ambiguous; the unfused fallback
// puts a bare hyp index in the output, which trips
// TestLintNoPositionalHypIndices. Same session move, same recorded
// steps, one rendering.
//
// Returns the full call argument list (payload expr + witness exprs),
// the fused constructor name, and the specialize node whose children
// are the continuation the caller must keep walking.
func (e *_Emitter) tryCiteSpecializeFusion(n *msNode) (name, args string, spec *msNode, ok bool) {
	if len(n.children) != 2 {
		return "", "", nil, false
	}
	// Only the `lemma_preserve` install fuses. A tag-10 `lemma` install
	// replays through the ADAPTIVE ApplyLemma, while the fused Action
	// installs the payload exactly — the two can pick different σ. This
	// is checked on the proto, since both installs render as the same
	// `Cite` verb.
	if _, isPreserve := n.step.Step.(*proof.StepProto_LemmaPreserve); !isPreserve {
		return "", "", nil, false
	}
	expr, citeOK := e.tryCiteFusion(n.step, n.children[0].step)
	if !citeOK {
		return "", "", nil, false
	}
	spec = n.children[1]
	sp, isSpec := spec.step.Step.(*proof.StepProto_Specialize)
	if !isSpec || len(sp.Specialize.GetHyps()) != 1 {
		return "", "", nil, false
	}
	entry := sp.Specialize.GetHyps()[0]
	if len(entry.GetWitnesses()) == 0 {
		return "", "", nil, false
	}
	if n.step.Goal == nil || spec.step.Goal == nil {
		return "", "", nil, false
	}
	// NB: PoolReader.Prop's second return is the recorded ClaimProved
	// flag, not a success indicator — mirror keyFromGoalProto's nil
	// check instead.
	before, _ := e.reader.Prop(n.step.Goal)
	after, _ := e.reader.Prop(spec.step.Goal)
	if before == nil || after == nil {
		return "", "", nil, false
	}
	installed, _ := e.reader.Prop(n.step.Step.(*proof.StepProto_LemmaPreserve).LemmaPreserve)
	if installed == nil {
		return "", "", nil, false
	}
	if installedHypIndexStatic(before, after, installed) != int(entry.GetHypIndex()) {
		return "", "", nil, false
	}
	name = "Cite"
	if sp.Specialize.GetKeepSources() {
		name = "CiteKeep"
	}
	parts := make([]string, 0, len(entry.GetWitnesses())+1)
	parts = append(parts, expr)
	for _, ref := range entry.GetWitnesses() {
		parts = append(parts, e.witnessExpr(e.reader.Term(ref)))
	}
	return name, strings.Join(parts, ", "), spec, true
}

// deriveStaircaseMin is the chain length at which a right-nested
// AssertStep run becomes a Derive block. Two consecutive claim/continue
// nestings is the constitution's own flag rule for the staircase shape
// (§"Argument structure"): one assert is a genuine binary branch and
// keeps AssertStep.
const deriveStaircaseMin = 2

// collectAssertStaircase walks the residual spine of a right-nested
// `assert` run — each AssertStep's SECOND child (the continuation)
// being the next AssertStep — and returns the chain plus the tail
// subtree that closes the goal.
//
// The shape is what a session records when it establishes k facts in
// order, and it is the staircase the plan bans from bodies:
// the i-th continuation has no independent mathematical identity to
// label, so the "after" labels degenerate into control-flow filler no
// matter how disciplined the author. Derive dissolves the obligation
// instead — each fact is a labeled `a.Have` whose VALUE flows into the
// later premise lists, and the close is `a.Show`.
//
// Requires every intermediate continuation to be a bare spine step
// (exactly the next assert, nothing beside it), because that is what
// `a.Have` reproduces: its desugar leaves the continuation Case empty_set
// and carries on down the spine.
//
// An assert that renders whole as a cite of an earlier section
// (sectionCite.installs) is no Have — it states nothing of its own —
// so the run ends before it and the cite opens the tail. So does an
// assert that opens an induction by a cited principle (planByInductions):
// its asserts are the verb's obligations, so the Haves stop there and
// the tail is `Show(…, ByInduction(…))`.
//
// An assert whose continuation opens the asserted ∃ at once
// (obtainStrip) is an Obtain, and the run continues below the strip. An
// Obtain has no AssertStep spelling a chapter writes, so a run holding
// one is a block however short.
func (e *_Emitter) collectAssertStaircase(n *msNode) (chain []*msNode, tail *msNode, ok bool) {
	cur := n
	obtains := false
	for {
		if _, isAssert := cur.step.Step.(*proof.StepProto_Assert); !isAssert {
			break
		}
		if len(cur.children) != 2 || cur.finallyFold > 0 {
			break
		}
		if e.sectionCites[cur.step].installs || e.byInductions[cur.step] != nil {
			break
		}
		chain = append(chain, cur)
		if strip := e.obtainStrip(cur); strip != nil {
			if e.obtained == nil {
				e.obtained = map[*proof.StepProto]*msNode{}
			}
			e.obtained[cur.step] = strip
			obtains = true
			cur = strip.children[0]
			continue
		}
		cur = cur.children[1]
	}
	if cur == nil || len(chain) == 0 || len(chain) < deriveStaircaseMin && !obtains {
		return nil, nil, false
	}
	return chain, cur, true
}

// obtainStrip reports the step that opens an assert's ∃ at once — the
// shape Argument.Obtain records: the assert, and on its continuation a
// `strip_quant` at the very hypothesis the assert added, with one
// child. nil for anything else, and for a claim whose ∃-prefix no
// Obtain verb opens (obtainVerbs).
func (e *_Emitter) obtainStrip(n *msNode) *msNode {
	strip := n.children[1]
	sq, ok := strip.step.Step.(*proof.StepProto_StripQuant)
	if !ok || sq.StripQuant == nil || sq.StripQuant.HypIndex == nil || len(strip.children) != 1 || strip.finallyFold > 0 {
		return nil
	}
	claim, _ := e.reader.Prop(n.step.Step.(*proof.StepProto_Assert).Assert)
	goal, _ := e.reader.Prop(strip.step.Goal)
	idx := int(*sq.StripQuant.HypIndex)
	if claim == nil || goal == nil || idx >= goal.NumHyps() || obtainVerbs[existsPrefixLen(claim.Conclusion())] == "" ||
		!goal.Hyp(idx).AlphaEquals(claim.Conclusion()) {
		return nil
	}
	return strip
}

// obtainVerbs names the Obtain verb by its witness count. The strip
// opens the claim's whole ∃-prefix and each verb opens exactly its own
// count (prover/proof/derive.go obtainN), so the prefix length picks
// the verb; a longer prefix has none and stays an assert and its strip.
var obtainVerbs = map[int]string{1: "Obtain", 2: "Obtain2", 3: "Obtain3", 4: "Obtain4", 5: "Obtain5"}

// existsPrefixLen counts t's leading ∃-binders.
func existsPrefixLen(t core.Term) int {
	n := 0
	for abs := ext.MatchesEXISTS(t); !abs.IsZero(); abs = ext.MatchesEXISTS(abs.Body()) {
		n++
	}
	return n
}

// obtainedInstance is the hypothesis an Obtain's Skolemization adds —
// the instance of the ∃ its strip opened, the fact Obtain returns.
func (e *_Emitter) obtainedInstance(strip *msNode) core.Prop {
	before, _ := e.reader.Prop(strip.step.Goal)
	after, _ := e.reader.Prop(strip.children[0].step.Goal)
	if before == nil || after == nil {
		return nil
	}
	for i := 0; i < after.NumHyps(); i++ {
		if h := after.Hyp(i); !before.AnyHyp(h.AlphaEquals) {
			return core.MakeProp(h)
		}
	}
	return nil
}

// byInductionFusion is a recorded induction by a cited principle, as
// the Go verb ByInduction records it (prover/proof/induction.go — a
// spelling of this shape, not a step of its own): one assert per
// obligation of the principle, in the principle's order, and a by that
// closes the goal from the asserted obligations, the principle grounded
// at its tuple, and whatever extras the conclusion needs.
type byInductionFusion struct {
	cases []*msNode // the asserts, one per obligation
	by    *proof.ByProto
	// principle is the principle as the verb cites it: the recorded
	// premise, or — where the recorded predicate is the one the goal
	// reads (proof.InductionMotive) — that premise at the witnesses
	// before the predicate alone.
	principle *proof.ByPremiseProto
	extras    []*proof.ByPremiseProto
}

// planByInductions finds every induction by a cited principle in the
// sections' records (byInductionAt) before the symbol passes run: an
// assert of such a chain prints no claim text, so nothing of the
// claim's is a Go-used ident, and the chain renders as the verb
// (renderByInduction) where a Derive block or an AssertStep fan would
// otherwise render it.
func (e *_Emitter) planByInductions() {
	e.byInductions = map[*proof.StepProto]*byInductionFusion{}
	e.byInductionAsserts = map[*proof.StepProto]bool{}
	for _, s := range e.sections {
		e.reader = s.reader
		var visit func(n *msNode)
		visit = func(n *msNode) {
			if n == nil {
				return
			}
			if f := e.byInductionAt(n); f != nil {
				e.byInductions[n.step] = f
				for _, c := range f.cases {
					e.byInductionAsserts[c.step] = true
					// The cases' own proofs may hold inductions too.
					visit(c.children[0])
				}
				return
			}
			for _, c := range n.children {
				visit(c)
			}
		}
		visit(e.foldFinallyTails(buildMSTree(s.detailedSteps)))
	}
}

// byInductionAt reads the shape ByInduction records off n: a run of
// asserts down the continuation spine whose tail is a by with exactly
// one named premise grounded at a tuple — the principle — such that the
// obligations the principle has at that tuple (proof.InductionObligations)
// are, in order, the asserted claims, each of which the by also names
// as a resident premise. Every other premise is an extra. Anything else
// is nil: an assert run whose tail is not that by is a Derive block.
func (e *_Emitter) byInductionAt(n *msNode) *byInductionFusion {
	var chain []*msNode
	cur := n
	for cur != nil {
		if _, isAssert := cur.step.Step.(*proof.StepProto_Assert); !isAssert {
			break
		}
		if len(cur.children) != 2 || cur.finallyFold > 0 || e.sectionCites[cur.step].installs {
			break
		}
		chain = append(chain, cur)
		cur = cur.children[1]
	}
	if len(chain) == 0 || cur == nil {
		return nil
	}
	by, isBy := cur.step.Step.(*proof.StepProto_By)
	if !isBy || by.By == nil || by.By.GetArith() || by.By.GetSettac() || by.By.GetBroadcast() {
		return nil
	}
	var principle *proof.ByPremiseProto
	var others []*proof.ByPremiseProto
	for _, p := range e.byPremisesPrinted(by.By) {
		if !p.GetResident() && !p.GetDerived() && p.GetReading().GetLaw() == nil && len(p.GetWitnesses()) > 0 {
			if principle != nil {
				return nil
			}
			principle = p
			continue
		}
		others = append(others, p)
	}
	if principle == nil {
		return nil
	}
	stated, _ := e.reader.Prop(principle.GetInstall())
	if stated == nil {
		return nil
	}
	witnesses := make([]core.Term, len(principle.GetWitnesses()))
	for i, ref := range principle.GetWitnesses() {
		witnesses[i] = e.reader.Term(ref)
	}
	obligations, err := proof.InductionObligations(stated, witnesses, "the principle")
	if err != nil || len(obligations) != len(chain) {
		return nil
	}
	claims := make([]core.Prop, len(chain))
	for i, node := range chain {
		claim, _ := e.reader.Prop(node.step.Step.(*proof.StepProto_Assert).Assert)
		if claim == nil || !claim.Conclusion().AlphaEquals(obligations[i].Conclusion()) {
			return nil
		}
		claims[i] = claim
	}
	// Each claim is a resident premise of the by; the rest are extras.
	stated_ := make([]bool, len(claims))
	var extras []*proof.ByPremiseProto
	for _, p := range others {
		consumed := false
		if namesResidentHypothesis(p) && len(p.GetWitnesses()) == 0 {
			for i, claim := range claims {
				if !stated_[i] && e.residentPremiseOf(p, claim.Conclusion()) {
					stated_[i] = true
					consumed = true
					break
				}
			}
		}
		if !consumed {
			extras = append(extras, p)
		}
	}
	for _, s := range stated_ {
		if !s {
			return nil
		}
	}
	return &byInductionFusion{cases: chain, by: by.By, principle: e.citedBeforePredicate(n, principle, stated, witnesses, extras), extras: extras}
}

// citedBeforePredicate is the principle premise as the verb cites it.
// Where the recorded tuple is the one ByInduction reads from the goal
// for a cite that stops before the predicate — the principle bare, or
// at its parameters — the premise is returned at those leading
// witnesses alone, the shortest such cite; otherwise as recorded. n is
// the induction's own leaf, the extras the facts beside the principle.
func (e *_Emitter) citedBeforePredicate(n *msNode, principle *proof.ByPremiseProto, stated core.Prop, witnesses []core.Term, extras []*proof.ByPremiseProto) *proof.ByPremiseProto {
	goal, _ := e.reader.Prop(n.step.Goal)
	slot, isPrinciple := proof.PredicateSlot(stated.Conclusion())
	if goal == nil || !isPrinciple {
		return principle
	}
	var facts []core.Term
	for _, p := range extras {
		if namesResidentHypothesis(p) && len(p.GetWitnesses()) == 0 {
			if install, _ := e.reader.Prop(p.GetInstall()); install != nil {
				facts = append(facts, install.Conclusion())
			}
		}
	}
	for k := 0; k <= slot && k <= len(witnesses); k++ {
		tuple, _, err := proof.InductionMotive(stated, witnesses[:k], goal, facts, nil, "the principle")
		if err != nil || len(tuple) != len(witnesses) {
			continue
		}
		same := true
		for i := range tuple {
			if !tuple[i].AlphaEquals(witnesses[i]) {
				same = false
				break
			}
		}
		if same {
			cited := proto.Clone(principle).(*proof.ByPremiseProto)
			cited.Witnesses = cited.Witnesses[:k]
			return cited
		}
	}
	return principle
}

// renderByInduction renders a fused induction as the verb:
//
//	ByInduction(At(<principle>, w…), <shaping>, <extras>,
//		Case("case_0: <obligation>", <its proof>),
//		…
//	),
//
// with the principle cited before its predicate where the recorded
// predicate is the one the goal reads (citedBeforePredicate).
//
// The labels carry the numbered role tag, which the chapter lint
// refuses: a pasted induction stays red until each case is restated as
// the mathematics it carries, the one thing the verb cannot compute.
func (e *_Emitter) renderByInduction(b *strings.Builder, s *_SectionEmit, f *byInductionFusion, indent string) {
	args := []string{e.byPremiseExpr(f.principle)}
	if sh := f.by.GetShape(); sh != nil {
		args = append(args, e.byShapeArgs(sh)...)
	}
	for _, p := range f.extras {
		args = append(args, e.byPremiseExpr(p))
	}
	fmt.Fprintf(b, "%sByInduction(%s,\n", indent, strings.Join(args, ", "))
	for i, node := range f.cases {
		branch := node.children[0]
		branchGoal, _ := e.reader.Prop(branch.step.Goal)
		fmt.Fprintf(b, "%s\tCase(%q,\n", indent, fmt.Sprintf("case_%d: %s", i, e.conclusionLabel(branchGoal)))
		b.WriteString(e.contextComment(indent+"\t\t", branchGoal))
		if cite, cited := e.sectionCites[node.step]; cited {
			fmt.Fprintf(b, "%s\t\tCite(%s),\n", indent, cite.lemma)
		} else {
			e.renderStepExpr(b, s, branch, indent+"\t\t")
		}
		fmt.Fprintf(b, "%s\t),\n", indent)
	}
	fmt.Fprintf(b, "%s),\n", indent)
}

// tryDeriveFusion reports whether n opens an assert staircase worth
// rendering as a Derive block: a run collectAssertStaircase takes, or a
// lone a.Unfolded, which has no AssertStep spelling a chapter writes
// (loneUnfolded).
func (e *_Emitter) tryDeriveFusion(n *msNode) ([]*msNode, *msNode, bool) {
	if chain, tail, ok := e.collectAssertStaircase(n); ok {
		return chain, tail, true
	}
	return e.loneUnfolded(n)
}

// deriveReceiver names the Argument receiver at a Derive nesting depth:
// the chartered `a` at depth 0, then the free names in order — the
// letters from `b` on, then arg1, arg2, … once the letters run out. A
// name is free when no declared symbol, no scaffold name
// (reservedIdent) and not the closure's own receiver uses it, so a
// nested receiver never shadows a local the block's steps reference.
// `h` is never a receiver: it is the name a Given branch's hypothesis
// handle is drawn under (renderGivenBranch), and a handle stays in scope
// through every block nested in its branch. The name is a function of
// the depth and the declarations alone, so argumentReceiver recomputes
// it.
func (e *_Emitter) deriveReceiver(depth int) string {
	if depth <= 0 {
		if e.closureReceiver != "" {
			return e.closureReceiver
		}
		return "a"
	}
	taken := e.declSet()
	free := func(name string) bool {
		return !taken[name] && !e.reservedIdent(name) && name != e.closureReceiver
	}
	for r := 'b'; r <= 'z'; r++ {
		if r != 'h' && free(string(r)) {
			if depth--; depth == 0 {
				return string(r)
			}
		}
	}
	for n := 1; ; n++ {
		if name := fmt.Sprintf("arg%d", n); free(name) {
			if depth--; depth == 0 {
				return name
			}
		}
	}
}

// argumentReceiver names the Argument the steps being rendered run
// under: the member closure's own `a`, or the receiver of the innermost
// Derive block or Given branch around them.
func (e *_Emitter) argumentReceiver() string {
	return e.deriveReceiver(e.deriveDepth - 1)
}

// renderDeriveBlock renders an assert staircase as
//
//	Derive(func(a *Argument) {
//	 a.Have("<claim>", <claim prop>, <proof…>)
//	 …
//	 a.Show("<goal>", <closing…>)
//	})
//
// The desugar is tree-identical to the nesting it replaces (Have runs
// the SAME bare AssertStep with a claim Case and an empty continuation
// Case), so recorded goal keys and pbs are untouched — the reason this
// is a rendering change and not a proof change.
//
// Labels are the same goal-text labels the Case rendering produces.
// They are placeholders in the sense: naming a fact for what it
// MEANS is the author's judgment, and emit deliberately does not
// invent it (constitution §"The session": emit-section is a machine
// interface, not a chapter-code generator).
// The caller positions the opening (no leading indent is written);
// `indent` is the level the closing brace and the block's statements
// hang off.
func (e *_Emitter) renderDeriveBlock(b *strings.Builder, s *_SectionEmit, chain []*msNode, tail *msNode, indent string) {
	recv := e.deriveReceiver(e.deriveDepth)
	e.deriveDepth++
	defer func() { e.deriveDepth-- }()

	fmt.Fprintf(b, "Derive(func(%s *Argument) {\n", recv)
	e.renderDeriveStatements(b, s, chain, tail, recv, indent+"\t")
	fmt.Fprintf(b, "%s})", indent)
}

// haveHandleIdents decides, for each Have of a Derive block, whether
// its Fact is bound to a Go ident: it is when a step LATER in the
// block — inside a later Have's proof or under the Show, the stretch
// the ident is in scope for — uses the hypothesis that Have introduced.
// Two uses are read:
//
//   - a hyp-addressing ministep that rewrites with the hypothesis. The
//     recorded step carries the hyp's position; the position is resolved
//     back to the Have by CONTENT (the goal's hyp at that index α-equals
//     the claim), which is exactly what the handle does at replay
//     (HypHandle tracks the hyp by content), so the rendered
//     `fact1.Rw()` runs the identical ministep and the recorded keys are
//     untouched. A step addressing a hyp no Have introduced (an
//     assumption a strip left, a transformed fact) keeps its positional
//     spelling — the lint then names it, loudly.
//   - a resident premise of a `by` whose statement is the claim, up to
//     bound names (residentPremiseOf), where the claim is a hypothesis
//     of every goal from the Have down to that `by`. There the Have's
//     Fact names the hypothesis the claim states, and the By reads
//     `fact1` as the record's premise: the hypothesis itself, resident,
//     grounded at the same witnesses. Where a step in between rewrites
//     the hypothesis or drops it, the handle names something else or
//     nothing, and the premise keeps its statement (`ResidentHyp(…)`);
//     so does a `by` outside the stretch — another branch, an earlier
//     Have's proof — where the ident is not in scope.
//
// A use an enclosing block's Have already names is left to that Have.
//
// Returns one ident per chain node ("" for a Have nothing uses) and
// records the use → ident mapping the step and premise renderers read.
func (e *_Emitter) haveHandleIdents(chain []*msNode, tail *msNode) []string {
	idents := make([]string, len(chain))
	var pending []_PendingBranches
	for i, node := range chain {
		claim, _ := e.reader.Prop(node.step.Step.(*proof.StepProto_Assert).Assert)
		if strip := e.obtained[node.step]; strip != nil {
			claim = e.obtainedInstance(strip)
		}
		if claim == nil {
			continue
		}
		var placed []_PlacedUse
		var path []*msNode
		note := func(use _HypUse, rewrite bool) {
			if _, named := e.hypHandleByUse[use]; !named {
				placed = append(placed, _PlacedUse{use: use, path: slices.Clone(path), rewrite: rewrite})
			}
		}
		// held is the hypothesis as it stands at each node visited: the
		// fact as the Have stated it, or as a Simp at it rewrote it.
		held := map[*msNode]core.Term{}
		// resident says content is a hypothesis of every goal from the
		// Have's continuation down to n's parent.
		var visit func(n *msNode, resident bool, content core.Term)
		visit = func(n *msNode, resident bool, content core.Term) {
			if n == nil || e.sectionCitedSteps[n.step] {
				return
			}
			path = append(path, n)
			defer func() { path = path[:len(path)-1] }()
			held[n] = content
			goal, _ := e.reader.Prop(n.step.Goal)
			resident = resident && goal != nil && goal.AnyHyp(content.AlphaEquals)
			rewrites := false
			if idx, ok := hypAddressedBy(n.step); ok {
				if goal != nil && idx < goal.NumHyps() && goal.Hyp(idx).AlphaEquals(content) {
					_, rewrites = n.step.Step.(*proof.StepProto_SimpWith)
					note(_HypUse{step: n.step}, rewrites)
				}
			}
			if by, ok := n.step.Step.(*proof.StepProto_By); ok && resident {
				for _, p := range e.byPremisesPrinted(by.By) {
					if e.residentPremiseOf(p, content) || e.readingUnderPremiseOf(p, content) {
						note(_HypUse{premise: p}, false)
					}
				}
			}
			if simp, ok := n.step.Step.(*proof.StepProto_SimpWith); ok && resident && simp.SimpWith != nil {
				// A resident simp rule stating this hypothesis is a use of
				// the fact (residentSimpRules): the rule renders as it.
				refs := simp.SimpWith.GetRules()
				rules := make([]core.Prop, len(refs))
				for r, ref := range refs {
					rules[r], _ = e.reader.Prop(ref)
				}
				for r, isResident := range residentSimpRules(goal, simp.SimpWith, rules) {
					if isResident && rules[r].Conclusion().AlphaEquals(content) {
						note(_HypUse{step: n.step, rule: r + 1}, false)
					}
				}
			}
			for k, c := range n.children {
				next := content
				if rewrites && k == len(n.children)-1 {
					// A Simp at the fact rewrites it in its place, and
					// the fact goes on naming the rewritten hypothesis
					// from the residual — the step's last child — down
					// (HypHandle.Simp).
					if residual, _ := e.reader.Prop(c.step.Goal); residual != nil {
						if introduced := hypsIntroduced(goal, residual); len(introduced) == 1 {
							next = introduced[0]
						}
					}
				}
				visit(c, resident, next)
			}
		}
		for _, later := range chain[i+1:] {
			if len(later.children) > 0 {
				visit(later.children[0], true, claim.Conclusion())
			}
		}
		visit(tail, true, claim.Conclusion())
		kept, branches := branchLocalUses(placed)
		if len(kept) > 0 {
			e.factHandleCount++
			idents[i] = e.freshIdent(fmt.Sprintf("fact%d", e.factHandleCount), e.handleNamesTaken())
			e.nameHandleUses(kept, idents[i])
		}
		pending = append(pending, _PendingBranches{held: held, branches: branches})
	}
	// The subtrees that bind a fact of their own are named after the
	// block's Haves, which keep the block's numbering.
	for _, p := range pending {
		e.bindBranchFacts(p.held, p.branches)
	}
	return idents
}

// _PendingBranches is one Have's subtrees that bind a fact of their own,
// with the hypothesis as it stands at each node visited.
type _PendingBranches struct {
	held     map[*msNode]core.Term
	branches []_BranchUses
}

// _BranchUses is a subtree that binds a fact of its own, by its root,
// and the uses inside it.
type _BranchUses struct {
	root []*msNode
	uses []_PlacedUse
}

// nameHandleUses records ident as the Go name of every use.
func (e *_Emitter) nameHandleUses(uses []_PlacedUse, ident string) {
	if e.hypHandleByUse == nil {
		e.hypHandleByUse = map[_HypUse]string{}
	}
	for _, u := range uses {
		e.hypHandleByUse[u.use] = ident
	}
}

// bindBranchFacts names each subtree's fact and the uses in it, the
// subtrees nested in it in turn (branchLocalUses).
func (e *_Emitter) bindBranchFacts(held map[*msNode]core.Term, branches []_BranchUses) {
	for _, branch := range branches {
		root := branch.root[len(branch.root)-1]
		content := held[root]
		goal, _ := e.reader.Prop(root.step.Goal)
		if content == nil || goal == nil || !goal.AnyHyp(content.AlphaEquals) {
			panic("emit: a subtree that binds a fact of its own does not hold the hypothesis at its root")
		}
		kept, nested := branchLocalUses(branch.uses)
		e.factHandleCount++
		ident := e.freshIdent(fmt.Sprintf("fact%d", e.factHandleCount), e.handleNamesTaken())
		e.nameHandleUses(kept, ident)
		if e.branchFacts == nil {
			e.branchFacts = map[*proof.StepProto][]_BranchFact{}
		}
		e.branchFacts[root.step] = append(e.branchFacts[root.step], _BranchFact{ident: ident, content: content})
		e.bindBranchFacts(held, nested)
	}
}

// branchLocalUses splits one fact's uses, in rendering order, into those
// its handle names and the subtrees that must bind a fact of their own.
// A Simp at the fact moves its handle to the Simp's residual (Fact.Simp),
// so a use rendered after the Simp outside that residual's subtree — the
// main line after a Have whose proof rewrote the fact, a later case —
// could not resolve it. Where the two diverge, the subtree holding the
// Simp binds its own fact over the same hypothesis: the Simp and every
// use inside move that one, and the fact outside stays where it was
// bound. The outermost such subtrees are returned; the uses inside one
// are split again against its own handle.
func branchLocalUses(placed []_PlacedUse) (kept []_PlacedUse, branches []_BranchUses) {
	var roots [][]*msNode
	for at, s := range placed {
		if !s.rewrite {
			continue
		}
		node := s.path[len(s.path)-1]
		split := -1
		for _, u := range placed[at+1:] {
			if slices.Contains(u.path, node) {
				continue
			}
			d := 0
			for d < len(s.path) && d < len(u.path) && s.path[d] == u.path[d] {
				d++
			}
			if d >= len(u.path) {
				panic("emit: a hypothesis use is rendered after a Simp below it")
			}
			if split < 0 || d < split {
				split = d
			}
		}
		if split >= 0 {
			roots = append(roots, s.path[:split+1])
		}
	}
	// Only the outermost: a subtree inside another is that one's to split.
	outermost := roots[:0:0]
	for _, r := range roots {
		inside := false
		for _, o := range roots {
			if len(o) < len(r) && slices.Contains(r, o[len(o)-1]) {
				inside = true
			}
		}
		if !inside && !slices.ContainsFunc(outermost, func(o []*msNode) bool { return o[len(o)-1] == r[len(r)-1] }) {
			outermost = append(outermost, r)
		}
	}
	branches = make([]_BranchUses, len(outermost))
	for i, r := range outermost {
		branches[i].root = r
	}
	for _, u := range placed {
		in := slices.IndexFunc(outermost, func(r []*msNode) bool { return slices.Contains(u.path, r[len(r)-1]) })
		if in < 0 {
			kept = append(kept, u)
			continue
		}
		branches[in].uses = append(branches[in].uses, u)
	}
	return kept, branches
}

// renderBranchFact renders the root of a subtree that binds facts of
// its own (branchFacts) as the Derive block that binds every one of
// them before the subtree's steps,
//
//	Derive(func(c *Argument) {
//		fact3 := c.Hyp(<a hypothesis>)
//		fact4 := c.Hyp(<another hypothesis>)
//		c.Show("<goal>", <the subtree's steps>)
//	}),
//
// Hyp records nothing, so the tree and every recorded key are the
// subtree's own.
func (e *_Emitter) renderBranchFact(b *strings.Builder, s *_SectionEmit, n *msNode, facts []_BranchFact, indent string) {
	if e.branchFactOpened == nil {
		e.branchFactOpened = map[*proof.StepProto]bool{}
	}
	e.branchFactOpened[n.step] = true
	goal, _ := e.reader.Prop(n.step.Goal)
	recv := e.deriveReceiver(e.deriveDepth)
	e.deriveDepth++
	defer func() { e.deriveDepth-- }()
	fmt.Fprintf(b, "%sDerive(func(%s *Argument) {\n", indent, recv)
	for _, fact := range facts {
		statement := prop.MakeProp(fact.content)
		e.markGoUsedFromPropPayload(statement)
		fmt.Fprintf(b, "%s\t%s := %s.Hyp(%s)\n", indent, fact.ident, recv, e.miniStepPropExpr(statement))
	}
	fmt.Fprintf(b, "%s\t%s.Show(%q,\n", indent, recv, e.conclusionLabel(goal))
	e.renderStepExpr(b, s, n, indent+"\t\t")
	fmt.Fprintf(b, "%s\t)\n", indent)
	fmt.Fprintf(b, "%s}),\n", indent)
}

// hypAddressedBy reports the hyp index a ministep addresses when it
// has a handle form (HypHandle.Rw / Subst / CongrArg).
func hypAddressedBy(step *proof.StepProto) (int, bool) {
	switch s := step.Step.(type) {
	case *proof.StepProto_Rw:
		return int(s.Rw.GetHypIndex()), true
	case *proof.StepProto_Subst:
		return int(s.Subst), true
	case *proof.StepProto_CongrArg:
		if s.CongrArg == nil {
			return 0, false
		}
		return int(s.CongrArg.GetHypIndex()), true
	case *proof.StepProto_SimpWith:
		if at := s.SimpWith.GetAtHyp(); at > 0 {
			return int(at - 1), true
		}
	}
	return 0, false
}

// renderDeriveStatements renders an assert staircase's Have/Show
// statement chain against an ALREADY-BOUND Argument receiver. Split
// from renderDeriveBlock for the Family profile, whose binder closure
// is itself an Argument context: a body that is one whole staircase
// renders directly on the closure's own `a`, no nested Derive wrapper.
func (e *_Emitter) renderDeriveStatements(b *strings.Builder, s *_SectionEmit, chain []*msNode, tail *msNode, recv, inner string) {
	handles := e.haveHandleIdents(chain, tail)
	e.factVerbHandles(chain, handles)
	for i, node := range chain {
		// An a.Unfolded and an a.Conjuncts render as the verbs
		// (emit_hypothesis_verbs.go).
		if e.renderFactVerb(b, chain, node, handles[i], recv, inner) {
			continue
		}
		claim, _ := e.reader.Prop(node.step.Step.(*proof.StepProto_Assert).Assert)
		// The label states the fact, with no role tag: a Have is no
		// branch of a fan, so it has no position to name.
		//
		// A Have whose fact a later step rewrites with is bound to a
		// Go ident, so that step addresses the fact by value
		// (`fact1.Rw()`) rather than by hyp position.
		bind := ""
		if handles[i] != "" {
			bind = handles[i] + " := "
		}
		verb := "Have"
		if e.obtained[node.step] != nil {
			// The witnesses are the Skolems the block's declarations
			// already name (ctx.Var), so only the instance is bound.
			witnesses := existsPrefixLen(claim.Conclusion())
			verb = obtainVerbs[witnesses]
			if handles[i] != "" {
				bind = strings.Repeat("_, ", witnesses) + handles[i] + " := "
			}
		}
		at, _ := e.reader.Prop(node.step.Goal)
		fmt.Fprintf(b, "%s%s%s.%s(%q, %s,\n",
			inner, bind, recv, verb, e.goalComment(claim), e.claimArg(claim, at, inner))
		if cite, cited := e.sectionCites[node.step]; cited {
			fmt.Fprintf(b, "%s\tCite(%s),\n", inner, cite.lemma)
		} else {
			e.renderStepExpr(b, s, node.children[0], inner+"\t")
		}
		fmt.Fprintf(b, "%s)\n", inner)
	}
	tailGoal, _ := e.reader.Prop(tail.step.Goal)
	fmt.Fprintf(b, "%s%s.Show(%q,\n", inner, recv, e.conclusionLabel(tailGoal))
	e.renderStepExpr(b, s, tail, inner+"\t")
	fmt.Fprintf(b, "%s)\n", inner)
}

// tryAtTypesFusion collapses the cross-type install PAIR — a
// `lemma_preserve` of the row at the TARGET type whose obligation child
// is a `type_inst` off the polymorphic row — into one
// `Cite(ctx.AtTypes(ctx.Dep("N"), τ…))`.
//
// Unfused, the pair renders as `Expect(LemmaPreserve(<CNF text at the
// target type>), Case(TypeInst(TypeInstSourceExact(<dep>, <CNF text at
// the row's OWN type var>))), Case(<residual>))` — two hand-copied
// session records, the second of which drags the row's machine type-var
// spelling (`?83488`) into blessed Go. AtTypes computes both forms from
// the dep cert instead: Normalize + positional type instantiation, no text and
// no machine names (Script.AtTypes).
//
// The type arguments are DERIVED and then VERIFIED. Deriving alone
// would be unsafe — a match that types-checks but instantiates the
// wrong var reads as a plausible cite and proves a different theorem —
// so the fusion rebuilds EXACTLY what Script.AtTypes will build at
// replay (same positional var order, via proof.OrderedPropTypeVars;
// same core.PropTypeInst) and requires it to α-equal the recorded
// payload. Anything less than an exact reproduction declines, and the
// unfused rendering stands.
//
// Returns the fused call argument (the AtTypes expression) and the
// residual children the caller keeps walking.
func (e *_Emitter) tryAtTypesFusion(n *msNode) (string, []*msNode, bool) {
	if len(n.children) == 0 {
		return "", nil, false
	}
	lp, isPreserve := n.step.Step.(*proof.StepProto_LemmaPreserve)
	if !isPreserve || lp.LemmaPreserve == nil {
		return "", nil, false
	}
	ti, isTypeInst := n.children[0].step.Step.(*proof.StepProto_TypeInst)
	if !isTypeInst || ti.TypeInst == nil {
		return "", nil, false
	}
	// The type_inst obligation must itself be a leaf: a child of its own
	// would be proof steps the fused single call cannot carry.
	if len(n.children[0].children) != 0 {
		return "", nil, false
	}
	payload, _ := e.reader.Prop(lp.LemmaPreserve)
	source, _ := e.reader.Prop(ti.TypeInst)
	if payload == nil || source == nil {
		return "", nil, false
	}
	// The source must name a dep — AtTypes takes a cert, and the whole
	// point is to stop spelling the row's own polymorphic statement.
	// Its first parameter is a Thm SLOT, not a Cite target: Cite
	// resolves a bare dep name through its own dispatch, AtTypes does
	// not, so the dep renders as ctx.Dep(<var>.Name) (the bare-name shortcut
	// here did not compile).
	target, section, ok := e.thmSlotTarget(source)
	if !ok {
		return "", nil, false
	}
	if leaf, found := e.resolveExternalLeafProp(source); !section && found && leaf.Kind == LeafLibraryThm {
		if expr, ok := e.wrapperInstExpr(leaf.ThmName, leaf.Key, source, payload); ok {
			return expr, n.children[1:], true
		}
	}
	_, full, ok := atTypesInstance(source, payload)
	if !ok {
		return "", nil, false
	}
	if section {
		return e.sectionInstExpr(target, full), n.children[1:], true
	}
	args, _ := e.atTypesArgs(source, payload)
	expr := fmt.Sprintf("ctx.AtTypes(%s%s)", target, args)
	return expr, n.children[1:], true
}

// wrapperInstExpr renders a landed entry's type instance in the bound
// family's own spelling — the typed wrapper's explicit instance: for a
// statement of ONE type variable `X.Inst[τ]()`, which names no letter,
// and for one of several `X.Inst(TypeBinder.BindA[τ](),
// TypeBinder.BindB[σ]())`, each letter of the stated form bound by name
// (typeBindings). The instance types are spelled as phantoms
// (phantomInScope: the letters the family declares, Bool, Nat, Prod,
// the arrow sugar, and a typedef's phantom — Real, Int). The wrapper
// resolves into the same install tail as `ctx.AtTypes(ctx.Dep(X), τ…)`
// (Script.AtSoleType, Script.AtTypeVars), so the two are one theorem at
// one instance; the difference is that the wrapper form is the
// chapter's spelling and carries no string channel. Declines — the
// caller keeps the AtTypes form — for a dep nothing landed or a bare
// datatype theorem field (no wrapper to call), an instance type no
// phantom spells, and a statement of several letters one of which has
// no Bind method.
func (e *_Emitter) wrapperInstExpr(name string, key core.PropKey, source, payload core.Prop) (string, bool) {
	_, full, ok := atTypesInstance(source, payload)
	if !ok {
		return "", false
	}
	return e.wrapperInstAt(name, key, full)
}

// wrapperInstAt is wrapperInstExpr at a type instance already read:
// full pairs each type variable of the entry's statement with the type
// it takes.
func (e *_Emitter) wrapperInstAt(name string, key core.PropKey, full []core.TypeSubst) (string, bool) {
	if e.opts.FamilyDepEntry == nil || len(full) == 0 {
		return "", false
	}
	ref, ok := e.opts.FamilyDepEntry(name, key)
	if !ok || ref.Expr == "" || ref.BareEntry {
		return "", false
	}
	if len(full) == 1 {
		phantom, ok := e.phantomInScope(full[0].HolType)
		if !ok {
			return "", false
		}
		e.markDepName(name, key)
		return fmt.Sprintf("%s.Inst[%s]()", ref.Expr, phantom), true
	}
	bindings, ok := e.typeBindings(full)
	if !ok {
		return "", false
	}
	e.markDepName(name, key)
	return fmt.Sprintf("%s.Inst(%s)", ref.Expr, bindings), true
}

// typeBindings spells a type instance by the statement's own letters —
// `TypeBinder.BindA[Real](), TypeBinder.BindB[Nat]()`, in letter order,
// which carries no meaning: each binding names its letter — the
// arguments of a typed wrapper's `Inst` and of `ctx.AtTypeVars`.
// ok=false where a type variable has no Bind method (typedgen.BindLetter:
// a letter outside the corpus's alphabet, a machine name) or takes a
// type no phantom in the family's scope spells.
func (e *_Emitter) typeBindings(full []core.TypeSubst) (string, bool) {
	bindings := make([]string, 0, len(full))
	for _, s := range full {
		letter := string(s.VarType.Name())
		if !typedgen.BindLetter(letter) {
			return "", false
		}
		phantom, ok := e.phantomInScope(s.HolType)
		if !ok {
			return "", false
		}
		bindings = append(bindings, fmt.Sprintf("TypeBinder.Bind%s[%s]()", letter, phantom))
	}
	sort.Strings(bindings)
	return strings.Join(bindings, ", "), true
}

// sectionInstExpr renders an earlier section of the member, or its
// theorem, at a type instance: `ctx.AtTypeVars(lemma1,
// TypeBinder.BindA[Real]())`, each type variable of the section's
// statement bound by its letter (typeBindings), and the positional
// `ctx.AtTypes(lemma1, MakeType("real"))` where a letter has no Bind
// method or a type no phantom. Both read the section's stated binders
// and install one instance (Script.atTypeInstance).
func (e *_Emitter) sectionInstExpr(target string, full []core.TypeSubst) string {
	if bindings, ok := e.typeBindings(full); ok {
		return fmt.Sprintf("ctx.AtTypeVars(%s, %s)", target, bindings)
	}
	var args strings.Builder
	for _, s := range full {
		fmt.Fprintf(&args, ", %s", e.printer.PrintType(s.HolType))
	}
	return fmt.Sprintf("ctx.AtTypes(%s%s)", target, args.String())
}

// phantomInScope is phantomSpelling for a line of the member being
// emitted: the spelling, where every letter and typedef it names has
// its phantom in scope in the family the member lands in. The letters
// A–E, Bool, Nat, Prod and the arrow sugar are library/authoring's, in
// every proof file's scope, and so is the phantom of a type minted
// below the chapters (Real, Int, Ind). A letter beyond E is in scope
// where the family's generated file declares it, a letter some
// registered statement of the family binds (typedgen.LettersInScope).
// The phantom of a typedef a CHAPTER mints is in scope only where the
// family declares it or one of its wrappers' signatures names the type
// (typedgen.TypedefsInScope, the member's own statement counted among
// them, its wrapper being generated when it lands). Elsewhere the
// spelling would not compile, and the caller keeps its string-channel
// form.
func (e *_Emitter) phantomInScope(t core.HolType) (string, bool) {
	if e.lettersInScope == nil {
		family, _ := registry.FamilyByName(e.opts.Family)
		e.lettersInScope = typedgen.LettersInScope(family)
	}
	spelling, ok := phantomSpelling(t, e.lettersInScope)
	if !ok {
		return "", false
	}
	if e.typedefsInScope == nil {
		family, _ := registry.FamilyByName(e.opts.Family)
		// The member's statement is its last section's, read through
		// that section's own pool.
		var member core.Prop
		if n := len(e.sections); n > 0 {
			reading := e.reader
			e.reader = e.sections[n-1].reader
			member = e.sectionInitGoal(e.sections[n-1])
			e.reader = reading
		}
		e.typedefsInScope = typedgen.TypedefsInScope(family, member)
	}
	for metatype := range typedefsNamed(t, nil) {
		if !e.typedefsInScope[metatype] {
			return "", false
		}
	}
	return spelling, true
}

// typedefsNamed adds to named the metatypes of the typedefs t is built
// from — every type constructor a typedef phantom spells.
func typedefsNamed(t core.HolType, named map[string]bool) map[string]bool {
	if named == nil {
		named = map[string]bool{}
	}
	c, composite := t.(core.CompositeType)
	if !composite {
		return named
	}
	if _, _, declared := typedgen.TypedefPhantom(string(c.Meta().Name())); declared {
		named[string(c.Meta().Name())] = true
	}
	for i := range c.Meta().Arity() {
		typedefsNamed(c.SubType(i), named)
	}
	return named
}

// phantomSpelling spells a HOL type in the typed surface's phantom
// vocabulary as a family's generated wrapper preamble aliases it
// (typedgen's renderPhantom, the same sugar): a statement letter in
// letters as itself, bool as Bool, num as Nat, a pair as Prod, an arrow as Set
// (X → bool), Op (X → X → X), Fun / Fun2 / Fun3 by arity, and a
// typedef as the phantom its owner declares (typedgen.TypedefPhantom:
// real as Real, int as Int, a constructor over its arguments'
// spellings). The preamble aliases a typedef's phantom only where a
// signature of the family names the type, which is why a rendered line
// asks phantomInScope. A type it cannot spell — a letter outside
// letters, a typedef with no declared phantom, a deeper arrow —
// declines, and the caller keeps the string-channel form.
func phantomSpelling(t core.HolType, letters map[string]bool) (string, bool) {
	if v, ok := t.(core.VarType); ok {
		if name := string(v.Name()); letters[name] {
			return name, true
		}
		return "", false
	}
	if t.Equals(core.TypeBool()) {
		return "Bool", true
	}
	if t.Equals(ext.NumType) {
		return "Nat", true
	}
	if c, ok := t.(core.CompositeType); ok && c.Meta().Equals(ext.MetaTypeProd) {
		left, ok := phantomSpelling(c.SubType(0), letters)
		if !ok {
			return "", false
		}
		right, ok := phantomSpelling(c.SubType(1), letters)
		if !ok {
			return "", false
		}
		return fmt.Sprintf("Prod[%s, %s]", left, right), true
	}
	if ext.IsFunType(t) {
		spine := ext.MatchesFun(t)
		parts := make([]string, len(spine))
		for i, s := range spine {
			p, ok := phantomSpelling(s, letters)
			if !ok {
				return "", false
			}
			parts[i] = p
		}
		args, result := parts[:len(parts)-1], parts[len(parts)-1]
		switch {
		case len(args) == 1 && result == "Bool":
			return fmt.Sprintf("Set[%s]", args[0]), true
		case len(args) == 2 && args[0] == args[1] && args[1] == result:
			return fmt.Sprintf("Op[%s]", result), true
		case len(args) == 1:
			return fmt.Sprintf("Fun[%s, %s]", args[0], result), true
		case len(args) == 2:
			return fmt.Sprintf("Fun2[%s, %s, %s]", args[0], args[1], result), true
		case len(args) == 3:
			return fmt.Sprintf("Fun3[%s, %s, %s, %s]", args[0], args[1], args[2], result), true
		}
		return "", false
	}
	if c, ok := t.(core.CompositeType); ok {
		name, arity, declared := typedgen.TypedefPhantom(string(c.Meta().Name()))
		if !declared || arity != c.Meta().Arity() {
			return "", false
		}
		if arity == 0 {
			return name, true
		}
		arguments := make([]string, arity)
		for i := range arguments {
			argument, ok := phantomSpelling(c.SubType(i), letters)
			if !ok {
				return "", false
			}
			arguments[i] = argument
		}
		return fmt.Sprintf("%s[%s]", name, strings.Join(arguments, ", ")), true
	}
	return "", false
}

// atTypesArgs derives the positional type-argument list that makes
// Script.AtTypes(source, …) reproduce payload, rendered as Go source
// (leading ", " included, empty when the derivation fails).
//
// The verification at the end is what makes the derivation safe to
// trust: it rebuilds the instance the way AtTypes will and compares it
// to the recorded payload, so a mis-derived σ can only ever produce a
// DECLINE, never a wrong cite.
func (e *_Emitter) atTypesArgs(source, payload core.Prop) (string, bool) {
	at, _, ok := atTypesInstance(source, payload)
	if !ok {
		return "", false
	}
	var b strings.Builder
	for _, t := range at {
		fmt.Fprintf(&b, ", %s", e.printer.PrintType(t))
	}
	return b.String(), true
}

// atTypesInstance derives the positional type arguments (and the full
// substitution, in the same order) that make Script.AtTypes(source,
// at…) produce payload; ok=false when payload is not a PROPER type
// instance of source — α-equal to it, or no instance at all.
//
// AtTypes builds two forms at the instance: the install half,
// InstallForm(source) at σ, and the reference half, source itself at σ
// (TypedThm.Reference — what a By premise installs and a Simp rule
// fires). A session records whichever its move consumed, and neither
// form commutes with type instantiation, so BOTH are accepted as the
// recorded payload: the match runs install-against-install first, then
// canonical-against-canonical (an adapted instance the session
// re-normalized), then stated-against-recorded, and the derived σ is
// verified by rebuilding the matched half exactly as AtTypes will. A σ
// that rebuilds none declines.
func atTypesInstance(source, payload core.Prop) (at []core.HolType, full []core.TypeSubst, ok bool) {
	norm := proof.InstallForm(source)
	vars := proof.OrderedPropTypeVars(norm)
	if len(vars) == 0 {
		return nil, nil, false // AtTypes panics on a monomorphic dep
	}
	// Three readings of the record, tried in order: the install half
	// given verbatim (a LemmaPreserve payload), the canonical form of
	// the record against the canonical form of the source (an adapted
	// instance the session re-normalized), the reference half (a By
	// premise's install, a Simp rule: the stated form at the instance).
	canonical, _ := proof.Normalize(source)
	payloadNorm, _ := proof.Normalize(payload)
	var substs []core.TypeSubst
	if norm.NumHyps() == 0 && payload.NumHyps() == 0 {
		substs, ok = proof.NormalizedPropTypeMatch(norm, payload)
	}
	if !ok && canonical.NumHyps() == 0 && payloadNorm.NumHyps() == 0 {
		substs, ok = proof.NormalizedPropTypeMatch(canonical, payloadNorm)
	}
	if !ok && source.NumHyps() == 0 && payload.NumHyps() == 0 {
		substs, ok = prop.IsTypeMatchOf(source, payload, func(core.VarType) bool { return true })
		ok = ok && len(substs) > 0
	}
	if !ok {
		return nil, nil, false
	}
	byName := make(map[core.TypeName]core.HolType, len(substs))
	for _, s := range substs {
		byName[s.VarType.Name()] = s.HolType
	}
	at = make([]core.HolType, len(vars))
	full = make([]core.TypeSubst, len(vars))
	for i, v := range vars {
		// A var the match left alone stays itself — AtTypes documents
		// the identity substitution as legal, and the row may well
		// instantiate only some of its type vars.
		at[i] = core.HolType(v)
		if t, hit := byName[v.Name()]; hit {
			at[i] = t
		}
		full[i] = core.MakeTypeSubst(v, at[i])
	}
	if install := core.PropTypeInst(norm, full...); !install.AlphaEquals(payload) &&
		!core.PropTypeInst(canonical, full...).AlphaEquals(payloadNorm) &&
		!core.PropTypeInst(source, full...).AlphaEquals(payload) {
		return nil, nil, false
	}
	return at, full, true
}

// simpRuleTarget renders one recorded simp rule as a `Simp` CITE
// TARGET (the resolveLemmaTarget universe: a section node, a dep name,
// a cert, a typed instance) and reports the rule statement that target
// SERVES at replay — nil when emit cannot know it. Returns ok=false
// when the rule resolves to no target — the caller then declines the
// whole fusion and the pinned-prop SimpWith rendering stands.
//
// The section arm takes EXACT (non-viaNormalize) hits only, for
// leanRwLemmaExpr's reason: a normalize-equivalent section can differ in
// binder order or equation orientation, and the rule prop the driver
// records must be the one the emitted target resolves to. An exact hit
// serves the rule as recorded.
//
// The external-leaf arm serves what the leaf's statement says it
// serves (ExternalLeaf.Stated — an entry's headline): the stated form
// for a bare name or a cert, the stated form at the instance for a
// typed instance (TypedThm.Reference). The session
// fired the rule in the form IT served — an entry's normalized clause
// (a cite by key), a member's headline, a type instance of either —
// and the two forms agree only up to the chapter's restatements; the caller
// (trySimpFusion) compares them and carries the difference into the
// marker, or declines.
func (e *_Emitter) simpRuleTarget(l core.Prop) (expr string, served core.Prop, ok bool) {
	if ref, viaNormalize, hit := e.resolveLemmaRefDetailed(l); hit && !viaNormalize {
		// A section's *GoalStackNode is a target verbatim — no
		// .PromisedThm() (Simp reads the promise itself, as Cite does).
		return ref, l, true
	}
	// A target that resolves to nothing declines the fusion outright
	// rather than rendering a placeholder.
	leaf, found := e.resolveExternalLeafProp(l)
	if !found {
		return "", nil, false
	}
	target, rendered := e.tryExternalLeafExpr(l, leafCite, false)
	if !rendered {
		return "", nil, false
	}
	return target, e.servedRuleForm(leaf, l, target), true
}

// servedRuleForm is the statement a rendered Simp target delivers to
// the driver at replay (resolveLemmaTarget), computed from the leaf's
// Stated statement: nil when the leaf is not a library theorem or its
// served statement is unknown. Mirrors the three target spellings
// renderExternalLeaf produces for a library theorem — the typed
// instance (Reference: the stated form at the
// instance, when hyp-free; else the install half), the cert
// (ctx.Dep: the stated form verbatim), the bare name (statedInstallForm:
// the stated form when closed, its ∀-closure when sequent-shaped).
func (e *_Emitter) servedRuleForm(leaf ExternalLeaf, payload core.Prop, expr string) core.Prop {
	if leaf.Kind != LeafLibraryThm || leaf.Stated == nil {
		return nil
	}
	if _, full, ok := atTypesInstance(leaf.Stated, payload); ok {
		ref := core.PropTypeInst(leaf.Stated, full...)
		if ref.NumHyps() == 0 {
			return ref
		}
		norm, _ := proof.Normalize(leaf.Stated)
		return core.PropTypeInst(norm, full...)
	}
	if leaf.Stated.NumHyps() == 0 || strings.HasPrefix(expr, "MakeFact(ctx."+"Dep(") {
		return leaf.Stated
	}
	norm, _ := proof.Normalize(leaf.Stated)
	return norm
}

// certSlotExpr renders a recorded certificate statement for a Thm slot
// (thmSlotTargetExpr), or the loud nil-cert placeholder when nothing
// resolves it — a slot that takes a certificate cannot take the
// statement's text.
func (e *_Emitter) certSlotExpr(l core.Prop) string {
	if l == nil {
		return "/* TODO: certificate statement missing from the record */ ThmCert{}"
	}
	if expr, ok := e.thmSlotTargetExpr(l); ok {
		return expr
	}
	return fmt.Sprintf("/* TODO: external lemma %q — no entry states it */ ThmCert{}", l.AlphaKey())
}

// thmSlotTargetExpr renders a recorded dep statement as the argument
// of a Thm SLOT — Script.AtTypes's dep parameter: a section node
// through PromisedThm(), an external leaf in its plain Thm form
// (ctx.Dep(name)). The Cite
// target universe is wider — Cite resolves a bare dep NAME through its
// own dispatch — and a name is not a Thm, so the two renderings are
// kept apart. Returns ok=false when the statement resolves to
// nothing; the caller declines.
func (e *_Emitter) thmSlotTargetExpr(l core.Prop) (string, bool) {
	expr, _, ok := e.thmSlotTarget(l)
	return expr, ok
}

// thmSlotTarget is thmSlotTargetExpr with whether the target is an
// earlier section of the member.
func (e *_Emitter) thmSlotTarget(l core.Prop) (expr string, section, ok bool) {
	if ref, viaNormalize, ok := e.resolveLemmaRefDetailed(l); ok && !viaNormalize {
		return ref + ".PromisedThm()", true, true
	}
	if expr, ok := e.tryExternalLeafExpr(l, leafPlain, false); ok {
		return expr, false, true
	}
	return "", false, false
}

// trySimpFusion renders a recorded `simp_with` composite as the `Simp`
// verb.
//
// The SimpWith Step takes rule PROPS, so its unfused rendering spells
// every rule as a full-statement MakePropText literal and leaves one
// obligation leaf per FIRED rule for the caller to discharge — one
// `Case(…, CiteKnown(<thm>))` apiece. In a chapter both halves are
// defects: the literals are pinned copies of dep
// statements checked against nothing (§"Citation forms: compute, don't
// pin" on the simp face), and the per-rule Cases state a fact about
// driver behavior rather than about the mathematics. `Simp` takes cite
// targets and discharges the obligations from those same certificates,
// so both disappear.
//
// The partition is exact, not heuristic: SimpWithExpandFlipped builds
// its children as the used rules' props VERBATIM followed by the
// residual last, so a child α-equal to a rule IS that rule's obligation
// — the same identity `Simp`'s own matchingRule uses at replay. What
// remains is the residual the caller keeps proving; anything else means
// the recorded tree is not the shape Simp reconstructs, and the fusion
// declines rather than guess.
//
// The flip marker is computed, not copied. The recorded bit reads
// against the rule the SESSION served; the emitted marker reads against
// the rule the TARGET serves at replay (simpRuleTarget's served form),
// and the two differ wherever the chapter restated a headline away from
// the form the session fired, or the member is cited at a type instance.
// Same statement → the bit as recorded; the statement's equation turned
// around → the bit toggled; any other shape → the fusion declines, since
// a Simp over that target cannot re-fire the recorded rewrite and the
// pinned rendering is the faithful transport.
//
// Returns the `Simp(...)` expression and the residual children the
// caller must keep walking.
func (e *_Emitter) trySimpFusion(n *msNode) (string, []*msNode, bool) {
	s, isSimp := n.step.Step.(*proof.StepProto_SimpWith)
	if !isSimp || s.SimpWith == nil {
		return "", nil, false
	}
	refs := s.SimpWith.GetRules()
	if len(refs) == 0 {
		return "", nil, false
	}
	flips := s.SimpWith.GetRuleFlip()
	ruleProps := make([]core.Prop, len(refs))
	for i, ref := range refs {
		l, _ := e.reader.Prop(ref)
		if l == nil {
			return "", nil, false
		}
		ruleProps[i] = l
	}
	goal, _ := e.reader.Prop(n.step.Goal)
	resident := residentSimpRules(goal, s.SimpWith, ruleProps)
	kept, rest := e.simpRulesKept(ruleProps, resident, n.children)
	// Simp leaves exactly the residual. More than one unmatched child
	// means the recorded fan-out is not what Simp will produce.
	if len(rest) > 1 {
		return "", nil, false
	}
	printed := make([]int, 0, len(refs))
	for i := range ruleProps {
		if kept[i] {
			printed = append(printed, i)
		}
	}
	var bare map[int]simpBareEntryRule
	var skip map[int]bool
	if goal != nil && len(rest) == 1 {
		residual, _ := e.reader.Prop(rest[0].step.Goal)
		bare, skip = e.simpEntryRulesGoAdapts(s.SimpWith, goal, residual, ruleProps, resident, flips, printed)
	}
	parts := make([]string, 0, len(refs))
	for _, i := range printed {
		l := ruleProps[i]
		if skip[i] {
			continue
		}
		if reading := simpRuleReading(s.SimpWith, i); reading != nil {
			// A law read at an instance is its own target, served as
			// the session fired it: the bit is the recorded one.
			ctor := "Fwd"
			if i < len(flips) && flips[i] {
				ctor = "Rev"
			}
			parts = append(parts, fmt.Sprintf("%s(%s)", ctor, e.readingExpr(reading, "")))
			continue
		}
		if resident[i] {
			// A resident hypothesis is its own target, the fact naming
			// it: the Have's handle where one names it, else its
			// statement.
			ctor := "Fwd"
			if i < len(flips) && flips[i] {
				ctor = "Rev"
			}
			parts = append(parts, fmt.Sprintf("%s(%s)", ctor, e.residentRuleExpr(n.step, i, l)))
			continue
		}
		var target string
		var served core.Prop
		if entry, cited := bare[i]; cited {
			target, served = entry.target, entry.served
		} else {
			var ok bool
			if target, served, ok = e.simpRuleTarget(l); !ok {
				return "", nil, false
			}
		}
		flip := i < len(flips) && flips[i]
		if served != nil {
			switch {
			case sameStatement(l, served):
			case sameStatement(l, tactic.FlipRuleLemma(served)):
				flip = !flip
			default:
				// The session fired the rule in the NORMALIZER's
				// orientation (`normalized: true`): the target that
				// serves that form is MakeFact(ctx.DepNormalized(name)),
				// at the instance where the record is one.
				normTarget, normFlip, isNorm := e.simpRuleNormalizedTarget(l)
				if !isNorm {
					return "", nil, false
				}
				target = normTarget
				if normFlip {
					flip = !flip
				}
			}
		}
		ctor := "Fwd"
		if flip {
			ctor = "Rev"
		}
		parts = append(parts, fmt.Sprintf("%s(%s)", ctor, target))
	}
	return e.simpCallExpr(n.step, s.SimpWith.GetAtHyp(), parts), rest, true
}

// simpRulesKept reports, per rule of a recorded simp_with, whether the
// rendering keeps it, and returns the step's children that state no
// rule — the residual. A child α-equal to a rule is that rule's
// obligation: the driver's rule children carry those props verbatim,
// with the residual last. A resident rule (residentSimpRules) is
// discharged by the context without a child, so its absence does not
// show that it was unused. Those rules are kept; pruned is only a
// named rule with no obligation — a bound family's bare `simp` hands
// the driver its whole installed set, and the session's type
// adaptation records beside a rule the copies it reached, whose
// unfired members enter neither the rendering nor Deps nor the
// declarations (walkMiniStep). With no rule child, every rule is kept
// (nothing to prune by).
func (e *_Emitter) simpRulesKept(ruleProps []core.Prop, resident []bool, children []*msNode) (kept []bool, rest []*msNode) {
	used := make([]bool, len(ruleProps))
	anyUsed := false
	for _, c := range children {
		childGoal, _ := e.reader.Prop(c.step.Goal)
		stated := false
		if childGoal != nil {
			for i, r := range ruleProps {
				if r.AlphaEquals(childGoal) {
					used[i], anyUsed, stated = true, true, true
				}
			}
		}
		if !stated {
			rest = append(rest, c)
		}
	}
	kept = make([]bool, len(ruleProps))
	for i := range ruleProps {
		kept[i] = !anyUsed || used[i] || resident[i]
	}
	return kept, rest
}

// residentSimpRules reports, per rule of a recorded simp_with, whether
// the step's context discharges it: a resident hypothesis assumed
// (proof.AssumedRule), or a claim with no hypotheses whose statement is
// a hypothesis the driver rewrites under — every hypothesis of the goal
// but the one an at-hypothesis step rewrites. The driver discharges
// such a rule's clause against that hypothesis without an obligation
// child (a session's text rule spelling a resident hypothesis records
// so), and the rule renders as the fact naming the hypothesis. A rule
// that did not decode (nil) is not resident.
func residentSimpRules(goal core.Prop, sw *proof.SimpWithProto, rules []core.Prop) []bool {
	resident := make([]bool, len(rules))
	for i, rule := range rules {
		if rule == nil {
			continue
		}
		if proof.AssumedRule(rule) {
			resident[i] = true
			continue
		}
		if goal == nil || rule.NumHyps() != 0 {
			continue
		}
		for h := 0; h < goal.NumHyps(); h++ {
			if int32(h+1) != sw.GetAtHyp() && goal.Hyp(h).AlphaEquals(rule.Conclusion()) {
				resident[i] = true
				break
			}
		}
	}
	return resident
}

// noteSimpRulesKept records, for every simp_with step of the tree at n,
// which rules the rendering keeps (simpRulesKept), read by the symbol
// walk before any step renders; a step whose rules do not all decode
// renders unfused, every rule printed, and is noted not at all.
func (e *_Emitter) noteSimpRulesKept(n *msNode) {
	if n == nil {
		return
	}
	if s, isSimp := n.step.Step.(*proof.StepProto_SimpWith); isSimp && s.SimpWith != nil {
		refs := s.SimpWith.GetRules()
		ruleProps := make([]core.Prop, 0, len(refs))
		for _, ref := range refs {
			l, _ := e.reader.Prop(ref)
			if l == nil {
				ruleProps = nil
				break
			}
			ruleProps = append(ruleProps, l)
		}
		if len(ruleProps) == len(refs) && len(refs) > 0 {
			if e.simpRulesKeptByStep == nil {
				e.simpRulesKeptByStep = map[*proof.StepProto][]bool{}
			}
			goal, _ := e.reader.Prop(n.step.Goal)
			e.simpRulesKeptByStep[n.step], _ = e.simpRulesKept(ruleProps, residentSimpRules(goal, s.SimpWith, ruleProps), n.children)
		}
	}
	for _, c := range n.children {
		e.noteSimpRulesKept(c)
	}
}

// residentRuleExpr spells rule i of a simp step, a resident hypothesis
// assumed, as the fact naming the hypothesis: a Have's handle, the law
// closure's own hypothesis, or `ResidentHyp(<statement>)`.
func (e *_Emitter) residentRuleExpr(step *proof.StepProto, i int, l core.Prop) string {
	if h, ok := e.hypHandleByUse[_HypUse{step: step, rule: i + 1}]; ok {
		return h
	}
	stated := core.MakeProp(l.Conclusion())
	if handle := e.lawHandleFor(stated); handle != "" {
		return handle
	}
	return e.residentHypExpr(stated)
}

// simpCallExpr spells a simp step's call: `Simp(rules…)` on the
// conclusion; at a hypothesis (SimpWithProto.at_hyp = k+1), the fact's
// own verb `fact.Simp(rules…)` when a Have bound the hypothesis to a Go
// ident, else the positional `SimpAt(k, rules…)` emit falls back to.
func (e *_Emitter) simpCallExpr(step *proof.StepProto, atHyp int32, parts []string) string {
	rules := strings.Join(parts, ", ")
	if atHyp <= 0 {
		return fmt.Sprintf("Simp(%s)", rules)
	}
	if h, ok := e.hypHandleByUse[_HypUse{step: step}]; ok {
		return fmt.Sprintf("%s.Simp(%s)", h, rules)
	}
	return fmt.Sprintf("SimpAt(%d, %s)", atHyp-1, rules)
}

// simpBareEntryRule is a recorded rule instance a Simp call cites as
// its bare entry: the cite target, and the statement the entry serves
// at the instance the session fired, which the recorded flip is read
// against.
type simpBareEntryRule struct {
	target string
	served core.Prop
}

// simpEntryRulesGoAdapts decides, among the rules of a recorded
// simp_with the Simp prints (printed, indices into rules), which type
// instances of one library entry Go's Simp adapts on its own from the
// bare entry: those print as the entry once — the first instance
// carrying the cite (bare), the others nothing (skip), nothing at all
// when the entry at its own letters is printed beside them. The oracle
// is the rewrite: the call with the entry bare, its instances the ones
// Go adapts beside it (proof.SimpInstancesAdapted), must leave the
// residual the session recorded — Go reaches every instance the goal
// spells, copies with no redex being inert, and chooses differently
// where the session pinned one instance of a goal that spells more.
// Each entry is decided on its own, the entries already decided bare
// standing bare in its trial; instances in two orientations, and an
// entry stated as a sequent, keep each instance explicit.
func (e *_Emitter) simpEntryRulesGoAdapts(sw *proof.SimpWithProto, goal, residual core.Prop, rules []core.Prop, resident, flips []bool, printed []int) (bare map[int]simpBareEntryRule, skip map[int]bool) {
	if residual == nil {
		return nil, nil
	}
	flipOf := func(i int) bool { return i < len(flips) && flips[i] }
	type entryGroup struct {
		leaf    ExternalLeaf
		members []int
		own     bool
		flip    bool
		oneFlip bool
	}
	groups := map[string]*entryGroup{}
	groupOf := map[int]string{}
	var names []string
	for _, i := range printed {
		l := rules[i]
		var leaf ExternalLeaf
		found := false
		if simpRuleReading(sw, i) == nil && !resident[i] {
			leaf, found = e.resolveExternalLeafProp(l)
			found = found && leaf.Kind == LeafLibraryThm && leaf.Stated != nil && leaf.Stated.NumHyps() == 0
		}
		own := found && sameStatement(l, leaf.Stated)
		instance := false
		if found && !own {
			_, _, instance = atTypesInstance(leaf.Stated, l)
		}
		if !own && !instance {
			continue
		}
		g := groups[leaf.ThmName]
		if g == nil {
			g = &entryGroup{leaf: leaf, flip: flipOf(i), oneFlip: true}
			groups[leaf.ThmName] = g
			names = append(names, leaf.ThmName)
		}
		groupOf[i] = leaf.ThmName
		g.oneFlip = g.oneFlip && flipOf(i) == g.flip
		if own {
			g.own = true
		} else {
			g.members = append(g.members, i)
		}
	}
	if len(groups) == 0 {
		return nil, nil
	}
	var hyp *int
	if at := sw.GetAtHyp(); at > 0 {
		h := int(at - 1)
		hyp = &h
	}
	// callRules is the rule list the printed call hands Simp with the
	// entries in accepted bare — each once, at its first rule's place —
	// and every other rule as recorded; theorems marks the rules Simp
	// adapts, the entries handed bare: an accepted entry, and a rule that
	// is its entry's own statement. An instance the call spells (`Inst`,
	// `ctx.AtTypes`) is exact, as a reading or a text rule is.
	callRules := func(accepted map[string]bool) (call []core.Prop, callFlips, theorems []bool) {
		seen := map[string]bool{}
		for _, i := range printed {
			name, grouped := groupOf[i]
			if grouped && accepted[name] {
				if seen[name] {
					continue
				}
				seen[name] = true
				call = append(call, groups[name].leaf.Stated)
				callFlips = append(callFlips, groups[name].flip)
				theorems = append(theorems, true)
				continue
			}
			call = append(call, rules[i])
			callFlips = append(callFlips, flipOf(i))
			theorems = append(theorems, grouped && sameStatement(rules[i], groups[name].leaf.Stated))
		}
		return call, callFlips, theorems
	}
	accepted := map[string]bool{}
	for _, name := range names {
		g := groups[name]
		if len(g.members) == 0 || !g.oneFlip {
			continue
		}
		accepted[name] = true
		call, callFlips, theorems := callRules(accepted)
		instances, sources := proof.SimpInstancesAdapted(call, callFlips, theorems, hyp, goal)
		for k, instance := range instances {
			call = append(call, instance)
			callFlips = append(callFlips, callFlips[sources[k]])
		}
		if left := proof.SimpResidual(goal, hyp, call, callFlips); left == nil || !left.AlphaEquals(residual) {
			delete(accepted, name)
		}
	}
	bare, skip = map[int]simpBareEntryRule{}, map[int]bool{}
	for _, name := range names {
		g := groups[name]
		if !accepted[name] {
			continue
		}
		rest := g.members
		if !g.own {
			target, _, ok := e.simpRuleTarget(g.leaf.Stated)
			if !ok {
				continue
			}
			first := g.members[0]
			bare[first] = simpBareEntryRule{target: target, served: e.servedRuleForm(g.leaf, rules[first], target)}
			rest = g.members[1:]
		}
		for _, i := range rest {
			skip[i] = true
		}
	}
	return bare, skip
}

// simpRuleNormalizedTarget renders a recorded simp rule that is a
// library theorem's NORMALIZED form — the session's per-rule
// `normalized: true`, proof.NormalizedForm of the entry's statement —
// as the Go target that serves exactly that form at replay:
// `MakeFact(ctx.DepNormalized(<name>))` (Script.DepNormalized =
// NormalizedThm ∘ Dep, the same function, its certificate named as a
// fact), or `ctx.AtTypes(ctx.DepNormalized(<name>),
// τ…)` when the record is the normalized form at a type instance (the
// session's multi-instance expansion of a polymorphic normalized rule;
// AtTypes serves its dep's stated form at the instance, and the dep
// here IS the normalized form). flip reports the record as the
// normalized form's equation turned around. ok=false when the rule is
// not a library theorem's normalized form in either reading — the
// caller declines the fusion.
func (e *_Emitter) simpRuleNormalizedTarget(l core.Prop) (target string, flip, ok bool) {
	leaf, found := e.resolveExternalLeafProp(l)
	if !found || leaf.Kind != LeafLibraryThm || leaf.Stated == nil || leaf.ThmName == "" {
		return "", false, false
	}
	normalized := proof.NormalizedForm(leaf.Stated)
	dep := fmt.Sprintf("ctx.DepNormalized(%s)", e.depNameExpr(leaf.ThmName, leaf.Key))
	// The normalized form is a certificate, named as a fact; its type
	// instance is a cite target already.
	named := "MakeFact(" + dep + ")"
	switch {
	case sameStatement(l, normalized):
		e.markDepName(leaf.ThmName, leaf.Key)
		return named, false, true
	case sameStatement(l, tactic.FlipRuleLemma(normalized)):
		e.markDepName(leaf.ThmName, leaf.Key)
		return named, true, true
	}
	if at, full, hit := atTypesInstance(normalized, l); hit {
		// The instance is read off the NORMALIZED form, the dep the
		// AtTypes call receives: Normalize does not commute with type
		// instantiation, so the stated form's σ is not the answer.
		instance := core.PropTypeInst(normalized, full...)
		var args strings.Builder
		for _, t := range at {
			fmt.Fprintf(&args, ", %s", e.printer.PrintType(t))
		}
		switch {
		case sameStatement(l, instance):
			e.markDepName(leaf.ThmName, leaf.Key)
			return fmt.Sprintf("ctx.AtTypes(%s%s)", dep, args.String()), false, true
		case sameStatement(l, tactic.FlipRuleLemma(instance)):
			e.markDepName(leaf.ThmName, leaf.Key)
			return fmt.Sprintf("ctx.AtTypes(%s%s)", dep, args.String()), true, true
		}
	}
	return "", false, false
}

// sameStatement reports whether two statements are one theorem in the
// sense a simp rule's form matters: α-equal. A nil side is never the
// same.
func sameStatement(a, b core.Prop) bool {
	if a == nil || b == nil {
		return false
	}
	return a.AlphaEquals(b)
}

// installedHypIndexStatic predicts, from the recorded before/after
// goals, which hyp the runtime cite-at-use locator will pick — the
// emit-time mirror of prover's installedHypIndex. Returns -1 when the
// runtime would fail to locate one (nothing added, or several added with
// none matching the cited conclusion), which is the caller's signal to
// decline the fusion.
//
// Keep in lockstep with prover.installedHypIndex: a divergence renders a
// fused call whose runtime index differs from the recorded one, and the
// specialize then grounds the WRONG hypothesis.
func installedHypIndexStatic(before, after core.Prop, installed core.Prop) int {
	concl := installed.AsProp().Conclusion()
	found := -1
	for i := 0; i < after.NumHyps(); i++ {
		h := after.Hyp(i)
		if before.HasHyp(h) || before.AnyHyp(h.AlphaEquals) {
			continue
		}
		if !h.AlphaEquals(concl) {
			continue
		}
		if found >= 0 {
			return -1
		}
		found = i
	}
	if found >= 0 {
		return found
	}
	return addedHypIndex(before, after)
}

// addedHypIndex diffs two goals' hyp lists and returns the index (in
// `after`) of the single hyp present in after but not in before, or -1
// when there is no such hyp or more than one (either way the caller
// must decline). Mirrors prover's newHypIndex runtime locator.
func addedHypIndex(before, after core.Prop) int {
	added := -1
	for i := 0; i < after.NumHyps(); i++ {
		h := after.Hyp(i)
		if before.HasHyp(h) || before.AnyHyp(h.AlphaEquals) {
			continue
		}
		if added >= 0 {
			return -1
		}
		added = i
	}
	return added
}

// tryRewriteFusion checks whether (a, b) is the `LeanRw(d) +
// AxiomDef(c)` idiom — both shapes adjacent. Returns the rendered
// `<d>` and `<c>` expressions and true on success. No further
// consistency check is required: the fused `Rewrite(d, c)` just
// forwards both to the underlying two-Do sequence, preserving runtime
// behavior regardless of whether d and c are semantically related.
func (e *_Emitter) tryRewriteFusion(n *msNode) (dExpr, cExpr string, ok bool) {
	if len(n.children) == 0 {
		return "", "", false
	}
	a, b := n.step, n.children[0].step
	aLeanRw, isLeanRw := a.Step.(*proof.StepProto_LeanRw)
	if !isLeanRw {
		return "", "", false
	}
	bAxiomDef, isAxiomDef := b.Step.(*proof.StepProto_AxiomDef)
	if !isAxiomDef {
		return "", "", false
	}
	propA, _ := e.reader.Prop(aLeanRw.LeanRw)
	ct := e.constAt(bAxiomDef.AxiomDef.GetConst())

	// The LeanRw rule's obligation (child[0] = propA in its exact α-form)
	// is closed by the fused AxiomDef(c) below, which proves `⊢ c = def_c`.
	// So in a valid fusion propA *is* c's def equation, and `d` must render
	// in that exact α-form for the obligation leaf to match what AxiomDef(c)
	// discharges.
	//
	// lemmaRefExpr resolves an α-exact earlier section correctly (its
	// Thm carries propA's α-form). But it also has a *normalize* tier:
	// when propA only Normalize-equals an earlier section (NOT α-equal),
	// it still returns that section's `.PromisedThm()` — whose α-form
	// differs.
	// For a plain lemma citation that's fine, but for a rewrite rule it is
	// not: replaying the section form yields a *different* obligation that
	// AxiomDef(c) cannot close and whose AlphaKey diverges from the
	// recorded step. The canonical collision: mk_pair's def `mk_pair = λ…`
	// Normalize-equals an earlier section iff `∀… (a=x)∧(b=y) ⇔ mk_pair(…)`.
	//
	// So: only when the section resolution would be via-normalize do we
	// divert to the const-def, which recovers c's def equation in its exact
	// recorded form.
	if _, viaNormalize, ok := e.resolveLemmaRefDetailed(propA); !ok || viaNormalize {
		// allowInstance=false: a rule that is a PROPER type instance of the
		// const's def must NOT round-trip through `ctx.ConstDef(name)` — that
		// rendering discards the recorded instantiation and re-derives it at
		// replay via chooseTypeAdaptedStep, which is only faithful when the
		// goal pins the instance unambiguously. When the goal carries the
		// const at several distinct instances, the (deterministic, post-
		// bareConstAnchorAmbiguous) adapter abstains, the general rule
		// rewrites a different occurrence set than the recorded pinned rule,
		// and the whole downstream trajectory drifts off the recording
		// (the image/iterate 25-replay incident). leanRwLemmaExpr below
		// renders the exact recorded rule instead.
		if cd, ok := e.tryConstDefByName(propA, leafPlain, false); ok {
			return cd, e.printer.PrintTerm(ct), true
		}
		// via-normalize / unresolved AND not a recognized raw const-def: the
		// rule is only Normalize-equal to some earlier section, so lemmaRefExpr
		// would return that section's ref — whose α-form differs from propA
		// (binder order / equation orientation), making child[0] diverge from
		// the recorded step at replay (the lemma10 case of nonneg_real_formal_diff.InvWellDef:
		// the recorded treal_inv def-rewrite rule is a projection-shaped
		// def-equation that resolves via-normalize to lemma9 but is NOT
		// α-equal to it). Fall back to leanRwLemmaExpr, which emits the EXACT
		// recorded rule verbatim (MakeProp) — the following AxiomDef/cite then
		// discharges it up to Normalize. Mirrors leanRwLemmaExpr's exact-only
		// contract; never the normalize-ref tier of lemmaRefExpr.
		return e.leanRwLemmaExpr(propA), e.printer.PrintTerm(ct), true
	}
	return e.leanRwLemmaExpr(propA), e.printer.PrintTerm(ct), true
}

// reindentMiniStep re-anchors any multi-line output from emitMiniStep
// (currently only the Specialize composite, when it has ≥2 entries)
// against the caller's own indent. emitMiniStep uses a `\n\t`
// continuation convention that treats "\t" as one level DEEPER than
// the ministep's own baseline; the caller prepends its own indent to
// each continuation so the arms nest correctly. A single-line output
// (every other ministep) is returned unchanged.
func reindentMiniStep(line, callerIndent string) string {
	if !strings.Contains(line, "\n") {
		return line
	}
	return strings.ReplaceAll(line, "\n", "\n"+callerIndent)
}

// emitMiniStep renders one StepProto as a Step expression. Lemma /
// LeanRw / TypeInst / KnownThm payloads resolve to either an earlier
// section's node or an external-leaf expression.
func (e *_Emitter) emitMiniStep(step *proof.StepProto) string {
	// Ministep constructors render as bare names (`Basic()`,
	// `Witness(t)`) — library/authoring declares them.
	// InductStep reads the Script's induction principles and stays
	// routed through ctx.
	sx := "ctx."
	switch s := step.Step.(type) {
	case *proof.StepProto_Elementarity:
		return e.renderElementarityExpr(s.Elementarity)
	case *proof.StepProto_By:
		// Normally handled by renderStepExpr's dedicated arm (which also
		// skips the claim children); this fallback keeps
		// any other route (Finally fold, diagnostics) rendering the
		// same expression.
		return e.renderByExpr(s.By)
	case *proof.StepProto_AcRegroup:
		// The AC kit's goal face (prover/proof/step_ac.go): the
		// certificate pair as cite targets — the derived equation is
		// the executor's to rebuild.
		assoc, _ := e.reader.Prop(s.AcRegroup.GetAssoc())
		sym, _ := e.reader.Prop(s.AcRegroup.GetSym())
		return fmt.Sprintf("ACRegroup(%s, %s)", e.certSlotExpr(assoc), e.certSlotExpr(sym))
	case *proof.StepProto_Basic:
		return "Basic()"
	case *proof.StepProto_CondRewrite:
		return "CondRewrite()"
	case *proof.StepProto_Rewrite:
		// Bare no-arg rewrite ministep. Renamed at package level
		// from `Rewrite` to `RewriteAuto` so the `Rewrite` identifier
		// is free for the fused 2-arg `Rewrite(d, c) Step` form
		// used inside Case bodies.
		return "RewriteAuto()"
	case *proof.StepProto_SplitConj:
		return "SplitConj()"
	case *proof.StepProto_SplitConjAll:
		return "SplitConjAll()"
	case *proof.StepProto_SplitDisj:
		// The caseless forms: the typed SplitDisj takes its two branches.
		if s.SplitDisj != nil && s.SplitDisj.HypIndex != nil {
			return fmt.Sprintf("SplitDisjAtCases(%d)", *s.SplitDisj.HypIndex)
		}
		return "SplitDisjCases()"
	case *proof.StepProto_StripImp:
		return "StripImp()"
	case *proof.StepProto_StripQuant:
		if s.StripQuant != nil && s.StripQuant.HypIndex != nil {
			return fmt.Sprintf("StripQuantAt(%d)", *s.StripQuant.HypIndex)
		}
		return "StripQuant()"
	case *proof.StepProto_StripQuant1:
		// The bounded single-binder strip (proto tag 54) — a.Fix's
		// ministep, and one link of the StripQuantN desugar. No
		// session tactic records it today (a session
		// `intro` strips every leading ∀ at once, tag StripQuant); the
		// arm exists so a Go-recorded tree re-emitted through this
		// switch cannot fall through to the unhandled-ministep panic.
		return "StripQuant1()"
	case *proof.StepProto_SplitIff:
		// The flat path has no Case block and so no halves to name: the
		// positional bottom is the only spelling that takes none.
		return "SplitIffCases()"
	case *proof.StepProto_SplitHypIff:
		if s.SplitHypIff != nil && s.SplitHypIff.HypIndex != nil {
			return fmt.Sprintf("SplitHypIffAtCases(%d)", *s.SplitHypIff.HypIndex)
		}
		return "SplitHypIffCases()"
	case *proof.StepProto_SplitHypImply:
		if s.SplitHypImply != nil && s.SplitHypImply.HypIndex != nil {
			return fmt.Sprintf("SplitHypImplyAt(%d)", *s.SplitHypImply.HypIndex)
		}
		return "SplitHypImply()"
	case *proof.StepProto_TrivialSimplify:
		return "TrivialSimplify()"
	case *proof.StepProto_TrivialNormalized:
		return "TrivialNormalized()"
	case *proof.StepProto_Assumption:
		return "Assumption()"
	case *proof.StepProto_Refl:
		return "Refl()"
	case *proof.StepProto_Left:
		return "Left()"
	case *proof.StepProto_Right:
		return "Right()"
	case *proof.StepProto_Funext:
		return "Funext()"
	case *proof.StepProto_ByContra:
		return "ByContra()"
	case *proof.StepProto_Symm:
		return "Symm()"
	case *proof.StepProto_Congr:
		return "Congr()"
	case *proof.StepProto_Arith:
		// Unified arithmetic automation; replay re-runs the internal
		// ring → linarith dispatch on the goal + hyps.
		return "Arith()"
	case *proof.StepProto_RingNormalize:
		// The ring normal form as a rewrite; replay re-runs it.
		return "RingNf()"
	case *proof.StepProto_CongrArg:
		// Forward congruence (PropLeftApply): hyps[idx] `a=b` + fn ⇒ `fn(a)=fn(b)`.
		t := e.reader.Term(s.CongrArg.GetFunction())
		if h, ok := e.hypHandleByUse[_HypUse{step: step}]; ok {
			return fmt.Sprintf("%s.CongrArg(%s)", h, e.printer.PrintTerm(t))
		}
		return fmt.Sprintf("CongrArg(%s, %d)", e.printer.PrintTerm(t), s.CongrArg.GetHypIndex())
	case *proof.StepProto_CongrFun:
		// Dual (PropRightApply): hyps[idx] `f=g` + arg ⇒ `f(arg)=g(arg)`.
		t := e.reader.Term(s.CongrFun.GetArgument())
		return fmt.Sprintf("CongrFun(%s, %d)", e.printer.PrintTerm(t), s.CongrFun.GetHypIndex())
	case *proof.StepProto_ClearHyps:
		// Batch weakening: drops the whole index set in one step.
		parts := make([]string, len(s.ClearHyps.GetHypIndices()))
		for i, idx := range s.ClearHyps.GetHypIndices() {
			parts[i] = fmt.Sprintf("%d", idx)
		}
		return fmt.Sprintf("ClearHyps(%s)", strings.Join(parts, ", "))
	case *proof.StepProto_CnfRefute:
		// CnfRefute needs env, but the package-level constructor returns a
		// nil-env step and Script.Do injects env when it runs — so emit
		// the bare `CnfRefute()` form. See proof.CnfRefute.
		return "CnfRefute()"
	case *proof.StepProto_SetTac:
		// Same env-injection pattern as CnfRefute: bare
		// `SetTacMembership(...)` / `SetTacLegacy(...)` — Script.Do
		// injects env. The exact-mode form, never the door `SetTac()`:
		// replay re-runs the recorded MODE's full driver (the membership
		// rewrite + residence driver, or the legacy SetTacExpand
		// fixpoint) + bare refute per residual leaf, with exactly the
		// recorded consts. The const list is the DRIVER's fixed
		// vocabulary, not a per-caller choice: a record carrying exactly
		// proof.StandardSetVocabulary — what the session's set_tac always
		// records — renders as the bare zero-argument call, which
		// supplies that same list (the form every chapter set family
		// spells); only a deliberately narrowed list is spelled out.
		ctor := "SetTacLegacy"
		if s.SetTac.GetMode() == proof.SetTacMode_SET_TAC_MEMBERSHIP {
			ctor = "SetTacMembership"
		}
		if isStandardSetVocabulary(s.SetTac.GetConsts()) {
			return ctor + "()"
		}
		parts := make([]string, len(s.SetTac.GetConsts()))
		for i, c := range s.SetTac.GetConsts() {
			parts[i] = fmt.Sprintf("%q", c)
		}
		return fmt.Sprintf("%s(%s)", ctor, strings.Join(parts, ", "))
	case *proof.StepProto_SimpWith:
		// SimpWith is a Script method (same as SetTac). Each recorded rule
		// renders via the LeanRw payload resolver — an EXACT thm ref when
		// one resolves, else the verbatim MakeProp literal — and replay
		// re-runs the full driver (tactic.SimpWithExpand: joint fixpoint +
		// conditional instance mining) on exactly these rules.
		//
		// When any rule was recorded flipped (rule_flip[i]=true), emit
		// the SimpWithFlipped variant that threads the parallel flip
		// slice — the driver EqSym's the flipped rules before mining so
		// they fire right-to-left. When no rule was flipped, emit the
		// zero-flip SimpWith form so pre-flip snapshots round-trip
		// byte-for-byte to the same Go source.
		parts := make([]string, len(s.SimpWith.GetRules()))
		for i, ref := range s.SimpWith.GetRules() {
			l, _ := e.reader.Prop(ref)
			parts[i] = e.leanRwLemmaExpr(l)
			if e.leanRwRendersMakeProp(l) {
				// The inline literal references the rule's consts and
				// frees — the family profile's binding decision is made
				// here, after the Simp fusion has had its chance (see
				// markGoUsedFromMiniStep's SimpWith arm). A pinned rule
				// (a term instance of a resolved dep) says so.
				e.markGoUsedFromPropPayload(l)
				parts[i] = e.pinnedRuleNote(l) + parts[i]
			}
		}
		flipsWire := s.SimpWith.GetRuleFlip()
		anyFlip := false
		for _, f := range flipsWire {
			if f {
				anyFlip = true
				break
			}
		}
		if at := s.SimpWith.GetAtHyp(); at > 0 {
			// At a hypothesis the Go surface is the rule form (fact.Simp /
			// SimpAt over Fwd / Rev targets); the resolved props become
			// rule targets as they are.
			ruleParts := make([]string, len(parts))
			for i, p := range parts {
				ctor := "Fwd"
				if i < len(flipsWire) && flipsWire[i] {
					ctor = "Rev"
				}
				ruleParts[i] = fmt.Sprintf("%s(MakeFact(%s))", ctor, p)
			}
			return sx + e.simpCallExpr(step, at, ruleParts)
		}
		if !anyFlip {
			return sx + fmt.Sprintf("SimpWith(%s)", strings.Join(parts, ", "))
		}
		flipParts := make([]string, len(flipsWire))
		for i, f := range flipsWire {
			if f {
				flipParts[i] = "true"
			} else {
				flipParts[i] = "false"
			}
		}
		return sx + fmt.Sprintf("SimpWithFlipped([]Prop{%s}, []bool{%s})",
			strings.Join(parts, ", "), strings.Join(flipParts, ", "))
	case *proof.StepProto_Witness:
		t := e.reader.Term(s.Witness)
		return fmt.Sprintf("Witness(%s)", e.printer.PrintTerm(t))
	case *proof.StepProto_Specialize:
		// specialize composite: one InstHyp(idx, terms...) per grounded
		// ∀-hyp; every index refers to the step's own input goal.
		// Multi-entry calls break onto separate lines (with a `\n\t`
		// continuation convention the caller re-indents) so the mega-
		// grounding case reads down the page instead of scrolling.
		entries := make([]string, len(s.Specialize.GetHyps()))
		for i, h := range s.Specialize.GetHyps() {
			args := make([]string, 0, len(h.GetWitnesses())+1)
			args = append(args, fmt.Sprintf("%d", h.GetHypIndex()))
			for _, ref := range h.GetWitnesses() {
				args = append(args, e.goTermExpr(e.reader.Term(ref)))
			}
			entries[i] = fmt.Sprintf("InstHyp(%s)", strings.Join(args, ", "))
		}
		name := "Specialize"
		if s.Specialize.GetKeepSources() {
			name = "SpecializeKeep"
		}
		if len(entries) <= 1 {
			return fmt.Sprintf("%s(%s)", name, strings.Join(entries, ", "))
		}
		return name + "(\n\t" + strings.Join(entries, ",\n\t") + ",\n)"
	case *proof.StepProto_Subst:
		if h, ok := e.hypHandleByUse[_HypUse{step: step}]; ok {
			return h + ".Subst()"
		}
		return fmt.Sprintf("Subst(%d)", s.Subst)
	case *proof.StepProto_Rw:
		// Directed rewrite-to-fixpoint with the equality hyp at the index;
		// flip reverses the direction. Parameterized only by (index, flip).
		// When the hyp is one a Derive block's Have introduced, the
		// handle form (`fact1.Rw()` / `fact1.RwRev()`) — the same
		// ministep, addressed by the Fact instead of the position the
		// chapter lint bans, with the direction in the verb rather than
		// in an argument (the authoring surface carries no flip bool;
		// only the positional Step below still takes one).
		if h, ok := e.hypHandleByUse[_HypUse{step: step}]; ok {
			if s.Rw.GetFlip() {
				return h + ".RwRev()"
			}
			return h + ".Rw()"
		}
		return fmt.Sprintf("Rw(%d, %v)", s.Rw.GetHypIndex(), s.Rw.GetFlip())
	case *proof.StepProto_Trans:
		t := e.reader.Term(s.Trans)
		return fmt.Sprintf("Trans(%s)", e.goTermExpr(t))
	case *proof.StepProto_Denote:
		// An explicit record renders the explicit form — the name and
		// the term the step chose, never the size recipe that would
		// re-derive the choice at replay; a let record has no other
		// rendering at all, since Denote(n) would move the goal to
		// ⊥-form where the record kept it.
		if ref := s.Denote.GetTerm(); ref != 0 {
			t := e.printer.PrintTerm(e.reader.Term(ref))
			switch {
			case s.Denote.GetLet():
				return fmt.Sprintf("LetTerm(%q, %s)", s.Denote.GetName(), t)
			case s.Denote.GetHilbert():
				return fmt.Sprintf("HilbertDenoteTerm(%q, %s)", s.Denote.GetName(), t)
			}
			return fmt.Sprintf("DenoteTerm(%q, %s)", s.Denote.GetName(), t)
		}
		// A search firing that placed its selection nowhere (the
		// degenerate add-the-equation case, denoteTerm) is recorded
		// without a choice; only the search form reproduces it.
		if s.Denote.GetHilbert() {
			return "HilbertDenote()"
		}
		return fmt.Sprintf("Denote(%d)", s.Denote.GetSizeThreshold())
	case *proof.StepProto_Lemma:
		// Introduce the payload as a sub-claim (child(0) = the lemma,
		// proved by the following steps; child(1) = residual). Render the
		// STATEMENT via MakeProp — `Lemma(lemma Prop, ...)` takes a Prop,
		// not a Thm. External citations are handled by the Cite fusion
		// (Lemma + KnownThm) upstream; a bare Lemma reaching here is an
		// in-proof sub-claim. Mirrors Assert below. See
		// emitMiniStepCaseHead's Lemma arm for the case-bearing form.
		l, _ := e.reader.Prop(s.Lemma)
		return fmt.Sprintf("Lemma(%s)", e.miniStepPropExpr(l))
	case *proof.StepProto_LemmaPreserve:
		// Hypothesis-preserving counterpart of Lemma (agent-session
		// `lemma` dispatch). External citations fuse upstream into
		// CitePreserve; a bare step here renders the statement inline,
		// replaying via tactic.LemmaPreserveTactic.
		l, _ := e.reader.Prop(s.LemmaPreserve)
		return fmt.Sprintf("LemmaPreserve(%s)", e.miniStepPropExpr(l))
	case *proof.StepProto_LeanRw:
		l, _ := e.reader.Prop(s.LeanRw)
		return fmt.Sprintf("LeanRw(%s)", e.leanRwLemmaExpr(l))
	case *proof.StepProto_TypeInst:
		l, _ := e.reader.Prop(s.TypeInst)
		return fmt.Sprintf("TypeInst(%s)", e.typeInstSourceExpr(l))
	case *proof.StepProto_KnownThm:
		// strongerGoal — the cache-matched prior thm. Script.Do
		// dispatches via cache lookup at replay; the arg here is
		// informational, but we still resolve it the same way so the
		// emitted call self-documents which thm closed the leaf.
		//
		// An earlier section renders `CiteNode(<section>)` — a shorthand
		// that threads the section's PromisedThm() lazily; an external
		// statement renders as the consolidated `Cite(<entry>)` when it
		// is a named entry, else the general `CiteKnown(<expr>)`.
		if r := s.KnownThm.GetReading(); r.GetLaw() != nil {
			// A close on a structure law read at an instance (the session's
			// `lemma {key, read_at}`): the consolidated verb over the
			// reading, which no entry states.
			return fmt.Sprintf("Cite(%s)", e.readingExpr(r, e.hypHandleByUse[_HypUse{step: step}]))
		}
		stronger, _ := e.reader.Prop(s.KnownThm.GetStrongerGoal())
		name, refOK := e.resolveLemmaRef(stronger)
		if refOK {
			return fmt.Sprintf("CiteNode(%s)", name)
		}
		{
			// An auto-match close whose payload
			// resolves to a NAMED entry renders as the consolidated verb —
			// `Cite(N)` reproduces the close through the normalize-tier
			// gate (prover/proof/fact.go citeNormalizedClose: the leaf IS
			// the entry's statement modulo Normalize, which is exactly the
			// match the session's auto-match committed). The
			// `CiteKnown(ctx.Dep("N"))` spelling is the internal close
			// Step, lint-banned in the hand-blessed corpus
			// (TestLintOneCiteVerb), so emit never renders it for a named
			// entry. A landed entry is cited as its var, the spelling a
			// By premise and the Deps list give the same name; the quoted
			// name is for a name nothing states, which the verb refuses
			// (it takes a CiteTarget): a dep is an entry, landed first.
			if leaf, ok := e.resolveExternalLeafProp(stronger); ok &&
				leaf.Kind == LeafLibraryThm && leaf.ThmName != "" {
				e.markDepName(leaf.ThmName, leaf.Key)
				if id, ok := e.depIdent(leaf.ThmName, leaf.Key); ok {
					return fmt.Sprintf("Cite(%s)", id)
				}
				return fmt.Sprintf("Cite(%q)", leaf.ThmName)
			}
		}
		return fmt.Sprintf("CiteKnown(%s)", e.lemmaRefExpr(stronger))
	case *proof.StepProto_PairedBeta:
		// paired_beta composite (proto tag 53): the payload is the
		// POLYMORPHIC source (pairs.PairedLambda), which resolves through the
		// standard lemma-reference tiers — a named dep the external-leaf
		// resolver classifies.
		// Replay re-runs the shared driver (computePairedBetaSubGoals);
		// nothing per-site is rendered. This resolvability is the point
		// of the composite: its predecessor recorded the per-site TERM
		// instance in a KnownThm, which no tier can resolve — emit
		// panicked in externalLeafExprCtx ([auto-pipeline-gap]).
		src, _ := e.reader.Prop(s.PairedBeta)
		return fmt.Sprintf("PairedBetaStep(%s)", e.lemmaRefExpr(src))
	case *proof.StepProto_ByCase:
		t := e.reader.Term(s.ByCase)
		return fmt.Sprintf("ByCaseStep(%s)", e.caseTermExpr(t))
	case *proof.StepProto_Induction:
		// InductStep needs env (pulls _0 / suc + num_induction) — kept on ctx.
		t := e.reader.Term(s.Induction)
		return fmt.Sprintf("%sInductStep(%s.Core())", sx, e.goTermExpr(t))
	case *proof.StepProto_AxiomDef:
		ct := e.constAt(s.AxiomDef.GetConst())
		return fmt.Sprintf("AxiomDefStep(%s)", e.printer.PrintTerm(ct))
	case *proof.StepProto_ExistentialConstDef:
		ct := e.constAt(s.ExistentialConstDef)
		return fmt.Sprintf("ExistentialConstDefStep(%s)", e.printer.PrintTerm(ct))
	case *proof.StepProto_DefExpand:
		// Composite def_expand — renders as a single ministep call. Replay
		// reproduces the LeanRw+AxiomDef+TrivialSimplify subtree via
		// computeDefExpandSubGoals; there is nothing to fuse and no residual
		// menu to disambiguate.
		// The chapter spelling names the definition: Unfold opens the
		// constant it defines and records the IDENTICAL ministep — the
		// walker instantiates per occurrence, so the recorded instance
		// was never load-bearing.
		ct := e.constAt(s.DefExpand)
		return fmt.Sprintf("Unfold(%s)", e.definitionExpr(string(ct.Name())))
	case *proof.StepProto_Assert:
		// Fresh hyp-free sub-claim (Coq `assert` / Lean `have`). Render
		// inline as the claim's text (claimExpr); the claim's symbols
		// were registered by walkMiniStep's Assert arm. Distinct from
		// Lemma/KnownThm, which resolve a lemma reference via
		// lemmaRefExpr.
		claim, _ := e.reader.Prop(s.Assert)
		return fmt.Sprintf("AssertStep(%s)", e.claimExpr(claim))
	case *proof.StepProto_Define, *proof.StepProto_DefineData,
		*proof.StepProto_DefineSpec, *proof.StepProto_DefineType,
		*proof.StepProto_DefineInductive, *proof.StepProto_DefineQuotient:
		// A definition section is an ENTRY, not a body: its mint must
		// re-run at package init (the family door), which a Build body
		// cannot host — rendering the composite here would compile and
		// then panic at replay on the missing const. Two ways here: a
		// definition section emitted without `family` (route the caller
		// to the profile that renders it whole), or a definition's
		// composite INSIDE a member's body, which no record may hold — a
		// cite of a definition is a known-theorem leaf (ApplyCiteNode),
		// so a nested composite is a recording fault.
		panic(fmt.Sprintf("emit: a definition section renders only as the root of a "+
			"Family-profile emit (%s — pass `family` in the emit-section request); "+
			"a definition composite inside a body is a recording fault: a cite of a "+
			"definition records a known-theorem leaf, never its derivation",
			definitionDoorCall(step)))
	}
	// Fail loud at EMIT time: a nil Step would compile fine but nil-deref
	// at REPLAY (TestReplayAll), far from the cause. A new ministep variant
	// (or one the proto knows but emit doesn't yet render — e.g. a freshly
	// added tactic like congr/clear) must get a case above; surfacing it
	// here pins the gap to the offending proof during emit instead.
	panic(fmt.Sprintf("emit: unhandled ministep %T — add a case to "+
		"emitMiniStep (and walkMiniStep if it carries terms, plus a "+
		"package-level Script constructor + alias). A nil Step would "+
		"otherwise nil-deref at replay.", step.Step))
}

// isStandardSetVocabulary reports whether a recorded set_tac const
// list is exactly the driver's own vocabulary
// (proof.StandardSetVocabulary) as a SET — the list the zero-argument
// SetTac / SetTacMembership calls supply. Order is immaterial to the
// driver (the unfolder's fixpoint runs over the whole set), so an
// order-insensitive comparison spells the same step.
func isStandardSetVocabulary(consts []string) bool {
	standard := proof.StandardSetVocabulary()
	if len(consts) != len(standard) {
		return false
	}
	want := make(map[string]bool, len(standard))
	for _, c := range standard {
		want[c] = true
	}
	seen := make(map[string]bool, len(consts))
	for _, c := range consts {
		if !want[c] || seen[c] {
			return false
		}
		seen[c] = true
	}
	return true
}

// lemmaRefExpr renders the Go expression that resolves a lemma's Thm
// at runtime: an earlier section's `.PromisedThm()`, or an
// external-leaf expression (`ctx.ConstDef("list_append")`, `ctx.Dep("N")`,
// …). Used by emitMiniStep for Lemma / LeanRw / TypeInst / KnownThm
// payloads.
func (e *_Emitter) lemmaRefExpr(l core.Prop) string {
	return e.lemmaRefExprCtx(l, leafPlain)
}

// lemmaRefExprCtx is lemmaRefExpr with an explicit consumption context
// for the external-leaf fallback (see renderExternalLeaf: an
// applied-as-lemma context makes a const-def leaf render as
// ConstDefNormalized — required when the payload is APPLIED as a lemma,
// e.g. the Cite fusion).
//
// A leafCite context also changes the SECTION arm: the `Cite` verb takes
// a *GoalStackNode directly (promise-transparent — it reads
// PromisedThm itself), so the node reference is rendered bare rather
// than with the `.PromisedThm()` suffix every static Thm slot needs.
func (e *_Emitter) lemmaRefExprCtx(l core.Prop, ctx leafCtx) string {
	if expr, ok := e.tryLemmaRefExprCtx(l, ctx, true); ok {
		return expr
	}
	return e.externalLeafExprCtx(l, ctx)
}

// tryLemmaRefExprCtx is the core of lemmaRefExprCtx: an earlier section
// first, then the external-leaf tiers (tryExternalLeafExpr).
// allowPlaceholder=false reports a total miss as ("", false) instead of
// the TODO placeholder, for a caller with a further tier to try.
func (e *_Emitter) tryLemmaRefExprCtx(l core.Prop, ctx leafCtx, allowPlaceholder bool) (string, bool) {
	if ref, ok := e.resolveLemmaRef(l); ok {
		if ctx == leafCite {
			return ref, true
		}
		return fmt.Sprintf("%s.PromisedThm()", ref), true
	}
	return e.tryExternalLeafExprPlaceholder(l, ctx, true, allowPlaceholder)
}

// typeInstSourceExpr renders the Thm a TypeInst step instantiates. An
// EXACT (`!viaNormalize`) hit already carries the recorded raw source's
// α-form and is used as-is. A referent resolved VIA NORMALIZE is only
// normalize-equivalent to the recorded source — its own statement form can
// be structurally UNRECOVERABLE from the recorded goal at every one of
// `_TypeInstStep`'s match tiers, because Normalize does not commute with
// type instantiation (funext expansion of type-var equalities at
// function-type instances; ∀-binder MERGE when a multi-type-var source's
// conjuncts collapse to one concrete type — both at once in one
// comprehension-membership cite, where the raw-tier miss AND the normalized-tier miss
// left no recovery). So the viaNormalize arm renders the RECORDED source
// verbatim (miniStepPropExpr — the payload-faithfulness rule) and bridges
// the referent thm into that exact α-form via Script.TypeInstSourceExact,
// which also keeps TypeInstSource's normalized-registration side effect
// (downstream cites and ClaimProved integrity checks depend on it —
// dropping it broke 86 replays when a bare unwrapped referent was
// tried). See set_basic.InUnions / InInters and set_algebra.UnionsEmpty.
func (e *_Emitter) typeInstSourceExpr(l core.Prop) string {
	if ref, viaNormalize, ok := e.resolveLemmaRefDetailed(l); ok {
		// Promise-transparent: an earlier section's cert is an unforced
		// ThmPromise on the define-then-run path, so reference it via
		// PromisedThm() (not ProvedThm(), which collapses and panics on a
		// promise).
		thmExpr := ref + ".PromisedThm()"
		if viaNormalize {
			return fmt.Sprintf("ctx.TypeInstSourceExact(%s, %s)", thmExpr, e.miniStepPropExpr(l))
		}
		return thmExpr
	}
	return e.externalLeafExpr(l)
}

// typeInstRendersProp reports whether typeInstSourceExpr will render the
// recorded source prop inline (the viaNormalize arm's MakePropText /
// MakeProp payload). When true, the prop's consts / free vars become
// Go-side references that walkMiniStep must register and
// markGoUsedFromMiniStep must flag. Single source of truth for the
// rendering decision — keep in lockstep with typeInstSourceExpr (mirrors
// leanRwRendersMakeProp).
func (e *_Emitter) typeInstRendersProp(l core.Prop) bool {
	_, viaNormalize, ok := e.resolveLemmaRefDetailed(l)
	return ok && viaNormalize
}

// leanRwLemmaExpr renders the rewrite-rule argument of a LeanRw
// ministep. Unlike KnownThm / TypeInst (which genuinely need a proven
// Thm), a LeanRw's child[0] is ALWAYS the rewrite rule as a proof
// OBLIGATION discharged by the following step(s) — usually a cite
// (KnownThm of an entry / section thm), occasionally a non-trivial
// inline subtree (e.g. a binder-reordered variant of the goal proven in
// place). So the argument only has to carry the rule's PROPOSITION;
// `LeanRw(lemma Prop)` accepts an unproved Prop and the obligation is
// proven separately. Prefer a resolvable thm ref (readable, and lets the
// dep show through); fall back to MakeProp(<concl>) when none
// resolves, instead of emitting a nil external-leaf placeholder that
// nil-derefs at replay. Mirrors emitMiniStep's Lemma arm. Rewrite rules
// are hyp-free (LeanRwTactic's directConclusionRewriteTactic bails on
// hyps), so rendering only the conclusion is complete.
// leanRwRendersMakeProp reports whether leanRwLemmaExpr will render the
// LeanRw rule as an inline MakeProp(<concl>) (rather than a resolved thm
// ref or an external-leaf expr). When true, the rule's conclusion
// vars/consts become Go-side references that markGoUsedFromMiniStep must
// flag so renderVarDecls / renderStructDef declare them. Single source of
// truth for the rendering decision — keep in lockstep with leanRwLemmaExpr.
func (e *_Emitter) leanRwRendersMakeProp(l core.Prop) bool {
	_, ok := e.leanRwRuleTarget(l)
	return !ok
}

// leanRwRuleTarget renders a rewrite rule (a LeanRw's, or a pinned
// SimpWith's) as a RESOLVED reference when the reference delivers the
// recorded rule EXACTLY — the rule's instantiation is load-bearing, so
// the reference must not merely name the same theorem: an earlier
// section on an exact (non-normalize) hit, or a library theorem whose
// served statement (ExternalLeaf.Stated) is the recorded rule,
// `ctx.Dep(name)`, or has the recorded rule as a proper type instance,
// `ctx.AtTypes(ctx.Dep(name), τ…).Reference()` (the stated form at the
// instance, TypedThm.Reference). A leaf whose served statement the
// resolver cannot say (Stated nil) is referenced only when the record
// IS the leaf (a raw-key hit). ok=false means the
// caller spells the rule verbatim (MakeProp) — the pinned rendering,
// faithful by construction.
func (e *_Emitter) leanRwRuleTarget(l core.Prop) (string, bool) {
	if ref, viaNormalize, ok := e.resolveLemmaRefDetailed(l); ok && !viaNormalize {
		return fmt.Sprintf("%s.PromisedThm()", ref), true
	}
	if e.opts.ResolveExternalLeaf == nil {
		return "", false
	}
	leaf, ok := e.resolveExternalLeafProp(l)
	if !ok || leaf.Kind != LeafLibraryThm {
		return "", false
	}
	sx := "ctx."
	if leaf.Stated == nil {
		if leaf.Key != l.AlphaKey() {
			return "", false
		}
		e.markDepName(leaf.ThmName, leaf.Key)
		return fmt.Sprintf("%sDep(%s)", sx, e.depNameExpr(leaf.ThmName, leaf.Key)), true
	}
	if sameStatement(l, leaf.Stated) {
		e.markDepName(leaf.ThmName, leaf.Key)
		return fmt.Sprintf("%sDep(%s)", sx, e.depNameExpr(leaf.ThmName, leaf.Key)), true
	}
	if _, full, ok := atTypesInstance(leaf.Stated, l); ok &&
		core.PropTypeInst(leaf.Stated, full...).AlphaEquals(l) {
		args, _ := e.atTypesArgs(leaf.Stated, l)
		e.markDepName(leaf.ThmName, leaf.Key)
		return fmt.Sprintf("%sAtTypes(%sDep(%s)%s).Reference()", sx, sx, e.depNameExpr(leaf.ThmName, leaf.Key), args), true
	}
	return "", false
}

// pinnedRuleNote annotates a simp rule the pinned rendering spells out
// because it is a TERM instance of a resolved dep — a session
// `term_specialize` pin (`real_construction.MulSym` at x₀, w). The literal replays
// as recorded; the note says which fact was pinned and where, since a
// simp rule has no ground form on the Go side and the chapter spelling
// is the ground premise. Empty when the rule is not such a pin.
func (e *_Emitter) pinnedRuleNote(l core.Prop) string {
	if e.opts.ResolveExternalLeaf == nil {
		return ""
	}
	leaf, ok := e.resolveExternalLeafProp(l)
	if !ok || leaf.Kind != LeafLibraryThm || leaf.Stated == nil || sameStatement(l, leaf.Stated) {
		return ""
	}
	if _, _, isType := atTypesInstance(leaf.Stated, l); isType {
		return ""
	}
	witnesses, ok := termInstanceWitnesses(leaf.Stated, l)
	if !ok {
		return ""
	}
	ws := make([]string, len(witnesses))
	for i, w := range witnesses {
		ws[i] = e.display(ext.PrintTerm(w))
	}
	at := strings.Join(ws, ", ")
	return fmt.Sprintf("/* %s pinned at %s — a simp rule has no ground form; the chapter spells "+
		"the pinned fact as a premise, At(<entry>, %s), in a By or a Have */ ", leaf.ThmName, at, at)
}

// termInstanceWitnesses matches instance against stated's ∀-stripped
// matrix with stated's binders instantiable, and returns the binders'
// images in binder order — ok only when the match binds at least one
// binder to something other than itself (a genuine pin; an α-copy is
// not one).
func termInstanceWitnesses(stated, instance core.Prop) ([]core.Term, bool) {
	vars, body := stripLeadingForalls(stated.Conclusion())
	if len(vars) == 0 {
		return nil, false
	}
	_, target := stripLeadingForalls(instance.Conclusion())
	names := unify.TermNameSet{}
	for _, v := range vars {
		names.Add(v.Name())
	}
	bindings, ok := unify.TermMatch(body, target, names)
	if !ok {
		return nil, false
	}
	out := make([]core.Term, len(vars))
	pinned := false
	for i, v := range vars {
		out[i] = v
		if b, hit := bindings[v.Name()]; hit {
			out[i] = b
			if !b.AlphaEquals(v) {
				pinned = true
			}
		}
	}
	return out, pinned
}

// stripLeadingForalls peels a term's leading ∀ binders.
func stripLeadingForalls(t core.Term) ([]core.VarTerm, core.Term) {
	var vars []core.VarTerm
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return vars, t
		}
		vars = append(vars, abs.Var())
		t = abs.Body()
	}
}

func (e *_Emitter) leanRwLemmaExpr(l core.Prop) string {
	// EXACT match only. A LeanRw's rule becomes child[0] (the rewrite
	// obligation) VERBATIM in its raw form, and the recording keyed that
	// obligation on exactly that form. A `viaNormalize` ref resolves to
	// a section thm that is merely normalize-equivalent — it can differ
	// in binder order / equation orientation (e.g. recorded rule
	// `∀y.∀x.(x=fst(,(x,y)))` vs the section's `∀x.∀y.…`), so emitting
	// that ref yields a child[0] whose raw key diverges from the recorded
	// one even though the two are the same theorem up to Normalize. So
	// only take the ref on an EXACT (non-normalize) hit; otherwise render
	// the EXACT recorded rule via MakeProp (below), and let the following
	// KnownThm/cite (which DOES match up to Normalize) discharge it.
	if expr, ok := e.leanRwRuleTarget(l); ok {
		return expr
	}
	return e.miniStepPropExpr(l)
}

// externalLeafExpr returns the Go expression that serves an external
// statement at replay (renderExternalLeaf's lowering of the resolver's
// classification), or the TODO placeholder when nothing resolves it.
func (e *_Emitter) externalLeafExpr(l core.Prop) string {
	return e.externalLeafExprCtx(l, leafPlain)
}

// externalLeafExprCtx is externalLeafExpr with an explicit consumption
// context (threaded to renderExternalLeaf's
// ConstDef-vs-ConstDefNormalized and dep-name-vs-wrap dispatches).
func (e *_Emitter) externalLeafExprCtx(l core.Prop, ctx leafCtx) string {
	expr, _ := e.tryExternalLeafExpr(l, ctx, true)
	return expr
}

// tryExternalLeafExpr renders the classified leaf for a payload, or the
// placeholder when nothing classifies it (see
// tryExternalLeafExprPlaceholder).
//
// allowConstDefInstance gates the by-name const-def fallback tier for
// payloads that are PROPER type instances of a polymorphic def (see
// tryConstDefByName). LeanRw renderers (leanRwLemmaExpr /
// leanRwRendersMakeProp / tryRewriteFusion) pass false — a rewrite
// rule's recorded instantiation is load-bearing and must render
// verbatim, not round-trip through `ctx.ConstDef(name)` + replay-time
// re-adaptation. All other consumers (Cite fusion, TypeInst,
// externalLeafExprCtx) pass true.
func (e *_Emitter) tryExternalLeafExpr(l core.Prop, ctx leafCtx, allowConstDefInstance bool) (string, bool) {
	return e.tryExternalLeafExprPlaceholder(l, ctx, allowConstDefInstance, true)
}

// resolveExternalLeafProp classifies a payload prop no section of this
// member proves, through the caller's resolver (EmitOptions.
// ResolveExternalLeaf) at the payload's raw key and then its normalized
// key. The lookup half of tryExternalLeafExpr, split out so
// non-rendering consumers (the KnownThm arm, the symbol walk's
// predicates) can identify a leaf without committing to a rendering
// context.
func (e *_Emitter) resolveExternalLeafProp(l core.Prop) (ExternalLeaf, bool) {
	if e.opts.ResolveExternalLeaf == nil {
		return ExternalLeaf{}, false
	}
	normalized, _ := proof.Normalize(l)
	for _, k := range []core.PropKey{l.AlphaKey(), normalized.AlphaKey()} {
		if leaf, ok := e.opts.ResolveExternalLeaf(k); ok {
			return leaf, true
		}
	}
	return ExternalLeaf{}, false
}

// tryExternalLeafExprPlaceholder is tryExternalLeafExpr with the
// TODO-placeholder affordance made explicit: allowPlaceholder=false
// reports a total miss as a MISS instead of the `ThmCert{}`
// placeholder — required where a caller has a further tier to try.
func (e *_Emitter) tryExternalLeafExprPlaceholder(l core.Prop, ctx leafCtx, allowConstDefInstance, allowPlaceholder bool) (string, bool) {
	leaf, ok := e.resolveExternalLeafProp(l)
	if ok {
		// Payload-exact form dispatch for const-def leaves: the rendered
		// thm's conclusion becomes the obligation/leaf goal VERBATIM (LeanRw
		// child[0], Cite's KnownThm match), so it must reproduce the form
		// the session RECORDED — not the form the caller's context guesses.
		// A session that cites a const's def equation in its normalized
		// form (∀-lifted, equation oriented `def_body = c(x…)`) records a
		// payload that α-equals Normalize(def) — raw `ctx.ConstDef` would
		// replay the `c = λ…` equation and the leaf AlphaKey would diverge
		// from the recorded step. Promote-only: a payload that is NOT
		// exactly the normalized def (raw, or a type instance) keeps the
		// caller's flag.
		//
		// For the verbatim-form callers (allowConstDefInstance=false —
		// LeanRw / SimpWith rule renderers), a payload that matches
		// NEITHER the raw def NOR the normalized def is reported as a
		// MISS so the caller falls through to the verbatim MakeProp
		// rendering. Engine sessions can record a def-equation rule in a
		// form that Normalize does not reproduce — e.g. real_sub's
		// `∀a,b.((a-b) = (a+ -b))` (const-applied on the LHS) vs
		// Normalize's `def_body = c(x…)` orientation — and both ConstDef
		// forms would then diverge from the recorded obligation
		// (real_polynomial.Sub). The proven-thm callers keep the hit:
		// their payload is matched up to Normalize at replay, not
		// verbatim.
		if leaf.Kind == LeafConstDef && e.loadConstMeta != nil {
			if meta, mok := e.loadConstMeta(core.TermName(leaf.ConstName)); mok && !meta.IsZero() && !meta.DefThm().IsZero() {
				nDef, _ := proof.Normalize(meta.DefThm())
				if !ctx.appliesAsLemma() && nDef.AlphaKey() == l.AlphaKey() {
					ctx = leafLemma
				}
				if !allowConstDefInstance {
					replayed := core.Prop(meta.DefThm())
					if ctx.appliesAsLemma() {
						replayed = nDef
					}
					if replayed.AlphaKey() != l.AlphaKey() {
						return "", false
					}
				}
			}
		}
		return e.renderExternalLeaf(leaf, ctx, l), true
	}
	// Const-def fallback for type-instantiated rewrite rules. The engine
	// adapts a polymorphic const def to the goal's concrete types at the
	// lemma-application boundary, so the inline payload is a *type
	// instance* of the polymorphic def — its AlphaKey is absent
	// from the resolver and from the const-def reverse index (which is
	// keyed on the abstract-type
	// form). Identify the const by name and emit `ctx.ConstDef(name)`;
	// at replay the rewrite engine re-adapts the polymorphic def back
	// to the goal's types. The canonical case is surjective's def cited as a
	// rewrite rule inside peano.sucZeroExists.
	//
	// Whether the proper-instance tier is admissible is the CALLER's
	// call (allowConstDefInstance): the re-adaptation round-trip is
	// only faithful when the goal pins the instance unambiguously, so
	// LeanRw renderers opt out and emit the recorded rule verbatim.
	if expr, ok := e.tryConstDefByName(l, ctx, allowConstDefInstance); ok {
		return expr, true
	}
	// Unresolved: an inspectable TODO placeholder that does not compile
	// — loud, never a wrong reference.
	if allowPlaceholder {
		return ctx.certificate(fmt.Sprintf("/* TODO: unresolved lemma %q — no section or entry states it */ ThmCert{}",
			l.AlphaKey())), true
	}
	return "", false
}

// tryConstDefByName resolves a leaf that is (a type instance of) some
// constant's defining equation, by the head constant of the
// equation's LHS rather than by AlphaKey. Returns the rendered
// `ctx.ConstDef(name)` expression on success.
//
// Why by-name: the inline rewrite-rule payload is the goal-adapted
// (concretely-typed) form of a polymorphic def, so neither its raw nor
// its normalized AlphaKey matches the abstract-type def's key.
// We instead (1) read the const name off the LHS head, (2) fetch that
// const's canonical def, (3) confirm the leaf really is that def up to
// type instantiation (guarding against an unrelated equation whose LHS
// happens to head with the same const), and only then render ConstDef.
//
// allowInstance=false restricts step (3) to α-equality (up to
// Normalize): a payload that is a PROPER type instance of the def is
// rejected, so the caller falls through to verbatim rendering. LeanRw
// renderers need this — `ctx.ConstDef(name)` erases the recorded
// instantiation and re-derives it at replay via chooseTypeAdaptedStep,
// which diverges from the record whenever the goal carries the const
// at several distinct type instances (the deterministic adapter
// abstains instead of re-picking the recorded pin; see
// bareConstAnchorAmbiguous in prover/typematch and the
// image/iterate replay incident).
func (e *_Emitter) tryConstDefByName(l core.Prop, ctx leafCtx, allowInstance bool) (string, bool) {
	if e.loadConstMeta == nil {
		return "", false
	}
	name, ok := equationLHSConstName(l)
	if !ok {
		return "", false
	}
	meta, ok := e.loadConstMeta(name)
	if !ok || meta.IsZero() || meta.DefThm().IsZero() {
		return "", false
	}
	nDef, _ := proof.Normalize(meta.DefThm())
	nLeaf, _ := proof.Normalize(l)
	if !nDef.AlphaEquals(nLeaf) {
		if !allowInstance {
			return "", false
		}
		if _, matched := proof.NormalizedPropTypeMatch(nDef, nLeaf); !matched {
			return "", false
		}
	}
	return e.renderExternalLeaf(ExternalLeaf{
		Kind:      LeafConstDef,
		ConstName: string(name),
	}, ctx, l), true
}

// equationLHSConstName returns the name of the constant at the head of
// the LHS of an equational conclusion `lhs = rhs`. HOL represents `⇔`
// as `=` at bool, so iff conclusions are covered too. Returns ok=false
// when the conclusion isn't a binary-operator application or the LHS
// head isn't a constant.
func equationLHSConstName(l core.Prop) (core.TermName, bool) {
	app, ok := l.Conclusion().Core().(core.AppliedTerm) // (= lhs) rhs
	if !ok {
		return "", false
	}
	inner, ok := app.Fun().Core().(core.AppliedTerm) // = lhs
	if !ok {
		return "", false
	}
	head := inner.Arg() // lhs
	for {
		a, ok := head.Core().(core.AppliedTerm)
		if !ok {
			break
		}
		head = a.Fun()
	}
	if ct, ok := head.Core().(core.ConstTerm); ok {
		return ct.Name(), true
	}
	return "", false
}

// leafCtx says how the caller CONSUMES the external leaf it asks emit
// to render. It selects the install FORM, which is not cosmetic — see
// renderExternalLeaf.
type leafCtx int

const (
	// leafPlain — the leaf fills a static Thm slot that tolerates the
	// raw recorded form: a TypeInst Source, a CiteKnown bridge, a LeanRw
	// rule, a def-expansion.
	leafPlain leafCtx = iota
	// leafLemma — the leaf is APPLIED as a lemma rule (a Lemma /
	// LemmaPreserve ministep).
	leafLemma
	// leafCite — the leaf is the target of the consolidated `Cite` verb.
	// Applied as a lemma like leafLemma, but Cite's own target dispatch
	// resolves an ENTRY to the canonical install form, so the emitted
	// target can be the entry var instead of a hand-spelled wrap.
	leafCite
)

// appliesAsLemma reports whether the leaf will be run through the lemma
// machinery (as opposed to occupying a static Thm slot).
func (c leafCtx) appliesAsLemma() bool { return c != leafPlain }

// certificate is a certificate-valued expression as this context takes
// it: the target of a cite verb is a proof.CiteTarget, which names a
// certificate through MakeFact; every other slot takes it as it is.
func (c leafCtx) certificate(expr string) string {
	if c == leafCite {
		return "MakeFact(" + expr + ")"
	}
	return expr
}

// payloadIsClosedNormalizeUnstable reports whether p is a CLOSED
// formula (no hypotheses, no free term variables) that proof.Normalize
// does not fix — the multi-clause-conjunction class (per-conjunct
// binders re-bound under one shared ∀-prefix). Free-var payloads are
// excluded: Normalize ∀-closes frees, a change that says nothing about
// the packing pathology this predicate exists to detect.
func payloadIsClosedNormalizeUnstable(p core.Prop) bool {
	if p.NumHyps() != 0 {
		return false
	}
	if len(p.Conclusion().Frees(func(core.VarTerm) bool { return true })) != 0 {
		return false
	}
	n, _ := proof.Normalize(p)
	return n.AlphaKey() != p.AlphaKey()
}

// renderExternalLeaf turns a classified leaf into its Go expression.
//
// ctx.appliesAsLemma() must hold when the leaf is consumed as a LEMMA
// rule (a Lemma ministep, a Cite). In that case a LeafConstDef renders
// as ConstDefNormalized(name) — the applied/iff form
// `∀P,x.(P(x)⇔set_member(x,P))` that the session's search applies —
// NOT the raw lambda equation `set_member = λ_._( _)` that ConstDef returns. The
// raw equation only UNFOLDS the const; a proof that INTRODUCES
// membership (fold `s(ẋ)→set_member(ẋ,s)`) needs the normalized iff. Every other
// consumer (TypeInst / CiteKnown / LeanRw / def-expansion) passes
// leafPlain and keeps the raw ConstDef — those either need only the type
// skeleton (TypeInst) or rewrite in the unfold direction, where raw and
// normalized coincide. See set_algebra.UnionIdempot / InterIdempot / the set-difference
// family.
//
// payload is the recorded lemma payload prop when the caller has it,
// nil otherwise. The LeafLibraryThm arm dispatches its NormalizedThm
// wrap on the payload's normalize-stability
// (payloadIsClosedNormalizeUnstable).
func (e *_Emitter) renderExternalLeaf(leaf ExternalLeaf, ctx leafCtx, payload core.Prop) string {
	switch leaf.Kind {
	case LeafConstDef:
		if leaf.ConstName == "" {
			panic(fmt.Sprintf(
				"emit: const-def leaf %q missing const name — "+
					"the external-leaf resolver produced LeafConstDef with empty "+
					"ConstName, which should be unreachable", leaf.Key))
		}
		if ctx.appliesAsLemma() {
			return ctx.certificate(fmt.Sprintf("ctx.ConstDefNormalized(%q)", leaf.ConstName))
		}
		return fmt.Sprintf("ctx.ConstDef(%q)", leaf.ConstName)
	case LeafLibraryThm:
		if leaf.ThmName == "" {
			panic(fmt.Sprintf(
				"emit: library-thm leaf %q missing thm name — "+
					"the external-leaf resolver produced LeafLibraryThm with empty "+
					"ThmName, which should be unreachable", leaf.Key))
		}
		e.markDepName(leaf.ThmName, leaf.Key)
		// A payload that is a PROPER type instance of the statement
		// the dep serves (ExternalLeaf.Stated) renders as that
		// instance — ctx.AtTypes(ctx.Dep(name), τ…) — so the dep's
		// identity AND the recorded σ both survive: a By premise
		// installs the instance exactly (a *TypedThm premise records
		// exact), a Simp rule fires the stated form at the instance,
		// a Cite reads it. The bare name would serve the polymorphic
		// statement and leave the instance to replay's speculative
		// re-adaptation, which picks another width on a two-type goal. Only a
		// lemma-applied context: a static Thm slot (TypeInst's
		// source) holds the polymorphic statement itself.
		if ctx.appliesAsLemma() && payload != nil && leaf.Stated != nil {
			if expr, ok := e.wrapperInstExpr(leaf.ThmName, leaf.Key, leaf.Stated, payload); ok {
				return expr
			}
			if args, ok := e.atTypesArgs(leaf.Stated, payload); ok {
				return fmt.Sprintf("ctx.AtTypes(ctx.Dep(%s)%s)", e.depNameExpr(leaf.ThmName, leaf.Key), args)
			}
		}
		// Chapter compute-route: cite through the claiming dep verb —
		// ctx.Dep is LibraryThm lookup + ClaimProvedThm + ThmCert in
		// one call (idempotent), so the emitted file needs no per-dep
		// claim ladder. In lemma context the NormalizedThm wrap is
		// dispatched on the recorded payload's normalize-stability:
		// a normalize-STABLE payload means the session installed the
		// entry's normalized form (the wrap recomputes it from the raw
		// harness cert — load-bearing for sequent-shaped statements);
		// a CLOSED payload Normalize CHANGES means the session
		// installed the raw surface form itself, and wrapping would
		// re-bind it (multi-clause conjunction statements pack
		// per-conjunct binders under one shared ∀-prefix,
		// un-splittable at replay). The closedness guard keeps
		// free-var payloads on the wrap arm: Normalize ∀-closes frees
		// — an instability that is NOT the conjunction-packing
		// pathology.
		//
		// leafCite folds the same dispatch into `Cite`'s own target
		// resolution: a dep NAME resolves to the canonical install
		// form (NormalizedThm(Dep(name))), so the wrap arm renders as
		// the bare name — one string instead of two nested calls —
		// while the raw arm keeps the explicit
		// cert, which is exactly the marked-minority spelling
		// prover/proof/fact.go documents for surface-form cites.
		if ctx.appliesAsLemma() {
			// A landed entry is cited as its var in every lemma slot —
			// the By premise, the Simp rule, the Cite target — which is
			// how the chapters spell it (`By(carried, real_sum.Clauses)`,
			// `Simp(Fwd(ConvexDef))`): the var serves the entry's STATED
			// form, which is what both arms below hand-spelled — the raw
			// cert for a closed statement Normalize repacks (an iff, a
			// clause pack), the normalized wrap otherwise — while the
			// premise machinery adds the normalized clause for the closer
			// itself. The two arms remain for a name nothing states.
			if id, ok := e.depIdent(leaf.ThmName, leaf.Key); ok {
				return id
			}
			if payload != nil && payloadIsClosedNormalizeUnstable(payload) {
				return ctx.certificate(fmt.Sprintf("ctx.Dep(%q)", leaf.ThmName))
			}
			if ctx == leafCite {
				// The quoted name, which no cite verb takes: a dep is
				// an entry, landed first (depNameExpr).
				return fmt.Sprintf("%q", leaf.ThmName)
			}
			return fmt.Sprintf("ctx.NormalizedThm(ctx.Dep(%q))", leaf.ThmName)
		}
		return fmt.Sprintf("ctx.Dep(%s)", e.depNameExpr(leaf.ThmName, leaf.Key))
	case LeafTypeDefAxiom:
		if leaf.ConstName == "" {
			panic(fmt.Sprintf(
				"emit: type-def axiom leaf %q missing const name — "+
					"the external-leaf resolver produced LeafTypeDefAxiom with empty "+
					"ConstName, which should be unreachable", leaf.Key))
		}
		return ctx.certificate(fmt.Sprintf("ctx.TypeDefAxiom(%q, %s)", leaf.ConstName,
			typeDefAxiomSelExpr(leaf.TypeDefWhich)))
	}
	panic(fmt.Sprintf("emit: unhandled external-leaf kind %d for %q", leaf.Kind, leaf.Key))
}

// typeDefAxiomSelExpr renders a TypeDefAxiomSel value as the Go
// expression naming the corresponding `prover` constant: a name of the
// bare-name surface, so importAuthoring sees the member spell it.
func typeDefAxiomSelExpr(sel TypeDefAxiomSel) string {
	switch sel {
	case TypeDefAbsRep:
		return "TypeDefAbsRep"
	case TypeDefPredRep:
		return "TypeDefPredRep"
	}
	panic(fmt.Sprintf("typeDefAxiomSelExpr: unhandled selector %d", sel))
}

// resolveLemmaRef looks up the section node ident a payload prop cites:
// a section the reading section may cite (citableSections) whose
// statement is the payload, raw or up to Normalize.
func (e *_Emitter) resolveLemmaRef(l core.Prop) (name string, ok bool) {
	name, _, ok = e.resolveLemmaRefDetailed(l)
	return
}

// resolveLemmaRefDetailed is resolveLemmaRef with a `viaNormalize`
// return: false when the section's statement α-equals `l`, true when
// the two are only normalize-equivalent. A slot that must deliver `l`'s
// exact α-form (a rewrite rule, a pinned simp rule) declines a
// normalize-bridged hit and spells the payload instead.
func (e *_Emitter) resolveLemmaRefDetailed(l core.Prop) (name string, viaNormalize, ok bool) {
	citable := e.citableSections()
	key := l.AlphaKey()
	for _, c := range citable {
		if c.outKey == key {
			return e.citeSection(c), false, true
		}
	}
	normalized, _ := proof.Normalize(l)
	key = normalized.AlphaKey()
	for _, c := range citable {
		if c.normKey == key {
			return e.citeSection(c), true, true
		}
	}
	return "", false, false
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

// sanitizeIdent maps a HOL TermName into a valid Go identifier. Go's
// identifier spec is `letter { letter | unicode_digit }` where
// `letter = unicode_letter | "_"`, and `unicode_letter` is any Unicode
// character in category L* (letters). So we KEEP any character Go
// classifies as a letter — Greek (`α`, `β`), precomposed accented
// letters (`ẋ` = U+1E8B "x with dot above", produced by prop.Normalize
// when renaming to avoid capture), modifier-letter primes (`ʹ` U+02B9,
// used in names like `kʹ`), superscript-letter modifiers (`ᴬ`, `ᴮ`),
// etc. — so the emitted Go stays visually close to the HOL surface.
// Only characters Go's spec rejects (symbols, punctuation, angle
// brackets, math operators, apostrophe, subscript / superscript
// digits) collapse to `_`, and a leading digit is prefixed by `_`.
//
// Symbolic operator names (`+`, `<=`, `,`, `==`, …) that would
// otherwise collapse to `_` go through symbolicIdent for a per-symbol
// readable name (`plus`, `le`, `pair`, `eqEq`, …) — without this, the
// same `_x` ident means different consts across files (e.g. `+` in
// `add_0.go` vs `<=` in `le_0.go`) and trains readers to the wrong
// mapping when scanning multiple proofs in sequence.
//
// Normalization to NFC (rather than NFD) keeps precomposed letters as
// a single codepoint: `ẋ` U+1E8B stays `ẋ`, not decomposed to
// `x` + combining-dot (which would then drop the mark and lose the
// diacritic). A HOL source encoded as NFD is composed here so both
// input encodings collapse to the same output ident.
//
// Collisions with an existing ident in the same file are handled by
// the freshIdent caller (appends `_2`/`_3` suffixes).
func sanitizeIdent(s string) string {
	if s == "" {
		return "_x"
	}
	if id, ok := symbolicIdent[s]; ok {
		return id
	}
	// NFC-compose: precomposed accented letters like `ẋ` U+1E8B survive
	// as a single codepoint so unicode.IsLetter recognizes them. Input
	// already in NFD (`x` + U+0307 combining-dot) round-trips to `ẋ`.
	composed := norm.NFC.String(s)
	var b strings.Builder
	for i, r := range composed {
		switch {
		case (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') ||
			(r >= '0' && r <= '9') || r == '_':
			// ASCII fast path.
			b.WriteRune(r)
		case unicode.IsLetter(r):
			// Any Unicode letter (L*): Greek, Cyrillic, modifier-
			// letters, precomposed diacritics, superscript-letter
			// modifiers, CJK, … — legal per Go spec (letter = L* | "_").
			b.WriteRune(r)
		case i > 0 && unicode.IsDigit(r):
			// Unicode Nd digits are legal AFTER the first identifier
			// character (Go spec's unicode_digit). `i` is the byte
			// index of the start of the rune; i > 0 iff not the first
			// rune, so this check is correct for multi-byte runes.
			b.WriteRune(r)
		case unicode.IsMark(r):
			// Combining marks (combining-dot, combining-tilde, …) —
			// drop. After NFC these only appear when the base+mark has
			// no precomposed form, in which case the base letter
			// preceded and we keep just it.
			continue
		default:
			// Symbols, punctuation, angle brackets, subscript/
			// superscript digits, apostrophe, math operators — Go
			// forbids these in identifiers. Collapse to `_`.
			b.WriteRune('_')
		}
	}
	out := cleanupSanitizedIdent(b.String())
	// `_` is Go's blank identifier and can't be referenced. HOL has
	// punctuation-heavy names — `,` (pair constructor), `=`, `@`, … —
	// that map to a string of underscores. Substitute a real ident.
	if out == "" || isAllUnderscores(out) {
		out = "_x"
	}
	if out[0] >= '0' && out[0] <= '9' {
		out = "_" + out
	}
	return out
}

// cleanupSanitizedIdent normalizes the per-rune sanitize output so runs
// of `_` from unsupported-char collapse don't turn into visual clutter:
//
// 1. Strip `_` adjacent to Unicode Lm (modifier letters). Modifier
// letters like `ʹ` (prime U+02B9), `ᴬ` (superscript letter) are
// designed to attach directly to the preceding base letter, so a
// separator `_` between them is noise. A HOL name like `y'ʹ` (ASCII
// apostrophe + modifier prime) sanitizes char-by-char to `y_ʹ` —
// the `_` from `'` sits between `y` and `ʹ`; drop it, giving `yʹ`
// which reads like the mathematical prime.
//
// 2. Collapse consecutive `_` runs to a single `_`. HOL names with
// multiple unsupported chars in a row (`y'ʹ'` → `y__ʹ__`, plus
// step 1) end up with `__+` runs; collapse so the ident stays
// compact. A pure-`_` input becomes `_` (single), which the caller
// then substitutes with `_x`.
//
// Collision handling (two conceptually different HOL names collapsing
// to the same ident post-cleanup) is the caller's job via freshIdent,
// which appends `_2`/`_3` suffixes on collision.
func cleanupSanitizedIdent(s string) string {
	// Step 1: strip `_` adjacent to Lm.
	runes := []rune(s)
	var stripped []rune
	for i, r := range runes {
		if r == '_' {
			var prev, next rune
			if i > 0 {
				prev = runes[i-1]
			}
			if i+1 < len(runes) {
				next = runes[i+1]
			}
			if (prev != 0 && unicode.Is(unicode.Lm, prev)) ||
				(next != 0 && unicode.Is(unicode.Lm, next)) {
				continue
			}
		}
		stripped = append(stripped, r)
	}
	// Step 2: collapse `_+` → `_`.
	result := string(stripped)
	for strings.Contains(result, "__") {
		result = strings.ReplaceAll(result, "__", "_")
	}
	return result
}

// symbolicIdent maps HOL operator / punctuation const names to a
// readable Go identifier. The keys are the const meta's stored Name()
// — exactly the strings the parser / printer round-trip. `=` and
// `ε` (Hilbert select) are filtered out earlier by isSpecialConst and
// never reach sanitizeIdent. Entries here cover every symbolic const
// observed in the corpus (`+`, `-`, `*`, `<=`, `==`, `<<`) plus the
// obvious extensions (`/`, `<`, `>`, `>=`, `,`). New entries land
// here when a new symbolic const would otherwise collapse to `_x`.
//
// Keep `<<` in sync with the parser's `multiCharIdents` lex table:
// without the lex-side entry the text form `<<(args)` tokenizes as
// two `<` operators and fails to parse.
var symbolicIdent = map[string]string{
	"+":  "plus",
	"-":  "minus",
	"*":  "times",
	"/":  "div",
	"<":  "lt",
	"<=": "le",
	"<<": "ll",
	">":  "gt",
	">=": "ge",
	"==": "eqEq",
	",":  "pair",
}

func isAllUnderscores(s string) bool {
	for _, r := range s {
		if r != '_' {
			return false
		}
	}
	return true
}

// freshIdent returns a name not in `taken`, starting from `base` and
// suffixing with _2, _3, … on collision.
func (e *_Emitter) freshIdent(base string, taken map[string]bool) string {
	if !taken[base] && !e.reservedIdent(base) {
		return base
	}
	for i := 2; ; i++ {
		cand := fmt.Sprintf("%s_%d", base, i)
		if !taken[cand] && !e.reservedIdent(cand) {
			return cand
		}
	}
}

// reservedIdent reports whether a name belongs to the member scaffold
// rather than to a declared symbol: a Go keyword or predeclared name, a
// name the closures bind (goReservedIdents), a parameter of the lifted
// signature (boundNames), or an earlier section's ctx.Lemma local, or
// an imported package.
func (e *_Emitter) reservedIdent(name string) bool {
	if goReservedIdents[name] || e.importIdents[name] || e.boundNames[name] {
		return true
	}
	for _, s := range e.sections {
		if s.varName == name {
			return true
		}
	}
	return false
}

// freshVarIdent is freshIdent for a VarTerm on the post-drain re-entry
// path (a walkTerm called after collectSymbols' assignVarIdents already
// ran). It layers a type-derived suffix (`ᐸAᐳ` for a bare type var,
// `ᐸboolᐳ` / `ᐸindᐳ` for a 0-arity CompositeType — the base types the
// reader can name at a glance) over freshIdent's numeric `_N` on
// collision. Composite types with subtypes have no short natural
// rendering, so they fall through to plain `_N`.
//
// Primary allocation goes through assignVarIdents (symmetric, sees
// every same-name-different-type variant up front); freshVarIdent
// handles the rare late-arrival case only.
func (e *_Emitter) freshVarIdent(base string, t core.HolType) string {
	taken := e.declSet()
	if !taken[base] && !e.reservedIdent(base) {
		return base
	}
	if suffix := typeSuffixForIdent(t); suffix != "" {
		return e.freshIdent(base+suffix, taken)
	}
	return e.freshIdent(base, taken)
}

// typeSuffixForIdent returns `ᐸ<name>ᐳ` when `t` is a bare type var or a
// 0-arity CompositeType (base type like `bool`, `ind`), else "". The
// bracketing Canadian Syllabics `ᐸ` (U+1438) / `ᐳ` (U+1433) are visually
// `⟨…⟩` but Unicode-categorized as `Lo` (Letter, other) — legal in Go
// identifiers, unlike math angle brackets which are Ps/Pe. This makes
// `p.yᐸAᐳ` read as `y⟨A⟩` (a variable `y` annotated with type A) and
// clearly distinct from `p.x_` (where `_` comes from sanitizing an
// ASCII apostrophe in the HOL name — a completely different mechanism).
//
// Used by the two-pass allocator (assignVarIdents) for informative
// same-name-different-type disambiguation; the caller falls back to
// numeric `_N` when this returns "" (composite types with subtypes
// like `A → bool` have no natural short rendering).
func typeSuffixForIdent(t core.HolType) string {
	switch t := t.(type) {
	case core.VarType:
		return "ᐸ" + sanitizeIdent(string(t.Name())) + "ᐳ"
	case core.CompositeType:
		if t.Meta().Arity() == 0 {
			return "ᐸ" + sanitizeIdent(string(t.Meta().Name())) + "ᐳ"
		}
	}
	return ""
}

var goReservedIdents = map[string]bool{
	"break": true, "case": true, "chan": true, "const": true, "continue": true,
	"default": true, "defer": true, "else": true, "fallthrough": true, "for": true,
	"func": true, "go": true, "goto": true, "if": true, "import": true,
	"interface": true, "map": true, "package": true, "range": true, "return": true,
	"select": true, "struct": true, "switch": true, "type": true, "var": true,
	"true": true, "false": true, "nil": true, "iota": true,
	// Identifiers the member scaffold binds: the Script, the section
	// closures' Argument receiver and family.Sections' headline
	// parameter. Symbol-derived names must not collide with them.
	"env": true, "ctx": true, "a": true, "headline": true,
}

// sortedValues returns the values of a map[K]string sorted, for stable
// declaration ordering.
func sortedValues[K comparable](m map[K]string) []string {
	out := make([]string, 0, len(m))
	for _, v := range m {
		out = append(out, v)
	}
	sort.Strings(out)
	return out
}

// decideSectionForms records each section's statement as parser text
// and marks what the rendered steps reference as Go expressions. A
// member statement is always spelled as text, in the chapter's surface
// form (surfaceText); one whose print does not read back has no text,
// and validateFamilyProfile refuses the member with the reason. So
// does a section whose goal carries hypotheses: a section states a
// closed theorem, and the session's goal is what it states. A
// definition section prints no headline — its door spells the defining
// equations — so its statement is only asked to round-trip, in the
// payload profile (tryTextForm). A lemma section — every section
// but the last — passes scope-override args for the multi-instance
// consts its text mentions (`ctx.Lemma(text, body, subset_2, …)`), and
// those args are Go expressions, so the consts are Go-used. The
// member's own statement parses under the family vocabulary with no
// override args: family.Theorem / family.Sections cannot take a
// closure local. A theorem's statement is the standard form
// (standardHeadline), which binds the telescope its lifted strips bind
// (planSectionLifts); a section whose proof opens with a strip the lift
// does not bind runs that strip against its statement as the session
// states it, and keeps the session's text.
//
// Must run after collectSymbols (so e.constMeta / e.varDecl /
// e.varIdent are populated, allowing buildParseScope and
// lookupVarIdent to function during the tryTextForm probe).
func (e *_Emitter) decideSectionForms() {
	e.planSectionLifts()
	for i, s := range e.sections {
		e.reader = s.reader
		goal := e.sectionInitGoal(s)
		if e.isDefinitionSection(s) {
			if text, ok := e.tryTextForm(goal, false); ok {
				e.sectionTextForm[i] = text
			}
		} else if goal.NumHyps() > 0 {
			e.sectionTextErr[i] = fmt.Errorf(
				"emit: section %q's goal carries hypotheses (%s), and a section states a closed theorem — "+
					"state the session's goal closed, its variables ∀-bound and its premises ⇒-antecedents: %s",
				s.varName, prop.PrintProp(goal), proof.ClosedSpelling(goal))
		} else if i == len(e.sections)-1 && e.readsAsStatement(e.opts.StatementText, goal) {
			// The authored text of the landed entry stating the member's
			// statement, kept as written.
			e.sectionTextForm[i] = e.opts.StatementText
		} else if text, err := e.surfaceText("headline", goal); err != nil {
			e.sectionTextErr[i] = err
		} else if e.sectionLifts[i].opensWithStrip() {
			e.sectionTextForm[i] = text
		} else if standard, err := e.standardHeadline(text, goal); err != nil {
			e.sectionTextErr[i] = err
		} else {
			e.sectionTextForm[i] = standard
		}
		if i < len(e.sections)-1 {
			e.markTextOverrides(e.sectionInitGoal(s))
		}
		e.readUnderLift(e.sectionLifts[i])
		e.markGoUsedFromSteps(s)
		e.readUnderLift(nil)
	}
}

// standardHeadline is text — the faithful print of goal, a section's
// statement — in the standard form a member is written in
// (dsl.StandardStatement): every binder in front, the premises one
// ∧-joined antecedent. A text in that form already is itself. The
// restated text spells the same names, and it reads at the member's
// door as a proposition of the goal's own key — the form the registry
// keys the member by — which is what is checked here and, for a member
// of several sections, at the replay scope (noteKeyedText). A
// restating the form refuses — a binder that would capture a name a
// hypothesis before it spells — is the author's to resolve in the
// session, and the error says so.
func (e *_Emitter) standardHeadline(text string, goal core.Prop) (string, error) {
	parts, err := dsl.StandardStatement(text)
	if err != nil {
		return "", fmt.Errorf("emit: section %q: the statement %q has no standard form — %v; "+
			"restate the session's goal with every binder in front and its premises one antecedent, ∀xs. H₁ ∧ … ∧ Hₙ ⇒ C",
			e.readingSectionName(), text, err)
	}
	standard, err := parts.Text()
	if err != nil {
		return "", fmt.Errorf("emit: section %q: the standard form of %q does not assemble: %v", e.readingSectionName(), text, err)
	}
	if standard == text {
		return text, nil
	}
	afterDecls := len(e.sections) > 1
	scope := e.textDoorScopeAt(goal, afterDecls)
	scope.AbbreviationBinders = leadingBinderSet(standard)
	res := dsl.ParsePropTextAtDoor(standard, scope)
	switch {
	case len(res.Errors) > 0:
		return "", fmt.Errorf("emit: section %q: the standard form %q of the statement %q does not parse — %s; "+
			"a defect of the restating, since the statement's own text reads: report both texts",
			e.readingSectionName(), standard, text, res.Errors[0].Message)
	case len(dsl.UnpinnedLetters(res.Prop)) > 0 || registry.KeyOf(res.Prop) != registry.KeyOf(goal):
		return "", fmt.Errorf("emit: section %q: the standard form %q of the statement %q reads as a proposition of another key, %s against %s; "+
			"a defect of the restating or the parser: report both texts",
			e.readingSectionName(), standard, text, registry.KeyOf(res.Prop), registry.KeyOf(goal))
	}
	if afterDecls {
		e.noteKeyedText(standard, goal)
	}
	return standard, nil
}

// markGoUsedFromTerm walks t and marks any ConstTerm / VarTerm
// whose Go ident is declared in the emit symbol tables as Go-side
// used. Idents not present in the tables (special consts handled
// inline, polymorphic-instantiation re-uses, etc.) are silently
// skipped — they have their own emit paths.
// constAt resolves a pooled const-node index in the current section to a
// core.ConstTerm (nil if the node isn't a const), replacing the legacy
// ext.DeserializeConstTerm(proto, loadConstMeta) call shape.
func (e *_Emitter) constAt(idx uint32) core.ConstTerm {
	c, _ := e.reader.Term(idx).AsConst()
	return c
}

// markGoUsedFromPropPayload marks the Go-side idents an inline prop
// payload (Lemma / LemmaPreserve / ResidentHyp statement) will
// reference. Every such render routes through miniStepPropExpr,
// which prefers the MakePropText form — there the parser re-introduces
// binders and the only Go expressions at the call site are the
// scope-override const args, so marking the payload's terms would bind
// locals nothing uses (a compile error in a closure). Only the Go-expr
// MakeProp fallback (payload does not round-trip as text) references
// the payload's consts and vars — conclusion AND hyps, both are
// printed.
//
// Conservative like leanRwRendersMakeProp: a payload that render-time
// resolution turns into a reference still gets its text-form
// scope-override marking here — that can only over-mark consts, never
// under-mark. tryTextForm is deterministic over state frozen after
// collectSymbols, so this pre-pass probe and miniStepPropExpr's
// render-time probe agree.
func (e *_Emitter) markGoUsedFromPropPayload(l core.Prop) {
	if l == nil {
		return
	}
	if _, ok := e.tryTextForm(l, true); ok {
		e.markTextOverrides(l)
		return
	}
	e.markGoUsedFromTerm(l.Conclusion())
	for i := range l.NumHyps() {
		e.markGoUsedFromTerm(l.Hyp(i))
	}
}

func (e *_Emitter) markGoUsedFromTerm(t core.Term) {
	switch tt := t.Core().(type) {
	case core.VarTerm:
		k := _VarKey{tt.Name(), tt.Type().Key()}
		if _, parameter := e.closureIdents[k]; parameter {
			// A split Skolem's parameter: no declaration is referenced.
			break
		}
		if id, ok := e.varIdent[k]; ok {
			e.goUsedVar[id] = true
		}
	case core.ConstTerm:
		if id, ok := e.constIdent[_ConstKey{tt.Name(), tt.Type().Key()}]; ok {
			e.goUsedConst[id] = true
		}
	case core.AppliedTerm:
		e.markGoUsedFromTerm(tt.Fun())
		e.markGoUsedFromTerm(tt.Arg())
	case core.AbsTerm:
		e.markGoUsedFromTerm(tt.Var())
		e.markGoUsedFromTerm(tt.Body())
	}
}

// markGoUsedFromSteps walks the action / ministep payload terms in s
// and marks their Go-side ident usage. Mirrors collectSymbols's
// step-walk: only the payloads that actually become Go expression
// referents matter (ByCase term, Induction var, AxiomDef const,
// ministep witness / instantiate / case-split / induction-var
// terms).
func (e *_Emitter) markGoUsedFromSteps(s *_SectionEmit) {
	for _, step := range s.detailedSteps {
		e.markGoUsedFromMiniStep(step)
	}
}

func (e *_Emitter) markGoUsedFromMiniStep(step *proof.StepProto) {
	if e.sectionCitedSteps[step] {
		return
	}
	switch s := step.Step.(type) {
	case *proof.StepProto_AxiomDef:
		if ct := e.constAt(s.AxiomDef.GetConst()); !ct.IsZero() {
			e.markGoUsedFromTerm(ct)
		}
	case *proof.StepProto_ExistentialConstDef:
		{
			ct := e.constAt(s.ExistentialConstDef)
			e.markGoUsedFromTerm(ct)
		}
	case *proof.StepProto_DefExpand:
		// `Unfold(<definition>)` references no declared term.
	case *proof.StepProto_Witness:
		{
			e.markGoUsedFromTerm(
				e.reader.Term(s.Witness))
		}
	case *proof.StepProto_Specialize:
		// A grounding's witnesses are marked where they are printed:
		// `Specialize(InstHyp(i, <w>, …), …)` prints Go expressions
		// (goTermExpr), and a cite fused with its grounding — of an
		// entry or of an earlier section — prints each through
		// witnessExpr, as a text that references no local where the
		// text reads back.
	case *proof.StepProto_Elementarity:
		// Renders as `ByElementarity(<source>, <facts>…).At(<params>…)`: a
		// resident statement is marked where residentHypExpr prints it;
		// each parameter is a Go expression.
		if t := s.Elementarity; t != nil {
			for _, ref := range t.GetParams() {
				e.markGoUsedFromTerm(e.reader.Term(ref))
			}
		}
	case *proof.StepProto_By:
		// Renders as `By(At(<target>, <w>, …), …)`. A named binder's
		// term is a Go-expression reference to a declared local. A derived
		// premise's install renders inline (`ResidentHyp(<stmt>)`), so
		// its idents get the text-form-aware
		// marking; a named premise rendered by reference prints nothing
		// of its install (byPremiseInstallPrinted). A resident premise's
		// statement, the hypothesis a reading is under and every
		// positional witness are marked where byPremiseExpr and
		// readingExpr print them; an explicit denote term is marked
		// where byShapeArgs prints it. A handle — a Have's, or the Law
		// door's — may stand for the statement, and a term may be written
		// as a text.
		if s.By != nil {
			for _, pr := range s.By.GetPremises() {
				// Same gate as the symbol walk: a named premise rendered
				// by reference prints no install to mark.
				if install, _ := e.reader.Prop(pr.GetInstall()); install != nil && !namesResidentHypothesis(pr) && e.byPremiseInstallPrinted(pr, install) {
					e.markGoUsedFromPropPayload(install)
				}
				for _, nw := range pr.GetNamed() {
					e.markGoUsedFromTerm(e.reader.Term(nw.GetTerm()))
				}
			}
		}
	case *proof.StepProto_Trans:
		{
			e.markGoUsedFromTerm(
				e.reader.Term(s.Trans))
		}
	case *proof.StepProto_Denote:
		if ref := s.Denote.GetTerm(); ref != 0 {
			e.markGoUsedFromTerm(e.reader.Term(ref))
		}
	case *proof.StepProto_ByCase:
		// The case term is marked where it is printed (caseTermExpr): as
		// a text the Argument parses, which references no local, or as
		// a Go expression over the member's declarations.
	case *proof.StepProto_Induction:
		{
			e.markGoUsedFromTerm(
				e.reader.Term(s.Induction))
		}
	case *proof.StepProto_Lemma:
		// Rendered inline via miniStepPropExpr (`Lemma(<payload>)`) —
		// text-form-aware payload marking, see markGoUsedFromPropPayload.
		if s.Lemma != nil {
			l, _ := e.reader.Prop(s.Lemma)
			e.markGoUsedFromPropPayload(l)
		}
	case *proof.StepProto_LemmaPreserve:
		// Same rationale as Lemma above (non-fused form renders
		// LemmaPreserve(<payload>) via miniStepPropExpr).
		if s.LemmaPreserve != nil {
			l, _ := e.reader.Prop(s.LemmaPreserve)
			e.markGoUsedFromPropPayload(l)
		}
	case *proof.StepProto_LeanRw:
		// When the rule resolves to a thm ref / external leaf, that
		// expression carries its own referents. But when leanRwLemmaExpr
		// falls back to miniStepPropExpr (rule proven inline by the
		// obligation subtree, no exact ref), the payload's Go-side
		// references must be marked — text-form-aware, mirrors Lemma.
		if s.LeanRw != nil {
			l, _ := e.reader.Prop(s.LeanRw)
			if e.leanRwRendersMakeProp(l) {
				e.markGoUsedFromPropPayload(l)
			}
		}
	case *proof.StepProto_TypeInst:
		// Same rationale as LeanRw: the viaNormalize arm renders the
		// recorded source prop inline (TypeInstSourceExact payload), so
		// its vars/consts are Go-side references.
		if s.TypeInst != nil {
			l, _ := e.reader.Prop(s.TypeInst)
			if e.typeInstRendersProp(l) {
				e.markGoUsedFromPropPayload(l)
			}
		}
	case *proof.StepProto_SimpWith:
		// A rule the Simp fusion cites (a dep name, a typed instance, a
		// reading's entries) references no payload ident, and the pinned
		// literal fallback and the hypothesis a reading is under are
		// marked where they are printed (emitMiniStep's SimpWith arm,
		// readingExpr): a pre-pass mark here would bind a local nothing
		// reads, and renderFamilyBody renders the steps before the
		// declarations.
	case *proof.StepProto_CongrArg:
		// Rendered as `CongrArg(<function term>, i)` — the term's vars
		// (including its λ-binder) and consts are Go-side references.
		// Mirrors walkMiniStep's CongrArg arm; omitting this pruned a
		// var used ONLY here as "Go-unused" (p.x undefined at compile).
		if s.CongrArg != nil {
			e.markGoUsedFromTerm(e.reader.Term(s.CongrArg.GetFunction()))
		}
	case *proof.StepProto_CongrFun:
		// Rendered as `CongrFun(<argument term>, i)` — same as CongrArg.
		if s.CongrFun != nil {
			e.markGoUsedFromTerm(e.reader.Term(s.CongrFun.GetArgument()))
		}
	case *proof.StepProto_Assert:
		// Assert's claim renders as its text (claimExpr): the parser
		// re-introduces the binders, and the only Go expressions at the
		// call site are the scope-override const args. An assert rendered
		// whole as a cite of an earlier section prints no claim, nor does
		// one an a.Unfolded or an a.Conjuncts made (factVerbAssert).
		if s.Assert != nil && !e.sectionCites[step].installs && !e.byInductionAsserts[step] && !e.factVerbAssert(step) {
			if claim, _ := e.reader.Prop(s.Assert); claim != nil {
				e.markTextOverrides(claim)
			}
		}
	}
}

// textFreeVars reports the free variables of p (name → type). A text
// of p states only mathematical content and its free variables' types
// are declared in Go: through `ctx.Var` for a name the member holds at
// one type, through a scope override for a name it holds at several
// (varOverrideEntries).
//
// The chapter charter bans ⊢ in blessed text — a decl piece left of it
// re-spells types the member already declares, and breaks the `a.Have`
// bare-statement form the math layer is written in — and the ban is
// lint-enforced (the gate suite’s TestLintNoTurnstileInStatementText),
// so no text carries a declaration prelude.
func (e *_Emitter) textFreeVars(p core.Prop) map[string]core.HolType {
	frees := map[string]core.HolType{}
	for _, v := range propFrees(p) {
		frees[string(v.Name())] = v.Type()
	}
	return frees
}

// propFrees is the free variables of p's conclusion and hypotheses.
func propFrees(p core.Prop) []core.VarTerm {
	all := func(core.VarTerm) bool { return true }
	frees := p.Conclusion().Frees(all)
	for i := range p.NumHyps() {
		frees = append(frees, p.Hyp(i).Frees(all)...)
	}
	return frees
}

// varOverrideEntry pairs the Go ident a text-form call passes as a
// scope override with the variable that ident is bound to.
type varOverrideEntry struct {
	ident string
	v     core.VarTerm
}

// varOverrideEntries is one entry per free variable of p whose NAME the
// member holds at more than one type (kernel-distinct variables of one
// name, minted in disjoint branches): `Script.Var` refuses a second
// type for a name, so no registration can serve the text, and the text
// passes the variable it means instead, as it passes a constant's
// instance (sectionScopeOverrideEntries). Sorted by ident, for
// deterministic output; a variable with no Go ident is no entry, and a
// text spelling it does not read back.
func (e *_Emitter) varOverrideEntries(p core.Prop) []varOverrideEntry {
	seen := map[_VarKey]bool{}
	var entries []varOverrideEntry
	for _, v := range propFrees(p) {
		if e.registerableVarNames[string(v.Name())] {
			continue
		}
		k := _VarKey{v.Name(), v.Type().Key()}
		id, ok := e.identOfVar(k)
		if !ok || seen[k] {
			continue
		}
		seen[k] = true
		entries = append(entries, varOverrideEntry{ident: id, v: v})
	}
	sort.Slice(entries, func(i, j int) bool { return entries[i].ident < entries[j].ident })
	return entries
}

// textOverrides is every Go value a text of p passes as a scope
// override: the constant instances sectionConstOverrides names, then
// the variables varOverrideEntries names.
func (e *_Emitter) textOverrides(p core.Prop) []string {
	overrides := e.sectionConstOverrides(p)
	for _, en := range e.varOverrideEntries(p) {
		// The identifier may be a typed closure parameter. Both parameter
		// forms expose the core term that the text parser accepts.
		overrides = append(overrides, en.ident+".Core()")
	}
	return overrides
}

// markTextOverrides marks the Go values a text of p passes as scope
// overrides as referenced, so renderDecls binds them.
func (e *_Emitter) markTextOverrides(p core.Prop) {
	for _, ident := range e.sectionScopeOverrideIdents(p) {
		e.goUsedConst[ident] = true
	}
	for _, en := range e.varOverrideEntries(p) {
		e.goUsedVar[en.ident] = true
	}
}

// noteTextScopeVars records the registered names a text of p reads, so
// the member declares exactly the scope entries a rendered text
// consults (textScopeVars, scopeOnlyVarDeclared).
func (e *_Emitter) noteTextScopeVars(p core.Prop) {
	for name := range e.textFreeVars(p) {
		if !e.registerableVarNames[name] {
			continue
		}
		if e.textScopeVars == nil {
			e.textScopeVars = map[string]bool{}
		}
		e.textScopeVars[name] = true
	}
}

// computeRegisterableVarNames fills e.registerableVarNames: the free-var
// NAMES emit may declare through `ctx.Var`, being those it collected at
// exactly one type. Multi-type names are excluded — a text passes the
// variable it means instead (varOverrideEntries). Runs after
// assignVarIdents, whose varDecl map is
// the collected (ident → var) table.
func (e *_Emitter) computeRegisterableVarNames() {
	types := map[string]core.HolType{}
	ambiguous := map[string]bool{}
	for _, v := range e.varDecl {
		name := string(v.Name())
		if prev, seen := types[name]; seen {
			if !prev.Equals(v.Type()) {
				ambiguous[name] = true
			}
			continue
		}
		types[name] = v.Type()
	}
	e.registerableVarNames = map[string]bool{}
	for name := range types {
		if !ambiguous[name] {
			e.registerableVarNames[name] = true
		}
	}
}

// textDoorScope is the scope a rendered text of p is read back in — the
// emitter's model of the door the emitted call parses the text at —
// and whether the text must carry its free variables' declarations.
//
// The model mirrors EXECUTION: the emitted call site is
// `<X>Text(text, <overrides>...)`, and proof.Script's
// parseScopeWithOverrides overlays those overrides onto its scope BY
// NAME, in argument order — so for a const name occurring in p at
// several distinct type instances, the LAST override wins and every
// un-annotated occurrence of that name in the text resolves to it.
// buildParseScope alone is more permissive (first occurrence wins,
// per-occurrence self-consistency), so a text that parses there could
// still be ill-typed at replay (cardinality.CardImageLe's intra-prop
// empty_set⟨A⟩/empty_set⟨B⟩ payload); the runtime overlay is replicated
// here.
//
// A text declares its free-variable types in Go, so the string states
// only mathematical content: the scope's Vars are seeded with the
// text's own free variables that renderDecls registers (a name the
// member holds at one type) and what the call's variable overrides
// overlay (varOverrideEntries). A text parsed after the member's
// declarations is parsed beside all of them at replay, and beside the
// Skolems the boundary of the closure it is read in declares
// (closureSkolems); which declarations those are is known once the
// bodies render, so textDoorScopeAt adds the ones a previous rendering
// registered, and verifyTextsAtReplayScope reads every such text again
// beside this rendering's.
func (e *_Emitter) textDoorScope(p core.Prop) *dsl.ParseScope {
	return e.textDoorScopeAt(p, false)
}

// textDoorScopeAt is textDoorScope for a text parsed after the member's
// declarations, where afterDecls is set: the Skolems the closure's
// boundary declares (closureSkolems) and the variables the previous
// rendering registered (declaredSeed) are in scope beside the text's
// own, as the replay's script scope holds them.
func (e *_Emitter) textDoorScopeAt(p core.Prop, afterDecls bool) *dsl.ParseScope {
	scope := e.buildParseScope(p)
	for _, en := range e.sectionScopeOverrideEntries(p) {
		scope.Consts[string(en.ct.Name())] = en.ct
	}
	if scope.Vars == nil {
		scope.Vars = map[string]core.HolType{}
	}
	for name, ty := range e.textFreeVars(p) {
		if e.registerableVarNames[name] {
			scope.Vars[name] = ty
		}
	}
	for _, en := range e.varOverrideEntries(p) {
		scope.Vars[string(en.v.Name())] = en.v.Type()
	}
	if afterDecls {
		addUnset(scope.Vars, e.closureSkolems())
		addUnset(scope.Vars, e.declaredSeed)
		// The Script's door exempts the member's own binders from the
		// abbreviation capture check (Script.UseAbbreviations): a text
		// rebinding one — an induction hypothesis `∀n. finite(«S»)`
		// over an entry S spelling n — reads there.
		scope.AbbreviationBinders = e.memberStatementBinders()
	}
	return scope
}

// memberStatementBinders names the leading binders of the member's
// statement — its last section's — which the member's constructor
// installs its abbreviation table over (registry.BuildSpec.
// installAbbreviations), so a text parsed at the Script's door may
// rebind them.
func (e *_Emitter) memberStatementBinders() map[string]bool {
	n := len(e.sections)
	if n == 0 {
		return nil
	}
	reading := e.reader
	e.reader = e.sections[n-1].reader
	defer func() { e.reader = reading }()
	return dsl.StatementBinderNames(e.sectionInitGoal(e.sections[n-1]))
}

// closureSkolems is the Skolems the boundary of the closure rendering
// now declares in the script's parse scope, each at its own type: the
// closure's Argument declares each as it binds the parameter that fixes
// it (proof.Argument.fixImpl) — a term parameter's, a bundle's
// components, a Law door's. The binder's name the Skolem is aliased by
// is no declaration of the script: only the closure's claim door reads
// it (proof.Argument.claimScope), so a text the Script parses
// (Script.MakePropText) reads beside the Skolem alone.
func (e *_Emitter) closureSkolems() map[string]core.HolType {
	if len(e.surfaceSkolems) == 0 {
		return nil
	}
	vars := make(map[string]core.HolType, len(e.surfaceSkolems))
	for _, sk := range e.surfaceSkolems {
		vars[string(sk.skolem.Name())] = sk.skolem.Type()
	}
	return vars
}

// addUnset adds to vars each of more's names vars does not hold.
func addUnset(vars, more map[string]core.HolType) {
	for name, ty := range more {
		if _, set := vars[name]; !set {
			vars[name] = ty
		}
	}
}

// _CheckedText is a text emit chose for a proposition the replay parses
// after the member's declarations: the text, the proposition, the
// resident facts its door reads it under, the Skolems the boundary of
// the closure it is read in declares (closureSkolems), and whether it
// must come back with its names (a payload, tryTextForm) or up to bound
// names.
type _CheckedText struct {
	text     string
	p        core.Prop
	resident []core.Term
	skolems  map[string]core.HolType
	exact    bool
	// key marks a text that reads back as a proposition of p's key
	// rather than as p itself: a statement restated in the standard
	// form (standardHeadline).
	key bool
	// headline marks a section's statement text, read at a door that
	// binds the statement's own binders.
	headline bool
}

// noteCheckedText records a text chosen for a proposition parsed after
// the member's declarations, for verifyTextsAtReplayScope.
func (e *_Emitter) noteCheckedText(text string, p core.Prop, resident []core.Term, exact bool) {
	e.checkedTexts = append(e.checkedTexts, _CheckedText{text: text, p: p, resident: resident, skolems: e.closureSkolems(), exact: exact})
}

// noteKeyedText records a statement text parsed after the member's
// declarations that reads back as a proposition of p's key, for
// verifyTextsAtReplayScope. A section's statement is parsed before its
// closure binds anything, so no Skolem is beside it.
func (e *_Emitter) noteKeyedText(text string, p core.Prop) {
	e.checkedTexts = append(e.checkedTexts, _CheckedText{text: text, p: p, key: true, headline: true})
}

// noteHeadlineText records a section's statement text parsed after the
// member's declarations, for verifyTextsAtReplayScope.
func (e *_Emitter) noteHeadlineText(text string, p core.Prop) {
	e.checkedTexts = append(e.checkedTexts, _CheckedText{text: text, p: p, headline: true})
}

// replayScopeVars is the variables the member's declarations register
// in the replay's script scope (registersVar), each at its type: what
// every text the bodies parse is read beside, with the Skolems the
// boundary of its closure declares (closureSkolems). The declarations
// are read in identifier order, so a name two of them register — which
// the replay refuses (Script.Var) — is read the same way every time.
func (e *_Emitter) replayScopeVars() map[string]core.HolType {
	vars := map[string]core.HolType{}
	for _, id := range slices.Sorted(maps.Keys(e.varDecl)) {
		if e.registersVar(id) {
			vars[string(e.varDecl[id].Name())] = e.varDecl[id].Type()
		}
	}
	return vars
}

// verifyTextsAtReplayScope re-reads every text chosen for a proposition
// parsed after the member's declarations (checkedTexts) in the scope
// the replay gives it — its own variables, the Skolems its closure's
// boundary declares, the variables the rendering registers
// (replayScopeVars), the resident facts of its door — and returns those
// variables, with an error naming the first text that does not read
// back as its proposition there.
func (e *_Emitter) verifyTextsAtReplayScope() (map[string]core.HolType, error) {
	declared := e.replayScopeVars()
	for _, c := range e.checkedTexts {
		scope := e.textDoorScope(c.p)
		// A section's door exempts its own leading binders from the
		// abbreviation capture check (Script.withSectionAbbreviations);
		// the Script's door, every other text's, the member's.
		scope.AbbreviationBinders = e.memberStatementBinders()
		if c.headline {
			scope.AbbreviationBinders = dsl.StatementBinderNames(c.p)
		}
		addUnset(scope.Vars, c.skolems)
		addUnset(scope.Vars, declared)
		if len(c.resident) > 0 {
			scope.ResidentFacts = c.resident
		}
		res := dsl.ParsePropTextAtDoor(c.text, scope)
		readsBack := len(res.Errors) == 0 && res.Prop != nil
		switch {
		case readsBack && c.exact:
			readsBack = res.Prop.AlphaKey() == c.p.AlphaKey() && propEqualsSyntactic(res.Prop, c.p)
		case readsBack && c.key:
			readsBack = len(dsl.UnpinnedLetters(res.Prop)) == 0 && registry.KeyOf(res.Prop) == registry.KeyOf(c.p)
		case readsBack:
			readsBack = len(dsl.UnpinnedLetters(res.Prop)) == 0 && res.Prop.AlphaEquals(c.p)
		}
		if !readsBack {
			read := "it reads as another statement"
			if len(res.Errors) > 0 {
				read = "the parser refuses it: " + res.Errors[0].Message
			}
			beside := maps.Clone(declared)
			addUnset(beside, c.skolems)
			return declared, fmt.Errorf("emit: the text %q does not read back at replay beside the member's declarations and its closure's Skolems (%s) — %s",
				c.text, strings.Join(slices.Sorted(maps.Keys(beside)), ", "), read)
		}
	}
	return declared, nil
}

// surfaceText prints p — a section's statement or an asserted claim —
// in the chapter's surface form: the sugared parser profile
// (prop.FormatPropForParser), in which a set-builder reads
// `{f(b, p) | b:A, p:… | P}` and a paired lambda `λ(x, y). t`, folded
// into the chapter's spelling where the fold reads back, a set binder
// spelled `set(τ)`, redundant instance ties and numeric embeddings dropped
// (dsl.SurfaceForm), each where the result reads back.
// If an abbreviation expands differently from the printed proposition,
// the unfolded surface spelling remains a candidate.
//
// The print is checked: it is read back in the scope the emitted call
// parses it in (textDoorScope) and must be the statement it prints —
// the proposition itself, up to bound names (α-equality), for a
// headline and a claim alike. Bound names are outside the comparison,
// which is what lets the sugar leave the name of the binder its
// encoding hides to the parser. A print that does not read back is an
// error naming the section, the text and what it read as: emitting the
// name-faithful machine form in its place would hide that the printer
// and the parser disagree on the statement. A text that reads back as
// another proposition of the SAME normalized key is that disagreement
// at its plainest — a printer or parser defect, since a faithful
// round trip gives the proposition back — and the error says so.
//
// role says what the text is in the member ("headline", "claim");
// resident are the facts a claim's door reads it under — the goal's
// hypotheses at a Have, which bind the bundles their structure facts
// state (ext/dsl/structure.go), so a text that spells a second bundle's
// operator is refused there as the door refuses it.
func (e *_Emitter) surfaceText(role string, p core.Prop, resident ...core.Term) (string, error) {
	// A claim `ctx.MakePropText` parses is parsed in the body, after the
	// declarations; a headline after them where the member renders as
	// family.Sections.
	afterDecls := role == "claim" || len(e.sections) > 1
	return e.surfaceTextIn(role, p, e.textDoorScopeAt(p, afterDecls), afterDecls, resident)
}

// surfaceClaimAtDoor is surfaceText for a claim the block's claim door
// parses — `a.Have(label, text, …)` asserted at goal — which reads it
// with the goal's own variables and surface names in scope and the
// goal's hypotheses resident (Argument.claimScope): the check's scope
// is that one, known here, so the text is not re-read beside the
// member's declarations.
func (e *_Emitter) surfaceClaimAtDoor(named, goal core.Prop) (string, error) {
	scope := e.textDoorScope(named)
	for _, g := range []core.Prop{goal, e.surfaceNamed(goal)} {
		for _, v := range propFrees(g) {
			if _, set := scope.Vars[string(v.Name())]; !set {
				scope.Vars[string(v.Name())] = v.Type()
			}
		}
	}
	return e.surfaceTextIn("claim", named, scope, false, goal.Hyps())
}

// surfaceTextIn is surfaceText at scope, the text recorded for
// verifyTextsAtReplayScope where record is set.
func (e *_Emitter) surfaceTextIn(role string, p core.Prop, scope *dsl.ParseScope, record bool, resident []core.Term) (string, error) {
	if len(resident) > 0 {
		scope.ResidentFacts = resident
	}
	chosen := func(text string) (string, error) {
		switch {
		case record && role == "headline":
			e.noteHeadlineText(text, p)
		case record:
			e.noteCheckedText(text, p, resident, false)
		}
		return e.noteAbbreviations(text), nil
	}
	if role == "headline" {
		// A headline binds the statement's own binders, which its
		// abbreviations are written over; a claim binds none of them.
		scope.AbbreviationBinders = dsl.StatementBinderNames(p)
	}
	plain := prop.FormatPropForParserNoDecls(e.foldProp(p, scope))
	// reads is what the text reads as, or why it does not read: a text
	// whose parse leaves a constant's letter unpinned reads as no
	// statement — the claim door refuses it (dsl.UnpinnedLetters), so a
	// tie the parse needs is kept.
	reads := func(text string) (core.Prop, string) {
		res := dsl.ParsePropTextAtDoor(text, scope)
		if len(res.Errors) > 0 {
			return nil, res.Errors[0].Message
		}
		if unpinned := dsl.UnpinnedLetters(res.Prop); len(unpinned) > 0 {
			return nil, "it leaves a type letter unpinned: " + unpinned[0].Repair()
		}
		return res.Prop, ""
	}
	readsBack := func(text string) bool {
		q, _ := reads(text)
		return q != nil && q.AlphaEquals(p)
	}
	trySpelling := func(text string) (string, bool) {
		short, err := dsl.ChapterSpelling(text, scope.Syntax, scope.ImplicitBindings)
		if err == nil && short != text && readsBack(short) {
			return dsl.SurfaceForm(short, readsBack), true
		}
		if readsBack(text) {
			return dsl.SurfaceForm(text, readsBack), true
		}
		return "", false
	}
	if text, ok := trySpelling(plain); ok {
		return chosen(text)
	}
	unfolded := prop.FormatPropForParserNoDecls(p)
	if unfolded != plain {
		if text, ok := trySpelling(unfolded); ok {
			return chosen(text)
		}
	}

	q, refusal := reads(plain)
	want := registry.KeyOf(p)
	var read string
	switch {
	case refusal != "":
		read = "the parser refuses it: " + refusal
	case registry.KeyOf(q) == want:
		read = "it reads as " + prop.PrintProp(q) + ", another proposition of the same normalized key — " +
			"a faithful round trip gives the proposition back, so this is a defect of the printer or the parser"
	default:
		read = fmt.Sprintf("it reads as the statement of key %s", registry.KeyOf(q))
	}
	restate := "the section's goal"
	switch role {
	case "claim":
		restate = "the asserted claim"
	case "hypothesis":
		restate = "the step that leaves the hypothesis resident"
	}
	return "", fmt.Errorf(
		"emit: section %q: the %s text %q does not read back as the statement it prints — %s; "+
			"the statement's key is %s. Report the text; until the printer and the parser agree, restate %s "+
			"in the session so that its print reads back",
		e.readingSectionName(), role, plain, read, want, restate)
}

// readsAsStatement reports whether text reads, at the door a rendered
// text of p parses at, as p itself — up to bound names, with no letter
// left unpinned. "" reads as nothing.
func (e *_Emitter) readsAsStatement(text string, p core.Prop) bool {
	if text == "" {
		return false
	}
	afterDecls := len(e.sections) > 1
	scope := e.textDoorScopeAt(p, afterDecls)
	scope.AbbreviationBinders = dsl.StatementBinderNames(p)
	res := dsl.ParsePropTextAtDoor(text, scope)
	reads := len(res.Errors) == 0 && len(dsl.UnpinnedLetters(res.Prop)) == 0 && res.Prop.AlphaEquals(p)
	if reads && afterDecls {
		e.noteHeadlineText(text, p)
	}
	return reads
}

// readingSectionName names the section whose steps the emitter is
// reading (the section e.reader belongs to), for an error.
func (e *_Emitter) readingSectionName() string {
	if s := e.readingSection(); s != nil {
		return s.varName
	}
	return ""
}

// tryTextForm tries to render p as a string the replay parses back to
// p itself. Returns (text, true) when the print → parse round-trip
// closes SYNTACTICALLY (names included) against the scope built from
// emit's known consts and vars; ("", false) otherwise, and the caller
// falls back to the Go-expression form.
//
// Failure modes: unknown free vars (the parser can't type them),
// non-scope const names read as variables, polymorphic consts at types
// other than the scope's chosen instantiation, prop shapes the parser
// doesn't handle.
//
// The print profile is the name-faithful one
// (prop.FormatPropForParserNameFaithful): it disables the set-builder
// shorthands, whose set_comprehension λ-binder name is re-synthesized position-
// derived at parse. Payload binder names are load-bearing: recorded
// steps re-derive fresh variable names via RenameToAvoid over ALL names
// in the goal — bound included — so an α-only round-trip lets a
// bound-binder rename leak into a FREE variable name downstream and
// diverge the goal α-keys from the recording (the funext ẋ → ẋʹ
// class of cardinality.HasSizeUnions).
func (e *_Emitter) tryTextForm(p core.Prop, afterDecls bool) (string, bool) {
	scope := e.textDoorScopeAt(p, afterDecls)
	text := prop.FormatPropForParserNameFaithfulNoDecls(p)
	res := dsl.ParsePropTextAtDoor(text, scope)
	if len(res.Errors) > 0 {
		if os.Getenv("EMIT_TEXT_DEBUG") != "" {
			fmt.Fprintf(os.Stderr, "[text-form fallback: parse err] %s\n  text: %s\n  err: %s\n  prop: %s\n",
				e.opts.FuncName, text, res.Errors[0].Message, prop.PrintProp(p))
		}
		return "", false
	}
	if res.Prop.AlphaKey() != p.AlphaKey() {
		if os.Getenv("EMIT_TEXT_DEBUG") != "" {
			fmt.Fprintf(os.Stderr, "[text-form fallback: alpha mismatch] %s\n  text:     %s\n  parsed:   %s\n  expected: %s\n",
				e.opts.FuncName, text,
				prop.PrintProp(res.Prop), prop.PrintProp(p))
		}
		return "", false
	}
	// The round-trip must be SYNTACTIC (names included), not just up to
	// α. Any residual name drift falls back to the Go-expr form (which
	// reproduces the recorded terms verbatim) rather than shipping a
	// payload that replays into α-divergent downstream goals.
	if !propEqualsSyntactic(res.Prop, p) {
		if os.Getenv("EMIT_TEXT_DEBUG") != "" {
			fmt.Fprintf(os.Stderr, "[text-form fallback: name drift] %s\n  text:     %s\n  parsed:   %s\n  expected: %s\n",
				e.opts.FuncName, text,
				prop.PrintProp(res.Prop), prop.PrintProp(p))
		}
		return "", false
	}
	// The chapter's spelling: implicit structure arguments the scope
	// reads back are dropped, and the short text is checked to parse to
	// the same prop under the same scope before it replaces the long one.
	if short, err := dsl.ChapterSpelling(text, scope.Syntax, scope.ImplicitBindings); err == nil && short != text {
		back := dsl.ParsePropTextAtDoor(short, scope)
		if len(back.Errors) == 0 && back.Prop.AlphaKey() == p.AlphaKey() &&
			propEqualsSyntactic(back.Prop, p) {
			text = short
		}
	}
	var defined core.ConstTerm
	if !afterDecls && e.readingSection() != nil {
		defined, _ = e.familyDefineConst(e.readingSection())
	}
	text = dsl.SurfaceForm(text, func(candidate string) bool {
		back := dsl.ParsePropTextAtDoor(candidate, scope)
		if len(back.Errors) > 0 || !propEqualsSyntactic(back.Prop, p) {
			return false
		}
		// A defining equation must still name its definiendum on the
		// left; an implicit embedding there can read identically after
		// the mint and yet be no definition before it.
		return defined.IsZero() || definitionEquationsReparse([]string{candidate}, defined, ext.FormatType(defined.Type()))
	})
	if afterDecls {
		e.noteCheckedText(text, p, nil, true)
	}
	return text, true
}

// propEqualsSyntactic reports whether two props are syntactically equal
// — conclusion and hypotheses pairwise Equals (names included), not
// merely α-equal. Both sides carry kernel-sorted hyp lists, and for
// name-identical props the sort order coincides, so pairwise-in-order
// comparison suffices; a tie-order divergence between α-equal-but-
// renamed hyps just fails the check (→ Go-expr fallback), never
// accepts a drifted payload.
func propEqualsSyntactic(a, b core.Prop) bool {
	if !a.Conclusion().Equals(b.Conclusion()) || a.NumHyps() != b.NumHyps() {
		return false
	}
	for i := range a.NumHyps() {
		if !a.Hyp(i).Equals(b.Hyp(i)) {
			return false
		}
	}
	return true
}

// miniStepPropExpr renders a ministep payload prop (the Prop arg of
// Lemma / LemmaPreserve / LeanRw, a ResidentHyp statement — an
// asserted claim is claimExpr's)
// as either the parser-text form `ctx.MakePropText("...", overrides...)`
// — when the print → parse → alpha-key round-trip closes — or the
// Go-expr fallback `MakeProp(<go term expr>)`, the same text-vs-Go
// choice decideSectionForms makes for section statements.
//
// The existing MakeProp(...) call sites drop hypotheses (only
// PrintTerm(concl) is emitted; no hyp args), so this helper does the
// same: it probes the round-trip against a hyp-free Prop, and the
// Go-expr fallback keeps rendering just the concl. Ministep payloads
// are hyp-free in practice (the Lemma/LemmaPreserve/Assert
// protos record a bare claim conclusion), so the drop is a no-op on
// real corpora; it stays explicit here so text form is α-equivalent
// to the Go-expr form even if a hyp-bearing prop shows up.
func (e *_Emitter) miniStepPropExpr(p core.Prop) string {
	if text, ok := e.tryTextForm(p, true); ok {
		return e.propTextExpr(p, text)
	}
	parts := make([]string, 0, p.NumHyps()+1)
	parts = append(parts, e.printer.PrintTerm(p.Conclusion()))
	for i := range p.NumHyps() {
		parts = append(parts, e.printer.PrintTerm(p.Hyp(i)))
	}
	return fmt.Sprintf("MakeProp(%s)", strings.Join(parts, ", "))
}

// residentHypExpr spells a resident hypothesis no Go value names — a
// premise of a by, a rule of a simp, the fact a verb reads, the
// hypothesis a reading is under — as the fact located by content at
// the leaf, `ResidentHyp(ctx.MakePropText("…"))`. The text is the
// chapter's surface form at the Script's door (surfaceTextIn): the
// sugared print with the member's abbreviations folded and the ties
// the parse needs, spelling the minted names that door reads, where it
// reads back as the hypothesis up to bound names — the match the leaf
// locates it by. Where no surface text reads back, the text is the
// name-faithful one a payload takes (tryTextForm); a hypothesis with
// neither fails the emit naming it (failText): the Go-expression form
// would declare every constant and variable it holds by hand. The
// values the text passes as scope overrides are marked referenced
// here, as a printed payload's are.
func (e *_Emitter) residentHypExpr(hyp core.Prop) string {
	stated := core.MakeProp(hyp.Conclusion())
	text, err := e.surfaceTextIn("hypothesis", stated, e.textDoorScopeAt(stated, true), true, nil)
	if err != nil {
		if os.Getenv("EMIT_TEXT_DEBUG") != "" {
			fmt.Fprintf(os.Stderr, "[hypothesis text fallback] %s\n  %v\n", e.opts.FuncName, err)
		}
		var ok bool
		if text, ok = e.tryTextForm(stated, true); !ok {
			e.failText(fmt.Errorf("emit: section %q: the resident hypothesis %s has no text that reads back at the member's door; %v",
				e.readingSectionName(), prop.PrintProp(stated), err))
			return "ResidentHyp(nil)"
		}
	}
	e.markTextOverrides(stated)
	return fmt.Sprintf("ResidentHyp(%s)", e.propTextExpr(stated, text))
}

// propTextExpr renders a text of p as the call that parses it back,
// `ctx.MakePropText("…", overrides...)`. The text reads its free
// variables' types off the ParseScope — a registered name's entry, or
// the variable the call passes (textOverrides) — and the registered
// names are recorded, so the member declares exactly the scope entries
// a rendered text consults (textScopeVars).
func (e *_Emitter) propTextExpr(p core.Prop, text string) string {
	e.noteTextScopeVars(p)
	scopeArgs := joinSectionScopeArgs(e.textOverrides(p))
	return fmt.Sprintf("ctx.MakePropText(%q%s)", text, scopeArgs)
}

// claimExpr renders an asserted claim — the statement of a Have, of an
// AssertStep — as the call that parses its text. A claim is stated in
// the chapter's surface form (surfaceText), as a section's headline
// is; a text that does not read back fails the emit (failText), and
// the member is not returned.
func (e *_Emitter) claimExpr(claim core.Prop) string {
	text, err := e.surfaceText("claim", claim)
	if err != nil {
		e.failText(err)
	}
	return e.propTextExpr(claim, text)
}

// claimArg renders the claim of a Have or an Obtain, asserted at goal:
// the statement the verb parses at the block's claim door, where every
// binder the closure bound is spelled under its own name
// (surfaceNamed), as the chapter writes it — the door aliases the
// names and reads under the goal's resident facts. A claim with a
// premise is written in parts (claimParts) where its one string would
// not fit: the verb's arguments stand one to a line under it, so the
// claim's line is indent, a tab, the quoted text and a comma, and past
// xugofmt.LineWidth columns from its indentation the parts are written. A claim that fits,
// or has no premise, is the one string. Where the text needs the scope
// overrides only a `ctx.MakePropText` call takes, the claim is that
// call (claimExpr). A text the claim door does not read back fails the
// emit (failText), as a claimExpr text does. indent is the indentation
// of the line the verb opens on, which a Statement literal's lines
// after the first take.
func (e *_Emitter) claimArg(claim, goal core.Prop, indent string) string {
	if len(e.textOverrides(claim)) > 0 {
		return e.claimExpr(claim)
	}
	named := e.surfaceNamed(claim)
	text, err := e.surfaceClaimAtDoor(named, goal)
	if err != nil {
		e.failText(err)
	}
	e.noteTextScopeVars(named)
	quoted := fmt.Sprintf("%q", text)
	if xugofmt.ContentWidth(indent+"\t"+quoted+",") <= xugofmt.LineWidth {
		return quoted
	}
	if parts := e.claimParts(text); parts != nil {
		return statementLiteral(parts, indent)
	}
	return quoted
}

// claimParts is a claim text in parts where it has a premise, `∀xs.
// H₁ ∧ … ∧ Hₙ ⇒ C`, and its parts and the one string are one statement
// (dsl.CanonicalParts); nil where the one string is the only rendering
// — a curried claim, whose consequent implies again, splits no
// hypothesis. The parts carry no abbreviations, since a claim reads the
// member's table.
func (e *_Emitter) claimParts(text string) *dsl.Statement {
	split, ok := dsl.CanonicalParts(text)
	if !ok || len(split.Hypotheses) == 0 {
		return nil
	}
	return &split
}

// failText records the first error the rendering meets — a claim text
// that did not read back, a declaration with no place to go; EmitMember
// returns it in place of the member.
func (e *_Emitter) failText(err error) {
	if e.textErr == nil {
		e.textErr = err
	}
}

// witnessExpr renders a witness a fact is grounded at — in a `by`
// premise's `At(fact, w…)` and in a fused `Cite(fact, w…)`. A variable
// is the Go local it is declared as. Any other term is the text a
// chapter writes, parsed by the Argument its steps run under —
// `a.TermAs[Real]("(m - l) / &2")` where a phantom in the family's
// scope spells its type, `a.Term("normal_distribution(&0, &1)")` where
// none does — where the text reads back as the term (witnessText); a
// term with no such text is its Go expression.
//
// What is printed decides what the member declares: the Go expression
// binds the locals it names (goTermExpr), and the text registers the
// free variables it mentions (textScopeVars), its constants being
// registered by the symbol walk either way.
func (e *_Emitter) witnessExpr(w core.Term) string {
	expr, _ := e.termExpr(w)
	return expr
}

// caseTermExpr renders the term a case split is on — `ByCaseStep(t,
// …)`, which takes the kernel term — as witnessExpr renders a witness,
// a text read at the Argument unwrapped (`.Core()`).
func (e *_Emitter) caseTermExpr(t core.Term) string {
	expr, text := e.termExpr(t)
	if text {
		return expr + ".Core()"
	}
	return expr
}

// termExpr is witnessExpr with whether the term is written as a text
// the Argument parses. The text registers the free variables it
// mentions (textScopeVars); a bound binder it spells under its own
// name is the boundary's (surfaceNamedTerm), which registers nothing.
func (e *_Emitter) termExpr(w core.Term) (expr string, isText bool) {
	text, phantom, ok := e.witnessText(w)
	if !ok {
		return e.goTermExpr(w), false
	}
	if e.textScopeVars == nil {
		e.textScopeVars = map[string]bool{}
	}
	for _, v := range w.Frees(func(core.VarTerm) bool { return true }) {
		e.textScopeVars[string(v.Name())] = true
	}
	if e.deriveDepth <= 1 {
		e.closureArgumentRead = true
	}
	if phantom == "" {
		return fmt.Sprintf("%s.Term(%q)", e.argumentReceiver(), text), true
	}
	return fmt.Sprintf("%s.TermAs[%s](%q)", e.argumentReceiver(), phantom, text), true
}

// witnessText is the text a witness is written as, with the phantom of
// its type — "" where no phantom in the family's scope spells the type
// (phantomInScope), and the text is read with no type expected, by
// `Term`; ok=false where the witness keeps its Go expression.
//
// The text is the parser profile's print of the term. It is used only
// when it reads back, at the type the emitted call expects — the
// phantom's for `TermAs`, none for `Term` — and in the scope that call
// parses it in, as the witness up to bound names. Redundant
// embeddings are dropped by the same check. That scope is the Script's own —
// Argument.Term takes no scope override — under which a polymorphic
// constant's type letters are the constant's own (FreshenMetaLetters).
// Its model here: the witness's free variables at their types, as the
// member's `ctx.Var` lines register them; the witness's constants at
// their own instances, as the member's `ctx.Const` lines register them,
// except a constant the family's scope already serves, for which the
// member has no line and the parse instantiates the constant's meta.
//
// A witness keeps its Go expression when it is a variable, when one of
// its free variables cannot be registered (a name the member holds at
// two types, registerableVarNames' rule), when the member holds one of
// its constants at several instances (the Script reads the name at
// whichever registered first), and when the text does not read back.
func (e *_Emitter) witnessText(w core.Term) (text, phantom string, ok bool) {
	// A variable is its Go local — but a bundle's component, which the
	// boundary fixes under its own name and no parameter binds, is the
	// text of that name, as the chapter writes it (`a.TermAs[RingOps[A]]("c")`).
	if v, isVar := w.Core().(core.VarTerm); isVar && !e.componentSkolem(v) {
		return "", "", false
	}
	// Typed where a phantom spells the type; read with none expected
	// otherwise.
	expected := w.Type()
	phantom, typed := e.phantomInScope(expected)
	if !typed {
		phantom, expected = "", nil
	}
	// The Argument the text is read at aliases every bound binder by its
	// own name: the text spells it so.
	w = e.surfaceNamedTerm(w)
	vars := map[string]core.HolType{}
	for _, v := range w.Frees(func(core.VarTerm) bool { return true }) {
		name := string(v.Name())
		if !e.registerableVarNames[name] {
			return "", "", false
		}
		vars[name] = v.Type()
	}
	scope := e.parseScopeOver(w)
	for name := range scope.Consts {
		if e.constInstanceCount(core.TermName(name)) > 1 {
			return "", "", false
		}
		if e.familyDeclaresConst(name) {
			delete(scope.Consts, name)
		}
	}
	scope.Vars = vars
	scope.FreshenMetaLetters = true
	// The chapter's spelling where it reads back, else the parser's
	// own print where that does.
	plain := ext.FormatTermForParser(e.foldTerm(w, scope))
	texts := []string{plain}
	if short := e.display(plain); short != plain {
		texts = []string{short, plain}
	}
	reads := func(text string) bool {
		read := dsl.ParseTermTextInScope(text, nil, scope, expected)
		return len(read.Errors) == 0 && read.Term != nil && read.Term.AlphaEquals(w)
	}
	for _, text := range texts {
		if reads(text) {
			return e.noteAbbreviations(dsl.SurfaceForm(text, reads)), phantom, true
		}
	}
	return "", "", false
}

// foldProp is p with every subterm an abbreviation names spelled
// «Name» (dsl.FoldAbbreviations), the entries read as terms under
// scope over p's own free variables; p itself when the member has no
// table.
func (e *_Emitter) foldProp(p core.Prop, scope *dsl.ParseScope) core.Prop {
	if e.abbrevTable == nil || p == nil {
		return p
	}
	terms := e.abbrevTable.Terms(dsl.StatementScopeVars(p), scope)
	if len(terms) == 0 {
		return p
	}
	hyps := make([]core.Term, 0, p.NumHyps())
	for i := range p.NumHyps() {
		hyps = append(hyps, dsl.FoldAbbreviations(p.Hyp(i), terms))
	}
	return core.MakeProp(dsl.FoldAbbreviations(p.Conclusion(), terms), hyps...)
}

// foldTerm is foldProp for one term, over its own free variables.
func (e *_Emitter) foldTerm(t core.Term, scope *dsl.ParseScope) core.Term {
	if e.abbrevTable == nil || t == nil {
		return t
	}
	vars := map[string]core.HolType{}
	for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
		vars[string(v.Name())] = v.Type()
	}
	return dsl.FoldAbbreviations(t, e.abbrevTable.Terms(vars, scope))
}

// noteAbbreviations records the names a rendered text spells, and
// returns the text.
func (e *_Emitter) noteAbbreviations(text string) string {
	for _, name := range dsl.AbbreviationNames(text) {
		e.abbrevUsed[name] = true
	}
	return text
}

// usedAbbreviations is the entries the member declares: the ones its
// rendered texts spell, and what those stand on, in table order, the
// chapter's among them left out.
func (e *_Emitter) usedAbbreviations() dsl.Abbrev {
	names := make([]string, 0, len(e.abbrevUsed))
	for name := range e.abbrevUsed {
		names = append(names, name)
	}
	return e.ownEntries(e.abbrevTable.Needed(names))
}

// ownEntries is entries without the chapter's: an entry the family's
// table declares (FamilyVocab.Abbrev) is in scope for every text of the
// chapter and is declared nowhere else.
func (e *_Emitter) ownEntries(entries dsl.Abbrev) dsl.Abbrev {
	v := e.opts.FamilyVocab
	if v == nil || len(v.Abbrev) == 0 {
		return entries
	}
	var own dsl.Abbrev
	for _, a := range entries {
		if !v.Abbrev[a.Name] {
			own = append(own, a)
		}
	}
	return own
}

// headlineArg is the member's statement argument, as the Go the member
// keeps: the headline in parts where it has a premise or the member
// spells an abbreviation of its own, the one string otherwise. The
// member declares every entry its rendered texts spell beyond the
// chapter's table — the headline's, its sections' and its proof's
// (usedAbbreviations) — because the Script reads all of them under the
// headline's table (registry.BuildSpec.installAbbreviations): the
// landed entry's own parts where the
// headline is its authored text (EmitOptions.StatementParts), the
// entries the proof adds appended to the author's; the printed headline
// split into parts otherwise. A headline that cannot be written in
// parts while a text spells a name is an emit error: the declaration
// has no place to go. indent is the indentation of the line the call
// opens on: gofmt sets the literal's fields one tab deeper and its
// closing brace there.
func (e *_Emitter) headlineArg(indent string) string {
	text := e.noteAbbreviations(e.familyGoalText)
	used := e.usedAbbreviations()
	var parts *dsl.Statement
	if authored := e.opts.StatementParts; authored != nil && text == e.opts.StatementText {
		parts = authoredStatement(authored, used)
	} else if parts = e.splitParts(text); parts != nil {
		parts.Abbrev = used
		if len(parts.Hypotheses) == 0 && len(used) == 0 {
			parts = nil
		}
	}
	if parts == nil {
		if len(used) > 0 {
			e.failText(fmt.Errorf("emit: the member's texts spell «%s», and its headline %q cannot be written "+
				"in parts (Statement{…}) to declare the entry", used[0].Name, text))
		}
		return fmt.Sprintf("%q", text)
	}
	return statementLiteral(parts, indent)
}

// authoredStatement is the landed entry's parts with the entries used
// beyond its table appended, the author's literal left as written. The
// table is read by parsing it, as the registry read it when the entry
// registered; an entry both tables declare is one entry, and a name
// under two texts is an inconsistency.
func authoredStatement(authored *dsl.Statement, used dsl.Abbrev) *dsl.Statement {
	declared, err := dsl.ParseAbbreviations(authored.Abbrev)
	if err != nil {
		panic(fmt.Sprintf("emit: the landed entry's abbreviations do not parse: %v", err))
	}
	texts := map[string]string{}
	for _, entry := range declared.Entries() {
		texts[entry.Name] = entry.Text
	}
	member := *authored
	member.Abbrev = append(dsl.Abbrev(nil), authored.Abbrev...)
	for _, entry := range used {
		if !declared.Has(entry.Name) {
			member.Abbrev = append(member.Abbrev, entry)
			continue
		}
		if own := texts[entry.Name]; own != entry.Text {
			panic(fmt.Sprintf("emit: «%s» is %q in the landed entry's statement and %q in the session's table — one name, one meaning",
				entry.Name, own, entry.Text))
		}
	}
	return &member
}

// lawArg is the law's body argument: in parts where it has a premise
// or the member spells an abbreviation of its own, which the parts
// declare, the one string otherwise. The structure door adds its own
// prefix to a Statement as it does to a string, so the table remains in
// scope for every claim of the law.
func (e *_Emitter) lawArg(text, indent string) string {
	text = e.noteAbbreviations(text)
	used := e.usedAbbreviations()
	parts := e.splitParts(text)
	if parts == nil {
		if len(used) > 0 {
			e.failText(fmt.Errorf("emit: the Law body %q cannot be written in parts to declare «%s»", text, used[0].Name))
		}
		return fmt.Sprintf("%q", text)
	}
	if len(parts.Hypotheses) == 0 && len(used) == 0 {
		return fmt.Sprintf("%q", text)
	}
	parts.Abbrev = used
	return statementLiteral(parts, indent)
}

// lemmaArg is a section's statement argument under family.Sections: in
// parts where it has a premise, the one string otherwise. The names it
// spells are the headline's to declare (headlineArg); a section with no
// table of its own reads under the member's (Script.Lemma).
func (e *_Emitter) lemmaArg(text, indent string) string {
	e.noteAbbreviations(text)
	parts := e.splitParts(text)
	if parts == nil || len(parts.Hypotheses) == 0 {
		return fmt.Sprintf("%q", text)
	}
	return statementLiteral(parts, indent)
}

// cardArg is a card's statement argument: in parts where it has a
// premise or spells an abbreviation beyond the chapter's, the one
// string otherwise. A card is a member of its own, stated by
// family.Card under its own table, so the names its text spells are
// declared on it and are not this member's to declare.
func (e *_Emitter) cardArg(text, indent string) string {
	parts := e.splitParts(text)
	if parts == nil {
		return fmt.Sprintf("%q", text)
	}
	parts.Abbrev = e.ownEntries(e.abbrevTable.Needed(dsl.AbbreviationNames(text)))
	if len(parts.Hypotheses) == 0 && len(parts.Abbrev) == 0 {
		return fmt.Sprintf("%q", text)
	}
	return statementLiteral(parts, indent)
}

// splitParts is text in parts, with no table, where the parts and the
// one string are one statement printed two ways (dsl.CanonicalParts);
// nil where the one string is the only rendering.
func (e *_Emitter) splitParts(text string) *dsl.Statement {
	split, ok := dsl.CanonicalParts(text)
	if !ok {
		return nil
	}
	return &split
}

// requireNoAbbreviations is the check a door whose statement is one
// string makes: a member stated through the Instance door has no
// Statement literal to declare an abbreviation on, so a text of its
// proof spelling one the chapter does not declare is an emit error
// rather than a declaration dropped.
func (e *_Emitter) requireNoAbbreviations(door string) {
	if used := e.usedAbbreviations(); len(used) > 0 {
		e.failText(fmt.Errorf("emit: the member's texts spell «%s», and the %s door states the member as one "+
			"string, which declares no abbreviation — state it through family.Theorem, or write the texts "+
			"without the entry", used[0].Name, door))
	}
}

// statementLiteral renders a statement in parts as the Statement
// literal the authoring surface spells, one hypothesis and one
// abbreviation per line, gofmt-aligned, its lines after the first
// indented by indent — the indentation of the line it opens on.
func statementLiteral(s *dsl.Statement, indent string) string {
	var b strings.Builder
	b.WriteString("Statement{\n")
	if s.Binders != "" {
		fmt.Fprintf(&b, "Binders: %q,\n", s.Binders)
	}
	if len(s.Hypotheses) > 0 {
		b.WriteString("Hypotheses: []string{\n")
		for _, h := range s.Hypotheses {
			fmt.Fprintf(&b, "%q,\n", h)
		}
		b.WriteString("},\n")
	}
	fmt.Fprintf(&b, "Conclusion: %q,\n", s.Conclusion)
	if len(s.Abbrev) > 0 {
		b.WriteString("Abbrev: Abbrev{\n")
		for _, a := range s.Abbrev {
			fmt.Fprintf(&b, "{Name: %q, Text: %q},\n", a.Name, a.Text)
		}
		b.WriteString("},\n")
	}
	b.WriteString("}")
	// gofmt decides the alignment of the keys: the literal is formatted
	// as the value of a declaration and taken back out of it.
	src, err := format.Source([]byte("package p\n\nvar _ = " + b.String() + "\n"))
	if err != nil {
		panic(fmt.Sprintf("emit: a Statement literal does not format: %v\n%s", err, b.String()))
	}
	formatted := strings.TrimSuffix(strings.TrimPrefix(string(src), "package p\n\nvar _ = "), "\n")
	lines := strings.Split(formatted, "\n")
	for i := 1; i < len(lines); i++ {
		lines[i] = indent + lines[i]
	}
	return strings.Join(lines, "\n")
}

// goTermExpr prints t as a Go term expression and marks the declared
// locals it names as referenced, so the member binds them
// (renderDecls; the steps render before the declarations).
func (e *_Emitter) goTermExpr(t core.Term) string {
	e.markGoUsedFromTerm(t)
	return e.printer.PrintTerm(t)
}

// constInstanceCount is the number of type instances the member holds
// the named constant at.
func (e *_Emitter) constInstanceCount(name core.TermName) int {
	count := 0
	for k := range e.constIdent {
		if k.name == name {
			count++
		}
	}
	return count
}

// buildParseScope reads emit's symbol tables and produces a
// ParseScope keyed by HOL name (not by Go ident — the parser sees
// the original name in the text). Const declarations come from
// recordConst; the ConstTerm reconstructed here matches what the
// runtime Script.Const call will register, ensuring round-trip
// alpha-equivalence.
func (e *_Emitter) buildParseScope(p core.Prop) *dsl.ParseScope {
	terms := make([]core.Term, 0, p.NumHyps()+1)
	terms = append(terms, p.Conclusion())
	for i := range p.NumHyps() {
		terms = append(terms, p.Hyp(i))
	}
	return e.parseScopeOver(terms...)
}

// parseScopeOver is buildParseScope over the terms a text spells: a
// prop's conclusion and hypotheses, or a single term. A constant's type
// letters are its own (FreshenMetaLetters), as in the Script a landed
// member's texts parse in and at every session door: a statement over
// its own `A` holding `∘` at an instance containing that `A` reads back.
func (e *_Emitter) parseScopeOver(terms ...core.Term) *dsl.ParseScope {
	scope := &dsl.ParseScope{
		Consts:             map[string]core.ConstTerm{},
		ConstMetas:         map[string]core.ConstTermMeta{},
		Syntax:             registry.GetConstMetaManager(),
		ImplicitBindings:   e.opts.ImplicitBindings,
		CoerceDomain:       e.opts.CoerceDomain,
		StrictCoercion:     true,
		FreshenMetaLetters: true,
		Abbreviations:      e.abbrevTable,
		// A name the text spells beyond the member's own constants
		// resolves through the constant inventory, as the Script a landed
		// member's texts parse in resolves it (proof.NewScript): a
		// chapter notation reads at every constant declaring it.
		ConstResolver: func(name string) core.ConstTermMeta {
			meta, ok := e.loadConstMeta(core.TermName(name))
			if !ok {
				return core.ConstTermMeta{}
			}
			return meta
		},
	}
	// Populate Consts from the section's OWN const occurrences — not
	// emit's global e.constMeta. The global path was wrong for
	// polymorphic-multi-instance: a section's set_member at type α and
	// empty_set at type β must agree (α = β for `set_member(x, empty_set)` to type-
	// check), but emit's global scope can record set_member and empty_set at
	// types from DIFFERENT sections that don't unify. Walking each
	// section's own prop gives a self-consistent scope.
	for _, t := range terms {
		collectScopeFromTerm(t, scope)
	}
	// A constant the family's scope serves has no ctx.Const line in the
	// member (renderDecls), so the Script reads it through the resolver
	// at the constant's own letters, freshened: a text fixing an
	// instance of it says so itself, or leaves a letter unpinned.
	for name := range scope.Consts {
		if e.familyDeclaresConst(name) {
			delete(scope.Consts, name)
		}
	}
	// Polymorphic fallback: every const has its meta available so
	// later occurrences at a different type (inside the same prop)
	// re-instantiate via buildAppViaMeta. Pull from emit's global
	// constMeta — meta identity is name-keyed, not type-keyed.
	for _, meta := range e.constMeta {
		scope.ConstMetas[string(meta.Name())] = meta
	}
	// Special consts (COND, NOT, AND, …) aren't recorded by recordConst
	// because their render path is inline (WrapTerm(COND), etc.), so
	// they never reach e.constMeta. The text probe still needs them
	// visible to the parser so a section's text form like
	// `COND(c, y, x)` resolves. Pull their metas in directly.
	for _, c := range specialConstsForScope() {
		scope.ConstMetas[string(c.Name())] = c.Meta()
	}
	return scope
}

// collectScopeFromTerm walks t and adds every ConstTerm encounter to
// scope.Consts (keyed by name, first occurrence wins). Within a
// single prop, all occurrences of a given const name share the same
// type-instance — the type-checker would have rejected the prop
// otherwise — so the first occurrence is canonical.
func collectScopeFromTerm(t core.Term, scope *dsl.ParseScope) {
	switch tt := t.Core().(type) {
	case core.ConstTerm:
		name := string(tt.Name())
		if _, exists := scope.Consts[name]; !exists {
			scope.Consts[name] = tt
		}
	case core.AppliedTerm:
		collectScopeFromTerm(tt.Fun(), scope)
		collectScopeFromTerm(tt.Arg(), scope)
	case core.AbsTerm:
		collectScopeFromTerm(tt.Body(), scope)
	}
}

// specialConstsForScope returns the ext-package special consts whose
// metas the parser needs in scope to round-trip an emit-output text
// form. COND is the main entry; other connectives (¬ ∧ ∨ ⇒ ∀ ∃) have
// their own dedicated parser syntax and don't go through buildApp's
// const-resolution path.
func specialConstsForScope() []core.ConstTerm {
	return []core.ConstTerm{ext.COND}
}

// display is the chapter's spelling of a display printer's text
// (dsl.DisplaySpelling under the family's instance bindings): what a
// Show, Have or Case label and a context comment say about a goal is
// what the chapter writes — `‖u‖_n`, `u + v` — not the kernel
// printer's `vec_norm(n, u)`. These are prose, not payloads: nothing
// parses them, so the spelling's own round trip is the only check,
// and a text it cannot read stays the printer's.
func (e *_Emitter) display(text string) string {
	return dsl.DisplaySpelling(text, registry.GetConstMetaManager(), e.opts.ImplicitBindings)
}

// goalComment renders a prop as a one-line human comment in the
// chapter's spelling, under the label cap — the text of a rendered
// Have label. Uses ext.PrintProp's text form.
//
// For the per-section method comment (emitted above the func, where a
// long line is fine), use goalCommentFull instead.
func (e *_Emitter) goalComment(p core.Prop) string {
	return capLabelRunes(e.goalCommentFull(p))
}

// conclusionLabel renders a goal's CONCLUSION as a one-line label in
// the chapter's spelling, under the label cap. It is the text of a
// rendered branch label (caseLabel) and of a rendered Show.
func (e *_Emitter) conclusionLabel(p core.Prop) string {
	if p == nil {
		return ""
	}
	return capLabelRunes(oneLine(e.display(ext.PrintTerm(e.displayed(p).Conclusion()))))
}

// displayed is p as a label or a comment shows it: every binder a
// term parameter binds under its own name (surfaceNamed), and every
// subterm the member's abbreviations name folded to its «Name».
func (e *_Emitter) displayed(p core.Prop) core.Prop {
	p = e.surfaceNamed(p)
	return e.foldProp(p, e.buildParseScope(p))
}

// goalCommentFull is goalComment without the truncation. A closed
// fact — a claim, a conjunct — reads as its proposition, with no ⊢.
func (e *_Emitter) goalCommentFull(p core.Prop) string {
	p = e.displayed(p)
	if p.NumHyps() == 0 {
		return oneLine(e.display(ext.PrintTerm(p.Conclusion())))
	}
	return oneLine(e.display(prop.PrintProp(p)))
}

// oneLine collapses a printed term's newlines, tabs and runs of spaces.
func oneLine(s string) string {
	s = strings.ReplaceAll(s, "\n", " ")
	s = strings.ReplaceAll(s, "\t", " ")
	for strings.Contains(s, "  ") {
		s = strings.ReplaceAll(s, "  ", " ")
	}
	return s
}

// capLabelRunes cuts a one-line text at 120 runes, so that a role tag
// in front of it still fits the chapter's 140-rune label cap. The cap
// counts runes: HOL notation is heavily Unicode (∀ ∃ ⊢ ⇒ etc.), and
// byte slicing would split a multi-byte sequence into invalid UTF-8.
func capLabelRunes(s string) string {
	const capRunes = 120
	runes := []rune(s)
	if len(runes) > capRunes {
		s = string(runes[:capRunes-1]) + "…"
	}
	return s
}

// contextComment renders the goal state at a specific point in the
// proof as a `// context:` comment block in the chapter's spelling:
// one `h<i>:` line per hypothesis (0-based, matching InstHyp /
// ClearHyps / Subst / Rw indexing) followed by a `concl:` line. Each
// line is prefixed by `indent + "// "` and truncated to a per-line
// rune cap so long HOL terms don't blow out the emitted file's column
// width.
//
// Emitted at the top of every Case body (both inline and hoisted-into-
// sibling-methods) so that `Specialize(InstHyp(2, …))` /
// `ClearHyps(2, 3)` indices are readable without running the proof.
// Returns "" when p is nil.
func (e *_Emitter) contextComment(indent string, p core.Prop) string {
	if p == nil {
		return ""
	}
	truncate := func(s string) string { return capLabelRunes(oneLine(s)) }
	p = e.displayed(p)
	var b strings.Builder
	fmt.Fprintf(&b, "%s// context:\n", indent)
	for i, h := range p.Hyps() {
		fmt.Fprintf(&b, "%s//   h%d: %s\n", indent, i, truncate(e.display(ext.PrintTerm(h))))
	}
	fmt.Fprintf(&b, "%s//   concl: %s\n", indent, truncate(e.display(ext.PrintTerm(p.Conclusion()))))
	return b.String()
}

// renderElementarityExpr renders an `elementarity` composite as the call it
// records: ByElementarity(<source>, <facts>…), with .At(<params>…) for the
// fixed-parameter form. An entry renders as its Go var, a resident fact
// as the statement it names (ResidentHyp(<stmt>)).
func (e *_Emitter) renderElementarityExpr(t *proof.ElementarityProto) string {
	entry := func(name string) string {
		var key core.PropKey
		if d, ok := registry.ByName(name); ok {
			key = core.PropKey(d.Key)
		}
		e.markDepName(name, key)
		return e.depNameExpr(name, key)
	}
	args := []string{"nil"}
	switch {
	case t.GetEntry() != "":
		args[0] = entry(t.GetEntry())
	case t.GetFamily() != nil:
		l, _ := e.reader.Prop(t.GetFamily())
		args[0] = e.residentHypExpr(l)
	}
	for _, ref := range t.GetFacts() {
		l, _ := e.reader.Prop(ref)
		args = append(args, e.residentHypExpr(l))
	}
	for _, name := range t.GetFactEntries() {
		args = append(args, entry(name))
	}
	expr := fmt.Sprintf("ByElementarity(%s)", strings.Join(args, ", "))
	if params := t.GetParams(); len(params) > 0 {
		rendered := make([]string, len(params))
		for i, ref := range params {
			rendered[i] = e.goTermExpr(e.reader.Term(ref))
		}
		expr += fmt.Sprintf(".At(%s)", strings.Join(rendered, ", "))
	}
	return expr
}
