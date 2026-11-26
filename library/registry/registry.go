// Package registry is the framework a chapter is written in: the
// ProofEntry / Family types, the constructors that state a member and
// its proof, and the central aggregation every chapter registers into at
// package-init time. It sits UNDER the mathematics — library/proofs
// imports this, never the reverse — and above it sit the readers that
// take the corpus as a whole: the replay harness, the CNF recorder, the
// DAG, the capability manifest.
//
// # Families
//
// A Family is one theory chapter as a Go package
// (library/proofs/nat_num/nat_order/, ...): a small set of proof files,
// a README.md that is the chapter's narrative, and ONE shared recorded
// CNF cache (<family>/<family>.cnf.pb) covering every member's refutes.
// Family.Name equals the package directory basename — the recorder
// derives the pb path from it. The README's title line,
// "# <name> — <gloss>", is the one place the chapter's gloss is written
// (ChapterGloss): the index's line for the family and the package's
// doc comment, which the family generator writes, are both read off it.
//
// # Dependencies — what a proof reads
//
// A proved member's dependencies are the entries its proof reads, and
// nothing in its entry repeats them. Every use of another entry reads
// one library theorem by name (proof.ProverEnv.LookupLibraryThm): a
// typed cite — the entry var in By, Cite, At or ctx.Dep — reads the
// entry's registered name, and an induction or recursion principle or
// a served row reads the conventional name an entry serves (ServesAs).
// The family CNF recorder builds the member with every corpus entry on
// call and writes the entries the build read into the family's blob
// (proof.CNFCache.member_deps, read back by Family.RecordedDeps); the
// replay harness serves the member exactly that record and fails a
// build that reads an entry off it or no longer reads one on it.
//
// Two kinds of member declare their Deps instead, because there is no
// proof to observe or the edge is not a read: a card, whose Deps are
// the chapter's narrative of what its proof will cite, and a
// definition door's entries, whose Deps are the schema rows its
// compile reads and the mints its definiens spells — a definition
// parses at package initialization, and the reference is what makes
// Go initialize the mint first (TestLintDefinitionMintsOrdered).
// DepEntries answers for both kinds, and every consumer of the graph
// (the replay harness, the corpus seam, the DAG, the manifest, the
// index) walks it and never resolves a name.
//
// A typed cite is a Go variable reference, so the edges a proof spells
// are compiler-checked acyclic: a cross-family cycle is an import
// cycle and a same-family one a package-level variable initialization
// cycle, both compile errors, and an entry var that does not exist yet
// cannot be cited. An edge read by a conventional name is no Go
// reference; the DAG gate's cycle scan (TestRegistryDAGIntegrity) is
// the check over the whole graph. Under both, force-replay still
// catches procedure-level circularity (the omega gate) that no
// dependency graph can express.
//
// # The statement
//
// An entry has ONE statement, ProofEntry.Statement(): the proposition
// as the member states it (a constructor headline, or the
// characterizing statement a definition kit computed), read once per
// process on first use, its own key computed once on first ask
// (Statement.Key). Every consumer — the harness's trust set and
// identity check, the corpus seam's promise, a session's lemma slot,
// the typed generator, retrieve's corpus scan — reads that one value;
// nothing re-parses the text.
package registry

import (
	"fmt"
	"go/token"
	"maps"
	"os"
	"path"
	"path/filepath"
	"runtime"
	"slices"
	"sort"
	"strconv"
	"strings"
	"sync"

	"crypto/sha256"
	"encoding/hex"
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// ProofEntry pairs a theorem's display name + normalized key
// with its Build function, its typed dep declarations (see the package
// doc) and its statement (Statement — elaborated once, from the
// member's headline, or computed by a definition kit).
//
// A Build returns `(Thm, *Proof)` with no memoization short-circuit,
// and the *Proof already records every section root in order
// (Proof.SectionThms), so the replay harness forces the proof in parts
// straight off Build's return value — no per-file Top/Sections/NamedDeps
// methods.
//
// The harness uses Statement for the corpus-wide trust set: every
// entry's stated theorem is trustable at the boundary when
// forcing another entry's proof (its own replay subprocess is
// what kernel-verifies it).
//
// A CARD is a member stated without a proof (Family.Card): its
// statement is served as an axiom — the corpus seam mints it with
// core.NewAxiom, the harness has nothing to replay for it — until
// its proof lands in place of the Card build. The corpus is sound
// relative to its cards; `xugo cards` lists them, and a member's
// card frontier (the cards its dependencies reach) says what it stands
// on — the whole of it, because a proof reaches a theorem only through
// its dependencies and no definition door stands on a card (the gate
// TestNoCardUnderADefinitionalDoor): a constant is reached by name
// and a type by its terms, so a card under a definition would stand
// under every user unseen.
type ProofEntry struct {
	Name string
	// goRef is the in-package expression for a theorem owned by a datatype handle.
	goRef string
	// recordField is the in-package expression that reaches a record
	// field's projection equation through its datatype handle
	// (`RingOpsData.Fields[0]`): what the family's generated file binds
	// the entry's own name to, so that a citation spells the name.
	recordField string
	// door is the door call that registered the entry together with
	// others from one literal, shared by them all; nil for an entry
	// registered alone.
	door *DoorCall
	// Key is the statement's OWN normalized key —
	// Normalize(Stmt).AlphaKey() — spelled in source, so the FILE
	// carries the entry's full identity and every by-key channel
	// (omega's circularity gate, PromiseByKey, the manifest, the policy
	// witness) speaks one key space. The replay harness and
	// TestEntryKeyIsOwnKey recompute it and fail with the paste-ready
	// value on a mismatch (an entry registered without one gets the
	// UnmintedKeyPrefix sentinel, minted the same way). Every door that
	// registers one entry from one literal — Add, Define,
	// DefineStructure, DefineSpec — reads the key it is given and
	// normalizes nothing, so linking the corpus costs no normalization.
	//
	// A door that registers several entries from one literal has no
	// entry literal to spell each key in. DefineInductive's literal
	// spells its entries' keys in one field (InductiveKeys) and the
	// door reads them: its entries are at most four, and a principle
	// of a relation with many rules takes over a second to normalize.
	// DefineData (its principles and its record's
	// field projections), DefineType and DefineQuotient compute their
	// entries' keys from the statements at registration: a record's
	// parts are many to a literal and each is a small statement.
	//
	// The key is sensitive to the statement's type-variable NAMES
	// (core.VarType.Key carries them) and to nothing Normalize absorbs
	// — binder order, equation orientation, ⇔ orientation.
	Key string
	// Build is the member's proof — or, for a CARD, the statement
	// alone: a member stated without a proof (Family.Card), served as
	// an axiom until its proof lands.
	Build BuildSpec
	// Deps are the entries a member DECLARES it stands on, for the
	// members whose dependencies are not observed: a card's narrative
	// of what its proof will cite, which nothing replays, and a
	// definition door's inputs (package doc, "Dependencies"). A proved
	// member declares none — the entries its proof reads are recorded
	// (Family.RecordedDeps), and Family.Add refuses Deps beside a
	// proof. DepEntries is the reader of either.
	Deps []EntryLike

	// Reading is the member's statement read in this encoding, for the
	// reader the dossier serves (library/index): which hypotheses it
	// carries and why, what a set outside the space or an empty family
	// does to it, which implicit argument the short spelling leaves
	// out — the mathematics of the statement as written, in two or
	// three sentences, never its proof. An author writes it; a referee
	// pass on a card's truth leaves its findings here. Empty is the
	// ordinary state.
	Reading string

	// ServesAs, when set, is a LIBRARY-THEOREM name this entry's
	// statement additionally binds in a consumer's env: a read of
	// ServesAs is a read of this entry, served and recorded exactly as
	// a read of its Name is. The channel exists for the by-NAME
	// resolution conventions — the induction tactic reads <T>_induction,
	// the recursion-schema compile reads <T>_RECURSION, the
	// spec-definition compiler reads the fst/snd projection rows — which
	// the entry's own name can never meet. DefineData sets it on a
	// datatype's Induct/Recursion entries, peano.Induction serves
	// num_induction, and a renamed member whose
	// row a compiler reads by name declares it (cartesian/pairs'
	// Fst/Snd); anything else leaves it empty. The statement must
	// already BE the shape the named consumer analyzes — the standard
	// form every member is written in, which the induction tactic's
	// analyzer and the recursion-schema compile read.
	ServesAs string

	// Definition marks an entry a definition door registered (Define /
	// DefineData / DefineSpec) with the SHAPE it served — a value
	// computed once at registration. An importer derives the entry's
	// default use rules as proof.DefinitionSimpRules(Definition,
	// <the entry's replayed theorem>) — the same function the session
	// `define` installs from, so the two sides cannot drift — and
	// never re-analyzes the equations. Zero for every other entry.
	Definition proof.DefinitionShape

	// Simp marks a theorem the chapter declares a rule of its SIMP SET —
	// Lean's `@[simp]`: a session bound to the family, or importing it,
	// rewrites with the theorem under the bare `simp` (beside the
	// definitions the bind installs), in its stated orientation, and
	// `Family.SimpSet()` is the same set as one Go rule a chapter names
	// in a `Simp`. The theorem must be a rewrite rule as the simp driver
	// reads one — an equation or an ⇔, under ∀ and under Horn antecedents
	// — which the simp-set gate checks (TestSimpRuleEntriesAreRules). A
	// chapter declares the identities it wants read without being named
	// (x + 0 = x, 1 · x = x) and nothing whose firing is a decision.
	Simp bool

	family *Family

	// depsRecorded marks a proved member registered through Family.Add:
	// its dependencies are its proof's recorded reads, joined to Deps
	// (the Build constructor's own) by DepEntries. A card, the
	// postulate and a definition door's entries declare theirs.
	depsRecorded bool

	// depsSpelled marks an entry of a door an author declares Deps on
	// (Define, DefineSpec): DepEntries joins its Deps to the definers of
	// the constants its statement spells, so an edge to a constant the
	// definition uses is read off the definition rather than declared.
	depsSpelled bool

	// stated is a definition kit's computed characterizing statement —
	// the one statement source that is a value rather than text.
	stated core.Prop

	// predicate is a direct definition's left side read as a predicate
	// over its variables — what Conjunct states a law over (structure.go).
	// nil for every other entry.
	predicate *definedPredicate

	// stmt memoizes Statement; allocated by Family.Add (a pointer, so
	// the entry literal Add receives by value copies no lock).
	stmt *statementCell

	// source is where the entry is registered — the chapter file and
	// line of the var that calls the door, relative to library/proofs
	// ("real/real_sequences/cauchy.go:201") — read off the call stack
	// at registration (addEntry). The corpus index links a member to
	// its proof text by it.
	source string

	// defines names the constants the entry's definition door minted:
	// the Define'd constant, a spec's constants, a datatype's
	// constructors, an inductive relation, a type definition's abs and
	// rep. Empty for a theorem. definesType is the type a DefineType /
	// DefineData door minted, empty otherwise. Together they are the
	// one place "which chapter defines c" is answered from.
	defines     []string
	definesType string

	// notations are the surface spellings the chapter declared for the
	// constants a definition door minted, by constant — a DefEntry's
	// Notation pattern, else its BigOp symbol, else its Overload word; a
	// SpecConst's Overload word. A constant spelled by name has no row.
	// The corpus index shows them.
	notations map[string]string
}

// Source is the chapter file and line the entry was registered at,
// relative to library/proofs ("real/real_sequences/cauchy.go:201").
func (e *ProofEntry) Source() string { return e.source }

// Defines lists the constants the entry's definition door minted, in
// the door's order; nil for a theorem.
func (e *ProofEntry) Defines() []string { return e.defines }

// Unfoldable reports whether a proof opens the entry by Unfold: a
// definition door registered it with exactly one constant, under a
// shape whose constant has a definition to open — a direct, recursive
// or well-founded definition, a lift, a specification. A datatype's, a
// quotient's and a type's entries define several constants or none a
// proof opens, and an inductive relation is read through its theorems.
// The typed wrapper of an unfoldable entry is a proof.Definition.
func (e *ProofEntry) Unfoldable() bool {
	if len(e.defines) != 1 {
		return false
	}
	switch e.Definition {
	case proof.DefinitionDirect, proof.DefinitionRecursive, proof.DefinitionWF,
		proof.DefinitionSpec, proof.DefinitionLift:
		return true
	}
	return false
}

// DefinedConstant is the constant an unfoldable entry defines, as the
// door minted it: what the entry's typed wrapper answers as a
// proof.Definition. An entry that is not unfoldable panics.
func DefinedConstant(e *ProofEntry) core.ConstTermMeta {
	if !e.Unfoldable() {
		panic(fmt.Sprintf("proof registry: %s is no definition a proof opens (it defines %v under %v)",
			e.Name, e.defines, e.Definition))
	}
	return mintedConstant(e.Name, e.defines[0])
}

// mintedConstant reads a constant a definition door minted at
// registration; one the manager does not hold panics, naming who asked.
func mintedConstant(owner, name string) core.ConstTermMeta {
	meta, ok := GetConstMetaManager().LoadConstMeta(core.TermName(name))
	if !ok {
		panic(fmt.Sprintf("proof registry: %s defines %s, which no door has minted", owner, name))
	}
	return meta
}

// Definer is the entry whose door minted the constant, nil for a
// constant the logic defines before any chapter or one no door minted.
func Definer(constant string) *ProofEntry { return definerOf[constant] }

// DefinesType is the type the entry's door minted (DefineType,
// DefineData), empty for every other entry.
func (e *ProofEntry) DefinesType() string { return e.definesType }

// Notation is the surface spelling the chapter declared for constant,
// one the entry's door minted: a notation pattern ("‖u‖_n", "u + v"), a
// big-operator symbol or an overloaded word; empty when the constant
// is spelled by name, and for a theorem.
func (e *ProofEntry) Notation(constant string) string { return e.notations[constant] }

// corpusSourceMarker is the path segment every chapter file carries;
// chapterFrame cuts a frame's path there.
const corpusSourceMarker = "/library/proofs/"

// chapterFrame reads the chapter file and line the calling goroutine is
// in off its call stack: the innermost frame in a file under
// library/proofs, as the path below that directory and the line. ok is
// false when no frame lies there.
func chapterFrame() (path string, line int, ok bool) {
	pcs := make([]uintptr, 64)
	n := runtime.Callers(2, pcs)
	for n == len(pcs) {
		pcs = make([]uintptr, 2*len(pcs))
		n = runtime.Callers(2, pcs)
	}
	frames := runtime.CallersFrames(pcs[:n])
	for {
		frame, more := frames.Next()
		if i := strings.LastIndex(frame.File, corpusSourceMarker); i >= 0 {
			return frame.File[i+len(corpusSourceMarker):], frame.Line, true
		}
		if !more {
			return "", 0, false
		}
	}
}

// registrationSource reads the registering chapter file and line off
// the call stack (chapterFrame). The door that registered the entry
// does not matter — Add, Define, DefineType and the datatype kit all
// pass through addEntry — and a wrapper var (`xThm{family.Add(…)}`)
// still registers at the var's own line. Empty when no frame lies
// under library/proofs (an entry a test registers).
func registrationSource() string {
	path, line, ok := chapterFrame()
	if !ok {
		return ""
	}
	return fmt.Sprintf("%s:%d", path, line)
}

// ChapterSite is the statement of a chapter the calling goroutine is
// running, as `library/proofs/<path>:<line>` from the module root: the
// innermost frame in a chapter file on its call stack. A hook called
// from inside a member's build names by it the verb of the proof that
// was running — the line that applied the step, for any step. Empty
// when the goroutine is running no chapter file: a proof a test wrote,
// a session's.
func ChapterSite() string {
	path, line, ok := chapterFrame()
	if !ok {
		return ""
	}
	return fmt.Sprintf("library/proofs/%s:%d", path, line)
}

// IsCard reports whether the member is a card: stated without a
// proof, served as an axiom until its proof lands (Family.Card).
func (e *ProofEntry) IsCard() bool { return e.Build.Card != nil }

// IsPostulate reports whether the member is the corpus's one permanent
// axiom (Family.Postulate).
func (e *ProofEntry) IsPostulate() bool { return e.Build.Postulate != nil }

// ServedAsAxiom reports whether the member has no proof to run and is
// served as an axiom wherever it is cited: a card, until its proof
// lands, or the postulate, always. A card is also debt — the cards
// listing, the frontier and a law's StandsOnCard read IsCard alone.
func (e *ProofEntry) ServedAsAxiom() bool { return e.IsCard() || e.IsPostulate() }

// PostulateTerm is the axiom the postulate is served as, built by its
// chapter in Go; it panics unless the term is α-equal to the member's
// statement, and on any member but the postulate.
func (e *ProofEntry) PostulateTerm() core.Prop {
	if !e.IsPostulate() {
		panic("proof registry: " + e.Name + " is not the postulate")
	}
	axiom := core.MakeProp(e.Build.Postulate.Term())
	if !axiom.AlphaEquals(e.Statement().Prop) {
		panic("proof registry: the postulate " + e.Name + " builds a term that is not its statement: built " +
			prop.PrintProp(axiom) + ", stated " + prop.PrintProp(e.Statement().Prop))
	}
	return axiom
}

// CardNote is the card's note — why the member deserves to exist and
// what its proof should establish, the brief its prover reads. Empty
// for a proved member.
func (e *ProofEntry) CardNote() string {
	if e.Build.Card == nil {
		return ""
	}
	return e.Build.Card.Note
}

// CardStatement is the statement a card is served at: the entry's
// statement, which is closed (Statement refuses a headline with
// hypotheses), so the axiom minted for it is `⊢ <statement>` and
// nothing weaker.
func (e *ProofEntry) CardStatement() core.Prop {
	if !e.IsCard() {
		panic("proof registry: " + e.Name + " is not a card")
	}
	return e.Statement().Prop
}

// KeyOf is a statement's identity as the registry keys it: its
// Normalize form's key — what Statement.Key computes for a member,
// and what a session computes for a goal to find the member stating
// it.
func KeyOf(p core.Prop) core.PropKey {
	normalized, _ := prop.Normalize(p)
	return normalized.AlphaKey()
}

// statementCell memoizes a statement that read: a statement that does
// not read leaves the cell empty and panics again on the next use — a
// sync.Once would mark the failed read done and hand out nil.
type statementCell struct {
	mu    sync.Mutex
	value *Statement
	// text memoizes StatementText the same way.
	textMu sync.Mutex
	text   string
}

// Statement is an entry's elaborated statement: the proposition as the
// member states it (the form every consumer serves — binder order
// included, which is what ground-cite witness tuples are read
// against), read once per process on first use; and its key — the
// Normalize form's, the entry's own Key — computed once, on first ask.
// The two are staged because they cost differently: reading a
// statement is a parse under the family vocabulary (tens of
// microseconds), normalizing it is not (half a millisecond — a second
// over the corpus), and the consumers that read EVERY member — the
// corpus scans of `retrieve` — ask no key but the hits'.
//
// Elaboration depends on nothing per-env: a statement parses under the
// family vocabulary against the process-global constant registry
// (ConstMetaManager — engine built-ins and chapter mints, and
// nothing else), so the one value is right for every env in the
// process, and the parse borrows no proof Script from a caller.
type Statement struct {
	Prop core.Prop

	// of names the member stating it — what the refusal of ⊤ in Key
	// names; empty for a statement no member states (a residual, a
	// minted text), of which the registry refuses nothing.
	of      string
	keyOnce sync.Once
	normal  core.Prop
	key     core.PropKey
	// constants are the names the statement spells (Constants), read
	// once; head is the statement prepared to be read as a head (Head),
	// once.
	constantsOnce sync.Once
	constants     []core.TermName
	headOnce      sync.Once
	head          *proof.StatedHead
}

// NewStatement wraps a parsed statement; its normal form and its key
// are computed on the first Normalized or Key.
func NewStatement(p core.Prop) *Statement {
	return &Statement{Prop: p}
}

// Normalized is the statement's Normalize form, computed once: the form
// Key is the key of, and the one a built theorem's own normal form is
// compared with to say the theorem is this statement.
func (s *Statement) Normalized() core.Prop {
	s.keyOnce.Do(func() {
		s.normal, _ = prop.Normalize(s.Prop)
		s.key = s.normal.AlphaKey()
	})
	return s.normal
}

// Key is the statement's identity: its Normalize form's key, computed
// once. A member's statement that normalizes to ⊤ panics here (see
// TautologyKey): addEntry refuses the spelled key, this refuses the
// computed one, so no consumer is handed ⊤ as a member's key.
func (s *Statement) Key() core.PropKey {
	s.Normalized()
	if s.of != "" && string(s.key) == TautologyKey() {
		panic("proof registry: " + s.of + " states a tautology (its normalized statement is ⊤): " +
			"normalization closes such a statement everywhere, so no member can prove it and none can be cited for it")
	}
	return s.key
}

// Constants lists the names of the constants the statement spells, the
// logic's own excluded, in name order: read once from the statement
// itself (ext.CollectConstNames) and never through a term's key, so
// that the scan listing the members by constant (retrieve's consts
// mode) reads what ReadStatements read and spells no key.
func (s *Statement) Constants() []core.TermName {
	s.constantsOnce.Do(func() {
		names := map[core.TermName]bool{}
		ext.CollectConstNames(s.Prop.Conclusion(), names)
		for _, h := range s.Prop.Hyps() {
			ext.CollectConstNames(h, names)
		}
		s.constants = slices.Sorted(maps.Keys(names))
	})
	return s.constants
}

// Head is the statement prepared to be read as a head at a goal
// (proof.StatedHeadOf), once: what the scan by goal (retrieve's corpus
// group) decides of a member before any match, computed when the
// statement is read (ReadStatements) and never on the request path.
func (s *Statement) Head() *proof.StatedHead {
	s.headOnce.Do(func() { s.head = proof.StatedHeadOf(s.Prop) })
	return s.head
}

// Statement returns the entry's elaborated statement. A statement
// that does not parse under the family vocabulary panics on every use
// (an authoring error to fix at the member) — it does not fall back.
// So does a statement with hypotheses left of ⊢, a door-computed one
// included: a member states a closed theorem, its variables ∀-bound
// and its premises ⇒-antecedents.
func (e *ProofEntry) Statement() *Statement {
	if e.stmt == nil {
		panic("proof registry: " + e.Name + " was not registered through Family.Add")
	}
	c := e.stmt
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.value == nil {
		p := e.stated
		if p == nil {
			p = e.parseStatement(e.Build.Headline, e.Build.HeadlineConsts)
		}
		if p.NumHyps() > 0 {
			panic("proof registry: " + e.Name + " states a sequent (hypotheses left of ⊢) — a member " +
				"states a closed theorem: ∀-bind its variables and ⇒ its premises: " + proof.ClosedSpelling(p))
		}
		st := NewStatement(p)
		st.of = e.Name
		c.value = st
	}
	return c.value
}

// StatementProp is the entry's elaborated statement as a Prop: what a
// reading of the entry's law says before the proof runs (prover/proof's
// instance content).
func (e *ProofEntry) StatementProp() core.Prop { return e.Statement().Prop }

// StatementText is the member's statement as the chapter states it
// TODAY, and the ONE text a door serves for a member: `query`,
// `retrieve` and `cards` (engine), the index pages (library/index). The text starts from what the member states — the
// headline its constructor parses (Theorem / Sections / Derived /
// Lifted) — or, for a statement a definition
// door computed (a Define's characterizing equation, a type's axioms,
// a datatype's principles), from the parser-faithful print in the
// sugared profile (a set-builder as `{x | φ}`). Either is then folded
// into the chapter's declared notation (dsl.ChapterSpelling: an
// overloaded word such as `exp` for real_exp, an operator such as `⟶`,
// a big operator, implicit arguments the scope reads), because a
// headline written before its chapter declared a notation still spells
// the long name, and a reader should see what the chapter now writes.
// A fold is served only when it parses back, under the member's own
// vocabulary, to the member's own key (readsAsOwn); otherwise the text
// stands as written. An authored text is kept as its author wrote it
// unless a notation folded — the spelling's re-print alone (a bracket
// the author set) is not a reason to replace it — while a computed
// statement takes the chapter's print whenever it parses back, and the
// plain print when it does not.
//
// The text reads at the member's statement door — under the family's
// vocabulary, which may declare its variables and type letters. The
// text that reads with nothing declared is the engine's typed spelling
// (engine.FormatStatementTypedUnder), served for a member as for a
// goal.
func (e *ProofEntry) StatementText() string {
	p := e.Statement().Prop
	c := e.stmt
	c.textMu.Lock()
	defer c.textMu.Unlock()
	if c.text == "" {
		c.text = e.statementText(p)
	}
	return c.text
}

func (e *ProofEntry) statementText(p core.Prop) string {
	manager := GetConstMetaManager()
	var bindings map[string]core.Term
	if e.family != nil {
		bindings = e.family.ImplicitBindings()
	}
	sameStatement := func(text string) bool { return e.readsAsOwn(text, p) }
	if authored := e.Build.Headline; authored != "" {
		if short, folded, err := dsl.ChapterSpellingFolded(authored, manager, bindings); err == nil && folded && sameStatement(short) {
			return short
		}
		return authored
	}
	text := prop.FormatPropForParser(p)
	if short, err := dsl.ChapterSpelling(text, manager, bindings); err == nil && sameStatement(short) {
		return short
	}
	if sameStatement(text) {
		return text
	}
	return prop.PrintProp(p)
}

// ReadStatements reads every registered member's statement, the
// constants it spells and its head, so the first whole-corpus scan
// (retrieve's corpus groups) finds them read; no key is computed. An
// engine calls it at construction: a member whose statement does not
// read under its family vocabulary fails there, not at the first
// request that scans past it.
func ReadStatements() {
	for _, e := range all {
		st := e.Statement()
		st.Constants()
		st.Head()
	}
}

// TautologyKey is the key of ⊤ — what every statement the normalizer
// closes outright normalizes to. No entry may carry it: such a member
// proves nothing (the section harness refuses the trivially true
// section), is cited for nothing (normalization closes the leaf
// itself), and holds a key any other tautology would collide with.
//
// A test fixture's statement keeps clear of three keys. This one: what
// the normalizer closes is wider than propositional — `X ⇒ X`, `∀a. a =
// a`, `∃n. n = 0`, a premise whose instance is the conclusion. The one
// every statement the normalizer REFUTES outright shares (`∀a b. a ⇒
// b`, a conjunction of free predicates), so two such fixtures collide
// as two tautologies would. And every registered member's: a test
// binary links the corpus, so a fixture's key is looked up with ByKey
// before it is added. A constant at a genuine non-instance
// (`∀n:num. n ≤ n * n * n`) is the shape that survives.
var TautologyKey = sync.OnceValue(func() string {
	normalized, _ := prop.Normalize(core.MakeProp(ext.T))
	return string(normalized.AlphaKey())
})

// parseStatement reads a statement literal under the entry's family
// vocabulary — the statement door: strict resolution (an undeclared
// name panics instead of freshening) and occurrence-local meta
// letters (a meta's internal letter can never capture a same-named
// author letter). Free VARIABLES are legitimate statement vocabulary:
// a spec-parametric chapter (cartesian/carrier) states its members
// over typed free variables the family vocab declares, and serving
// those members in any form but the stated one would hand consumers
// the ∀-closed, Skolem-prenexed form instead (unusable for witness
// grounding and hostile to the refuter).
// KeyOfText is the own key a member of this family stating text would
// carry: text read at the statement door, normalized. The error is the
// door's refusal (a name the vocabulary does not declare, a malformed
// text) — what a tool restating the entry's headline checks its
// candidate spelling against before writing it.
func (e *ProofEntry) KeyOfText(text string) (key string, err error) {
	defer func() {
		if r := recover(); r != nil {
			key, err = "", fmt.Errorf("%q does not read at %s's statement door: %v", text, e.Name, r)
		}
	}()
	normalized, _ := prop.Normalize(e.parseStatement(text, nil))
	return string(normalized.AlphaKey()), nil
}

// readsAsOwn reports whether text reads at the member's statement door
// as a statement whose key is the member's own Key. A text that reads
// α-equal to p, the member's statement, has the key p has; any other
// read is normalized and its key compared. A text the door refuses
// reads as nothing.
func (e *ProofEntry) readsAsOwn(text string, p core.Prop) (same bool) {
	defer func() {
		if recover() != nil {
			same = false
		}
	}()
	read := e.parseStatement(text, nil)
	if read.AlphaEquals(p) {
		return true
	}
	normalized, _ := prop.Normalize(read)
	return string(normalized.AlphaKey()) == e.Key
}

func (e *ProofEntry) parseStatement(text string, consts []ext.Term) core.Prop {
	ctx := e.family.statementScript()
	e.Build.installAbbreviations(ctx)
	p := e.statementProp(ctx, text, consts)
	if unpinned := dsl.UnpinnedLetters(p); len(unpinned) > 0 {
		panic(unpinnedLettersRefusal(e.Name, unpinned))
	}
	return p
}

// statementProp reads a statement text at the family's script. A text
// that does not parse panics naming the member: the reader is usually
// a gate iterating every member (the replay harness's key table, a
// lint), and the parser's own refusal names only the text, which a
// reader then charges to whichever member the gate was on.
func (e *ProofEntry) statementProp(ctx *proof.Script, text string, consts []ext.Term) core.Prop {
	defer func() {
		if r := recover(); r != nil {
			panic(fmt.Sprintf("proof registry: %s states a text that does not parse under the family vocabulary — fix the member: %v",
				e.Name, r))
		}
	}()
	return ctx.MakePropText(text, consts...)
}

// StatementParts is the member's statement as its author wrote it in
// parts (dsl.Statement); nil for a headline written as one string.
func (e *ProofEntry) StatementParts() *dsl.Statement { return e.Build.Statement }

// Abbreviations is the table every text of the member reads: the
// chapter's entries (Family.WithAbbrev), then the member's own, each
// name with the text it stands for — the whole of what a text of the
// member or of its proof may spell as «Name». nil for a member under
// none. A member's own declaration alone is StatementParts' Abbrev.
func (e *ProofEntry) Abbreviations() dsl.Abbrev { return e.Build.Abbreviations() }

// AbbreviationTable is that table as the member's registration parsed
// it; nil for a member under none.
func (e *ProofEntry) AbbreviationTable() *dsl.AbbreviationTable {
	return e.Build.AbbreviationTable()
}

// statementScript is the statement door's Script: the family's
// vocabulary against the parse env, strict resolution and
// occurrence-local meta letters. A nil family is the door with no
// vocabulary declared.
func (f *Family) statementScript() *proof.Script {
	ctx := proof.NewScript(parseEnv())
	if f != nil {
		f.applyVocab(ctx)
	}
	ctx.ParseScope.StrictResolution = true
	ctx.ParseScope.FreshenMetaLetters = true
	return ctx
}

// readsAs reports whether text reads at the family's statement door
// as the statement p, letter for letter.
func (f *Family) readsAs(text string, p core.Prop) (same bool) {
	defer func() {
		if recover() != nil {
			same = false
		}
	}()
	return f.statementScript().MakePropText(text).AlphaKey() == p.AlphaKey()
}

// SpellStatement spells a statement no member states — a law read
// through a projection (Readable.Statement) — in the chapter's
// spelling, as StatementText spells a member's computed statement: the
// parser-faithful print folded into the family's declared notation and
// implicit arguments where the fold reads back at the family's
// statement door as the same statement, the print where only it reads
// back, and the plain print otherwise.
func (f *Family) SpellStatement(p core.Prop) string {
	text := prop.FormatPropForParser(p)
	var bindings map[string]core.Term
	if f != nil {
		bindings = f.ImplicitBindings()
	}
	if short, err := dsl.ChapterSpelling(text, GetConstMetaManager(), bindings); err == nil && f.readsAs(short, p) {
		return short
	}
	if f.readsAs(text, p) {
		return text
	}
	return prop.PrintProp(p)
}

// unpinnedLettersRefusal is the statement door's refusal of a statement
// that names a polymorphic constant and no term of the letter's type.
// Such a statement registers with the parser's stand-in for a type
// variable: its key is not the key of the statement pinned, a typed
// witness at the family's letter does not fit it, and no Go type
// parameter can be named after it.
func unpinnedLettersRefusal(member string, unpinned []dsl.UnpinnedLetter) string {
	rows := make([]string, len(unpinned))
	for i, u := range unpinned {
		rows[i] = u.Repair()
	}
	return fmt.Sprintf("proof registry: the statement of %s leaves a type letter unpinned: no term of the "+
		"statement has that type, so nothing says at which type the constant is read. Pin it once where "+
		"the constant is written:\n  %s", member, strings.Join(rows, "\n  "))
}

// ImplicitVariable is an implicit argument a registered statement's
// text leaves out, which the parser completes to a variable the
// statement itself binds — not to an instance component of the family.
type ImplicitVariable struct {
	Const, Name string
}

// ImplicitVariables re-reads the entry's statement text under its
// family vocabulary and reports each implicit argument the parser
// completed to a variable of the statement. A statement that spells
// every such argument reports none.
func (e *ProofEntry) ImplicitVariables() []ImplicitVariable {
	text, consts := e.Build.Headline, e.Build.HeadlineConsts
	if text == "" {
		return nil
	}
	ctx := proof.NewScript(parseEnv())
	if e.family != nil {
		e.family.applyVocab(ctx)
	}
	ctx.ParseScope.StrictResolution = true
	ctx.ParseScope.FreshenMetaLetters = true
	e.Build.installAbbreviations(ctx)
	var out []ImplicitVariable
	ctx.ParseScope.ImplicitCompleted = func(constName, name string, variable bool) {
		if variable {
			out = append(out, ImplicitVariable{Const: constName, Name: name})
		}
	}
	ctx.MakePropText(text, consts...)
	return out
}

var (
	parseEnvOnce sync.Once
	parseEnvVal  *proof.ProverEnv
)

// parseEnv is the process-wide parse-only env statements elaborate
// against: constant metas from the global inventory, nothing else — a
// statement is read, never proved.
func parseEnv() *proof.ProverEnv {
	parseEnvOnce.Do(func() {
		mgr := GetConstMetaManager()
		parseEnvVal = &proof.ProverEnv{
			ProofService: &proof.ProofService{
				LoadConstMeta:        mgr.LoadConstMeta,
				LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
				Syntax:               mgr,
				TypeArity:            mgr.TypeArity,
			},
			LibraryThms: map[string]core.Thm{},
		}
	})
	return parseEnvVal
}

// Family returns the family this entry was registered under. Every
// entry has one.
func (e *ProofEntry) Family() *Family { return e.family }

// DepName makes *ProofEntry satisfy proof.NamedDep: the entry names
// its dep, resolved through Script.Dep at the use site (the registered
// Name is the harness-preload key).
func (e *ProofEntry) DepName() string { return e.Name }

// AsFact makes *ProofEntry a proof.CiteTarget, so cite verbs accept
// the entry var directly — `Cite(nat_arith.AddSym)`,
// `Cite(leTrans, m0, n0, p0)`: the fact the entry names.
func (e *ProofEntry) AsFact() proof.Fact { return proof.NamedFact(e) }

// BareName returns the Name the member was registered with before Add
// prefixed the family's short name. GoRef supplies its Go expression,
// including the datatype-handle path for a derived entry.
func (e *ProofEntry) BareName() string {
	if e.family == nil {
		return e.Name
	}
	return strings.TrimPrefix(e.Name, path.Base(e.family.Name)+".")
}

// GoRef returns the in-package Go expression that names this entry.
// Datatype theorems belong to their handle; other entries use their bare name.
func (e *ProofEntry) GoRef() string {
	if e.goRef != "" {
		return e.goRef
	}
	return e.BareName()
}

// UnreachableFrom says why Go code in the family package at dir — a
// directory under library/proofs, slash-separated — cannot name the
// entry, and is "" when it can. A member cites an entry by its Go
// reference, so another package reaches only an entry whose GoRef is
// exported at every selector (an unexported entry is its chapter's
// implementation, not its API) and whose package Go's internal-package
// rule lets dir import. The entry's own package reaches all of it. An
// empty dir is a package not yet placed, which no family registers: its
// location decides the internal-package rule, so only the export rule
// is read.
func (e *ProofEntry) UnreachableFrom(dir string) string {
	own := e.family.PackageDir()
	if own == dir {
		return ""
	}
	for _, selector := range strings.Split(e.GoRef(), ".") {
		if !token.IsExported(selector) {
			return fmt.Sprintf("%s is an unexported entry of %s, that chapter's implementation rather than its API",
				e.Name, e.family.Name)
		}
	}
	if dir == "" {
		return ""
	}
	parts := strings.Split(own, "/")
	for i, part := range parts {
		if part != "internal" {
			continue
		}
		if root := strings.Join(parts[:i], "/"); root != "" && dir != root && !strings.HasPrefix(dir, root+"/") {
			return fmt.Sprintf("%s lies in the internal package %s, which Go lets only the packages under %s import",
				e.Name, own, root)
		}
	}
	return ""
}

// RecordField returns the in-package expression that reaches a record
// field's projection equation through its datatype handle, and false
// for any other entry. The family generator declares a variable under
// the entry's name bound to it.
func (e *ProofEntry) RecordField() (string, bool) {
	return e.recordField, e.recordField != ""
}

// DoorCall is a definition door's call that registers several entries
// from one literal (ProofEntry.Key): a datatype with its principles and
// its record's parts, a type definition, a quotient, an inductive
// definition. Door is the door ("DefineData", "DefineType",
// "DefineQuotient" or "DefineInductive"); Name the literal's Name, the
// one its entries' names and its handle are made from; Type the type
// it mints, empty for an inductive definition, which mints a relation;
// Fields a record's parts as the literal declares them.
type DoorCall struct {
	Door   string
	Name   string
	Type   string
	Fields []DataField
}

// Door returns the door call that registered the entry together with
// others, and false for an entry registered alone.
func (e *ProofEntry) Door() (DoorCall, bool) {
	if e.door == nil {
		return DoorCall{}, false
	}
	return *e.door, true
}

// stampDoor marks the entries of one door call, nil ones (a principle
// the shape lacks) skipped.
func stampDoor(call DoorCall, entries ...*ProofEntry) {
	shared := &call
	for _, e := range entries {
		if e != nil {
			e.door = shared
		}
	}
}

// EntryLike is what a Deps list element is: anything that can hand
// back its *ProofEntry. A bare entry var is its own Entry; a typed
// theorem wrapper (a struct embedding *ProofEntry, per the Go 1.27
// wrapper-theorem surface) satisfies it by promotion — so a Deps list
// spells the same name a proof body cites, wrapper or not, and its
// elements are Go variable references.
type EntryLike interface {
	Entry() *ProofEntry
}

// Entry makes *ProofEntry its own EntryLike.
func (e *ProofEntry) Entry() *ProofEntry { return e }

// ParseScript returns a Script carrying the family's statement
// vocabulary against env — the scope member headlines and claim texts
// parse in (Statement's route). For parse-only consumers (the
// claim-text lints) that need the family ParseScope without arming
// entry proof identity: unlike Family.NewScript it reads statements,
// it does not build proofs.
func (f *Family) ParseScript(env *proof.ProverEnv) *proof.Script {
	ctx := proof.NewScript(env)
	f.applyVocab(ctx)
	// Parse-only statement consumers get the statement door's strict
	// resolution and letter freshening, so what they accept matches
	// what registration does.
	ctx.ParseScope.StrictResolution = true
	ctx.ParseScope.FreshenMetaLetters = true
	return ctx
}

// DepEntries returns the entries the entry stands on — the whole
// dependency edge set: its Deps in declaration order (a proved
// member's are the ones its Build constructor makes, BuildSpec.Deps),
// then, for a definition an author declares Deps on, the definers of
// the constants its statement spells (SpelledDeps), then, for a proved
// member, the entries its proof was recorded reading
// (Family.RecordedDeps) and the definitions it was recorded opening
// (Family.RecordedUnfolds). The corpus's graph — the index, the DAG
// gate, the card frontier, retrieval — reads this set; a build is
// served ServedDeps.
//
// A recorded name no entry registers panics: the family blob's record
// is stale (an entry renamed or deleted since the member was
// recorded), and the graph it would answer is not the corpus's. A
// rename is carried into the blobs by `rekey_cnf_blob -rename-entries`,
// a deletion by `rekey_cnf_blob -drop-entries`; each citer's replay
// then holds its row to what its proof reads.
func (e *ProofEntry) DepEntries() []*ProofEntry { return e.deps(true) }

// ServedDeps are the entries a build of the entry reads: DepEntries
// without the definitions the build reads off their constants — the
// spelled definers, which a definition's build never reads (the door
// mints the constant and closes on its own characterizing theorem),
// and the definitions a proof opens, which Unfold reads from the
// constant. The replay harness serves exactly these, and a promise
// forces them first.
func (e *ProofEntry) ServedDeps() []*ProofEntry { return e.deps(false) }

// deps is the entry's dependency set; graph adds the edges no build is
// served (SpelledDeps, the recorded unfolds).
func (e *ProofEntry) deps(graph bool) []*ProofEntry {
	out := make([]*ProofEntry, 0, len(e.Deps))
	seen := make(map[*ProofEntry]bool, len(e.Deps))
	for _, d := range e.Deps {
		if d := d.Entry(); !seen[d] {
			seen[d] = true
			out = append(out, d)
		}
	}
	if graph {
		for _, d := range e.SpelledDeps() {
			if !seen[d] {
				seen[d] = true
				out = append(out, d)
			}
		}
	}
	if !e.depsRecorded {
		return out
	}
	for _, name := range e.family.RecordedDeps()[e.Name] {
		d, ok := byName[name]
		if !ok {
			panic(fmt.Sprintf("proof registry: %s's recorded deps name %s, which no entry registers — "+
				"the family blob's record is stale: carry a rename into the blobs "+
				"(go run ./library/cmd/rekey_cnf_blob -rename-entries %s=<new name>), a deletion "+
				"(go run ./library/cmd/rekey_cnf_blob -drop-entries %s), or re-record the member",
				e.Name, name, name, name))
		}
		if !seen[d] {
			seen[d] = true
			out = append(out, d)
		}
	}
	if !graph {
		return out
	}
	for _, name := range e.family.RecordedUnfolds()[e.Name] {
		d, ok := byName[name]
		if !ok {
			panic(fmt.Sprintf("proof registry: %s's recorded unfolds name %s, which no entry registers — "+
				"the family blob's record is stale: carry a rename into the blobs "+
				"(go run ./library/cmd/rekey_cnf_blob -rename-entries %s=<new name>), a deletion "+
				"(go run ./library/cmd/rekey_cnf_blob -drop-entries %s), or re-record the member",
				e.Name, name, name, name))
		}
		if !seen[d] {
			seen[d] = true
			out = append(out, d)
		}
	}
	return out
}

// SpelledDeps are the definers of the constants the entry's statement
// spells, for an entry of a door an author declares Deps on (Define,
// DefineSpec), and nil for every other entry. Each lies in a family
// this one imports, directly or not — the equation parses at package
// init, so the mint must initialize first (TestLintDefinitionMintsOrdered)
// — which is what lets a generator walk them as it walks Deps.
func (e *ProofEntry) SpelledDeps() []*ProofEntry {
	if !e.depsSpelled {
		return nil
	}
	return e.spelledDefiners()
}

// spelledDefiners are the entries defining the constants the entry's
// statement spells, itself excluded, in constant-name order — the
// constants the parser builds on its own (an operator at its domain)
// included, since a corpus entry defines each of them too.
func (e *ProofEntry) spelledDefiners() []*ProofEntry {
	p := e.Statement().Prop
	found := map[core.TermKey]ext.ConstTerm{}
	ext.CollectConstTerms(p.Conclusion(), found)
	for _, h := range p.Hyps() {
		ext.CollectConstTerms(h, found)
	}
	names := make([]string, 0, len(found))
	for _, c := range found {
		names = append(names, string(c.Name()))
	}
	sort.Strings(names)
	var out []*ProofEntry
	for _, name := range names {
		if d := definerOf[name]; d != nil && d != e {
			out = append(out, d)
		}
	}
	return out
}

// DepsRecorded reports whether the entry's dependencies are what its
// proof reads, recorded into the family blob — a proved member
// registered through Family.Add — rather than declared in its Deps
// (a card, the postulate, a definition door's entries).
func (e *ProofEntry) DepsRecorded() bool { return e.depsRecorded }

// Family groups the entries of one theory chapter
// and carries the package's shared recorded CNF cache. Name is the
// display/subtest name; for a flat family (NewFamily) it MUST equal
// the package directory basename under library/proofs (the recorder writes
// <Name>/<Name>.cnf.pb by that convention). A family nested deeper
// than one directory (a tower group — real/tower/...) uses
// NewFamilyIn, which carries the directory explicitly.
type Family struct {
	Name string
	// Dir is the family package directory relative to library/proofs
	// (slash-separated). Empty means Dir == Name (the flat NewFamily
	// convention). The recorder writes the shared pb at
	// <Dir>/<basename(Dir)>.cnf.pb.
	Dir string
	// CNF is the family's shared recorded CNF cache blob
	// (//go:embed'd <family>.cnf.pb). The replay harness installs it
	// env-side (CNFStore → env.InstallCNFStore) before building every
	// member — family proof files install nothing themselves. Empty
	// (len 0) means "no refutes recorded yet": the harness skips the
	// install and refutes run live (nondeterministic — record before
	// blessing). Readers go through CNFStore, RecordedCapabilities and
	// RecordedDeps.
	CNF []byte

	// cnfOnce decodes CNF into cnfStore, its read-only certificate
	// store shared by every env that installs the family, once per
	// process and only when CNFStore is asked; nil when CNF is empty.
	cnfOnce  sync.Once
	cnfStore *proof.MemoryCNFStore

	// vocab declares the chapter's statement vocabulary into a member's
	// ParseScope — the spec's Install, see WithVocabSpec.
	vocab func(*proof.Script)

	// vocabSpec is the vocabulary's declarative form, when the family
	// has one — see WithVocabSpec. Its Install is what vocab runs; the
	// spec itself is what the vocab generator reads.
	vocabSpec *VocabSpec

	// coerce is the chapter's ambient numeric domain where the family
	// declares it on its handle — see WithCoerceDomain. CoerceDomain
	// reads the declaration, wherever it was made.
	coerce core.HolType

	// implicit binds the implicit binder NAMES of the chapter's derived
	// operations to the components of an instance the family works at
	// — see WithInstance (implicit.go). nil for a family stating its
	// laws under the structure's own binders.
	implicit map[string]core.Term

	// implicitFields marks derived record aliases, recomputed when an
	// instance adds another record to the family vocabulary.
	implicitFields map[string]bool

	// abbrev is the table every text of the chapter reads: the tables
	// it reads under (WithOuterAbbrev), then its own (WithAbbrev); nil
	// for a chapter under none. abbrevOuter names the chapters read
	// under, in order, and abbrevOwn is the own table as declared.
	abbrev      *dsl.AbbreviationTable
	abbrevOuter []string
	abbrevOwn   dsl.Abbrev

	// Nothing DECLARES a capability: a member uses whatever the
	// circularity gate allows, and its use is observed and recorded
	// (RecordedCapabilities).

	// recordOnce reads the per-member capability record (recorded),
	// dependency record (recordedDeps) and unfold record
	// (recordedUnfolds) from CNF, once per process (readRecords).
	recordOnce   sync.Once
	recorded     map[string][]string
	recordedDeps map[string][]string
	// recordedUnfolds is the member unfold record: per member, the
	// entries defining the constants its proof opened.
	recordedUnfolds map[string][]string

	entries []*ProofEntry
}

// WithVocabSpec attaches the family's statement VOCABULARY in its
// declarative form (vocabspec.go): the consts and the standard free
// variables every statement in the chapter is written in, one row per
// name. Family.NewScript installs the spec before the member's first
// section, so a member's statements parse with no per-proof preamble;
// the same rows are what the vocab generator renders into
// zz_vocab_gen.go. The chapter's spec variable must be named `vocab` —
// the generated file addresses it by that name.
//
// It exists because the per-proof declaration wall had two jobs and
// only one of them was ever per-proof. Registering `+`, `*`, `suc` (and
// a sequent chapter's recurring free variables) so the text parser can
// read a statement is a property of the CHAPTER — the same lines in
// every member. Building terms programmatically is per-proof, and that
// half stays in the member, which takes the handles it needs from the
// generated ops struct.
//
// Chained at declaration:
//
//	var family = registry.NewFamily("nat_num/nat_arith", familyCNF).WithVocabSpec(vocab)
func (f *Family) WithVocabSpec(spec *VocabSpec) *Family {
	if spec == nil {
		panic("registry.WithVocabSpec: nil spec")
	}
	if f.coerce != nil && spec.coerce != nil {
		panic(fmt.Sprintf("registry.WithVocabSpec(%s): the family declares its coercion domain on its handle "+
			"and the vocabulary declares one too — a chapter's domain is declared once, in its vocabulary", f.Name))
	}
	spec.finalize()
	f.vocabSpec = spec
	f.vocab = spec.Install
	return f
}

// WithAbbrev declares the chapter's own abbreviation table: the names
// every statement of the chapter and every text of its proofs may
// spell as «Name», each the term it stands for, written over the
// binders the chapter's statements share (ext/dsl/abbreviation.go). A
// member's own Abbrev is read under it — an entry of the member's may
// spell the chapter's, and a name both declare is refused at
// registration, one name, one meaning — so a member declares only the
// entries that are its own. The table is in scope for a session bound
// to the family and for every door that reads a text of the chapter,
// and the doors that render a member as written (emit, the index)
// write the chapter's entries nowhere but here. A chapter whose
// statements spell another chapter's names — one cut from it, as a
// rule — reads that chapter's table first (WithOuterAbbrev) and
// declares here only what is its own. Declared once, chained at
// declaration:
//
//	var family = registry.NewFamily("scheme/invertible_lattice_pair", familyCNF).WithAbbrev(Abbrev{
//		{Name: "wbRing", Text: "restrict_ring(field_ring(L))"},
//		…
//	})
func (f *Family) WithAbbrev(table dsl.Abbrev) *Family {
	if f.abbrevOwn != nil {
		panic(fmt.Sprintf("registry.WithAbbrev(%s): the chapter's abbreviations are declared once", f.Name))
	}
	if len(table) == 0 {
		panic(fmt.Sprintf("registry.WithAbbrev(%s): an empty table — drop the declaration", f.Name))
	}
	merged, err := f.abbrev.Extend(table)
	if err != nil {
		panic(fmt.Sprintf("registry.WithAbbrev(%s): %v", f.Name, err))
	}
	f.abbrev, f.abbrevOwn = merged, table
	return f
}

// ChapterAbbrev is a chapter's table as the chapters that read under it
// name it (WithOuterAbbrev): the chapter's name and the table every
// text of the chapter reads, the tables it reads under included. A
// chapter with a table exports it from its family.go, after the family
// handle:
//
//	var ChapterAbbrev = family.ChapterAbbrev()
type ChapterAbbrev struct {
	Family string
	table  *dsl.AbbreviationTable
}

// ChapterAbbrev is the chapter's table for the chapters that read under
// it; a chapter with no table has none to export.
func (f *Family) ChapterAbbrev() ChapterAbbrev {
	if f.abbrev == nil {
		panic(fmt.Sprintf("registry.ChapterAbbrev(%s): the chapter declares no table", f.Name))
	}
	return ChapterAbbrev{Family: f.Name, table: f.abbrev}
}

// WithOuterAbbrev reads every text of the chapter under another
// chapter's table: the entries of outer, in order, are the outer table
// of every statement and every text of this chapter, and of its own
// table, declared after (WithAbbrev). A chapter whose statements spell
// another chapter's names — one cut from it, as a rule — reads that
// chapter's table and declares only the entries that are its own; what
// it exports (ChapterAbbrev) carries what it read, so a chapter that
// reads under it in turn reads through. The entries are written over
// the read chapter's binders, so a chapter reads a table only where its
// statements bind the same names. An entry two of the tables hold, one
// name with one text, is read once: two chapters cut from one parent
// each export the parent's entries, and a chapter reads both. One name
// with two texts is refused — one name, one meaning — and the read is
// declared once, before the chapter's own table:
//
//	var family = registry.NewFamily("scheme/closed_divisor", familyCNF).WithOuterAbbrev(smooth_curve.ChapterAbbrev).WithAbbrev(Abbrev{
//		…
//	})
func (f *Family) WithOuterAbbrev(outer ...ChapterAbbrev) *Family {
	switch {
	case len(outer) == 0:
		panic(fmt.Sprintf("registry.WithOuterAbbrev(%s): no table named — drop the declaration", f.Name))
	case f.abbrevOuter != nil:
		panic(fmt.Sprintf("registry.WithOuterAbbrev(%s): the tables a chapter reads under are declared once", f.Name))
	case f.abbrevOwn != nil:
		panic(fmt.Sprintf("registry.WithOuterAbbrev(%s): the tables a chapter reads under are declared before its own (WithAbbrev)", f.Name))
	}
	for _, o := range outer {
		if o.table == nil {
			panic(fmt.Sprintf("registry.WithOuterAbbrev(%s): %q names no table", f.Name, o.Family))
		}
		merged, err := f.abbrev.Join(o.table.Entries())
		if err != nil {
			panic(fmt.Sprintf("registry.WithOuterAbbrev(%s) reading %s: %v", f.Name, o.Family, err))
		}
		f.abbrev = merged
		f.abbrevOuter = append(f.abbrevOuter, o.Family)
	}
	return f
}

// Abbrev is the table every text of the chapter reads, as entries: the
// tables the chapter reads under (WithOuterAbbrev), then its own
// (WithAbbrev); nil for a chapter under none.
func (f *Family) Abbrev() dsl.Abbrev { return f.AbbrevTable().Entries() }

// AbbrevOwn is the chapter's own table as declared (WithAbbrev), nil
// for a chapter declaring none.
func (f *Family) AbbrevOwn() dsl.Abbrev { return f.abbrevOwn }

// AbbrevOuter names the chapters whose tables this one reads under
// (WithOuterAbbrev), in order; nil for a chapter under none.
func (f *Family) AbbrevOuter() []string { return f.abbrevOuter }

// AbbrevTable is the chapter's table parsed, nil for a chapter
// declaring none; nil-safe, for the doors that read a text under no
// family.
func (f *Family) AbbrevTable() *dsl.AbbreviationTable {
	if f == nil {
		return nil
	}
	return f.abbrev
}

// SimpRuleEntries lists the family's theorems marked Simp, in
// registration order — the family's simp set.
func (f *Family) SimpRuleEntries() []*ProofEntry {
	var rules []*ProofEntry
	for _, e := range f.Entries() {
		if e.Simp {
			rules = append(rules, e)
		}
	}
	return rules
}

// SimpSet is the family's simp set as one Go rule: `Simp(fam.SimpSet())`
// rewrites with every theorem the chapter marked Simp, each in its stated
// orientation, and the step records only the rules that fired.
func (f *Family) SimpSet() proof.SimpRule {
	entries := f.SimpRuleEntries()
	rules := make([]proof.SimpRule, len(entries))
	for i, e := range entries {
		rules[i] = proof.Fwd(e)
	}
	return proof.RuleSet(rules...)
}

// WithCoerceDomain declares the chapter's ambient numeric domain on the
// family handle: an unanchored `&` in any text of the chapter — a
// member's statement, a claim in its proof, a definition's equation, a
// text of a session bound to the family — is this domain's embedding by
// declaration. It is the declaration of a chapter with no vocabulary of
// its own, whose every name resolves through its mint; a chapter with a
// vocabulary declares the domain there (VocabSpec.CoerceDomain), and
// declaring it twice is refused. The domain is ℝ, ℤ, or a type some
// constant is the declared coercion into (DefEntry.Coercion —
// complex_field declares ℂ): there `&` of a real is that lift, while a
// num under `&` is still read on the real line and lifts only where a
// position or a partner asks.
//
//	var family = registry.NewFamily("real/real_derivative", familyCNF).WithCoerceDomain(RealDomain)
func (f *Family) WithCoerceDomain(ty core.HolType) *Family {
	if ty == nil {
		panic(fmt.Sprintf("registry.WithCoerceDomain(%s): nil domain", f.Name))
	}
	if f.vocabSpec != nil {
		panic(fmt.Sprintf("registry.WithCoerceDomain(%s): the family has a vocabulary — declare the domain "+
			"there, as its CoerceDomain row", f.Name))
	}
	f.coerce = ty
	return f
}

// CoerceDomain returns the chapter's declared numeric domain — the
// vocabulary's row, or the handle's declaration — or nil when the
// chapter declares none. Every door that reads a text of the chapter
// outside a member's script reads the domain here: the definition
// doors, and the engine for a session bound to the family.
func (f *Family) CoerceDomain() core.HolType {
	if f.coerce != nil {
		return f.coerce
	}
	if f.vocabSpec != nil {
		return f.vocabSpec.coerce
	}
	return nil
}

// VocabSpec returns the family's declarative vocabulary, or nil when
// the family declares none. The vocab generator and its drift gate
// read the spec through here.
func (f *Family) VocabSpec() *VocabSpec { return f.vocabSpec }

// RecordedCapabilities returns, per registered member name, the
// capabilities the family CNF recorder observed that member's proof
// using — the member's declaration, written by the recorder into the
// family's blob (proof.CNFCache.member_capabilities) and read by the
// dependency manifest as the member's capability edges. A member the
// recorder has not measured since the record began has no entry.
func (f *Family) RecordedCapabilities() map[string][]string {
	f.readRecords()
	return f.recorded
}

// RecordedDeps returns, per registered member name, the entries the
// family CNF recorder observed that member's proof reading — the
// member's dependencies, written by the recorder into the family's
// blob (proof.CNFCache.member_deps), registered names, sorted. A
// member the recorder has not measured has no entry; a card, the
// postulate and a definition door's entries never have one.
func (f *Family) RecordedDeps() map[string][]string {
	f.readRecords()
	return f.recordedDeps
}

// RecordedUnfolds returns, per registered member name, the entries
// defining the constants the family CNF recorder observed that member's
// proof opening (proof.CNFCache.member_unfolds), registered names,
// sorted. A member that opens nothing has an empty entry, one the
// recorder has not measured since the record began none; a card, the
// postulate and a definition door's entries never have one.
func (f *Family) RecordedUnfolds() map[string][]string {
	f.readRecords()
	return f.recordedUnfolds
}

// readRecords reads the member records of the family blob, once per
// process, from a decode it does not keep. The dependency manifest
// reads every family's records, and the certificates decoded beside
// them are many times the blob's size: they are held only by
// CNFStore, for a family a caller installs.
func (f *Family) readRecords() {
	f.recordOnce.Do(func() {
		f.recorded, f.recordedDeps, f.recordedUnfolds = map[string][]string{}, map[string][]string{}, map[string][]string{}
		if len(f.CNF) == 0 {
			return
		}
		cache := proof.DecodeCNFCache(f.CNF)
		for name, list := range cache.GetMemberCapabilities() {
			names := append([]string(nil), list.GetNames()...)
			sort.Strings(names)
			f.recorded[name] = names
		}
		for name, list := range cache.GetMemberDeps() {
			names := append([]string(nil), list.GetNames()...)
			sort.Strings(names)
			f.recordedDeps[name] = names
		}
		for name, list := range cache.GetMemberUnfolds() {
			names := append([]string(nil), list.GetNames()...)
			sort.Strings(names)
			f.recordedUnfolds[name] = names
		}
	})
}

// CNFStore returns the family's recorded certificates as a read-only
// store for env.InstallCNFStore — decoded once and shared by every env
// that replays a member (an installed store is only ever read: writes
// go to the env's own store behind it). Nil when the family has no
// recording yet, so a caller installs nothing and refutes run live.
func (f *Family) CNFStore() *proof.MemoryCNFStore {
	f.cnfOnce.Do(func() {
		if len(f.CNF) > 0 {
			f.cnfStore = proof.NewMemoryCNFStoreFrom(proof.DecodeCNFCache(f.CNF))
		}
	})
	return f.cnfStore
}

// RecordedCapabilities returns e's recorded capability use — the
// family's record for it, plus what its Build constructor itself makes
// (BuildSpec.Capabilities: a Lifted member's int_of_real lift), which
// is a use by construction whether or not a recording has run.
func RecordedCapabilities(e *ProofEntry) []string {
	seen := map[string]bool{}
	var out []string
	add := func(names []string) {
		for _, n := range names {
			if !seen[n] {
				seen[n] = true
				out = append(out, n)
			}
		}
	}
	if e.family != nil {
		add(e.family.RecordedCapabilities()[e.Name])
	}
	add(e.Build.Capabilities)
	sort.Strings(out)
	return out
}

// Entries returns the family's registered entries in registration
// (variable-initialization) order.
func (f *Family) Entries() []*ProofEntry { return f.entries }

var (
	families    []*Family
	familyNames = map[string]bool{}
	all         []*ProofEntry
	byName      = map[string]*ProofEntry{}
	byKey       = map[string]*ProofEntry{}
	byServesAs  = map[string]*ProofEntry{}
	// definerOf is the entry whose door minted each constant (its
	// defines) — what DepEntries reads a definition's edges off.
	definerOf = map[string]*ProofEntry{}
)

// NewFamily declares a family. Called once from the family
// package's family.go:
//
//	//go:embed nat_order.cnf.pb
//	var familyCNF []byte
//	var family = registry.NewFamily("nat_order", familyCNF)
func NewFamily(name string, cnf []byte) *Family {
	return NewFamilyIn(name, "", cnf)
}

// NewFamilyIn declares a family whose package directory is
// nested deeper than <name> — the tower-group layout
// (real/tower/internal/eudoxus_slope). dir is the package directory
// relative to library/proofs, slash-separated; empty dir means dir == name
// (the flat NewFamily convention):
//
//	//go:embed eudoxus_slope.cnf.pb
//	var familyCNF []byte
//	var family = registry.NewFamilyIn("real/tower/eudoxus_slope", "real/tower/internal/eudoxus_slope", familyCNF)
func NewFamilyIn(name, dir string, cnf []byte) *Family {
	if name == "" {
		panic("registry.NewFamily: empty name")
	}
	if familyNames[name] {
		panic("registry.NewFamily: duplicate family: " + name)
	}
	familyNames[name] = true
	f := &Family{Name: name, Dir: dir, CNF: cnf}
	families = append(families, f)
	return f
}

// PackageDir is the family's package directory relative to
// library/proofs: Dir, or Name for a flat family.
func (f *Family) PackageDir() string {
	if f.Dir != "" {
		return f.Dir
	}
	return f.Name
}

// ChapterGloss reads a chapter's one-line gloss off the README.md in
// its family package directory: the tail of the title line
// "# <name> — <gloss>". A directory with no README, or a README whose
// first line has another shape, is an error — a chapter with no gloss
// has no line in the index and no doc comment on its package.
func ChapterGloss(dir string) (string, error) {
	file := filepath.Join(dir, "README.md")
	text, err := os.ReadFile(file)
	if err != nil {
		return "", fmt.Errorf("chapter gloss: %v", err)
	}
	title, _, _ := strings.Cut(string(text), "\n")
	heading, isHeading := strings.CutPrefix(title, "# ")
	name, gloss, hasDash := strings.Cut(heading, " — ")
	name, gloss = strings.TrimSpace(name), strings.TrimSpace(gloss)
	if !isHeading || !hasDash || name == "" || gloss == "" {
		return "", fmt.Errorf("chapter gloss: %s: the title line %q is not \"# <name> — <gloss>\"", file, title)
	}
	return gloss, nil
}

// Add registers a family member and returns its handle — the exported
// entry var other proofs cite:
//
//	var LessEqRefl = family.Add(registry.ProofEntry{Name: "LessEqRefl", ...})
//
// Ceremony is minimized at registration time:
//
// - Name is spelled BARE (no family prefix, no dot) — Add prefixes
// it with the family's short name (path.Base of Family.Name), so
// the registered name is "nat_order.LessEqRefl" / "eudoxus_slope.Cauchy"
// and a prefix typo is impossible. Every family registers prefixed
// names; there is no no-prefix knob.
// - Key is spelled in every entry (ProofEntry.Key). Stmt is derived
// from the constructor headline — the statement is stated once, in
// the file. An entry may omit Key at
// authoring time — the replay harness and TestEntryKeyIsOwnKey
// compute the statement's normalized key and fail with the
// paste-ready value (UnmintedKeyPrefix).
// - A proved member spells no Deps: its dependencies are what its
// proof reads, recorded into the family blob (package doc,
// "Dependencies"), and Add refuses a Deps beside a proof. A card
// keeps Deps as the narrative of what its proof will cite, and the
// postulate may name what it stands on.
func (f *Family) Add(e ProofEntry) *ProofEntry {
	if e.Build.Fn != nil && len(e.Deps) > 0 {
		panic(fmt.Sprintf("proof registry: %s declares Deps beside a proof — a proved member's "+
			"dependencies are the entries its proof reads, which the CNF recorder writes into the "+
			"family blob; drop the Deps field (a card keeps its narrative Deps)", e.Name))
	}
	return f.register(e, e.Build.Fn != nil)
}

// addDeclared registers an entry a definition door builds: its Deps
// are declared — the schema rows the door's compile reads, the mints
// its definiens spells — and never recorded.
func (f *Family) addDeclared(e ProofEntry) *ProofEntry { return f.register(e, false) }

// register is Add's body and the doors': recorded marks a proved
// member whose dependencies are its proof's recorded reads.
func (f *Family) register(e ProofEntry, recorded bool) *ProofEntry {
	p := &e
	p.family = f
	p.depsRecorded = recorded
	if strings.Contains(p.Name, ".") || strings.Contains(p.Name, "/") {
		panic("proof registry: family entry Name must be bare — the family prefix is added automatically: " + p.Name)
	}
	p.Name = path.Base(f.Name) + "." + p.Name
	p.Build.bindChapter(f, p.Name)
	if s := p.Build.axiomOf; s != nil {
		s.axioms = append(s.axioms, p)
	}
	for _, d := range p.Build.Deps {
		if d == nil || d.Entry() == nil {
			panic("proof registry: " + p.Name + ": the Build constructor declares a nil dep")
		}
		declared := false
		for _, own := range p.Deps {
			if own != nil && own.Entry() == d.Entry() {
				declared = true
				break
			}
		}
		if !declared {
			p.Deps = append(p.Deps, d)
		}
	}
	p.stmt = &statementCell{}
	deriveStatement(p)
	addEntry(p)
	f.entries = append(f.entries, p)
	return p
}

// UnmintedKeyPrefix marks an entry registered without a Key. The
// pinned-identity invariant stands — a blessed entry always carries its
// key in source — but the MINTING is assisted: the replay harness and
// the key lint recompute the statement's normalized key and fail with
// the paste-ready value, replacing the hand keyprobe recipe.
const UnmintedKeyPrefix = "unminted:"

// deriveStatement checks the entry has a statement source — a
// kit-computed value, else the constructor headline (Statement reads
// them in that order) — and gives an entry registered without a Key
// the unminted sentinel the replay harness and the key lint turn into
// a paste-ready computed key.
func deriveStatement(p *ProofEntry) {
	if p.stated != nil && p.Build.Headline != "" {
		panic("proof registry: " + p.Name + " has a computed statement and a text one")
	}
	if p.stated == nil && p.Build.Headline == "" {
		panic("proof registry: " + p.Name + " has no statement — use a headline constructor")
	}
	if p.Key == "" {
		p.Key = UnmintedKeyPrefix + p.Name
	}
}

// postulate is the one entry Family.Postulate built, once it has
// registered.
var postulate *ProofEntry

func addEntry(p *ProofEntry) {
	if p.Name == "" || (p.Build.Fn == nil && !p.ServedAsAxiom()) {
		panic("proof registry: incomplete ProofEntry: " + p.Name)
	}
	if p.IsCard() && p.Build.Fn != nil {
		panic("proof registry: " + p.Name + " is a card with a proof — a card has no Build.Fn; state it with Family.Card, or prove it")
	}
	if p.IsPostulate() {
		if p.Build.Fn != nil || p.IsCard() {
			panic("proof registry: " + p.Name + " is a postulate with a proof or a card's note — a postulate is stated by Family.Postulate alone")
		}
		if postulate != nil {
			panic("proof registry: " + p.Name + " is a second postulate — the corpus assumes one axiom outright, " + postulate.Name)
		}
		if t := p.Build.Postulate.Type; t == "" || strings.ContainsAny(t, " ()→,") {
			panic("proof registry: the postulate " + p.Name + " introduces no plain type name: " + strconv.Quote(t))
		}
		postulate = p
	}
	if p.IsCard() && strings.TrimSpace(p.Build.Card.Note) == "" {
		panic("proof registry: the card " + p.Name + " has no note — a card says why it is a member and what its proof must establish")
	}
	p.source = registrationSource()
	seenDeps := make(map[*ProofEntry]bool, len(p.Deps))
	for i, d := range p.Deps {
		if d == nil || d.Entry() == nil {
			panic(fmt.Sprintf("proof registry: %s Deps[%d] is nil", p.Name, i))
		}
		if seenDeps[d.Entry()] {
			panic(fmt.Sprintf("proof registry: %s declares %s twice in Deps", p.Name, d.Entry().Name))
		}
		seenDeps[d.Entry()] = true
	}
	if byName[p.Name] != nil {
		panic("proof registry: duplicate Name: " + p.Name)
	}
	if byKey[p.Key] != nil {
		panic("proof registry: duplicate Key: " + p.Key + " (" + p.Name + ")")
	}
	if p.Key == TautologyKey() {
		panic("proof registry: " + p.Name + " states a tautology (its normalized statement is ⊤): " +
			"normalization closes such a statement everywhere, so no member can prove it and none can be cited for it")
	}
	if p.ServesAs != "" {
		if prev := byServesAs[p.ServesAs]; prev != nil {
			panic("proof registry: " + p.Name + " and " + prev.Name + " both serve as " + p.ServesAs)
		}
		byServesAs[p.ServesAs] = p
	}
	for _, name := range p.defines {
		if prev := definerOf[name]; prev != nil {
			panic("proof registry: " + p.Name + " and " + prev.Name + " both define the constant " + name)
		}
		definerOf[name] = p
	}
	byName[p.Name] = p
	byKey[p.Key] = p
	all = append(all, p)
}

// ByServesAs looks up the entry serving a library-theorem name (the
// by-name conventions' names: num_recursion, <T>_RECURSION, wellfounded_recursion, fst…)
// — what a consumer that reads the name off env.LibraryThms declares as
// its typed dep.
func ByServesAs(name string) (*ProofEntry, bool) {
	e, ok := byServesAs[name]
	return e, ok
}

// InstallLibraryDep binds a resolved dep into env.LibraryThms under
// its registered name AND — when the dep entry declares ServesAs —
// under that library-theorem alias, so the by-name resolution
// conventions (induction dispatch, the recursion-schema compile)
// reach a dep's statement without a per-name overlay. The corpus seam
// and the replay harness's resolution of a dep's own deps bind
// through here.
func InstallLibraryDep(env *proof.ProverEnv, dep *ProofEntry, thm core.Thm) {
	env.LibraryThms[dep.Name] = thm
	if dep.ServesAs != "" {
		env.LibraryThms[dep.ServesAs] = thm
	}
}

// Serves reports whether one of deps binds name in a consumer's env —
// by its registered Name or its ServesAs — the check a definition kit
// makes at registration for each library name its Build reads.
func Serves(deps []EntryLike, name string) bool {
	for _, d := range deps {
		if e := d.Entry(); e != nil && (e.Name == name || e.ServesAs == name) {
			return true
		}
	}
	return false
}

// All returns every registered entry — every family's members — in
// registration order. The order is package-init
// order and carries NO semantic weight (the replay harness resolves
// deps recursively; every consumer is order-independent).
func All() []*ProofEntry { return all }

// Families returns every registered family in registration order.
func Families() []*Family { return families }

// Fingerprint identifies the registry a binary LINKED: the SHA-256 of
// every entry's `name\tkey` line in name order, with the entry count.
// Two binaries built from trees whose registered names or keys differ
// in any way report different fingerprints; a rebuild that changed
// nothing reports the same one. The serve answers it as the
// `registry-fingerprint` RPC and prints it at startup, and the CLI's
// `registry-fingerprint` command computes it for the binary at hand,
// so an orchestrator can tell a stale serve from a fresh build without
// guessing from file times: a serve links the registry at BUILD time,
// and a member landed after that build is a name it cannot cite.
func Fingerprint() (entries int, digest string) {
	names := make([]string, 0, len(all))
	for _, e := range all {
		names = append(names, e.Name)
	}
	sort.Strings(names)
	h := sha256.New()
	for _, n := range names {
		e := byName[n]
		fmt.Fprintf(h, "%s\t%s\n", n, e.Key)
	}
	return len(all), hex.EncodeToString(h.Sum(nil))
}

// ForceEntry realizes an entry's theorem outside the replay harness:
// the corpus seam (library/serve) installs it so a promise a
// definition door made at package init — a type minted on the promise
// of its inhabitation entry (DefineType) — can be forced by whoever
// holds it. The entry is forced through the supplied Forcer,
// so its dependency graph includes the entry's build. Replay never forces
// such a promise: the entry's Build takes the proved dep and derives
// from that. Nil until a seam installs it; forcing then panics, naming
// the entry.
var ForceEntry func(core.Forcer, *ProofEntry) core.ThmCert

// FamilyByName looks up a registered family by its Name — the
// corpus-relative package directory ("iterate/real/real_sum").
func FamilyByName(name string) (*Family, bool) {
	for _, f := range families {
		if f.Name == name {
			return f, true
		}
	}
	return nil, false
}

// ByName looks up an entry by its registered Name — the one name it
// answers to; there is deliberately NO aliasing here.
func ByName(name string) (*ProofEntry, bool) {
	e, ok := byName[name]
	return e, ok
}

// ByKey looks up an entry by its own key — the statement's
// normalized key.
func ByKey(key string) (*ProofEntry, bool) {
	e, ok := byKey[key]
	return e, ok
}

// Stating is the entry whose statement is p, by p's key (KeyOf).
func Stating(p core.Prop) (*ProofEntry, bool) {
	return ByKey(string(KeyOf(p)))
}

// statedIndex lists the entries under the key of each one's statement
// as stated; entries is how many were registered when it was built.
var statedIndex struct {
	mu      sync.Mutex
	entries int
	byKey   map[core.PropKey][]*ProofEntry
}

// EntriesStating is the entries whose statement, as stated, is p up to
// α. An entry is looked up under p's key and admitted by comparing the
// two statements. The comparison is what answers: a harness asks this
// to decide which statements a replay trusts and which entry a
// certificate's assumption is, and a key equal for two statements that
// are not α-equal, which no statement of the library has, can be made
// on purpose (core.PropKey).
func EntriesStating(p core.Prop) []*ProofEntry {
	var stating []*ProofEntry
	for _, e := range statedUnder(p.AlphaKey()) {
		if e.Statement().Prop.AlphaEquals(p) {
			stating = append(stating, e)
		}
	}
	return stating
}

// statedUnder is the entries whose statement, as stated, has key.
func statedUnder(key core.PropKey) []*ProofEntry {
	statedIndex.mu.Lock()
	defer statedIndex.mu.Unlock()
	if statedIndex.byKey == nil || statedIndex.entries != len(all) {
		byKey := make(map[core.PropKey][]*ProofEntry, len(all))
		for _, e := range all {
			k := e.Statement().Prop.AlphaKey()
			byKey[k] = append(byKey[k], e)
		}
		statedIndex.byKey, statedIndex.entries = byKey, len(all)
	}
	return statedIndex.byKey[key]
}

// SomeEntryStates reports whether an entry's statement, as stated, is p
// up to α (EntriesStating): the trust frontier of a replay that takes
// every member's statement as given.
func SomeEntryStates(p core.Prop) bool { return len(EntriesStating(p)) > 0 }

// The proof calculus finds the entry stating a proposition through the
// registry's key index: the elementarity step reads a concrete
// structure's instance by it (prover/proof.StatingEntry).
func init() {
	proof.StatingEntry = func(p core.Prop) (string, bool) {
		e, ok := Stating(p)
		if !ok {
			return "", false
		}
		return e.Name, true
	}
}

// mintedOnce hands names to the FIRST entry a multi-entry door
// registers and nothing to the rest: a type definition registers two
// theorems, a datatype up to four, an inductive relation several, and
// the constants they mint are defined once — by the first.
func mintedOnce(done *bool, names []string) []string {
	if *done {
		return nil
	}
	*done = true
	return names
}
