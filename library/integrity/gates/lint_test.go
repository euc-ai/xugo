// lint_test.go — source-hygiene lints for proof files.
//
// NO MACHINE TYPE-VAR NAMES IN HAND-AUTHORED STATEMENT TEXT. `var:?N`
// names are freshening artifacts (α-keys are type-var-name RIGID —
// core.VarType.Key embeds the name — so a statement's ?N spelling is
// pinned into its key). Blessed chapter text signing a fresh-name
// counter is exactly the search-trace leakage curation exists to
// remove. The compute-route primitives keep them out of every
// lemma-install site:
//
// - a ∀-form statement installs as the harness cert itself
// (`Cite(p.inDeleteThm, …)`);
// - a cross-type instance installs as `p.ctx.AtTypes(dep, τ)` —
// which absorbs the ?N-typed source form entirely (the ?83488
// machine-type-variable case).
//
// What remains legitimate is a SECTION statement whose registered
// form itself lives at a machine type var — tracked per-file in the
// allowlist below, to shrink and never grow: a new entry needs the
// same justification (the registered statement pins that spelling),
// and an existing entry disappears when its sections are re-authored
// at human type-var names with the goal bridging by type adaptation.
//
// (`⟨?N:τ⟩` const-instance ANNOTATIONS are not flagged: they pin a
// const META's own type var — the printer's spelling for disambiguating
// an overloaded const — and the text DSL currently has no positional
// alternative. DSL-surface wishlist; a separate population from
// statement type vars.)
//
// NO fmt.Sprintf IN PROOF FILES. Statement, claim and term text is
// written as literals — see the section comment above
// TestLintNoSprintfInProofFiles.
//
// NO ASSERT STAIRCASES. Sequential facts are spelled as a flat
// Deduce / Have / Show block — see the section comment above
// TestLintNoAssertStaircase.
//
// NO ⊢ IN STATEMENT TEXT. A statement is closed — its variables
// ∀-bound, its premises ⇒-antecedents, each a slot a closure parameter
// binds — and a claim is a proposition the proof establishes in its
// context, so no statement or claim literal of a proof file spells the
// turnstile: neither hypotheses left of it nor `name : type`
// declarations, whose types the binders or a `ctx.Var` declaration
// carry — see the section comment above
// TestLintNoTurnstileInStatementText.
//
// NO UNGROUND CITE PILES. A body whose cites are wide ∀-installs
// carrying no witnesses, four or more in a row, keeps its argument
// outside the kernel-checked layer — see the section comment above
// TestLintNoUngroundCitePile.
//
// ONE CITE VERB. Bodies bring facts to bear through `Cite` /
// `CiteKeep` — see the section comment above TestLintOneCiteVerb.
//
// A QUOTIENT IS DEFINED THROUGH ITS DOOR. A chapter does not carve a
// quotient type out by hand — see the section comment above
// TestLintQuotientsUseTheDoor.
//
// CASE / HAVE / SHOW LABELS STAY UNDER 140 RUNES. What lives above
// 140 is a label quoting a multi-factor formula the claim already
// states. A label carries the mathematical MOVE of its branch — when a
// formula is too long to quote, name its recurring quantities (the
// estTerms idiom) and refer to them by name.
//
// A LABEL IS A SENTENCE, NOT A POSITION. `claim`, `after`, `left`,
// `base`, `case_0` and their kin say where a branch sits in the step
// that fans it; the label says what the branch proves. They are also
// the tags `emit-section` renders a branch label with, so the lint is
// what keeps a pasted label from landing as written — see the comment
// above structuralLabelTokens.
//
// EVERY MEMBER-BEARING FAMILY HAS A MEASURED (NON-EMPTY) CNF PB — see
// the section comment above TestLintFamilyPBMeasured.
//
// NO CERTIFICATE IN A FAMILY BLOB EXCEEDS THE CEILING — see the section
// comment above TestLintCertificateSize.
//
// A COMMENT CARRIES NO DATE, in any .go file of the module — see the
// section comment above TestLintNoDateInComment.
//
// A PACKAGE HAS ONE DOC COMMENT, AND IT OPENS BY NAMING THE PACKAGE, in
// every package of the module; a chapter's is generated from its
// README's title line — see the section comment above
// TestLintPackageDoc.
//
// AN ENVIRONMENT VARIABLE THE CODE READS IS A ROW OF CONTRIBUTING'S
// TABLE, AND A ROW IS A VARIABLE THE CODE READS — see the section
// comment above TestLintEnvVarTable.
package gates

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/doc"
	"go/format"
	"go/parser"
	"go/scanner"
	"go/token"
	"go/types"
	"io/fs"
	"maps"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"slices"
	"sort"
	"strconv"
	"strings"
	"testing"
	"unicode"
	"unicode/utf8"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/emit"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/typedgen"
	"github.com/euc-ai/xugo/library/xugofmt"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/ematch"
)

// chapterProofFiles returns every proof .go file under the
// package dir, RECURSIVELY (family sub-packages nest arbitrarily deep:
// real/tower/internal/eudoxus_slope was invisible to the earlier */*.go glob).
// Tests are excluded. Every lint below runs over this set.
func chapterProofFiles(t *testing.T) []string {
	t.Helper()
	var files []string
	err := filepath.WalkDir(corpusRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		name := d.Name()
		if !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			return nil
		}
		files = append(files, path)
		return nil
	})
	if err != nil {
		t.Fatalf("walk: %v", err)
	}
	return files
}

// A MINTED TYPE'S PHANTOM LIVES IN THE FAMILY'S vocab.go. The typed
// surface's vocabulary is decentralized (ext/holtype_phantom.go): the
// family that mints a type declares the type's phantom, and the
// typed-wrapper generator finds it by PACKAGE, so no build step
// notices which file holds it. The file is vocab.go
// (chapter_constitution.md, "Families: a theory chapter as a
// sub-package") whether or not the family declares VocabSpec rows — a
// family with none has a vocab.go holding the phantom alone, so a
// first row added later joins it and nothing moves.
//
// A type LETTER is the other kind of phantom and is not this lint's
// (TestLintTypeLetterPhantomIsGenerated is): it is recognised here by
// its Reify returning MakeVarType directly.
func TestLintMintedTypePhantomInVocabFile(t *testing.T) {
	fset := token.NewFileSet()
	for _, dir := range familyPackageDirs(t) {
		entries, err := os.ReadDir(dir)
		if err != nil {
			t.Fatalf("read dir %s: %v", dir, err)
		}
		for _, e := range entries {
			name := e.Name()
			if e.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") || name == "vocab.go" {
				continue
			}
			file := filepath.Join(dir, name)
			af, err := parser.ParseFile(fset, file, nil, 0)
			if err != nil {
				t.Fatalf("parse %s: %v", file, err)
			}
			for _, decl := range af.Decls {
				fn, ok := decl.(*ast.FuncDecl)
				if !ok || fn.Recv == nil || fn.Name.Name != "Reify" || len(fn.Type.Params.List) != 0 || reifiesTypeLetter(fn) {
					continue
				}
				t.Errorf("%s:%d: a minted type's phantom is declared in %s — it belongs in %s/vocab.go "+
					"(create the file if the family has none).\n"+
					"    A type LETTER's phantom is not a minted type's; spell its Reify `return MakeVarType(\"…\")` "+
					"so this lint reads it as one.",
					file, fset.Position(fn.Pos()).Line, name, dir)
			}
		}
	}
}

// reifiesTypeLetter reports whether a Reify method's whole body is
// `return MakeVarType(…)` — the spelling of a type letter's phantom.
func reifiesTypeLetter(fn *ast.FuncDecl) bool {
	if fn.Body == nil || len(fn.Body.List) != 1 {
		return false
	}
	ret, ok := fn.Body.List[0].(*ast.ReturnStmt)
	if !ok || len(ret.Results) != 1 {
		return false
	}
	call, ok := ret.Results[0].(*ast.CallExpr)
	if !ok {
		return false
	}
	switch callee := call.Fun.(type) {
	case *ast.Ident:
		return callee.Name == "MakeVarType"
	case *ast.SelectorExpr:
		return callee.Sel.Name == "MakeVarType"
	}
	return false
}

// A TYPE LETTER'S PHANTOM IS GENERATED. The phantom of a statement
// letter beyond A–E is declared by the family's zz_typed_thms_gen.go,
// once, for every letter a registered statement of the family binds
// (typedgen.OwnerOfLetter), so two members filled in parallel trees
// never each declare it and collide at the merge. A proof file
// therefore declares no phantom reifying to a letter that has one —
// A–E, library/authoring's, or a letter the generator owns. The one
// exception is a letter with no phantom under its own name, whose bare
// name library/authoring exports under another meaning (F, M, N): a
// member that wants it typed declares a phantom under a name of its
// own, as set_category's ambient does for M.
func TestLintTypeLetterPhantomIsGenerated(t *testing.T) {
	fset := token.NewFileSet()
	for _, dir := range familyPackageDirs(t) {
		entries, err := os.ReadDir(dir)
		if err != nil {
			t.Fatalf("read dir %s: %v", dir, err)
		}
		for _, e := range entries {
			name := e.Name()
			if e.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") || strings.HasPrefix(name, "zz_") {
				continue
			}
			file := filepath.Join(dir, name)
			af, err := parser.ParseFile(fset, file, nil, 0)
			if err != nil {
				t.Fatalf("parse %s: %v", file, err)
			}
			for _, decl := range af.Decls {
				fn, ok := decl.(*ast.FuncDecl)
				if !ok || fn.Recv == nil || fn.Name.Name != "Reify" || len(fn.Type.Params.List) != 0 || !reifiesTypeLetter(fn) {
					continue
				}
				arg := fn.Body.List[0].(*ast.ReturnStmt).Results[0].(*ast.CallExpr).Args
				if len(arg) != 1 {
					continue
				}
				lit, ok := arg[0].(*ast.BasicLit)
				if !ok {
					continue
				}
				letter, err := strconv.Unquote(lit.Value)
				if err != nil {
					continue
				}
				line := fset.Position(fn.Pos()).Line
				switch typedgen.OwnerOfLetter(letter) {
				case typedgen.LetterOfAuthoring:
					t.Errorf("%s:%d: a phantom of the letter %s — library/authoring declares %s for every proof file; delete this one and spell %s",
						file, line, letter, letter, letter)
				case typedgen.LetterOfFamily:
					t.Errorf("%s:%d: a phantom of the letter %s declared by hand — the family's %s declares %s once a statement of the family binds it "+
						"(go generate ./library/proofs); delete this one and spell %s. A cite of another family's law at %s reads that family's phantom.",
						file, line, letter, typedgen.File, letter, letter, letter)
				}
			}
		}
	}
}

var machineTypeVarInText = regexp.MustCompile(`var:\?[0-9]+`)

// machineTypeVarAllowlist: files whose registered statement
// itself lives at a machine type-var name, so their section texts
// inherit it. Value = the justification.
var machineTypeVarAllowlist = map[string]string{}

// NO fmt.Sprintf IN PROOF FILES. Statement, claim and term text is
// written as LITERALS: a misspelled name fails loudly (the claim
// path's undeclared-free assert), where a printed Term smuggles a
// display form — type ties dropped, sugar applied — through an
// unchecked re-parse. The one permitted assembly is `+` concatenation
// with a named const, kept only where several sites must agree
// character for character (`deltaSummand`, `acceptedHalf`,
// `emptySecond`, …). A dug binder that needs a readable claim-text
// name takes it at the verb — Fix("u") / FixAs[T]("u") — instead of
// being printed into the text. The corpus infra package (registry/)
// formats error messages and is out of scope; a proof file that
// genuinely needs Sprintf for something other than term text earns an
// allowlist row with its justification.
var sprintfAllowlist = map[string]string{
	"real/tower/real_completeness/display.go": "init-time panic-message formatting — no term text",
	"cartesian/carrier/vectors.go":            "membership-gate panic-message formatting (Inhabit/AtVec tripwires print the mismatched terms) — no term text",
}

func TestLintNoSprintfInProofFiles(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		base := filepath.Base(f)
		if strings.HasPrefix(base, "zz_") {
			continue
		}
		if _, ok := sprintfAllowlist[chapterRel(f)]; ok {
			continue
		}
		src, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		for i, line := range strings.Split(string(src), "\n") {
			if strings.Contains(line, "fmt.Sprintf(") {
				t.Errorf("%s:%d: fmt.Sprintf in a proof file — statement/claim/term text is a literal "+
					"(named-const + concatenation only where sites must agree character for character); "+
					"a dug binder that needs a readable name takes it at the verb: Fix(\"u\") / FixAs[T](\"u\")",
					f, i+1)
			}
		}
	}
}

// THE LAYOUT IS THE READABILITY FLOOR'S ONE MECHANICAL CLAUSE, and this
// is the step that observes it. It is gofmt's, with each argument of a
// narration verb (Have, Show, Case, When, Leg, …) on a line of its own,
// the arguments of a list verb (By, BySets, Simp, …) on one line within
// 100 columns and one to a line past them, any other line of code past
// them broken at a list that stands on it, and a text past them a chain
// of literals, one line each (package xugofmt); `xugo_fmt -w` is
// prescribed at every landing and is the last step a hurried
// aggregation drops. A comment column lost when a relocation changes a
// dep identifier's length, a stray blank line before a closing paren, a
// label run into its proof on one line, or a statement left on one line
// of three hundred columns passes build, vet, replay and every other
// lint here — a whitespace defect has no other detector, which is
// exactly why it needs one.
//
// The gate reads the same population every other lint does. A generated
// file is its generator's to lay out, and the formatter returns it as
// it is.
func TestLintXugoFmt(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		src, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		formatted, err := xugofmt.Source(src)
		if err != nil {
			t.Errorf("%s: does not format: %v", f, err)
			continue
		}
		if string(formatted) != string(src) {
			t.Errorf("%s: not in xugo_fmt's layout — run `go run ./library/cmd/xugo_fmt -w %s`", f, f)
		}
	}
}

// TestLintExactKeysNameCertificates: every row of a family blob's
// exact-key table names a certificate the blob holds. The table is an
// index of the certificate table (proof.CNFCache's exact_keys), read
// before a certificate's key is computed; a row whose certificate is
// gone was left behind by a write that dropped the certificate alone.
func TestLintExactKeysNameCertificates(t *testing.T) {
	rows := 0
	for _, family := range registry.Families() {
		store := family.CNFStore()
		if store == nil {
			continue
		}
		proofs := store.Proofs()
		for exact, key := range store.ExactKeys() {
			rows++
			if _, held := proofs[key]; !held {
				t.Errorf("%s: exact key %s names the certificate %s, which the family's blob does not hold — "+
					"re-key the blob (go run ./library/cmd/rekey_cnf_blob -blob <the family's .cnf.pb>)", family.Name, exact, key)
			}
		}
	}
	t.Logf("%d exact keys, each naming a certificate of its blob", rows)
}

// NO PROOF-SIDE CNF INSTALLS. Every entry's refutes replay from its
// FAMILY's shared blob, installed env-side by the harness before Build
// (replay_test.go). A proof file installing its own cache was the
// retired legacy flat corpus's pattern, and it is what made those pbs
// un-re-recordable (the recorder's warm-merge cannot warm a cache the
// proof re-installs strict over). The recorder guards this at record
// time; this lint catches it at commit time.
func TestLintNoProofSideCNFInstall(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		src, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		for i, line := range strings.Split(string(src), "\n") {
			if strings.Contains(line, "InstallCNFCache(") {
				t.Errorf("%s:%d: proof-side InstallCNFCache — refutes replay from the family blob "+
					"(harness-installed); record via XUGO_RECORD_FAMILY_CNF=<member> instead "+
					"(see record_cnf_test.go's header)", f, i+1)
			}
		}
	}
}

// EVERY MEMBER-BEARING FAMILY HAS A MEASURED (NON-EMPTY) CNF PB. The
// replay harness arms strict CNF mode only on a non-empty family blob,
// so a family at 0 bytes replays every member NON-STRICT: refutes run
// live (nondeterministic parallel search) behind a green run. The
// recorder stamps a recorded_members marker into the pb on every run —
// including a zero-refute one — so "measured, zero keys" is a non-empty
// blob and this lint can tell it from "never measured" (without the
// marker a zero-key chapter could NEVER leave the window, however many
// times it was measured). A freshly chartered family fails here until
// its first recorder run.
func TestLintFamilyPBMeasured(t *testing.T) {
	for _, f := range registry.Families() {
		if len(f.CNF) > 0 || !familyHasReplayedProof(f) {
			continue
		}
		t.Errorf("family %s has %d member(s) but an EMPTY CNF pb — every member replays "+
			"non-strict (live, nondeterministic refutes behind a green run). Measure it "+
			"(records refutes AND stamps the recorded_members marker, even at zero keys):\n"+
			"  XUGO_FAMILY_CNF_GC=%s go test -count=1 -v -run TestRecordFamilyCNF ./library/integrity/gates/\n"+
			"then re-run the family replay to re-embed and strict-verify",
			f.Name, len(f.Entries()), f.Name)
	}
}

// familyHasReplayedProof reports whether some member of f is a proof
// the replay forces and the refuter may reach: neither a card (served
// as its axiom and SKIPped) nor a definition door's entry (a
// deterministic derivation that records nothing). A family of
// definitions and cards alone — a chapter laid as a skeleton before
// any proof — has nothing to measure, and the measured-blob lint waits
// for its first proved member.
func familyHasReplayedProof(f *registry.Family) bool { return hasReplayedProof(f.Entries()) }

// hasReplayedProof is familyHasReplayedProof over a family's entries.
func hasReplayedProof(entries []*registry.ProofEntry) bool {
	for _, e := range entries {
		if e.ServedAsAxiom() || e.Definition != proof.NotADefinition || e.DefinesType() != "" {
			continue
		}
		return true
	}
	return false
}

// A family whose members are all cards and definitions needs no
// measured blob; one with a proved member does. The entries are built
// here and registered nowhere, so the verdict does not move when a
// chapter's cards are filled.
func TestFamilyWithoutProvedMemberNeedsNoBlob(t *testing.T) {
	stub := registry.Bare(func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil })
	card := &registry.ProofEntry{Name: "Card", Build: registry.BuildSpec{
		Headline: "∀n:num. n ≤ n * n", Card: &registry.CardSpec{Note: "a skeleton's open member"}}}
	definition := &registry.ProofEntry{Name: "Definition", Definition: proof.DefinitionDirect, Build: stub}
	proved := &registry.ProofEntry{Name: "Proved", Build: stub}
	if hasReplayedProof([]*registry.ProofEntry{card, definition}) {
		t.Error("a family of a card and a definition is read as holding a replayed proof")
	}
	if !hasReplayedProof([]*registry.ProofEntry{card, definition, proved}) {
		t.Error("a family with a proved member is read as holding none")
	}
}

// NO CERTIFICATE IN A FAMILY BLOB EXCEEDS THE CEILING. A certificate's
// bytes are live memory in the serve and in every replay of its family,
// and record, replay and every other lint pass a certificate of any
// size, so this gate fails a compiled-in family blob holding one above
// certificateCeilingBytes. The recorder warns well below the ceiling,
// at the write; the two lines and why each sits where it does are the
// comment beside the constants (record_cnf_test.go).
func TestLintCertificateSize(t *testing.T) {
	checked := 0
	for _, f := range registry.Families() {
		var cache proof.CNFCache
		if err := proto.Unmarshal(f.CNF, &cache); err != nil {
			t.Fatalf("family %s: unmarshal its CNF pb: %v", f.Name, err)
		}
		keys := slices.Sorted(maps.Keys(cache.Entries))
		checked += len(keys)
		for _, k := range certificatesAbove(&cache, keys, certificateCeilingBytes) {
			holders := "no member's row"
			if members := membersNaming(&cache, k); len(members) > 0 {
				holders = "the row of " + strings.Join(members, ", ")
			}
			t.Errorf("family %s: certificate %s is %d bytes, above the %d-byte ceiling; %s names it — re-spell the close at its leaf "+
				"(a dry-run record, XUGO_RECORD_FAMILY_CNF=<member> with XUGO_RECORD_CNF_DRY_RUN=1, lists the member's rows with their sizes and leaves), "+
				"re-record the member, then GC the family to retire the key",
				f.Name, k, proto.Size(cache.Entries[k]), certificateCeilingBytes, holders)
		}
	}
	if checked == 0 {
		t.Fatal("no certificate checked: the walk read no family blob")
	}
}

// membersNaming lists, sorted, the members whose row names certificate
// key k.
func membersNaming(cache *proof.CNFCache, k string) []string {
	var members []string
	for member, row := range cache.GetMemberRows() {
		if slices.Contains(row.GetCertificates(), k) {
			members = append(members, member)
		}
	}
	slices.Sort(members)
	return members
}

// TestLintMemberRowsHeld: every row a member's row record names is a
// row its family blob holds, and every member with a row record is a
// recorded member. The family GC keeps exactly what the row records
// name, so a record naming a row the blob lacks is one the GC measures
// again, and a record under a name the blob does not record is one no
// recording wrote: both are a blob written by something other than the
// recorder, the merge tool and the rekey tool.
func TestLintMemberRowsHeld(t *testing.T) {
	checked := 0
	for _, f := range registry.Families() {
		var cache proof.CNFCache
		if err := proto.Unmarshal(f.CNF, &cache); err != nil {
			t.Fatalf("family %s: unmarshal its CNF pb: %v", f.Name, err)
		}
		for _, member := range slices.Sorted(maps.Keys(cache.GetMemberRows())) {
			checked++
			if !slices.Contains(cache.RecordedMembers, member) {
				t.Errorf("family %s: member_rows has a row for %s, which recorded_members does not list", f.Name, member)
			}
			row := cache.MemberRows[member]
			for _, k := range row.GetCertificates() {
				if _, held := cache.Entries[k]; !held {
					t.Errorf("family %s: %s's row names certificate %s, which the blob lacks — GC the family", f.Name, member, k)
				}
			}
			for _, k := range row.GetPlans() {
				if _, held := cache.Plans[k]; !held {
					t.Errorf("family %s: %s's row names plan %s, which the blob lacks — GC the family", f.Name, member, k)
				}
			}
		}
	}
	t.Logf("%d member row record(s) checked", checked)
}

// familyPackageDirs returns every directory under the corpus that
// carries a family.go — i.e. every chapter package. The domain
// aggregators (nat_num/nat_num.go, sets/sets.go), the shared alphabet
// packages (sets/internal/setvocab) and this harness package are NOT
// families, and a check that walks these directories reads none of
// them: they are ordinary Go library packages.
func familyPackageDirs(t *testing.T) []string {
	t.Helper()
	var dirs []string
	err := filepath.WalkDir(corpusRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() && d.Name() == "family.go" {
			dirs = append(dirs, filepath.Dir(path))
		}
		return nil
	})
	if err != nil {
		t.Fatalf("walk: %v", err)
	}
	sort.Strings(dirs)
	return dirs
}

// A PACKAGE HAS ONE DOC COMMENT, AND IT OPENS BY NAMING THE PACKAGE.
// CONTRIBUTING.md, "Comments state the contract". The first sentence of a
// package's doc comment is the line `go doc` opens on and the line
// pkg.go.dev prints beside the package in a directory listing and in a
// search result, so every package of the module carries one, and the
// sentence begins "Package <name>" — in a main package "Command
// <name>", or the command's own name.
//
// One, because Go takes EVERY comment block touching a package clause
// and concatenates them in file-name order. A file header left against
// its clause ("step.go — …", a generator's DO NOT EDIT banner) joins
// the package's documentation without anyone choosing it, and the file
// that sorts first supplies the sentence. A header is worth keeping —
// it is the file's own provenance and mathematics — so the repair is
// one blank line between it and the `package` clause, never a
// deletion.
//
// A chapter package's one comment is generated. Its sentence is the
// title line of the chapter's README.md, the one place the chapter's
// gloss is written: typedgen.Render writes it on the package clause of
// zz_typed_thms_gen.go, and TestTypedGenCurrent holds the text. What is
// checked here is that the comment comes from that file and from no
// hand-written one.
//
// The sentence is the one go/doc cuts, and go/doc ends a sentence at
// the first period followed by a space: "an active range `0 .. n`" and
// "(e.g. a list)" both stop it early, and the listing shows the stump.
// A stump is read here by what it leaves open — a code span, a
// parenthesis — or by its not ending in a period.
//
// What no lint reads is whether the sentence is true of the package.
// That is held by reading, when the package changes.
//
// The population is every directory of the module that holds a
// non-test .go file, found by walking and never listed, so a new
// package is inside the lint from its first file. The directories the
// go tool itself passes over — a name opening with "." or "_", and
// testdata — are passed over here.
func TestLintPackageDoc(t *testing.T) {
	if _, err := os.Stat(filepath.Join(moduleRoot, "go.mod")); err != nil {
		t.Fatalf("moduleRoot %q is not the module's root: %v", moduleRoot, err)
	}
	type packageDoc struct {
		name     string   // the package clause's name
		family   bool     // the directory holds a family.go: a chapter
		files    []string // the files whose comment touches the clause, in name order
		synopsis string   // go/doc's first sentence of the first of them
	}
	packages := map[string]*packageDoc{}
	fset := token.NewFileSet()
	err := filepath.WalkDir(moduleRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		name := d.Name()
		if d.IsDir() {
			if path != moduleRoot && (strings.HasPrefix(name, ".") || strings.HasPrefix(name, "_") || name == "testdata") {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			return nil
		}
		af, err := parser.ParseFile(fset, path, nil, parser.ParseComments|parser.PackageClauseOnly)
		if err != nil {
			return err
		}
		dir, err := filepath.Rel(moduleRoot, filepath.Dir(path))
		if err != nil {
			return err
		}
		p := packages[dir]
		if p == nil {
			p = &packageDoc{name: af.Name.Name}
			packages[dir] = p
		}
		if name == "family.go" {
			p.family = true
		}
		if af.Doc != nil {
			if len(p.files) == 0 {
				p.synopsis = new(doc.Package).Synopsis(af.Doc.Text())
			}
			p.files = append(p.files, name)
		}
		return nil
	})
	if err != nil {
		t.Fatalf("walk: %v", err)
	}

	families := 0
	for _, dir := range slices.Sorted(maps.Keys(packages)) {
		p := packages[dir]
		if p.family {
			families++
			// The generated file is the one home of a chapter's doc
			// comment; a missing one is TestTypedGenCurrent's to report.
			for _, file := range p.files {
				if file != typedgen.File {
					t.Errorf("%s/%s: the comment touching the package clause becomes part of package %s's doc comment "+
						"(Go concatenates one per file).\n"+
						"    A chapter's doc comment is generated: it is the title line of %s/README.md, written into %s by "+
						"go generate. Keep this comment as a FILE header: put one blank line between it and `package %s`.",
						dir, file, p.name, dir, typedgen.File, p.name)
				}
			}
			continue
		}
		switch len(p.files) {
		case 0:
			t.Errorf("%s: package %s has no doc comment, so `go doc` and pkg.go.dev's listing say nothing of it.\n"+
				"    Write one on the package clause of ONE file, opening with what the package is: %q.",
				dir, p.name, packageDocOpening(p.name, dir)+" …")
		case 1:
			if !opensWith(p.synopsis, packageDocOpening(p.name, dir)) &&
				!(p.name == "main" && opensWith(p.synopsis, filepath.Base(dir))) {
				t.Errorf("%s/%s: package %s's doc comment opens %q.\n"+
					"    Its first sentence is the line `go doc` and pkg.go.dev's listing show for the package, "+
					"and it opens by naming it: %q. A file header that was never meant as the package's "+
					"documentation is kept as one by a blank line between it and `package %s`.",
					dir, p.files[0], p.name, p.synopsis, packageDocOpening(p.name, dir)+" …", p.name)
			}
			if cutShort(p.synopsis) {
				t.Errorf("%s/%s: go/doc reads the first sentence of package %s's doc comment as %q — not a whole sentence.\n"+
					"    go/doc ends a sentence at the first period followed by a space, and what it cuts is the line "+
					"`go doc` and pkg.go.dev's listing show. Reword the opening into one sentence that ends in a "+
					"period and has no period-then-space inside it.",
					dir, p.files[0], p.name, p.synopsis)
			}
		default:
			t.Errorf("%s: %d files attach a comment to the package clause (%s), and Go concatenates them, in that "+
				"order, into package %s's doc comment.\n"+
				"    Keep the one that says what the package is; each of the others stays a FILE header by one "+
				"blank line between it and `package %s`.",
				dir, len(p.files), strings.Join(p.files, ", "), p.name, p.name)
		}
	}
	// A walk that found nothing, or no chapter, read the wrong tree.
	if len(packages) == 0 || families == 0 {
		t.Fatalf("walked %d packages, %d of them chapters, under %q", len(packages), families, moduleRoot)
	}
}

// packageDocOpening is the words a package's doc comment opens with:
// "Package <name>", and for a command — a main package, named for its
// directory — "Command <name>".
func packageDocOpening(name, dir string) string {
	if name == "main" {
		return "Command " + filepath.Base(dir)
	}
	return "Package " + name
}

// cutShort reports whether a first sentence, as go/doc cut it, is a
// stump: it leaves a code span or a parenthesis open, or does not end
// in a period.
func cutShort(sentence string) bool {
	return !strings.HasSuffix(sentence, ".") ||
		strings.Count(sentence, "`")%2 != 0 ||
		strings.Count(sentence, "(") != strings.Count(sentence, ")")
}

// opensWith reports whether sentence opens with words, ending at a
// word boundary: "Package set" does not open "Package sets is …".
func opensWith(sentence, words string) bool {
	rest, ok := strings.CutPrefix(sentence, words)
	if !ok {
		return false
	}
	next, _ := utf8.DecodeRuneInString(rest)
	return rest == "" || !(next == '_' || unicode.IsLetter(next) || unicode.IsDigit(next))
}

// THE MODULE HAS ONE DOT IMPORT, library/authoring.
// chapter_constitution.md, "Families: a theory chapter as a sub-package".
// A proof file reads the bare names
// of the proof surface (By, Cite, Argument, Expr) through a dot import
// of library/authoring: the names are in scope in the file and are no
// declaration of the chapter's package, which is why `go doc` on a
// chapter lists the chapter's members and nothing else.
//
// One, because a dot import empties a file of its qualifiers: a reader
// of a proof file who meets a bare name has one package to look in, and
// a second dot import would make every bare name a question. The
// compiler does not mind a second.
//
// The population is every .go file of the module, tests included,
// found by walking as TestLintPackageDoc walks.
func TestLintDotImport(t *testing.T) {
	if _, err := os.Stat(filepath.Join(moduleRoot, "go.mod")); err != nil {
		t.Fatalf("moduleRoot %q is not the module's root: %v", moduleRoot, err)
	}
	fset := token.NewFileSet()
	files, carrying := 0, 0
	err := filepath.WalkDir(moduleRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		name := d.Name()
		if d.IsDir() {
			if path != moduleRoot && (strings.HasPrefix(name, ".") || strings.HasPrefix(name, "_") || name == "testdata") {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(name, ".go") {
			return nil
		}
		af, err := parser.ParseFile(fset, path, nil, parser.ImportsOnly)
		if err != nil {
			return err
		}
		files++
		rel, err := filepath.Rel(moduleRoot, path)
		if err != nil {
			return err
		}
		rel = filepath.ToSlash(rel)
		for _, imp := range af.Imports {
			p, err := strconv.Unquote(imp.Path.Value)
			if err != nil {
				return err
			}
			dot := imp.Name != nil && imp.Name.Name == "."
			switch {
			case dot && p != authoringImportPath:
				t.Errorf("%s: dot-imports %s.\n"+
					"    The module has one dot import, %s — the bare names of a proof body. "+
					"Import %s by name and qualify what the file takes from it.",
					rel, p, authoringImportPath, p)
			case dot:
				carrying++
			}
		}
		return nil
	})
	if err != nil {
		t.Fatalf("walk: %v", err)
	}
	// A walk that found no file carrying the import read the wrong tree,
	// or the surface has moved and authoringImportPath names nothing.
	if files == 0 || carrying == 0 {
		t.Fatalf("walked %d .go files under %q, %d of them dot-importing %s", files, moduleRoot, carrying, authoringImportPath)
	}
}

// AN ENVIRONMENT VARIABLE THE CODE READS IS A ROW OF CONTRIBUTING'S
// TABLE, AND A ROW IS A VARIABLE THE CODE READS. CONTRIBUTING.md,
// "Environment variables". A switch read from the environment is
// invisible at its call site and in the tool's help: unlisted, it is a
// behaviour nobody can find, and once its reader is deleted the
// documents go on recommending a variable that does nothing. So the
// table is held from both sides, and so is every other mention:
//
//   - a name some Go file holds as a string literal of its own — the
//     argument of an os.Getenv, the constant a harness reads through —
//     is a row;
//   - a row is such a literal somewhere, or nothing reads it;
//   - a name written anywhere else — a comment, an error message, a
//     README, the skill, the agent file, the CI workflow — is a row, so
//     no text sends a reader to a variable that is not there.
//
// The population is every .go and .md file of the module, the pipeline's
// documents under .claude/, .agents/ and .gemini/, and the CI workflows. The
// dated working files under working_state/ are a log of what was once
// run and are not read.
func TestLintEnvVarTable(t *testing.T) {
	if _, err := os.Stat(filepath.Join(moduleRoot, "go.mod")); err != nil {
		t.Fatalf("moduleRoot %q is not the module's root: %v", moduleRoot, err)
	}
	const tableFile = "CONTRIBUTING.md"

	// The rows: the names in the first cell of a table line.
	rows := map[string]bool{}
	table, err := os.ReadFile(filepath.Join(moduleRoot, tableFile))
	if err != nil {
		t.Fatal(err)
	}
	for _, line := range strings.Split(string(table), "\n") {
		if !strings.HasPrefix(line, "| `") {
			continue
		}
		cell, _, _ := strings.Cut(line[2:], " |")
		for _, name := range envVarName.FindAllString(cell, -1) {
			rows[name] = true
		}
	}

	read := map[string]string{}        // name → where a Go file holds it as a literal of its own
	mentioned := map[string][]string{} // name → the places that write it
	scan := func(path string) error {
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(moduleRoot, path)
		if err != nil {
			return err
		}
		for i, line := range strings.Split(string(src), "\n") {
			for _, name := range envVarName.FindAllString(line, -1) {
				mentioned[name] = append(mentioned[name], fmt.Sprintf("%s:%d", rel, i+1))
			}
		}
		if !strings.HasSuffix(path, ".go") {
			return nil
		}
		fset := token.NewFileSet()
		var sc scanner.Scanner
		sc.Init(fset.AddFile(path, fset.Base(), len(src)), src, nil, 0)
		for {
			pos, tok, lit := sc.Scan()
			if tok == token.EOF {
				return nil
			}
			if tok != token.STRING {
				continue
			}
			if name, err := strconv.Unquote(lit); err == nil && envVarName.FindString(name) == name && name != "" {
				if _, seen := read[name]; !seen {
					read[name] = fmt.Sprintf("%s:%d", rel, fset.Position(pos).Line)
				}
			}
		}
	}
	walk := func(root string, exts ...string) {
		err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			name := d.Name()
			if d.IsDir() {
				if path != root && (strings.HasPrefix(name, ".") || name == "working_state") {
					return filepath.SkipDir
				}
				return nil
			}
			if slices.Contains(exts, filepath.Ext(name)) {
				return scan(path)
			}
			return nil
		})
		if err != nil {
			t.Fatalf("walk %s: %v", root, err)
		}
	}
	walk(moduleRoot, ".go", ".md")
	// The dot-directories a walk passes over that hold published text.
	for _, dir := range []string{".claude/skills", ".claude/agents", ".agents/skills", ".gemini/skills"} {
		walk(filepath.Join(moduleRoot, dir), ".md")
	}
	walk(filepath.Join(moduleRoot, ".github"), ".yml", ".yaml")

	if len(rows) == 0 || len(read) == 0 {
		t.Fatalf("%d table rows, %d variables read — the table or the tree was not found", len(rows), len(read))
	}
	for _, name := range slices.Sorted(maps.Keys(mentioned)) {
		if rows[name] {
			continue
		}
		if at, ok := read[name]; ok {
			t.Errorf("%s: the code reads this variable (%s) and %s's table has no row for it.\n"+
				"    Add the row, under \"Environment variables\": what reads it and what it changes.", name, at, tableFile)
		} else {
			t.Errorf("%s: named at %s, and it is not a row of %s's table — no code reads a variable of that name.\n"+
				"    A reader sent to it sets nothing: correct the name or take the mention out.",
				name, strings.Join(mentioned[name], ", "), tableFile)
		}
	}
	for _, name := range slices.Sorted(maps.Keys(rows)) {
		if _, ok := read[name]; !ok {
			t.Errorf("%s: a row of %s's table, and no Go file holds the name as a string literal of its own — nothing reads it.\n"+
				"    Delete the row, and the mentions with it.", name, tableFile)
		}
	}
}

// envVarName is the shape of an environment variable the module reads:
// the XUGO_ prefix and an upper-case name after it.
var envVarName = regexp.MustCompile(`XUGO_[A-Z0-9_]*[A-Z0-9]`)

// moduleRoot is the module's root, relative to this package's
// directory as corpusRoot is.
const moduleRoot = "../../.."

// isoDate is a date as a comment would carry one: year, month and day
// in digits, hyphenated.
var isoDate = regexp.MustCompile(`20\d\d-\d\d-\d\d`)

// A COMMENT CARRIES NO DATE. CONTRIBUTING.md, "Comments state the contract":
// a comment says what the code beside it does now, and git holds the
// history. A date is the one mark of a narrating comment that can be
// read mechanically — it says when a fix was made, a census taken or a
// ruling given, none of which the code beside it does. The section's
// other marks ("landed", "renamed from", the account of an earlier
// version) are ordinary English in true sentences — "a landed card" —
// and are held by reading, not here.
//
// The population is every .go file of the module, hand-written and
// generated, tests included. A generated file that fails is repaired
// in its generator. Comments are read through the scanner, so a date
// in a string literal — test data — is not a comment and passes.
func TestLintNoDateInComment(t *testing.T) {
	if _, err := os.Stat(filepath.Join(moduleRoot, "go.mod")); err != nil {
		t.Fatalf("moduleRoot %q is not the module's root: %v", moduleRoot, err)
	}
	scanned := 0
	err := filepath.WalkDir(moduleRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		name := d.Name()
		if d.IsDir() {
			if strings.HasPrefix(name, ".") && path != moduleRoot {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(name, ".go") {
			return nil
		}
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		scanned++
		rel, err := filepath.Rel(moduleRoot, path)
		if err != nil {
			return err
		}
		fset := token.NewFileSet()
		var s scanner.Scanner
		s.Init(fset.AddFile(path, fset.Base(), len(src)), src, nil, scanner.ScanComments)
		for {
			pos, tok, lit := s.Scan()
			if tok == token.EOF {
				break
			}
			if tok != token.COMMENT {
				continue
			}
			first := fset.Position(pos).Line
			for i, line := range strings.Split(lit, "\n") {
				if date := isoDate.FindString(line); date != "" {
					t.Errorf("%s:%d: a comment carries the date %s — a comment says what the code beside it "+
						"does now (CONTRIBUTING.md, \"Comments state the contract\"); git holds when it changed.\n"+
						"    State the present contract and drop the date; a measurement keeps its number "+
						"only where the code still relies on it.",
						rel, first+i, date)
				}
			}
		}
		return nil
	})
	if err != nil {
		t.Fatalf("walk: %v", err)
	}
	if scanned == 0 {
		t.Fatalf("no .go file found under %s", moduleRoot)
	}
	t.Logf("%d .go files scanned", scanned)
}

// harnessSection is the heading of the one section of the /prove skill
// that maps the pipeline to the supported harnesses.
const harnessSection = "# The harness"

// harnessWord names harness-specific tools, parameters, paths and
// configuration. These belong in the adapter section, not the shared
// proof instructions.
var harnessWord = regexp.MustCompile("subagent_type|run_in_background|isolation: ?\"worktree\"|`general-purpose`|" +
	"\\.claude/worktrees|`Agent`|TaskCreate|TaskUpdate|ScheduleWakeup|settings\\.local|Claude Code|" +
	"Codex|collaboration\\.|fork_turns|create_worktree|list_artifacts|create_thread|" +
	"Antigravity|Gemini CLI|define_subagent|invoke_subagent|manage_subagents|" +
	"BypassSandbox|IsDaemon|WaitMsBeforeAsync|activate_skill|run_shell_command|codebase_investigator")

// THE HARNESS IS ONE SECTION. The /prove skill and the prover agent's
// file share their proof instructions; the skill's section "The
// harness" maps their execution to Claude Code, Codex and Gemini. A port
// to another harness adds its mapping there. AGENTS.md and README.md
// repeat the claim to a reader on another harness. It is
// true only while no other section spells the harness's vocabulary,
// and that is what is read here: past its frontmatter, the agent file
// has none of harnessWord, and the skill has it inside the section
// alone. Everywhere else the two files say "dispatch", "in the
// background", "isolated", "generic sub-agent".
func TestLintHarnessInOneSection(t *testing.T) {
	for _, doc := range []struct {
		path       string
		hasSection bool
	}{
		{".claude/skills/prove/SKILL.md", true},
		{".claude/agents/xugo-prover.md", false},
	} {
		src, err := os.ReadFile(filepath.Join(moduleRoot, doc.path))
		if err != nil {
			t.Fatalf("%s: %v", doc.path, err)
		}
		lines := strings.Split(string(src), "\n")
		if lines[0] != "---" {
			t.Fatalf("%s does not open with its frontmatter", doc.path)
		}
		body := slices.Index(lines[1:], "---") + 2
		if body < 2 {
			t.Fatalf("%s: the frontmatter is not closed", doc.path)
		}
		sections, inSection, inFence := 0, false, false
		for i := body; i < len(lines); i++ {
			line := lines[i]
			if strings.HasPrefix(strings.TrimSpace(line), "```") {
				inFence = !inFence
			}
			// A top-level heading opens a section; inside a code fence a
			// line that starts with "# " is a shell comment.
			if !inFence && strings.HasPrefix(line, "# ") {
				inSection = doc.hasSection && line == harnessSection
				if inSection {
					sections++
				}
			}
			if inSection {
				continue
			}
			word := harnessWord.FindString(line)
			// A two-word harness name may wrap between lines in prose.
			if word == "" && i+1 < len(lines) {
				prev, next := strings.TrimRight(line, " "), strings.TrimLeft(lines[i+1], " ")
				switch {
				case strings.HasSuffix(prev, "Claude") && strings.HasPrefix(next, "Code"):
					word = "Claude Code"
				case strings.HasSuffix(prev, "Gemini") && strings.HasPrefix(next, "CLI"):
					word = "Gemini CLI"
				}
			}
			if word != "" {
				t.Errorf("%s:%d: %s is the harness's word, outside the skill's section %q — the two files name "+
					"the harness in that section alone, so that a port rewrites it and nothing else.\n"+
					"    Say it in the section's terms (dispatch, in the background, isolated, generic sub-agent), "+
					"or move the sentence into the section.",
					doc.path, i+1, word, harnessSection)
			}
		}
		if doc.hasSection && sections != 1 {
			t.Errorf("%s has %d sections headed %q, and the pipeline's claim on a harness is stated in exactly one",
				doc.path, sections, harnessSection)
		}
	}
}

// The /prove skill is edited under skillSource, where the harness it
// is packaged for finds it. skillCopies hold the same files for
// harnesses that look for a skill there.
const skillSource = ".claude/skills"

var skillCopies = []string{".agents/skills", ".gemini/skills"}

// THE SKILL'S COPIES ARE ITS SOURCE. Each copy is made of plain files: a
// symbolic link is not one, which CI refuses of every tracked file, and
// a checkout need not follow it. So nothing but this test keeps the
// trees one text, and it reads them file for file and byte for byte: a
// file of the source with no copy or a stale one, and a file of a copy
// the source does not have, each fail and name the command.
func TestLintSkillCopyCurrent(t *testing.T) {
	source := skillFiles(t, skillSource)
	if len(source) == 0 {
		t.Fatalf("no file found under %s", skillSource)
	}
	for _, copyTree := range skillCopies {
		copied := skillFiles(t, copyTree)
		for _, rel := range slices.Sorted(maps.Keys(source)) {
			from, to := path.Join(skillSource, rel), path.Join(copyTree, rel)
			const edit = "%s is the file to edit, %s its copy"
			regenerate := fmt.Sprintf("run mkdir -p %s && cp %s %s", path.Dir(to), from, to)
			got, ok := copied[rel]
			switch {
			case !ok:
				t.Errorf("%s missing — "+edit+"; %s", to, from, to, regenerate)
			case !bytes.Equal(got, source[rel]):
				t.Errorf("%s stale — "+edit+"; %s", to, from, to, regenerate)
			}
		}
		for _, rel := range slices.Sorted(maps.Keys(copied)) {
			if _, ok := source[rel]; !ok {
				t.Errorf("%s is a copy of no file under %s — a skill is written there and copied here; "+
					"move it there, or delete it", path.Join(copyTree, rel), skillSource)
			}
		}
	}
}

// skillFiles reads the files under a skill tree, keyed by their
// slash-separated path below it. A .DS_Store, which .gitignore names,
// is a file of none of them.
func skillFiles(t *testing.T, tree string) map[string][]byte {
	t.Helper()
	root := filepath.Join(moduleRoot, filepath.FromSlash(tree))
	files := map[string][]byte{}
	err := filepath.WalkDir(root, func(file string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() || d.Name() == ".DS_Store" {
			return nil
		}
		rel, err := filepath.Rel(root, file)
		if err != nil {
			return err
		}
		rel = filepath.ToSlash(rel)
		if !d.Type().IsRegular() {
			t.Errorf("%s is not a plain file — the copy is a copy, never a link to its source", path.Join(tree, rel))
			return nil
		}
		src, err := os.ReadFile(file)
		if err != nil {
			return err
		}
		files[rel] = src
		return nil
	})
	if err != nil {
		t.Fatalf("walk %s: %v", tree, err)
	}
	return files
}

func TestLintNoMachineTypeVarsInText(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		if why, allowed := machineTypeVarAllowlist[chapterRel(f)]; allowed {
			t.Logf("allowlisted %s: %s", f, why)
			continue
		}
		src, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		for _, loc := range machineTypeVarInText.FindAllIndex(src, -1) {
			line := 1 + strings.Count(string(src[:loc[0]]), "\n")
			t.Errorf("%s:%d: machine type-var name %q in chapter text — "+
				"compute the install form from the dep cert instead "+
				"(NormalizedThm / AtTypes; see file header of lint_test.go)",
				f, line, src[loc[0]:loc[1]])
		}
	}
}

// ---------------------------------------------------------------------------
// NO ASSERT STAIRCASES. Sequential facts are spelled as a flat
// Deduce / Have / Show block (constitution §"Argument structure", the
// operational rules): k right-nested AssertStep claim/after pairs are the
// staircase whose "after" labels cannot carry mathematical content
// (the i-th residual has no independent identity to name). The lint
// flags the structural core of the pattern: an AssertStep call
// appearing directly (descending through Chain only) in the body of
// another AssertStep's SECOND Case — the claim/after continuation.
//
// What it deliberately does NOT flag: an assert nested inside a
// genuine branching construct in the after-Case (ByCaseStep /
// Split* / InductStep branches are separate arguments), an assert
// inside the CLAIM Case (a sub-argument — prefer an inner Deduce,
// but that is fresh-eye guidance, not lint), and the method-
// fragmented variant (a helper call returning the next AssertStep) —
// cross-function shape is fresh-eye territory.
//
// Allowlist is shrink-only, same contract as the type-var lint.
var assertStaircaseAllowlist = map[string]string{}

// calleeName returns the terminal identifier of a call's function
// expression: `AssertStep` for both the bare alias and the
// p.ctx.AssertStep method form.
func calleeName(call *ast.CallExpr) string {
	switch fn := call.Fun.(type) {
	case *ast.Ident:
		return fn.Name
	case *ast.SelectorExpr:
		return fn.Sel.Name
	}
	return ""
}

func flagStaircase(t *testing.T, fset *token.FileSet, file string, body []ast.Expr) {
	for _, e := range body {
		call, ok := e.(*ast.CallExpr)
		if !ok {
			continue
		}
		switch calleeName(call) {
		case "AssertStep":
			pos := fset.Position(call.Pos())
			t.Errorf("%s:%d: AssertStep nested in another AssertStep's after-Case — "+
				"sequential facts use a flat Deduce/Have/Show block "+
				"(constitution §\"Argument structure\"; the desugar is tree-identical, pbs keep hitting)",
				file, pos.Line)
		case "Chain":
			flagStaircase(t, fset, file, call.Args)
		}
	}
}

func TestLintNoAssertStaircase(t *testing.T) {
	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		if why, allowed := assertStaircaseAllowlist[chapterRel(f)]; allowed {
			t.Logf("allowlisted %s: %s", f, why)
			continue
		}
		node, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		ast.Inspect(node, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || calleeName(call) != "AssertStep" || len(call.Args) < 3 {
				return true
			}
			afterCase, ok := call.Args[2].(*ast.CallExpr)
			if !ok {
				return true
			}
			if name := calleeName(afterCase); name != "Case" && name != "MakeCase" {
				return true
			}
			if len(afterCase.Args) > 1 {
				flagStaircase(t, fset, f, afterCase.Args[1:])
			}
			return true
		})
	}
}

// parseChapterFile parses one file; the caller walks the AST.
func parseChapterFile(t *testing.T, f string) (*token.FileSet, *ast.File) {
	t.Helper()
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, f, nil, 0)
	if err != nil {
		t.Fatalf("parse %s: %v", f, err)
	}
	return fset, node
}

// labelCallees are the labeled proof constructors, mapped to the
// argument index carrying their documentation label (a label is prose,
// not parsed text). Calc legs name their target term first, so their
// label sits at index 1; FinalLeg has no target and leads with it.
var labelCallees = map[string]int{
	"Case": 0, "Have": 0, "Show": 0,
	"Obtain": 0, "Obtain2": 0, "Obtain3": 0, "Obtain4": 0, "Obtain5": 0, "ObtainChosen": 0,
	"FinalLeg": 0,
	"Leg":      1, "LeLeg": 1, "EqLeg": 1,

	// The named branches: a claimed branch's label is prose exactly as
	// a Case label is, and it is the ONLY label the branch carries.
	// (prover/proof/branch.go, iff_direction.go)
	"When": 0, "Otherwise": 0, "Base": 0, "Step": 0,
	"Forward": 0, "Backward": 0, "BothHold": 0, "NeitherHolds": 0,
	"LeftHolds": 0, "RightHolds": 0,
	// A dismissed disjunct is a branch too. (prover/proof/fact.go,
	// hyp_handle.go)
	"DismissLeft": 0, "DismissRight": 0,
}

// labelArg returns the label of a labeled-constructor call: the
// expression that spells it, a string literal or a chain of them laid
// out over lines (xugofmt.StringValue), and its text; false where the
// call is no labeled constructor's or its label is not written so.
func labelArg(call *ast.CallExpr) (ast.Expr, string, bool) {
	// Case/Leg/FinalLeg are called bare; Have/Show are METHODS on the
	// Argument (`a.Have(...)`), and a typed verb (`a.ObtainAs[T](...)`) is
	// a generic instantiation read as its untyped twin — verbName reads
	// all three, so no labeled verb is exempted by its spelling.
	i, ok := labelCallees[verbName(call)]
	if !ok || len(call.Args) <= i {
		return nil, "", false
	}
	text, ok := xugofmt.StringValue(call.Args[i])
	return call.Args[i], text, ok
}

// stringLiterals are the string literals e is written with: e itself,
// or the literals of a chain joined by `+`.
func stringLiterals(e ast.Expr) []*ast.BasicLit {
	var lits []*ast.BasicLit
	ast.Inspect(e, func(n ast.Node) bool {
		if lit, ok := n.(*ast.BasicLit); ok && lit.Kind == token.STRING {
			lits = append(lits, lit)
		}
		return true
	})
	return lits
}

// labelVerb names the labeled constructor a call invokes ("Case",
// "Have", "Show", …), whether it is called bare or as a method; a typed
// verb by its untyped twin (verbName).
func labelVerb(call *ast.CallExpr) string {
	if name := verbName(call); name != "" {
		return name
	}
	return "label"
}

// TestLintNoTurnstileInStatementText: every string literal of a proof
// file is statement or claim text — a constructor headline, a section
// statement, a claim, a located hypothesis, a chapter helper's
// statement argument — except the prose ones: a label (labelArg), a
// card's note, a member's Reading. None of the text spells ⊢ (see the
// file header). Reading every literal rather than a verb list is what
// keeps a statement handed through a chapter's own helper in scope.
func TestLintNoTurnstileInStatementText(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		fset, node := parseChapterFile(t, f)
		prose := map[*ast.BasicLit]bool{}
		ast.Inspect(node, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.KeyValueExpr:
				if id, ok := n.Key.(*ast.Ident); ok && id.Name == "Reading" {
					for _, lit := range stringLiterals(n.Value) {
						prose[lit] = true
					}
				}
			case *ast.CallExpr:
				if label, _, ok := labelArg(n); ok {
					for _, lit := range stringLiterals(label) {
						prose[lit] = true
					}
				}
				if verbName(n) == "Card" && len(n.Args) > 1 {
					for _, lit := range stringLiterals(n.Args[1]) {
						prose[lit] = true
					}
				}
			}
			return true
		})
		ast.Inspect(node, func(n ast.Node) bool {
			lit, ok := n.(*ast.BasicLit)
			if !ok || lit.Kind != token.STRING || prose[lit] {
				return true
			}
			text, err := strconv.Unquote(lit.Value)
			if err != nil || !strings.Contains(text, "⊢") {
				return true
			}
			t.Errorf("%s: the text spells ⊢ — a statement is closed: ∀-bind its variables and ⇒ its "+
				"premises, one antecedent per Fact parameter (see file header of lint_test.go)\n  %s",
				fset.Position(lit.Pos()), text)
			return true
		})
	}
}

const maxCaseLabelRunes = 140

func TestLintCaseLabelLength(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		fset, node := parseChapterFile(t, f)
		ast.Inspect(node, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) == 0 {
				return true
			}
			lit, label, ok := labelArg(call)
			if !ok {
				return true
			}
			if n := utf8.RuneCountInString(label); n > maxCaseLabelRunes {
				t.Errorf("%s: %s label is %d runes (max %d) — state the "+
					"branch's mathematical move; name recurring quantities "+
					"instead of quoting them (see file header of lint_test.go)",
					fset.Position(lit.Pos()), labelVerb(call), n, maxCaseLabelRunes)
			}
			return true
		})
	}
}

// structuralLabelTokens name a branch's POSITION in the step that fans
// it — which conjunct, which side of an assertion or a case split,
// which half of an induction — and never what the branch proves. One
// is refused as a whole label and as a `token:` prefix;
// `left-commutativity — …` and `after removing the cut …` open with
// the same word and are mathematics.
//
// The set holds every role tag `emit-section` leads a rendered branch
// label with (TestLintRefusesEveryEmittedRoleTag), so a pasted branch
// is refused until its label is restated.
var structuralLabelTokens = map[string]bool{
	"claim": true, "after": true, "residual": true, "premise": true,
	"left": true, "right": true,
	"true": true, "false": true,
	"base": true, "step": true,
	"forward": true, "backward": true,
}

// numberedCaseToken is the emitter's tag for a branch it has no role
// name for — the constitution's "step number".
var numberedCaseToken = regexp.MustCompile(`^case_[0-9]+$`)

// structuralLabelToken returns the structural token a label leads
// with, and whether it leads with one. Under `Base` and `Step` the
// verb's own word is refused as the label's first word whatever
// follows it: `a.Base("base n = 0: …")` is `base: …` with the instance
// moved inside the prefix, and the verb has already said it.
func structuralLabelToken(verb, label string) (string, bool) {
	label = strings.TrimSpace(label)
	end := strings.IndexFunc(label, func(r rune) bool {
		return !unicode.IsLetter(r) && !unicode.IsDigit(r) && r != '_'
	})
	if end < 0 {
		end = len(label)
	}
	word, rest := strings.ToLower(label[:end]), label[end:]
	if !structuralLabelTokens[word] && !numberedCaseToken.MatchString(word) {
		return "", false
	}
	ownVerb := (verb == "Base" || verb == "Step") && word == strings.ToLower(verb)
	if rest == "" || strings.HasPrefix(rest, ":") || ownVerb {
		return word, true
	}
	return "", false
}

// TestLintRefusesEveryEmittedRoleTag holds the lint to the emitter: a
// role tag the emitter writes and this lint let through would be a
// rendered label no gate reads.
func TestLintRefusesEveryEmittedRoleTag(t *testing.T) {
	for _, tag := range append(emit.CaseRoleTags(), "case_0", "case_12") {
		for _, label := range []string{tag, tag + ": x ≤ y"} {
			if _, refused := structuralLabelToken("Case", label); !refused {
				t.Errorf("label %q leads with the emitter's role tag %q and is not refused", label, tag)
			}
		}
	}
}

func TestLintNoStructuralTokenInLabel(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		fset, node := parseChapterFile(t, f)
		ast.Inspect(node, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) == 0 {
				return true
			}
			lit, label, ok := labelArg(call)
			if !ok {
				return true
			}
			if token, ok := structuralLabelToken(labelVerb(call), label); ok {
				t.Errorf("%s: %s label leads with the structural token %q — "+
					"a label is one mathematical sentence saying what the "+
					"branch proves; its position is in the verb, or in what "+
					"the sentence says (constitution §\"Argument structure: "+
					"flat chain → named cases\")",
					fset.Position(lit.Pos()), labelVerb(call), token)
			}
			return true
		})
	}
}

// ---------------------------------------------------------------------------
// NO UNGROUND CITE PILES. A proof puts its argument into the
// kernel-checked body. The defect this lint names is the opposite: the
// body is a pile of wide ∀-facts installed WITHOUT witnesses, closed by
// a single refutation, while the surrounding comment narrates a
// multi-step chain that only the refuter ever reconstructs. Deleting
// the comments deletes the proof's content — the body-only
// reconstruction test of constitution §"Argument structure" (the operational
// rule "the argument lives in the checked layer" and its composition
// closing-form ladder).
//
// The older quality bar counts consecutive CLOSE Actions (two-plus
// CnfRefute / Basic), so it triggers on *existing* structure. A pile of
// unground cites terminated by ONE refute has no structure to trigger
// on: it passes the letter of the flat-chain rule while violating its
// spirit. This lint closes that hole by counting the INSTALLS instead.
//
// The ladder the flag points at: L0 bare (~3 installs + one refute —
// legal when the honest justification names no intermediate; model
// nat_arith.AddClauses), L1 ground CiteSpecialize witnesses
// spelling the chain's waypoints (model real/tower/real_completeness's
// arch lemma), L2 Deduce/Have/Show, L3 CalcEq / CalcRel.Calc. The
// level is chosen by the argument's complexity, so the bar sits at the
// top of L0: a run of FOUR unground installs is the flag.
//
// Counting rules, and why:
//
// - COUNTED: bare Cite (one argument — a dep/cert, no witnesses),
// plus the legacy UseLemma / UseLemmaExact (single-argument by
// signature) — every such call is by construction an unground
// install. Any receiver form counts; only the terminal selector
// is read (bare, goal.X, p.field.X). Cite WITH witnesses is the
// ground form (the old CiteSpecialize) and is not counted.
// - NOT COUNTED, and NEUTRAL (a run survives across them):
// Cite(dep, w…) / CiteKeep / CiteSpecialize / CiteSpecializeKeep /
// UseLemmaSpecialize put the
// INSTANCE in the checked layer, and hygiene steps (StripQuant,
// Clear, Basic, DefExpandStep, Ground, …) are not installs at all.
// Neutral rather than resetting on purpose: a hygiene step wedged
// between two cites must not launder a pile, and neither should a
// single ground cite dropped into the middle of eight wide ones.
// - Cite is a CLOSE (prover/proof/script.go: _KnownThmStep), not an
// install — a different population, left to the close-run bar.
// - RESET: the constructs that put a step of the argument into the
// checked layer or fork it — Case/Have/Show/Deduce/Assuming/
// Unless/Suffices/Leg/FinalLeg/CalcEq/Calc, plus the branching
// forms whose arms are separate arguments (AssertStep, InductStep,
// ByCaseStep, Split*). Their bodies are then scanned as fresh
// runs of their own, so structure cannot hide a pile inside a
// branch.
// - A run also resets at every function and SECTION boundary. Runs
// are followed through the three carriers the corpus actually
// uses: Chain(…) argument lists, statement sequences
// (goal.Do(…) / goal.UseLemmaExact(…) side by side), and the
// handle-binding wrappers From / KeepAs, whose argument IS the
// install (an `h.From(UseLemmaExact(…))` ladder). A statement-level
// action names the goal node it acts
// on, so a change of receiver marks the section boundary — two
// sections proved side by side in one Build function (a canonical
// form, then the goal) are two sequences.
// Cross-function shape — a helper method returning the next slab
// of Actions — is fresh-eye territory, same boundary the
// assert-staircase lint draws.
// - An install bound to a handle that is later GROUNDED is not
// counted: `h.From(UseLemmaExact(L))` … `inst.From(h.GroundKeep(w…))`
// is CiteSpecialize(L, w…) in two moves, and the witnesses land in
// the checked layer either way. The install-then-ground pair is L1,
// not a pile.
//
// The allowlist is shrink-only, same contract as the type-var lint: an
// entry is deleted as its file converts. Never grow it — a new pile is
// the thing the lint exists to stop.
// ---------------------------------------------------------------------------

// maxUngroundInstallRun — a run STRICTLY GREATER than this is flagged.
// 3 is the top of the ladder's L0 (~3 installs plus one refute).
const maxUngroundInstallRun = 3

// closeVerbs: the Actions that finish a leaf. A cite pile TERMINATED BY
// a close is the shape the chain-comment census correlates against.
var closeVerbs = map[string]bool{
	"CnfRefute": true, "Basic": true,
	"CloseByAuto": true, "CloseByNormalize": true,
	"TrivialNormalized": true, "TrivialSimplify": true,
}

// ungroundInstallVerbs: the wide-∀ install verbs that carry no witness
// terms. UseLemma/UseLemmaExact are single-argument by signature
// (prover/proof/action.go); Cite is variadic and counts ONLY at one argument
// (the scanner's len(e.Args) == 1 guard) — Cite-with-witnesses is the
// ground form.
var ungroundInstallVerbs = map[string]bool{
	"UseLemma":      true,
	"UseLemmaExact": true,
	"Cite":          true,
}

// actionSeqPassthrough: wrappers a run continues THROUGH — sequencing
// combinators and the handle-binding surfaces whose argument is itself
// the install.
var actionSeqPassthrough = map[string]bool{
	"Chain": true, "Do": true,
	"From": true, "KeepAs": true,
}

// argumentStructure: constructs that interrupt a run — either they put
// a named step of the argument into the checked layer, or they fork it
// into arms that are separate arguments.
var argumentStructure = map[string]bool{
	"Case": true, "MakeCase": true,
	// The statement-form splits: an opener forks the argument and each
	// branch verb is a separate arm, exactly as a Case body is. Without
	// these the pile scanner walked THROUGH a split as if it were
	// sequencing (prover/proof/branch.go).
	"Cases": true, "Induct": true, "Iff": true,
	"When": true, "Otherwise": true, "Base": true, "Step": true,
	"Forward": true, "Backward": true, "BothHold": true, "NeitherHolds": true,
	"LeftHolds": true, "RightHolds": true,
	"Deduce":   true,
	"Assuming": true, "Unless": true, "Suffices": true,
	"CalcEq": true, "Calc": true,
	"AssertStep": true, "InductStep": true, "ByCaseStep": true,
	"SplitDisj": true, "SplitDisjAt": true, "SplitIff": true,
	"SplitConj": true, "SplitConjAll": true,
	"SplitHypIff": true, "SplitHypImply": true,
}

// claimBearing: constructors whose label/claim IS an author-stated
// checked waypoint (a Have's Prop, a Show's labeled close, a Calc
// leg's target term). Installs inside their bodies justify that ONE
// named step — the argument-in-the-checked-layer invariant is already
// satisfied at the step's granularity — so the pile scanner does not
// count them: four wide installs discharging a single checked claim
// are not four phantom chain links. A genuinely hidden chain inside
// such a body still surfaces through the chain-comment census, which
// reads docs, not bodies. Case is deliberately NOT here: its label
// describes a machine-made branch goal, and a long bare pile in a Case
// body is exactly the population this lint exists to flag.
var claimBearing = map[string]bool{
	"Have": true, "Show": true,
	"Leg": true, "LeLeg": true, "EqLeg": true, "FinalLeg": true,
}

// citePileScan walks one file's action sequences, carrying the
// length of the run of unground installs in progress.
// citeRun is one completed run of unground installs.
type citeRun struct {
	sites  []string // "file:line: verb", in order
	closed bool     // a close Action (CnfRefute / Basic / …) followed it
	decl   string   // enclosing top-level declaration, for doc lookup
}

type citePileScan struct {
	fset *token.FileSet
	file string
	decl string // top-level declaration currently being walked

	run       []string // sites of the run in progress
	runClosed bool     // a close Action was seen while the run stood
	runs      []citeRun

	// grounded: handle names that are somewhere the receiver of a
	// Ground / GroundKeep call. `h.From(UseLemmaExact(L))` followed by
	// `inst.From(h.GroundKeep(w…))` is the two-step spelling of
	// CiteSpecialize(L, w…) — the witnesses ARE in the checked layer,
	// so that install is not part of an unground pile. Collected
	// file-wide (handle vars are function-local, so the only effect of
	// the wider scope is to under-flag, never to over-flag).
	grounded map[string]bool

	// groundedFactSources: rendered source expressions of the deps whose
	// RESIDENT factorial is grounded with witnesses. The Fact-layer spelling
	// of a grounded install splits into two statements — `Cite(D)`, then
	// `f := a.Hyp(ctx.DepNormalized(D))`, then `f.At(w…)` — so the
	// install and its witnesses do not share a syntax node the way
	// `h.From(Cite(D))` + `h.GroundKeep(w…)` do. Every sub-expression of
	// a grounded a.Hyp's argument is recorded here, and an install whose
	// target renders to one of them is grounded after all.
	groundedFactSources map[string]bool

	mute int // >0 while inside a grounded handle's binding
}

func (s *citePileScan) hit(call *ast.CallExpr, verb string) {
	if s.mute > 0 || s.installGroundedAsFact(call) {
		return
	}
	pos := s.fset.Position(call.Pos())
	s.run = append(s.run, fmt.Sprintf("%s:%d: %s", s.file, pos.Line, verb))
}

// installGroundedAsFact reports whether the install's target is a dep
// whose resident Fact is grounded with witnesses elsewhere — the
// Fact-layer counterpart of bindsGroundedHandle.
func (s *citePileScan) installGroundedAsFact(call *ast.CallExpr) bool {
	if len(call.Args) != 1 {
		return false
	}
	return s.groundedFactSources[types.ExprString(call.Args[0])]
}

// bindsGroundedHandle reports whether call is `h.From(…)` / `h.KeepAs(…)`
// for a handle h that gets grounded with witnesses elsewhere.
func (s *citePileScan) bindsGroundedHandle(call *ast.CallExpr) bool {
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return false
	}
	return s.grounded[types.ExprString(sel.X)]
}

// flush ends the run in progress, banking it if it is over the bar.
func (s *citePileScan) flush() {
	if len(s.run) >= 2 {
		s.runs = append(s.runs, citeRun{sites: s.run, closed: s.runClosed, decl: s.decl})
	}
	s.run = nil
	s.runClosed = false
}

// sub scans exprs as a sequence of their own, leaving the run in
// progress untouched — a nested body inside a neutral or structural
// call is its own argument.
func (s *citePileScan) sub(exprs []ast.Expr) {
	saved, savedClosed := s.run, s.runClosed
	s.run, s.runClosed = nil, false
	for _, e := range exprs {
		s.expr(e)
	}
	s.flush()
	s.run, s.runClosed = saved, savedClosed
}

// block scans a statement list as a sequence: the run spans adjacent
// statements (goal.UseLemmaExact(…) three lines running) and ends at
// the block boundary.
func (s *citePileScan) block(list []ast.Stmt) {
	saved, savedClosed := s.run, s.runClosed
	s.run, s.runClosed = nil, false
	recv := ""
	for _, st := range list {
		// A statement-level action names the goal node it acts on
		// (`canonical.Do(…)` then `goal.Do(…)`). A change of receiver is
		// a SECTION boundary — two sections proved side by side in one
		// Build function are two sequences, not one.
		if es, ok := st.(*ast.ExprStmt); ok {
			if r := stmtReceiver(es.X); r != recv {
				s.flush()
				recv = r
			}
		}
		switch st := st.(type) {
		case *ast.ExprStmt:
			s.expr(st.X)
		case *ast.AssignStmt:
			// Term / handle bookkeeping between action statements is
			// neutral; the RHS may still carry an action body.
			s.sub(st.Rhs)
		case *ast.DeclStmt:
			s.generic(st)
		default:
			s.flush()
			s.generic(st)
		}
	}
	s.flush()
	s.run, s.runClosed = saved, savedClosed
}

// stmtReceiver renders the receiver of a statement-level method call
// (`p.goal` of `p.goal.Do(…)`), or "" for anything else.
func stmtReceiver(e ast.Expr) string {
	call, ok := e.(*ast.CallExpr)
	if !ok {
		return ""
	}
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return ""
	}
	return types.ExprString(sel.X)
}

// generic descends an unmodelled node (control flow, a declaration)
// looking for the sequences inside it, pruning at each one so nothing
// is counted twice.
func (s *citePileScan) generic(n ast.Node) {
	ast.Inspect(n, func(c ast.Node) bool {
		switch c := c.(type) {
		case nil:
			return false
		case *ast.BlockStmt:
			s.block(c.List)
			return false
		case *ast.FuncLit:
			s.block(c.Body.List)
			return false
		case *ast.CallExpr:
			s.sub([]ast.Expr{c})
			return false
		}
		return true
	})
}

func (s *citePileScan) expr(e ast.Expr) {
	switch e := e.(type) {
	case *ast.CallExpr:
		name := calleeName(e)
		switch {
		case actionSeqPassthrough[name]:
			muted := s.bindsGroundedHandle(e)
			if muted {
				s.mute++
			}
			for _, a := range e.Args {
				s.expr(a)
			}
			if muted {
				s.mute--
			}
		case ungroundInstallVerbs[name] && len(e.Args) == 1:
			s.hit(e, name)
		case claimBearing[name]:
			// The claim is the checked waypoint; its body justifies one
			// named step and is exempt from pile counting entirely.
			s.flush()
		case argumentStructure[name]:
			s.flush()
			s.sub(e.Args)
		default:
			// A close Action standing after installs marks the run as
			// "cite pile terminated by a refutation" — the shape the
			// correlated detector below looks for. Still neutral for the
			// count: closes are the OTHER quality bar's population.
			if closeVerbs[name] && len(s.run) > 0 {
				s.runClosed = true
			}
			// Neutral action (or plain expression): the run survives,
			// and any body it carries is scanned on its own.
			s.sub(e.Args)
		}
	case *ast.FuncLit:
		s.block(e.Body.List)
	case *ast.CompositeLit:
		s.sub(e.Elts) // []Action{…} slabs
	case *ast.KeyValueExpr:
		s.expr(e.Value)
	case *ast.UnaryExpr:
		s.expr(e.X)
	case *ast.ParenExpr:
		s.expr(e.X)
	case nil:
		return
	default:
		s.generic(e)
	}
}

// ungroundCitePileAllowlist: the files exempt from the pile lint, by
// corpus-relative path, each with its reason. SHRINK-ONLY — an entry
// is deleted when its file converts to L1/L2/L3, and no entry is ever
// added. An exemption covers a whole file, so a row is not carried
// into a file its member is merged into. It stands empty.
var ungroundCitePileAllowlist = map[string]string{}

// scanCitePiles walks one parsed file and returns every run of
// two or more unground installs it contains. Shared by the failing count
// lint and the chain-comment census.
func scanCitePiles(fset *token.FileSet, file string, af *ast.File) []citeRun {
	s := &citePileScan{
		fset:                fset,
		file:                file,
		grounded:            map[string]bool{},
		groundedFactSources: map[string]bool{},
	}
	ast.Inspect(af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || len(call.Args) == 0 {
			return true
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		// `f.At(w…)` is the Fact-layer spelling of `h.GroundKeep(w…)`;
		// an install whose value is grounded through any of the three is
		// not part of an unground pile. (`At` matches only as a METHOD —
		// the package-level `At(dep, w…)` constructor parses as an
		// *ast.Ident and never reaches here.)
		if !ok || (sel.Sel.Name != "Ground" && sel.Sel.Name != "GroundKeep" && sel.Sel.Name != "At") {
			return true
		}
		s.grounded[types.ExprString(sel.X)] = true
		return true
	})
	// Second pass: `f := a.Hyp(<dep expr>)` where f is grounded above
	// makes every sub-expression of <dep expr> a grounded install target.
	ast.Inspect(af, func(n ast.Node) bool {
		as, ok := n.(*ast.AssignStmt)
		if !ok || len(as.Lhs) != 1 || len(as.Rhs) != 1 {
			return true
		}
		if !s.grounded[types.ExprString(as.Lhs[0])] {
			return true
		}
		call, ok := as.Rhs[0].(*ast.CallExpr)
		if !ok || len(call.Args) != 1 {
			return true
		}
		if sel, ok := call.Fun.(*ast.SelectorExpr); !ok || sel.Sel.Name != "Hyp" {
			return true
		}
		ast.Inspect(call.Args[0], func(c ast.Node) bool {
			if e, ok := c.(ast.Expr); ok {
				s.groundedFactSources[types.ExprString(e)] = true
			}
			return true
		})
		return true
	})
	for _, d := range af.Decls {
		switch d := d.(type) {
		case *ast.FuncDecl:
			if d.Body != nil {
				s.decl = d.Name.Name
				s.block(d.Body.List)
			}
		case *ast.GenDecl:
			for _, spec := range d.Specs {
				vs, ok := spec.(*ast.ValueSpec)
				if !ok {
					continue
				}
				if len(vs.Names) > 0 {
					s.decl = vs.Names[0].Name
				}
				s.sub(vs.Values)
			}
		}
	}
	return s.runs
}

func TestLintNoUngroundCitePile(t *testing.T) {
	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		if why, allowed := ungroundCitePileAllowlist[chapterRel(f)]; allowed {
			t.Logf("allowlisted %s: %s", f, why)
			continue
		}
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		for _, run := range scanCitePiles(fset, f, af) {
			if len(run.sites) <= maxUngroundInstallRun {
				continue
			}
			t.Errorf("%s: %d consecutive unground ∀-installs, no witnesses between "+
				"them — the argument is not in the checked layer, only in the "+
				"comment (constitution §\"Argument structure\", operational rule \"the "+
				"argument lives in the checked layer\" + its closing-form ladder: "+
				"L0 tops out at ~%d installs plus one refute). Make the steps "+
				"visible — ground CiteSpecialize witnesses (L1), a Deduce/Have/Show "+
				"block (L2), or a CalcEq / CalcRel.Calc chain (L3). Sites:\n  %s",
				f, len(run.sites), maxUngroundInstallRun, strings.Join(run.sites, "\n  "))
		}
	}
}

// ---------------------------------------------------------------------------
// CHAIN-COMMENT CENSUS (diagnostic, not an assertion). The count lint
// above is a backstop for the long tail; it cannot separate a body of
// three installs whose comment draws a four-leg ≈-ladder from a genuine
// short form at the same count — two installs under a one-sentence
// justification. The discriminator is not the
// count, it is the COMMENT: a cite pile is a defect when the surrounding
// prose draws a chain, because then every interior waypoint is phantom
// by construction. So this census correlates
//
//	(a run of ≥2 unground installs, terminated by a close Action)
//	 ∧ (a LADDER in the entry's doc comment)
//
// and reports the pairs. It does NOT fail the build — see the precision
// note at the bottom of this block.
//
// LADDER LINE — the signal, read off the corpus rather than guessed. The
// corpus writes chains as Go doc DISPLAY blocks (a comment line starting
// with a tab), one leg per line, relation symbol carrying the leg, and a
// column-aligned justification per leg:
//
//	(x + y) · z ~ z · (x + y) [MulSym]
//	 ~ (z · x) + (z · y) [LeftDistrib]
//
// A line counts as a ladder line when it is displayed, carries a
// relation symbol, and is MATH RATHER THAN PROSE. Four exclusions do
// the separating work, each calibrated against a real corpus line:
//
// - Statement restatements: a line starting with ⊢, ∀ or ∃ is the
// entry's own goal, not an intermediate.
// - Label lines: a `word:` prefix within the first 30 characters
// (`base:`, `step, n = 0:`, `Residual:`) annotates a goal STATE.
// - Sentence punctuation: a line ending in `;` `.` `,` `:` is a
// narrative step, not a leg. This is what keeps LessThanAsym's
// "assume m < n and n < m;" ladder-shaped prose out.
// - English stopwords: a whitespace-delimited token that is an
// ordinary English word ("the", "and", "into", "turns") marks
// prose. Matching is per WHOLE TOKEN, never per substring, so
// `nadd_of_num(x)` is not read as containing "of".
//
// The justification column is cut before the prose test (two-plus
// spaces followed by `(` or `[`), so "(MulWellDefRight, x = x' with y'
// fixed left)" does not make its own leg look like prose.
//
// WHY THE nonneg_real "Residual:" CONVENTION DOES NOT FIRE. Those files
// annotate ONE intermediate goal between two tactic lines that are both
// present in the body — the audit ruled them non-defects, and
// conflating them with real ladders would balloon the worklist. Two
// independent guards keep them out: the census reads only comments
// OUTSIDE function bodies (entry doc, build doc, file header), and every
// `Residual:` site is an in-body annotation between tactic lines; and
// the label-line exclusion would drop them even if they moved.
//
// SCOPE. A run is attributed to its enclosing top-level declaration, and
// the doc set is that declaration's doc PLUS the doc of the entry whose
// `Build:` field names it (the corpus splits `var Foo = family.Add(…)`
// from `var Build_Foo = …`, and the ladder lives on the former), plus
// the file header when the file declares a single entry (a one-member
// file carries its ladder there). Per-declaration rather than per-file
// is load-bearing: one file can hold a member whose doc displays two
// recursion clauses beside a member that must not inherit them.
//
// PRECISION, AND WHY THIS IS A t.Logf CENSUS. Every exclusion above is
// a heuristic over English prose, and the threshold that catches a
// doc whose only display line is a single transformed goal is ONE
// ladder line — low enough that any displayed math line next to a
// 2-run fires. The census reports the LEG COUNT precisely so the
// reader can triage: multi-leg hits are a drawn chain and are
// reliable; single-leg hits are a judgement call (a true positive
// whose second leg was merely not counted reads the same as a
// case-analysis narration that is no waypoint chain). A
// failing lint at single-leg precision gets allowlisted into
// irrelevance, which is worse than no lint. So this ships as a census
// the orchestrator reads (go test -v -run TestCiteChainCommentCensus),
// and the FAILING bar stays the count lint, whose signal is structural.
// ---------------------------------------------------------------------------

// ladderRelations: the symbols that carry a leg of a chain.
var ladderRelations = []string{"≈", "~", "⇔", "⇒", "≤", "≥", "=", "<", ">"}

// justificationColumn: the per-leg justification, set off by two or
// more spaces — "… z · (x + y) [MulSym]".
// Three styles occur: "[MulSym]", "(Add, zero clause)" and "-- OfNum".
var justificationColumn = regexp.MustCompile(`\s{2,}(--|—|[\(\[])`)

// proseStopwords: ordinary English words that never occur as a whole
// whitespace-delimited token in HOL term notation. Matched per token,
// so identifier pieces (nadd_of_num, dest_nadd) are untouched.
var proseStopwords = map[string]bool{
	"the": true, "and": true, "into": true, "from": true, "with": true,
	"that": true, "this": true, "these": true, "those": true, "its": true,
	"then": true, "but": true, "not": true, "all": true, "both": true,
	"each": true, "every": true, "one": true, "two": true, "three": true,
	"four": true, "gives": true, "give": true, "turns": true, "turn": true,
	"makes": true, "make": true, "chains": true, "refutes": true,
	"assume": true, "sides": true, "side": true, "instance": true,
	"clause": true, "clauses": true, "yields": true, "becomes": true,
	"closes": true, "when": true, "while": true, "which": true,
	"where": true, "only": true, "just": true, "same": true, "other": true,
	"than": true, "via": true, "over": true, "under": true, "after": true,
	"before": true, "again": true, "back": true, "also": true,
	"still": true, "must": true, "does": true, "are": true, "for": true,
	"has": true, "have": true, "here": true, "there": true, "they": true,
	"them": true, "their": true, "our": true, "reflexive": true,
	"leaving": true, "substituting": true, "strip": true, "outer": true,
	"folds": true, "fold": true, "reduces": true, "rewrites": true,
	// Short function words. Whole-token matching makes these safe:
	// no HOL term is spelled as a bare "of" or "to", and identifier
	// pieces (nadd_of_num) are never split.
	"to": true, "of": true, "in": true, "is": true, "as": true,
	"by": true, "at": true, "it": true, "or": true, "if": true,
	"an": true, "on": true, "be": true, "do": true, "we": true,
}

// isLadderLine reports whether one raw comment line ("// …") is a leg of
// a displayed chain. See the block comment above for each exclusion.
func isLadderLine(raw string) bool {
	body, ok := strings.CutPrefix(raw, "//")
	if !ok {
		return false
	}
	// Go doc DISPLAY block: the line is indented past the marker.
	if !strings.HasPrefix(body, "\t") && !strings.HasPrefix(body, "  ") {
		return false
	}
	body = strings.TrimSpace(body)
	if body == "" || strings.Contains(body, ";") {
		return false // a leg never contains a clause separator
	}
	// The entry's own statement, not an intermediate.
	for _, p := range []string{"⊢", "∀", "∃"} {
		if strings.HasPrefix(body, p) {
			return false
		}
	}
	// A `label:` prefix annotates a goal STATE (base:, step:, Residual:).
	if i := strings.Index(body, ":"); i >= 0 && i <= 30 && !strings.ContainsAny(body[:i], "([") {
		return false
	}
	// Cut the justification column before judging prose.
	if loc := justificationColumn.FindStringIndex(body); loc != nil {
		body = strings.TrimSpace(body[:loc[0]])
	}
	if body == "" {
		return false
	}
	switch body[len(body)-1] { // sentence punctuation ⇒ narrative prose
	case ';', '.', ',', ':':
		return false
	}
	hasRelation := false
	for _, rel := range ladderRelations {
		if strings.Contains(body, rel) {
			hasRelation = true
			break
		}
	}
	if !hasRelation {
		return false
	}
	for _, tok := range strings.Fields(body) {
		if proseStopwords[strings.ToLower(strings.Trim(tok, "()[],;.:'`\"·×∘"))] {
			return false
		}
	}
	return true
}

// ladderLineCount counts the ladder legs in a set of comment groups.
func ladderLineCount(groups []*ast.CommentGroup) int {
	n := 0
	for _, g := range groups {
		if g == nil {
			continue
		}
		for _, c := range g.List {
			for _, line := range strings.Split(c.Text, "\n") {
				if isLadderLine(strings.TrimSpace(line)) {
					n++
				}
			}
		}
	}
	return n
}

// entryDocFor maps a build symbol's name to the doc comment of the
// registry entry whose `Build:` field names it, plus the file header
// when the file declares exactly one entry.
func entryDocFor(af *ast.File) (map[string][]*ast.CommentGroup, int) {
	byBuild := map[string][]*ast.CommentGroup{}
	entries := 0
	for _, d := range af.Decls {
		gd, ok := d.(*ast.GenDecl)
		if !ok {
			continue
		}
		ast.Inspect(gd, func(n ast.Node) bool {
			cl, ok := n.(*ast.CompositeLit)
			if !ok {
				return true
			}
			if sel, ok := cl.Type.(*ast.SelectorExpr); !ok || sel.Sel.Name != "ProofEntry" {
				return true
			}
			entries++
			for _, elt := range cl.Elts {
				kv, ok := elt.(*ast.KeyValueExpr)
				if !ok {
					continue
				}
				if key, ok := kv.Key.(*ast.Ident); !ok || key.Name != "Build" {
					continue
				}
				if id, ok := kv.Value.(*ast.Ident); ok {
					byBuild[id.Name] = append(byBuild[id.Name], gd.Doc)
				}
			}
			return true
		})
	}
	return byBuild, entries
}

func TestCiteChainCommentCensus(t *testing.T) {
	type finding struct {
		file, decl string
		n, legs    int
		site       string
	}
	var found []finding
	popAtLeast := map[int]int{} // run length → number of files with such a run

	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, parser.ParseComments)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		runs := scanCitePiles(fset, f, af)
		byBuild, entries := entryDocFor(af)

		// Doc lookup per declaration, with the file header folded in
		// for single-entry files.
		declDoc := map[string][]*ast.CommentGroup{}
		for _, d := range af.Decls {
			var name string
			var doc *ast.CommentGroup
			switch d := d.(type) {
			case *ast.FuncDecl:
				name, doc = d.Name.Name, d.Doc
			case *ast.GenDecl:
				doc = d.Doc
				for _, spec := range d.Specs {
					if vs, ok := spec.(*ast.ValueSpec); ok && len(vs.Names) > 0 {
						name = vs.Names[0].Name
					}
				}
			}
			if name == "" {
				continue
			}
			groups := []*ast.CommentGroup{doc}
			groups = append(groups, byBuild[name]...)
			if entries == 1 {
				// The file header. Often DETACHED (a blank line before
				// `package …`), so af.Doc is nil and the group only
				// appears in af.Comments — a one-member file keeps its
				// whole ladder there.
				groups = append(groups, af.Doc)
				for _, cg := range af.Comments {
					if cg.End() < af.Package {
						groups = append(groups, cg)
					}
				}
			}
			declDoc[name] = groups
		}

		seen := map[int]bool{}
		for _, r := range runs {
			for k := 2; k <= len(r.sites); k++ {
				if !seen[k] {
					seen[k] = true
					popAtLeast[k]++
				}
			}
			if len(r.sites) < 2 || !r.closed {
				continue
			}
			legs := ladderLineCount(declDoc[r.decl])
			if legs == 0 {
				continue
			}
			found = append(found, finding{f, r.decl, len(r.sites), legs, r.sites[0]})
		}
	}

	sort.Slice(found, func(i, j int) bool {
		if found[i].n != found[j].n {
			return found[i].n > found[j].n
		}
		return found[i].file < found[j].file
	})
	t.Logf("cite-pile ∧ chain-comment census: %d correlated sites", len(found))
	for _, x := range found {
		t.Logf("  [chain-comment] %s (%s): %d unground installs + close, %d ladder leg(s) in doc — at %s",
			x.file, x.decl, x.n, x.legs, x.site)
	}
	for _, k := range []int{2, 3, 4} {
		t.Logf("population: files with a run of ≥%d unground installs: %d", k, popAtLeast[k])
	}
	// Breakdown the orchestrator needs to site the real boundary: how
	// many correlated sites the count lint already catches (run > bar)
	// versus how many the comment signal ADDS at each shorter run, and
	// how many of those carry a multi-leg ladder (high confidence) as
	// opposed to a single displayed line (needs a human look).
	byRun, multiLeg := map[int]int{}, map[int]int{}
	for _, x := range found {
		byRun[x.n]++
		if x.legs >= 2 {
			multiLeg[x.n]++
		}
	}
	for n := 2; n <= 8; n++ {
		if byRun[n] == 0 {
			continue
		}
		note := "ADDED by the comment signal (count lint misses it)"
		if n > maxUngroundInstallRun {
			note = "already failed by the count lint"
		}
		t.Logf("correlated sites at run=%d: %d (%d with ≥2 ladder legs) — %s",
			n, byRun[n], multiLeg[n], note)
	}
}

// ---------------------------------------------------------------------------
// TWIN-BODY CENSUS (diagnostic, not an assertion). Two single-section
// members of the same package whose Build bodies are token-identical
// prove DIFFERENT statements with the SAME action sequence — every
// distinction between them lives in the refuter's goal-directed
// search, never in the checked text. That is the comment-fiction
// shape: two byte-equal bodies whose doc comments claim mirrored
// instances ("the same pair of siblings at (m, n) instead of (n, m)")
// that no witness in either body spells. The fix is ground witnesses
// (Cite(dep, w…)) that make the mirrored instances visible — after
// which the bodies differ and the pair drops out of this census.
//
// A twin may be benign. The honest form is the definitional
// projection: the body cites a pack or source whole and the STATEMENT
// selects what is taken, as the site's comment says — the zero clauses
// of a division and its remainder, the ∀- and ∃-forms of one bridge
// closing by the same single cite. Projections that bind different
// ∀-arities do not group here, their closures differing, so whether a
// projection pair lands in this census is a fact about arity, not
// about honesty — which is why it is a triage worklist, not a bar to
// drive to zero.
//
// It matches EVERY entry constructor that carries a (statement,
// body-closure) argument shape — `Theorem`, `Sections`, `Derived` —
// because that shape is what this census keys on. The list must track
// the constructor set: a census that scans an empty set reports
// exactly what a clean corpus reports, "0 group(s)", and nothing
// surfaces the gap. A constructor that carries a statement joins this
// list in the change that adds it.
// ---------------------------------------------------------------------------

func TestTwinBodyCensus(t *testing.T) {
	type site struct{ file, stmt string }
	byBody := map[string][]site{}

	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		pkgDir := filepath.ToSlash(filepath.Dir(f))
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) < 2 {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || (sel.Sel.Name != "Theorem" && sel.Sel.Name != "Sections" && sel.Sel.Name != "Derived") {
				return true
			}
			// ENTRY-level constructors only. `Theorem` names two verbs:
			// the family's entry constructor (family.Theorem) and the
			// Script's section opener (ctx.Theorem) — and only the first
			// is an entry whose Build body this census can meaningfully
			// compare. A section body routinely reads
			// `a.Do(CiteNode(clauseForm))`, textually identical across
			// files while `clauseForm` is a DIFFERENT captured local in
			// each; comparing those reports the chartered clause-form
			// bridge (constitution §"The headline invariant") as a twin.
			if recv, ok := sel.X.(*ast.Ident); ok && recv.Name == "ctx" {
				return true
			}
			fn, ok := call.Args[len(call.Args)-1].(*ast.FuncLit)
			if !ok {
				return true
			}
			var body strings.Builder
			if err := format.Node(&body, fset, fn); err != nil {
				return true
			}
			var stmt string
			switch a := call.Args[0].(type) {
			case *ast.BasicLit:
				stmt = a.Value
			default:
				stmt = types.ExprString(call.Args[0])
			}
			key := pkgDir + "\x00" + body.String()
			byBody[key] = append(byBody[key], site{f, stmt})
			return true
		})
	}

	twins := 0
	var keys []string
	for k, sites := range byBody {
		if len(sites) < 2 {
			continue
		}
		distinct := map[string]bool{}
		for _, s := range sites {
			distinct[s.stmt] = true
		}
		if len(distinct) < 2 {
			continue
		}
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		twins++
		var lines []string
		for _, s := range byBody[k] {
			lines = append(lines, fmt.Sprintf("%s: %s", s.file, s.stmt))
		}
		t.Logf("[twin-body] identical Build bodies, distinct statements:\n  %s",
			strings.Join(lines, "\n  "))
	}
	t.Logf("twin-body census: %d group(s)", twins)
}

// ---------------------------------------------------------------------------
// NO POSITIONAL HYP INDICES. Goal hyp lists are canonically sorted and
// renumber on every hyp-adding step, so an integer hyp address in a
// proof is unreadable (the reader must simulate the hyp list)
// and brittle (any upstream edit shifts it) — the files that carry them
// also carry index-bookkeeping comments ("the second bound has
// renumbered to index 0"), which is the readability tax this lint
// exists to remove. Address hypotheses as VALUES instead — a Fact
// carries the hypothesis lexically, so nothing has to be re-found:
//
// - a branch / just-introduced hyp: Given(func(a *Argument, h Fact){…})
// — the IH, a ByCase or SplitDisj arm's hyp, or whatever the
// immediately preceding step installed; binding records no ministep
// - a leading ⇒ of the section statement: a Fact PARAMETER on the
// Build closure, or a.Assume() mid-proof
// - an ∃ already established — a dep, a cert, a resident Fact, or
// At(dep, w…): w, f := a.Unpack(target) (Unpack2 for ∃∃) installs,
// Skolemizes, and hands back the witnesses AND the instance
// - an already-resident hyp, by content: a.Hyp(t)
// - a fact this proof asserts: f := a.Have(label, claim, proof…)
// - use later: By(f, …) / By(f.At(w…), …) as a premise (clear-first:
// a By prunes what its premise list does not name), a.Do(f.At(w…))
// for a ground instance a downstream STEP consumes, f.Rw() /
// f.Subst() / f.CongrArg(fn) for a goal-surface move
// - branch on it: f.SplitDisj / f.SplitIff / f.SplitImply, or
// f.DismissLeft(label, …) / f.DismissRight to discharge one arm and
// continue on the other (a named Fact installs first, a resident
// one delegates)
// - drop a spent source: Clear(f) — for a ladder that closes on a
// terminal refute / Finally, which meets the whole
// context and so gets no clear-first discipline from By. Reaching
// for Clear ahead of a By is the misuse.
// - or, for an untransformed hyp, content addressing:
// GroundHyp(cert, w…) / CiteSpecialize(dep, w…)
//
// LEGACY: the *HypHandle ceremony (NewHypHandle + From / FromResident /
// Ground / GroundKeep / Clear, prover/proof/hyp_handle.go) was the
// original remedy and still resolves indices at run time, tracked
// through Skolemization. It is a superseded spelling — don't author new
// sites (chapter_constitution.md §"The math layer: facts as values").
//
// What keeps the residue alive is ONE criterion with three faces: THE
// LANDED FORM IS NOT THE DEP'S STATEMENT, so there is nothing for a
// content-addressed Fact to name. (i) a non-preserving UseLemma
// rewrites resident hyps as it installs; (ii) a higher-order cite lands
// as β-redexes over its λ-arguments; (iii) a spine grounding that a
// downstream StripQuant Skolemizes is neither the source nor f.At(w…)
// but their descendant. A site of the residue carries its reason at
// the site.
//
// The allowlist below maps a file to the EXACT count of its
// integer-literal hyp addresses. Shrink-only ratchet: a
// count above the entry fails (no new positional sites); a count below
// fails too, telling you to lower the entry (so the list tracks
// reality down to zero, then the entry is deleted).
// ---------------------------------------------------------------------------

// positionalHypVerbs: callee name → argument positions holding hyp
// indices (-1 = every argument, for ClearHyps).
var positionalHypVerbs = map[string][]int{
	"InstHyp":          {0},
	"ClearHyp":         {0},
	"ClearHyps":        {-1},
	"Rw":               {0},
	"Subst":            {0},
	"SplitDisjAt":      {0},
	"SplitDisjAtCases": {0},
	"SplitHypIffAt":    {0},
	"CongrArg":         {1},
}

// positionalHypAddrAllowlist: empty — no file holds a positional hyp
// address, and the map stays so the ratchet is armed against a new
// one. A hyp the preceding Rw rewrites TOGETHER with several others
// (the tracker's ambiguous-successor limit) is re-bound by content
// with FromResident right after that Rw.
var positionalHypAddrAllowlist = map[string]int{}

func TestLintNoPositionalHypIndices(t *testing.T) {
	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		var sites []string
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			ident, ok := call.Fun.(*ast.Ident)
			if !ok {
				return true // handle methods (h.Rw, h.Subst) resolve via selector — not flagged
			}
			positions, ok := positionalHypVerbs[ident.Name]
			if !ok {
				return true
			}
			check := func(arg ast.Expr) {
				if lit, ok := arg.(*ast.BasicLit); ok && lit.Kind == token.INT {
					pos := fset.Position(lit.Pos())
					sites = append(sites, fmt.Sprintf("%s:%d: %s(%s…)", f, pos.Line, ident.Name, lit.Value))
				}
			}
			if positions[0] == -1 {
				for _, arg := range call.Args {
					check(arg)
				}
			} else {
				for _, p := range positions {
					if p < len(call.Args) {
						check(call.Args[p])
					}
				}
			}
			return true
		})
		want := positionalHypAddrAllowlist[chapterRel(f)]
		if len(sites) > want {
			t.Errorf("%s: %d positional hyp address(es), allowlist permits %d — "+
				"address new hypotheses as VALUES (Given / a.Assume / a.Unpack / "+
				"a.Hyp hand the hypothesis back as a Fact; see this lint's header). Sites:\n  %s",
				f, len(sites), want, strings.Join(sites, "\n  "))
		} else if len(sites) < want {
			t.Errorf("%s: %d positional hyp address(es) but the allowlist still says %d — "+
				"lower (or delete) its entry so the ratchet tracks reality",
				f, len(sites), want)
		}
	}
}

// ---------------------------------------------------------------------------
// NAMED ⇔ HALVES. An ⇔ splits two ways and neither split's halves are
// interchangeable: a goal `L ⇔ R` yields `R ⊢ L` FIRST and `L ⊢ R`
// second, a hypothesis `L ⇔ R` yields "both hold" then "neither does".
// Positional `Case` args make the author remember which, and then say
// in prose which they meant — prose nothing checks, and it drifts: an
// arrow naming the opposite branch, no arrow at all, a hyp split's
// halves called "directions" when it has none.
//
// The surface takes Forward/Backward and BothHold/NeitherHolds —
// distinct types, so a swap is a compile error and the rendered arrow
// comes from the slot (prover/proof/iff_direction.go). The positional
// bottoms survive for ONE reason: emit renders a split whose children
// did not become a Case block as a bare caseless step. Caseless is
// therefore fine; labeled is the spelling this lint exists to keep out.
// ---------------------------------------------------------------------------

var positionalBranchVerbs = map[string]string{
	"SplitIffCases":      "SplitIff(Forward(…), Backward(…))",
	"SplitHypIffCases":   "SplitHypIff(BothHold(…), NeitherHolds(…))",
	"SplitHypIffAtCases": "SplitHypIffAt(i, BothHold(…), NeitherHolds(…))",
	"SplitDisjCases":     "SplitDisj(LeftHolds(…), RightHolds(…))",
	"SplitDisjAtCases":   "SplitDisjAt(i, LeftHolds(…), RightHolds(…))",
}

// TestLintNoPositionalBranchCases: a split whose branches have names —
// the two halves of an ⇔, the two disjuncts of an ∨ hypothesis — is
// written through them, never through a labeled positional Case
// (prover/proof/iff_direction.go, disjunction_branches.go).
func TestLintNoPositionalBranchCases(t *testing.T) {
	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			ident, ok := call.Fun.(*ast.Ident)
			if !ok {
				return true
			}
			want, ok := positionalBranchVerbs[ident.Name]
			if !ok {
				return true
			}
			for _, arg := range call.Args {
				c, ok := arg.(*ast.CallExpr)
				if !ok {
					continue
				}
				id, ok := c.Fun.(*ast.Ident)
				if !ok || (id.Name != "Case" && id.Name != "MakeCase") {
					continue
				}
				t.Errorf("%s:%d: %s with a labeled Case — this split's branches are named, "+
					"not positional: %s", f, fset.Position(c.Pos()).Line, ident.Name, want)
			}
			return true
		})
	}
}

// ---------------------------------------------------------------------------
// ONE CITE VERB. The cite surface once grew one spelling per plumbing
// decision: UseLemmaExact vs UseLemma picked the install tactic,
// CiteSpecialize added grounding, and each dep cite chose its install
// FORM by wrapping (`ctx.NormalizedThm(ctx.Dep(N))`). Every one of those
// is a function of the goal state and the dep's shape — not of the
// mathematics — so a body spelling them is narrating plumbing.
// `Cite` / `CiteKeep` (prover/proof/fact.go) decide all of it per call, and
// emit's curate transport renders them, so the demoted spellings can
// only re-enter by hand.
//
// Demoted, not deleted: the prover keeps UseLemmaExact /
// CiteSpecialize as Actions. This lint scopes the ban to the
// hand-blessed corpus.
//
// `UseLemma` is NOT banned: it replays through the ADAPTIVE, non-
// preserving ApplyLemma and can rewrite the goal rather than install a
// hypothesis. That is a different move, not a different spelling of the
// same one.
// ---------------------------------------------------------------------------

var demotedCiteVerbs = map[string]string{
	"UseLemmaExact":      "Cite(target) — it decides install-vs-close and the install form from the goal state",
	"CiteSpecialize":     "Cite(target, w…)",
	"CiteSpecializeKeep": "CiteKeep(target, w…)",

	// The simp face of the same consolidation. The raw Step surface
	// takes rule PROPS, so every call site re-spelled its
	// deps' statements as MakePropText — pinned text, checked against
	// nothing — and then hand-maintained one rule Case per rule that
	// both fires and fails to auto-close (the count is a fact about
	// driver behavior, and two files carried decoder comments for
	// getting it wrong). `Simp` takes cite targets and discharges the
	// obligations from those same certificates. Demoted, not deleted:
	// emit's pinned rendering still spells a rule the Simp fusion
	// declines as SimpWith / SimpWithFlipped.
	"SimpWith":         "Simp(Fwd(dep)…) — rules are cite targets, obligations self-discharge",
	"SimpWithFlipped":  "Simp(Rev(dep)…)",
	"SimpWithOriented": "Simp(Fwd(dep), Rev(dep)…)",
}

// stepAuthoringKits are the packages BELOW the corpus that emit proof
// steps INTO members — prover/solver kits whose Actions land in
// a member's recorded tree. This lint's jurisdiction is
// "everything that authors a step a proof replays through", not
// "everything in one package": a member reading its own file must
// not find one cite verb there and a demoted one in the machinery it
// calls.
//
// Only THIS lint extends here. The rest of the file's rules are about
// statements, headlines, Case labels and dep manifests — things a kit
// does not have.
var stepAuthoringKits = []string{
	"../../../prover/algebra",
}

// stepAuthoringFiles is chapterProofFiles plus the kit sources above.
func stepAuthoringFiles(t *testing.T) []string {
	t.Helper()
	files := chapterProofFiles(t)
	for _, dir := range stepAuthoringKits {
		entries, err := os.ReadDir(dir)
		if err != nil {
			t.Fatalf("read kit dir %s: %v", dir, err)
		}
		var seen int
		for _, e := range entries {
			name := e.Name()
			if e.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
				continue
			}
			files = append(files, filepath.Join(dir, name))
			seen++
		}
		if seen == 0 {
			t.Fatalf("kit dir %s contributed no .go files — the path is stale and this "+
				"lint silently stopped covering it", dir)
		}
	}
	return files
}

func TestLintOneCiteVerb(t *testing.T) {
	fset := token.NewFileSet()
	for _, f := range stepAuthoringFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			// Bare Action form (`CiteSpecialize(…)`) and the node-method
			// form (`p.lemma1.UseLemmaExact(…)`) alike.
			var name string
			switch fun := call.Fun.(type) {
			case *ast.Ident:
				name = fun.Name
			case *ast.SelectorExpr:
				name = fun.Sel.Name
			default:
				return true
			}
			if want, banned := demotedCiteVerbs[name]; banned {
				pos := fset.Position(call.Pos())
				t.Errorf("%s:%d: %s is demoted to the generated profile — spell it %s "+
					"(see this lint's header)", f, pos.Line, name, want)
			}
			return true
		})
	}
}

// ---------------------------------------------------------------------------
// NARRATION ECONOMY: NO ENGINE-FORENSICS TEMPLATES, NO DEP-RECAP
// COMMENTS, NO CONSTRUCTION-LEDGER POINTERS. The cite default — a
// cited ∀-fact installs as a resident hypothesis and the closing
// refutation finds the groundings itself — lives in ONE home (the
// family README); proof-file comments mark only deviations, in
// self-contained words. A member's dependencies are recorded (the
// family blob, read by `xugo query deps`): a comment restating them
// goes stale on every dep migration (the real/tower fresh-eye
// stale-dep-comment class) — dep prose is for WHY a surprising dep
// exists, never a list recap. Reader-facing proof
// files never point into construction ledgers (PLAN.md, numbered
// "cite-count rule case N" conventions) and never carry construction
// status ("tier N complete"). Enforced as phrase bans over comment
// text: the templates propagate by copy-paste from sibling files,
// which exact-phrase bans kill at the source. family.go manifests and
// the registry framework are exempt (construction-side linkage is
// their job).
// ---------------------------------------------------------------------------

var narrationEconomyBans = []struct {
	pattern *regexp.Regexp
	why     string
}{
	{regexp.MustCompile(`Per-dep cite behavior`),
		"engine-forensics template — the cite default lives in the family README; comment only the deviating site"},
	{regexp.MustCompile(`cite-count`),
		"pointer into a PLAN's numbered conventions — engine notes are self-contained words"},
	{regexp.MustCompile(`PLAN\.md|PLAN §`),
		"construction-ledger pointer in a reader-facing file"},
	{regexp.MustCompile(`(?i)\btier [0-9]+ (complete|pending)\b`),
		"construction status in a reader-facing file"},
	{regexp.MustCompile(`Deps?:.*\btyped\b|Deps? \(typed`),
		"dep-recap comment — the recorded deps are the record; prose only for WHY a surprising dep exists"},
}

func TestLintNarrationEconomy(t *testing.T) {
	for _, f := range chapterProofFiles(t) {
		// Manifests, wiring, and the framework are exempt —
		// construction-side linkage is their job.
		slash := filepath.ToSlash(f)
		if filepath.Base(f) == "family.go" ||
			strings.HasPrefix(slash, "registry/") ||
			slash == "registry.go" || slash == "zz_families.go" ||
			slash == "real/tower/tower.go" {
			continue
		}
		data, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		for i, line := range strings.Split(string(data), "\n") {
			_, comment, found := strings.Cut(line, "//")
			if !found {
				continue
			}
			for _, ban := range narrationEconomyBans {
				if ban.pattern.MatchString(comment) {
					t.Errorf("%s:%d: %s\n  %s", f, i+1, ban.why, strings.TrimSpace(line))
				}
			}
		}
	}
}

// ---------------------------------------------------------------------------
// A QUOTIENT IS DEFINED THROUGH ITS DOOR.
//
// `family.DefineQuotient` mints a quotient type over the
// equivalence-class shape and derives the seven facts it comes with
// (library/registry/define_quotient.go); a function on its classes is
// a `family.Define` with class patterns, whose respectfulness is the
// one obligation. A chapter that carved the same type out by
// `family.DefineType` over the class shape — `λs. ∃x. s = R(x)` — and
// then proved surjectivity, class equality and the descent of each
// operation by hand would be re-authoring what the door derives, which
// is what the two real-tower families did before the door existed
// (each ~300 lines of bridge proofs over a shared kit). The class shape
// in a DefineType's predicate is the tell, and it is read off the
// literal.
//
// The allowlist is shrink-only, same contract as this file's others: a
// type that genuinely IS a set of classes but not a quotient in the
// door's sense says why here.
var classShapedTypeDefAllowlist = map[string]string{}

// classShapePred matches a type definition's predicate that carves out
// the equivalence classes of a relation: a λ over a set whose body says
// the set is R(x) for some x.
var classShapePred = regexp.MustCompile(`^λ\s*\w+\s*:[^.]*\.\s*∃\s*\w+\s*:[^.]*\.\s*\w+\s*=\s*[\w.]+\(\s*\w+\s*\)\s*$`)

func TestLintQuotientsUseTheDoor(t *testing.T) {
	if !classShapePred.MatchString("λs:set(nadd). ∃x:nadd. s = nadd_eq(x)") {
		t.Fatalf("instrument guard: the class-shape pattern does not match its own example")
	}
	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		key := chapterRel(f)
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || sel.Sel.Name != "DefineType" || len(call.Args) != 1 {
				return true
			}
			lit, ok := call.Args[0].(*ast.CompositeLit)
			if !ok {
				return true
			}
			for _, elt := range lit.Elts {
				kv, ok := elt.(*ast.KeyValueExpr)
				if !ok {
					continue
				}
				if k, ok := kv.Key.(*ast.Ident); !ok || k.Name != "Pred" {
					continue
				}
				bl, ok := kv.Value.(*ast.BasicLit)
				if !ok || bl.Kind != token.STRING {
					continue
				}
				pred, err := strconv.Unquote(bl.Value)
				if err != nil || !classShapePred.MatchString(pred) {
					continue
				}
				if why, allowed := classShapedTypeDefAllowlist[key]; allowed {
					t.Logf("allowlisted %s: %s", f, why)
					continue
				}
				pos := fset.Position(call.Pos())
				t.Errorf("%s:%d: DefineType over the equivalence-class shape %q — a quotient is "+
					"defined through family.DefineQuotient (the class map, the seven facts and the "+
					"lift of each operation come with it), or allowlisted with a reason (see this "+
					"lint's header).", f, pos.Line, pred)
			}
			return true
		})
	}
}

// ---------------------------------------------------------------------------
// BINDER-CLOSURE PARAMETER NAMES MATCH THE STATEMENT'S BINDERS.
//
// A binder-closure section (`family.Theorem(stmt, func(a *Argument, A, B, C
// Term) {…})`, `ctx.Lemma(…)`) binds the statement's leading ∀/⇒ slots to
// the closure's parameters POSITIONALLY — Go reflection cannot read
// parameter names, so the boundary (prover/proof/section.go) can check
// arity, kind and shape but not identity. Two same-typed parameters
// written in the wrong order (A and B swapped) would type-check, run, and
// prove a theorem whose Go text says something else.
//
// The names are right here in the source, though: the statement literal
// and the parameter list are two halves of the same call. This lint reads
// both and requires the i-th Term parameter to be spelled like the i-th
// ∀-binder. It replaces the old `ctx.Var("A_0", …)` + "declaration order
// == strip order" convention, which nothing checked at all.
//
// Fact parameters carry no name obligation: a hypothesis has no binder
// name to match, and a fact's Go name states its mathematical role
// instead; where a fact binds a bundle, the binders it fixes are named
// by the statement alone.
func TestLintBinderClosureNames(t *testing.T) {
	fset := token.NewFileSet()
	checked := 0
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) != 2 {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || (sel.Sel.Name != "Theorem" && sel.Sel.Name != "Lemma") {
				return true
			}
			stmt, ok := statementLiteralText(call.Args[0])
			if !ok {
				return true
			}
			fn, ok := sectionClosure(call.Args[1])
			if !ok {
				return true
			}
			checked++
			pos := fset.Position(call.Pos())
			checkBinderNames(t, fmt.Sprintf("%s:%d", f, pos.Line), stmt, fn)
			return true
		})
	}
	t.Logf("binder-closure sections checked: %d", checked)
}

// statementLiteralText is the statement a Theorem/Lemma call's first
// argument states, where it is written as a literal: a string literal
// or a chain of them laid out over lines (xugofmt.StringValue), or a
// `Statement{…}` literal (statementLiteral), assembled as the
// constructor assembles it. A statement built otherwise — a helper
// call, a constant — is not read, as the binder lint has never read
// one.
func statementLiteralText(arg ast.Expr) (string, bool) {
	if s, ok := xugofmt.StringValue(arg); ok {
		return s, true
	}
	stmt, ok := statementLiteral(arg)
	if !ok {
		return "", false
	}
	text, err := stmt.Text()
	return text, err == nil
}

// statementLiteral reads a `Statement{…}` literal whose Binders,
// Hypotheses, Conclusion and Abbrev entries are string literals, or
// chains of them laid out over lines (xugofmt.StringValue), as
// dsl.Statement; anything else is not read.
func statementLiteral(arg ast.Expr) (dsl.Statement, bool) {
	var stmt dsl.Statement
	cl, ok := arg.(*ast.CompositeLit)
	if !ok {
		return stmt, false
	}
	if id, isIdent := cl.Type.(*ast.Ident); !isIdent || id.Name != "Statement" {
		return stmt, false
	}
	unquote := xugofmt.StringValue
	for _, elt := range cl.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok {
			return stmt, false
		}
		key, ok := kv.Key.(*ast.Ident)
		if !ok {
			return stmt, false
		}
		switch key.Name {
		case "Binders":
			if stmt.Binders, ok = unquote(kv.Value); !ok {
				return stmt, false
			}
		case "Conclusion":
			if stmt.Conclusion, ok = unquote(kv.Value); !ok {
				return stmt, false
			}
		case "Hypotheses":
			hyps, ok := kv.Value.(*ast.CompositeLit)
			if !ok {
				return stmt, false
			}
			for _, h := range hyps.Elts {
				text, ok := unquote(h)
				if !ok {
					return stmt, false
				}
				stmt.Hypotheses = append(stmt.Hypotheses, text)
			}
		case "Abbrev":
			entries, ok := kv.Value.(*ast.CompositeLit)
			if !ok {
				return stmt, false
			}
			for _, e := range entries.Elts {
				entry, ok := e.(*ast.CompositeLit)
				if !ok {
					return stmt, false
				}
				var abbreviation dsl.Abbreviation
				for _, field := range entry.Elts {
					kv, ok := field.(*ast.KeyValueExpr)
					if !ok {
						return stmt, false
					}
					key, ok := kv.Key.(*ast.Ident)
					if !ok {
						return stmt, false
					}
					text, ok := unquote(kv.Value)
					if !ok {
						return stmt, false
					}
					switch key.Name {
					case "Name":
						abbreviation.Name = text
					case "Text":
						abbreviation.Text = text
					default:
						return stmt, false
					}
				}
				stmt.Abbrev = append(stmt.Abbrev, abbreviation)
			}
		}
	}
	return stmt, true
}

// sectionClosure returns the binder closure a Theorem/Lemma body
// argument carries: the FuncLit itself, or the FuncLit inside an
// `Opening(open, func…)` wrapper (proof.Opening — the opened section,
// whose closure still binds the statement's prefix after the opening
// move and so is still subject to the name check). A one-Action body
// binds nothing and is not checked.
func sectionClosure(arg ast.Expr) (*ast.FuncLit, bool) {
	if fn, ok := arg.(*ast.FuncLit); ok {
		return fn, true
	}
	call, ok := arg.(*ast.CallExpr)
	if !ok || len(call.Args) != 2 {
		return nil, false
	}
	switch fun := call.Fun.(type) {
	case *ast.Ident:
		if fun.Name != "Opening" {
			return nil, false
		}
	case *ast.SelectorExpr:
		if fun.Sel.Name != "Opening" {
			return nil, false
		}
	default:
		return nil, false
	}
	fn, ok := call.Args[1].(*ast.FuncLit)
	return fn, ok
}

// checkBinderNames compares the closure's bound parameters against the
// statement's binders, bound as the section boundary binds them
// (prover/proof/section_binding.go): a term parameter the next binder in
// order; a fact parameter the hypotheses whose binders are bound before
// it, or, with none available, a bundle — a bundle binder
// (`∀K:field_on(A).`, whose hypothesis the text leaves implicit) or the
// binders next in order up to the first hypothesis they make available;
// a member its binder, its membership its evidence. The hypotheses are
// read textually: the antecedent's top-level conjuncts, each mentioning
// the binder names it spells as identifiers.
func checkBinderNames(t *testing.T, where, stmt string, fn *ast.FuncLit) {
	t.Helper()
	type param struct {
		name     string
		isFact   bool
		isMember bool
	}
	var params []param
	for i, fld := range fn.Type.Params.List {
		if i == 0 {
			continue // the *Argument context
		}
		isFact := isFactType(fld.Type)
		isMember := isMemberType(fld.Type)
		for _, nm := range fld.Names {
			params = append(params, param{nm.Name, isFact, isMember})
		}
	}
	if len(params) == 0 {
		return
	}
	names, bundles, pieces, ok := statementTelescope(stmt)
	if !ok {
		t.Errorf("%s: cannot read the binders and hypotheses of %q, but the closure declares %d bound "+
			"parameter(s) — the lint must be able to check their names against the statement",
			where, stmt, len(params))
		return
	}
	taken := make([]bool, len(pieces))
	bound := 0
	available := func() []int {
		var out []int
		for i, piece := range pieces {
			if taken[i] {
				continue
			}
			ok := true
			for _, name := range names[bound:] {
				if mentionsIdentifier(piece, name) {
					ok = false
					break
				}
			}
			if ok {
				out = append(out, i)
			}
		}
		return out
	}
	for i := 0; i < len(params); i++ {
		p := params[i]
		if !p.isFact {
			if bound >= len(names) {
				return // the boundary's own arity check reports this
			}
			want := asciiSubscripts(names[bound])
			bound++
			if p.name == "_" {
				continue // a binder the body does not use has no name to match
			}
			if p.isMember {
				// The member's evidence: its membership, taken when its
				// binders are bound.
				for j, piece := range pieces {
					if !taken[j] && strings.HasPrefix(strings.TrimSpace(piece), names[bound-1]+" ∈") {
						taken[j] = true
						break
					}
				}
			}
			if !isGoIdentifier(want) {
				t.Logf("%s: binder %q is not a Go identifier — parameter %q exempt from the name check",
					where, want, p.name)
				continue
			}
			if p.name != want {
				t.Errorf("%s: parameter %d is named %q but binds the statement's ∀%s — "+
					"binding is by order, so a mismatched name is either a wrong name or a "+
					"wrong ORDER, and the second one silently proves something else\n  statement: %s",
					where, i+1, p.name, want, stmt)
			}
			continue
		}
		if bound < len(names) && bundles[bound] {
			// A fact at a bundle binder binds it, with the hypothesis the
			// binder states.
			bound++
			continue
		}
		// A run of fact parameters.
		run := 1
		for i+run < len(params) && params[i+run].isFact {
			run++
		}
		avail := available()
		if len(avail) == 0 {
			// A bundle: the binders next in order, up to the first
			// hypothesis they make available.
			for bound < len(names) && len(avail) == 0 {
				bound++
				avail = available()
			}
			if len(avail) == 0 {
				return // the boundary reports the fact that binds nothing
			}
			for _, j := range avail {
				taken[j] = true
			}
			continue
		}
		if run == 1 {
			for _, j := range avail {
				taken[j] = true
			}
		} else {
			for k := 0; k < run && k < len(avail); k++ {
				taken[avail[k]] = true
			}
			i += run - 1
		}
	}
}

// isFactType reports whether a parameter type is a fact: `Fact`, or a
// typed structure fact — a struct type named `…Fact` instantiated at its
// carriers (`GroupFact[on.G]`, `comm_ring.CommRingFact[on.R]`).
func isFactType(t ast.Expr) bool {
	switch x := t.(type) {
	case *ast.Ident:
		return strings.HasSuffix(x.Name, "Fact")
	case *ast.IndexExpr:
		return isFactType(x.X)
	case *ast.IndexListExpr:
		return isFactType(x.X)
	case *ast.SelectorExpr:
		return strings.HasSuffix(x.Sel.Name, "Fact")
	}
	return false
}

// statementTelescope reads a statement textually as the boundary binds
// it: its binder names in order, over every ∀-group of its telescope,
// which of them are bundle binders (a structure predicate as the type),
// and its hypotheses — the top-level conjuncts of each antecedent, in
// order. ok is false where the text does not read so.
func statementTelescope(stmt string) (names []string, bundles []bool, pieces []string, ok bool) {
	rest := stmt
	for {
		rest = stripEnclosingParens(rest)
		if strings.HasPrefix(rest, "∀") {
			group, typeText, tail, ok := readForAllGroupTyped(rest)
			if !ok {
				return nil, nil, nil, false
			}
			head, _, _ := strings.Cut(strings.TrimSpace(typeText), "(")
			bundle := strings.Contains(typeText, "(") && registry.IsStructurePredicate(strings.TrimSpace(head))
			for _, name := range group {
				names = append(names, name)
				bundles = append(bundles, bundle)
			}
			rest = tail
			continue
		}
		ante, tail, ok := splitTopLevelImply(rest)
		if !ok {
			return names, bundles, pieces, true
		}
		for _, piece := range topLevelConjuncts(ante) {
			pieces = append(pieces, stripEnclosingParens(piece))
		}
		rest = tail
	}
}

// readForAllGroupTyped is readForAllGroup with the group's type
// annotation, "" where the group spells none.
func readForAllGroupTyped(s string) (names []string, typeText, rest string, ok bool) {
	names, rest, ok = readForAllGroup(s)
	if !ok {
		return nil, "", "", false
	}
	body := strings.TrimPrefix(strings.TrimSpace(s), "∀")
	head := body[:len(body)-len(rest)]
	if _, after, found := strings.Cut(head, ":"); found {
		typeText = strings.TrimSuffix(strings.TrimSpace(after), ".")
	}
	return names, typeText, rest, true
}

// splitTopLevelImply is afterTopLevelImply with the antecedent too.
func splitTopLevelImply(s string) (ante, tail string, ok bool) {
	tail, ok = afterTopLevelImply(s)
	if !ok {
		return "", "", false
	}
	return strings.TrimSpace(s[:len(s)-len(tail)-len("⇒")]), tail, true
}

// topLevelConjuncts splits s at its top-level ∧, as the parser joins
// `H₁ ∧ … ∧ Hₙ`; a parenthesized conjunction is one piece, and a
// binder at the top takes the rest of the text as its body.
func topLevelConjuncts(s string) []string {
	var out []string
	depth, start := 0, 0
scan:
	for i, r := range s {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
		case '∀', '∃', 'λ':
			if depth == 0 {
				break scan
			}
		case '∧':
			if depth == 0 {
				out = append(out, strings.TrimSpace(s[start:i]))
				start = i + len("∧")
			}
		}
	}
	return append(out, strings.TrimSpace(s[start:]))
}

// mentionsIdentifier reports whether text spells name as an identifier
// of its own — a maximal run of identifier runes equal to it — outside
// the binders the text itself opens with, which bind a name of their
// own.
func mentionsIdentifier(text, name string) bool {
	rest := stripEnclosingParens(text)
	for strings.HasPrefix(rest, "∀") || strings.HasPrefix(rest, "∃") {
		group, tail, ok := readForAllGroup("∀" + rest[len("∀"):])
		if !ok {
			break
		}
		for _, bound := range group {
			if bound == name {
				return false
			}
		}
		rest = strings.TrimSpace(tail)
	}
	isIdent := func(r rune) bool {
		return r == '_' || r == '\'' || r == 'ʹ' || r == 'ʺ' || unicode.IsLetter(r) || unicode.IsDigit(r) ||
			(r >= '₀' && r <= '₉') || unicode.Is(unicode.Mn, r)
	}
	for _, token := range strings.FieldsFunc(text, func(r rune) bool { return !isIdent(r) }) {
		if token == name {
			return true
		}
	}
	return false
}

// isMemberType reports whether a parameter type is `*Member[…]` — a
// point bound together with its guard (prover/proof/member.go).
func isMemberType(t ast.Expr) bool {
	star, ok := t.(*ast.StarExpr)
	if !ok {
		return false
	}
	index, ok := star.X.(*ast.IndexListExpr)
	if !ok {
		return false
	}
	switch x := index.X.(type) {
	case *ast.Ident:
		return x.Name == "Member"
	case *ast.SelectorExpr:
		return x.Sel.Name == "Member"
	}
	return false
}

// statementBinderNames reads a statement's leading binder slots
// textually, returning one entry per slot ("" for a ⇒-antecedent,
// which carries no name) and whether the prefix parsed at all.
// It walks the same grammar the boundary walks over the parsed Prop:
// ∀-groups and top-level ⇒, left to right.
func statementBinderNames(stmt string, want int) ([]string, bool) {
	var out []string
	rest := stmt
	for len(out) < want {
		// A slot may be wrapped in parentheses that carry no meaning —
		// `H ⇒ (∀s. …)` states the same proposition as `H ⇒ ∀s. …`, and
		// the parser and the section boundary both see through them. The
		// walk has to as well, or a statement is unreadable here for a
		// reason its author cannot act on.
		rest = stripEnclosingParens(rest)
		if strings.HasPrefix(rest, "∀") {
			names, tail, ok := readForAllGroup(rest)
			if !ok {
				return out, false
			}
			out = append(out, names...)
			rest = tail
			continue
		}
		if tail, ok := afterTopLevelImply(rest); ok {
			out = append(out, "")
			rest = tail
			continue
		}
		return out, false
	}
	return out, true
}

// stripEnclosingParens removes paren pairs that wrap the WHOLE string,
// leaving `(A ∧ B) ⇒ C` alone — there the opening paren closes before
// the end, so the pair is grouping rather than wrapping.
func stripEnclosingParens(s string) string {
	for {
		s = strings.TrimSpace(s)
		if !strings.HasPrefix(s, "(") || !strings.HasSuffix(s, ")") {
			return s
		}
		depth := 0
		for i, r := range s {
			switch r {
			case '(':
				depth++
			case ')':
				depth--
			}
			if depth == 0 && i < len(s)-len(")") {
				return s // the leading paren closed early: grouping
			}
		}
		s = s[len("(") : len(s)-len(")")]
	}
}

// readForAllGroup consumes one `∀x y z:τ.` (or `∀x y z.`) group.
func readForAllGroup(s string) (names []string, rest string, ok bool) {
	s = strings.TrimPrefix(strings.TrimSpace(s), "∀")
	depth, end, stop := 0, -1, byte(0)
	for i := 0; i < len(s); i++ {
		switch s[i] {
		case '(':
			depth++
		case ')':
			depth--
		case ':', '.':
			if depth == 0 {
				end, stop = i, s[i]
			}
		}
		if end >= 0 {
			break
		}
	}
	if end < 0 {
		return nil, "", false
	}
	for _, f := range strings.Fields(s[:end]) {
		names = append(names, f)
	}
	if len(names) == 0 {
		return nil, "", false
	}
	if stop == '.' {
		return names, s[end+1:], true
	}
	// Skip the type annotation up to the group-closing '.'.
	depth = 0
	for i := end + 1; i < len(s); i++ {
		switch s[i] {
		case '(':
			depth++
		case ')':
			depth--
		case '.':
			if depth == 0 {
				return names, s[i+1:], true
			}
		}
	}
	return nil, "", false
}

// afterTopLevelImply returns the text after a top-level ⇒, when the
// statement's outermost connective is one. Only ⇔ disqualifies it: the
// DSL's precedence is ⇔ < ⇒ < ∨ < ∧ (the ext/dsl grammar), so a ⇒
// under a ⇔ is not the goal's leading antecedent, while a depth-0 ∨
// binds TIGHTER and therefore always sits inside one of the ⇒'s sides.
// (Bailing on ∨ too would reject the canonical
// `∀m n. m ∣ n ⇒ m ≤ n ∨ n = 0` — and a parenthesized spelling is no
// workaround, since FormatStmtText strips the redundant parens back
// off.)
func afterTopLevelImply(s string) (string, bool) {
	depth, impAt := 0, -1
scan:
	for i, r := range s {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
		case '∀', '∃', 'λ':
			// A binder at the top binds as far as it can: what follows
			// is its body, and no connective in it is the text's.
			if depth == 0 {
				break scan
			}
		case '⇔':
			if depth == 0 {
				return "", false
			}
		case '⇒':
			if depth == 0 && impAt < 0 {
				impAt = i
			}
		}
	}
	if impAt < 0 {
		return "", false
	}
	return s[impAt+len("⇒"):], true
}

// TestStatementBinderNamesReadsAWideBinder: a binder after the
// implication takes the rest of the text, an equivalence in its body
// included — `H ⇒ ∀i. P ⇔ Q` is an implication whose consequent binds i
// — and a binder before any implication takes that implication with it.
func TestStatementBinderNamesReadsAWideBinder(t *testing.T) {
	slots, ok := statementBinderNames("∀n:num. 1 ≤ n ⇒ ∀i:num. i = 0 ⇔ word_bit(i, 1)", 3)
	if !ok || strings.Join(slots, ",") != "n,,i" {
		t.Errorf("got %q, %v; want n, the premise, i", slots, ok)
	}
	if _, ok := afterTopLevelImply("p ⇒ q ⇔ r"); ok {
		t.Errorf("p ⇒ q ⇔ r is an equivalence, not an implication")
	}
	if _, ok := afterTopLevelImply("p ∧ ∀x:A. q(x) ⇒ r"); ok {
		t.Errorf("the implication belongs to the binder's body")
	}
}

// TestLintSequenceBindersUseSubscripts: a binder of a chapter text whose
// name ends in ASCII digits (`x1`, `op2`) is a member of a sequence, and
// a sequence is indexed by subscripts (`x₁`, `op₂`; the constitution's
// binder-name rule). The parser reads `x₁` as the kernel name `x_1`, the
// one the printer subscripts, so `x1` and `x₁` are two names a reader
// cannot tell apart from the printed goal. A label is prose and is not
// read.
func TestLintSequenceBindersUseSubscripts(t *testing.T) {
	group := regexp.MustCompile(`[∀∃λ]([^.:"()∀∃λ]*)[:.]`)
	digits := regexp.MustCompile(`^\pL[\pL']*[0-9]+$`)
	checked := 0
	for _, f := range chapterProofFiles(t) {
		fset, node := parseChapterFile(t, f)
		labels := map[*ast.BasicLit]bool{}
		ast.Inspect(node, func(n ast.Node) bool {
			if call, ok := n.(*ast.CallExpr); ok && len(call.Args) > 0 {
				if label, _, ok := labelArg(call); ok {
					for _, lit := range stringLiterals(label) {
						labels[lit] = true
					}
				}
			}
			return true
		})
		ast.Inspect(node, func(n ast.Node) bool {
			lit, ok := n.(*ast.BasicLit)
			if !ok || lit.Kind != token.STRING || labels[lit] {
				return true
			}
			text, err := strconv.Unquote(lit.Value)
			if err != nil {
				return true
			}
			for _, m := range group.FindAllStringSubmatch(text, -1) {
				for _, name := range strings.Fields(m[1]) {
					checked++
					if digits.MatchString(name) {
						t.Errorf("%s: binder %q ends in ASCII digits; a sequence is indexed by subscripts (%s), the name the printer writes",
							fset.Position(lit.Pos()), name, subscriptSpelling(name))
					}
				}
			}
			return true
		})
	}
	if checked == 0 {
		t.Fatal("no binder read: the scan is vacuous")
	}
}

// subscriptSpelling writes a name's trailing ASCII digits as subscripts.
func subscriptSpelling(name string) string {
	i := len(name)
	for i > 0 && name[i-1] >= '0' && name[i-1] <= '9' {
		i--
	}
	var b strings.Builder
	b.WriteString(name[:i])
	for _, r := range name[i:] {
		b.WriteRune('₀' + (r - '0'))
	}
	return b.String()
}

// asciiSubscripts spells a binder's subscript digits as ASCII digits,
// the closure parameter's spelling of it: `x₁` is bound by `x1`.
func asciiSubscripts(s string) string {
	return strings.Map(func(r rune) rune {
		if r >= '₀' && r <= '₉' {
			return '0' + (r - '₀')
		}
		return r
	}, s)
}

func isGoIdentifier(s string) bool {
	if s == "" {
		return false
	}
	for i, r := range s {
		if r == '_' || unicode.IsLetter(r) || (i > 0 && unicode.IsDigit(r)) {
			continue
		}
		return false
	}
	return true
}

// ---------------------------------------------------------------------------
// KIT ADOPTION CENSUS. A kit member and a hand-written equivalent both
// replay green and both read well alone, and no gate compares them:
// where the corpus derives by hand what a kit member derives, nothing
// says so. This census prints those places. It is a WORKLIST, never a
// bar (t.Logf, no t.Errorf) — good recall, middling precision — so a
// reader triages it and a build never goes red on it.
//
// Part A is statement-level: a string literal in a proof file that is
// an equation between two sums over one AC operation (+ or *), with the
// SAME leaf multiset on both sides, is an AC rearrangement whatever its
// proof — what algebra.Group.RegroupSection and Regroup derive. It is
// reported `[ac-rearrangement]` when its file spells none of the kit's
// verbs (acKitVerbs). The test is the file's, not the statement's: a
// rearrangement proved by hand beside a kit call is counted with the
// kit's. Statements with 2 or 3 leaves are excluded on principle, not
// as a fudge: at that size the statement IS commutativity or
// associativity, a CERTIFICATE the kit consumes, and proving it through
// the kit would be circular.
//
// Part B counts, for each exported function of the step-authoring kits
// (stepAuthoringKits), the occurrences of its name in the proof files.
// A member whose name occurs nowhere is reported `[kit-unused]`: either
// surface nothing calls, which stops following the corpus's style and
// is rewritten by hand rather than repaired, or a function that is the
// kit's own and should not be exported.
// ---------------------------------------------------------------------------

// acStatement reports the leaf multiset of a statement text that is an
// equation between two sums over ONE associative-commutative operation,
// and whether the text is such a statement at all.
//
// Text-level on purpose: it runs over the string literal a proof
// SIGNS, needs no Script to parse against, and an AC rearrangement is
// visible in the surface syntax.
func acStatement(text string) (leaves []string, ok bool) {
	s := strings.TrimSpace(text)
	// Strip the ∀-prefix, one binder group at a time: "∀a b c d:hreal. "
	for strings.HasPrefix(s, "∀") {
		i := strings.Index(s, ". ")
		if i < 0 {
			return nil, false
		}
		s = strings.TrimSpace(s[i+2:])
	}
	// Bare equations only — a connective means the statement is not a
	// rearrangement even if some sub-equation is.
	if strings.ContainsAny(s, "⇒⇔∧∨¬") || strings.Contains(s, "≤") {
		return nil, false
	}
	lhs, rhs, found := splitTopLevel(s, '=')
	if !found {
		return nil, false
	}
	lhs, rhs = strings.TrimSpace(lhs), strings.TrimSpace(rhs)
	if lhs == rhs {
		return nil, false // reflexivity, not a rearrangement
	}
	// The operation is whichever of + / * appears at depth 0; both
	// sides must agree on it (`x * (y + z) = x * y + x * z` does not —
	// that is distributivity, and its leaf multisets differ anyway).
	op, okOp := topLevelOp(lhs)
	if !okOp {
		return nil, false
	}
	if rop, okR := topLevelOp(rhs); !okR || rop != op {
		return nil, false
	}
	l := flattenOp(lhs, op)
	r := flattenOp(rhs, op)
	if len(l) < 4 || len(l) != len(r) {
		return nil, false
	}
	sort.Strings(l)
	sort.Strings(r)
	for i := range l {
		if l[i] != r[i] {
			return nil, false
		}
	}
	return l, true
}

// splitTopLevel splits s at the first occurrence of sep outside any
// parentheses.
func splitTopLevel(s string, sep rune) (before, after string, found bool) {
	depth := 0
	for i, r := range s {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
		case sep:
			if depth == 0 {
				return s[:i], s[i+len(string(sep)):], true
			}
		}
	}
	return "", "", false
}

// topLevelOp returns the sum operator appearing at paren depth 0.
func topLevelOp(s string) (rune, bool) {
	depth := 0
	for _, r := range s {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
		case '+', '*':
			if depth == 0 {
				return r, true
			}
		}
	}
	return 0, false
}

// flattenOp splits s into the leaves of its op-tree, descending through
// parentheses that are themselves op-sums.
func flattenOp(s string, op rune) []string {
	s = strings.TrimSpace(s)
	for strings.HasPrefix(s, "(") && strings.HasSuffix(s, ")") && balanced(s[1:len(s)-1]) {
		s = strings.TrimSpace(s[1 : len(s)-1])
	}
	if before, after, found := splitTopLevel(s, op); found {
		return append(flattenOp(before, op), flattenOp(after, op)...)
	}
	return []string{s}
}

func balanced(s string) bool {
	depth := 0
	for _, r := range s {
		switch r {
		case '(':
			depth++
		case ')':
			depth--
			if depth < 0 {
				return false
			}
		}
	}
	return depth == 0
}

// acKitVerbs are the spellings that route a rearrangement through the
// algebra kit / the ac solver.
var acKitVerbs = []string{"RegroupSection", "Regroup()", "ACRegroup", "CiteACRegroup"}

func TestKitAdoptionCensus(t *testing.T) {
	// ---- Part A: AC rearrangement statements ----
	fset := token.NewFileSet()
	handRolled, viaKit := 0, 0
	for _, f := range chapterProofFiles(t) {
		src, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		usesKit := false
		for _, v := range acKitVerbs {
			if strings.Contains(string(src), v) {
				usesKit = true
				break
			}
		}
		af, err := parser.ParseFile(fset, f, src, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		ast.Inspect(af, func(n ast.Node) bool {
			lit, ok := n.(*ast.BasicLit)
			if !ok || lit.Kind != token.STRING {
				return true
			}
			text, err := strconv.Unquote(lit.Value)
			if err != nil {
				return true
			}
			leaves, ok := acStatement(text)
			if !ok {
				return true
			}
			pos := fset.Position(lit.Pos())
			if usesKit {
				viaKit++
				return true
			}
			handRolled++
			t.Logf("[ac-rearrangement] %s:%d: %d-leaf AC rearrangement, no kit verb in file — "+
				"algebra.Group.RegroupSection/Regroup derives it\n  %s",
				f, pos.Line, len(leaves), text)
			return true
		})
	}
	t.Logf("AC-rearrangement census: %d hand-rolled, %d in kit-using files", handRolled, viaKit)

	// ---- Part B: kit member adoption ----
	chapterSrc := map[string]string{} // file -> source, for call-site counting
	for _, f := range chapterProofFiles(t) {
		src, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		chapterSrc[f] = string(src)
	}

	type member struct{ pkg, name string }
	var members []member
	for _, dir := range stepAuthoringKits {
		entries, err := os.ReadDir(dir)
		if err != nil {
			t.Fatalf("read kit dir %s: %v", dir, err)
		}
		pkg := path.Base(filepath.ToSlash(dir))
		for _, e := range entries {
			name := e.Name()
			if e.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
				continue
			}
			af, err := parser.ParseFile(fset, filepath.Join(dir, name), nil, 0)
			if err != nil {
				t.Fatalf("parse %s: %v", name, err)
			}
			for _, d := range af.Decls {
				fn, ok := d.(*ast.FuncDecl)
				if !ok || !fn.Name.IsExported() || fn.Name.Name == "String" {
					continue // String is a stringer, never kit API
				}
				members = append(members, member{pkg, fn.Name.Name})
			}
		}
	}
	sort.Slice(members, func(i, j int) bool {
		if members[i].pkg != members[j].pkg {
			return members[i].pkg < members[j].pkg
		}
		return members[i].name < members[j].name
	})

	unused := 0
	for _, m := range members {
		sites := 0
		for _, src := range chapterSrc {
			sites += strings.Count(src, m.name)
		}
		if sites == 0 {
			unused++
			t.Logf("[kit-unused] %s.%s: zero corpus call sites — either drift-prone dead "+
				"surface, or genuinely kit-internal and should not be exported", m.pkg, m.name)
		}
	}
	t.Logf("kit-member census: %d member(s) across %d kit package(s), %d with zero corpus adoption",
		len(members), len(stepAuthoringKits), unused)
}

// TestWitnessOrderCensus reports, for every proof registry entry, how
// the entry's SERVED statement (headline when statically known, twin
// Stmt otherwise — resolveDep parity) relates to its normalized install
// prefix — the two orders a ground cite's witness tuple connects since
// the witness-order landing (witnesses are written in the statement's
// binder order; the engine computes the permutation onto the install
// prefix, prover/proof/witness_order.go).
//
// Three populations, all t.Logf (census, not a gate):
//
// - [witness-permuted] — the install prefix is a genuine permutation
// of the statement's slots: the engine reorders at these deps'
// ground cites. Informational; a sudden GROWTH here means a
// Normalize refinement moved prefixes.
//
// - [prefix-renamed] — the install prefix carries a name the
// statement does not bind at all: Normalize renamed a stated
// binder (the DeBruijn spare slot) or minted a new one. A
// FULL-arity ground cite of such a dep is resolved by type-unique
// elimination or PANICS (reorderWitnessesToInstall — positional
// silence here was the measured wrong-instance trap); partial
// tuples stay positional as ever.
//
// - [prefix-merged] — the install prefix has names the statement does
// not bind once, because Normalize merged a multi-clause pack's
// binders across its clauses (MulClauses, ModMultAdd). No name map
// can exist for these, so a ground cite of the PACK can only be read
// positionally.
//
// Read the label as a cause, not a verdict. Prefix-merging is a
// permanent property of the statement's shape — it does not go away
// and is not debt by itself; what costs something is a call SITE
// reading the pack positionally, and the fix there is citing the
// right granularity (a clause projection / atomic entry), never
// witness order. So each line carries its ground-cite count, and the
// summary totals it: that number is the worklist, and zero means the
// merged prefix is inert.
//
// This split exists because the earlier label ([witness-unmapped])
// was computed from the entry alone. When arith re-pointed all 37 of
// its pack cites onto six new clause projections, the census printed
// exactly what it had printed before — it could not see the work,
// and a reader could not tell a solved pack from an unsolved one.
// A census that cannot go to zero manufactures its own re-discovery
// cost.
func TestWitnessOrderCensus(t *testing.T) {
	// Ground-cite call sites, for the paid/unpaid split below.
	chapterSrc := map[string]string{}
	for _, f := range chapterProofFiles(t) {
		src, err := os.ReadFile(f)
		if err != nil {
			t.Fatalf("read %s: %v", f, err)
		}
		chapterSrc[f] = string(src)
	}
	citeSites := newGroundCiteSiteIndex(chapterSrc)
	total, permuted, renamed, merged, paid := 0, 0, 0, 0, 0
	all := registry.All()
	prefixes := fanOut(all, func(e *registry.ProofEntry) []string {
		norm, _ := prop.Normalize(e.Statement().Prop)
		return forallPrefixNamesForCensus(norm.AsProp().Conclusion())
	})
	for i, e := range all {
		stmt := e.Statement().Prop
		prefix := prefixes[i]
		if len(prefix) < 2 {
			continue
		}
		total++
		pos, dup := statementSlotOrderForCensus(stmt)
		// The three lanes mirror reorderWitnessesToInstall exactly: a
		// DUP name anywhere puts the whole prefix in the pack lane
		// (positional pass-through), a FOREIGN name (one the statement
		// does not bind at all — Normalize renamed or minted that
		// binder) puts it in the elimination lane (a full-arity tuple
		// is resolved by type-unique elimination or panics; partial
		// tuples stay positional), and otherwise the name map is total.
		ordered, foreign, mergedHere := true, false, false
		last := -1
		for _, n := range prefix {
			if dup[n] {
				mergedHere = true
				continue
			}
			p, ok := pos[n]
			if !ok {
				foreign = true
				continue
			}
			if p < last {
				ordered = false
			}
			last = p
		}
		switch {
		case mergedHere:
			merged++
			sites := citeSites.sites(e.Name)
			paid += sites
			note := "no positional reads"
			if sites > 0 {
				note = fmt.Sprintf("%d ground cite(s) read positionally", sites)
			}
			t.Logf("[prefix-merged] %-36s install=(%s) — %s", e.Name, strings.Join(prefix, " "), note)
		case foreign:
			renamed++
			sites := citeSites.sites(e.Name)
			note := "no ground cites"
			if sites > 0 {
				note = fmt.Sprintf("%d ground cite(s): full tuples eliminate or panic, partial stay positional", sites)
			}
			t.Logf("[prefix-renamed] %-36s install=(%s) — %s", e.Name, strings.Join(prefix, " "), note)
		case !ordered:
			permuted++
			t.Logf("[witness-permuted] %-36s install=(%s)", e.Name, strings.Join(prefix, " "))
		}
	}
	t.Logf("witness-order census: %d entries with ≥2-binder install prefix, %d permuted, "+
		"%d prefix-renamed, %d prefix-merged (%d ground cite(s) still positional)",
		total, permuted, renamed, merged, paid)
}

// TestLintTwiceBoundPrefixBinderIsReadPositionally refuses a statement
// that a partial witness tuple reads wrong in silence. A tuple written
// against a statement is mapped onto the install prefix by binder name
// (prover/proof/witness_order.go); where the statement binds a prefix
// name a second time — a law's index bound again inside an obligation,
// a point re-bound under a quantifier of the body — no slot is
// addressable by name and the tuple is read POSITIONALLY against the
// install prefix. That reading is correct where the install prefix
// stands in the stated order, and it is corrected by type where the
// positional reading is ill-typed; where the clause form reorders the
// prefix AND two of its binders share a type, a partial tuple lands on
// the wrong binders and the premise fails to materialize, or proves
// another instance (real_polynomial.Compose's `Induction.At(P, p)`, read
// as (p, P) until the rules' binders were restated). The remedy is the
// statement's: bind the inner occurrence under another name — α-neutral,
// the entry's key unmoved.
func TestLintTwiceBoundPrefixBinderIsReadPositionally(t *testing.T) {
	for _, e := range registry.All() {
		stmt := e.Statement().Prop
		if stmt.NumHyps() > 0 {
			continue
		}
		prefix, _ := ematch.StripGuardedForalls(stmt.Conclusion())
		if len(prefix) < 2 {
			continue
		}
		_, dup := statementSlotOrderForCensus(stmt)
		var twice []string
		stated := make([]string, len(prefix))
		for i, v := range prefix {
			stated[i] = string(v.Name())
			if dup[stated[i]] {
				twice = append(twice, stated[i])
			}
		}
		if len(twice) == 0 {
			continue
		}
		norm, _ := prop.Normalize(stmt)
		clausePrefix, _ := ematch.StripGuardedForalls(norm.AsProp().Conclusion())
		clause := make([]string, len(clausePrefix))
		for i, v := range clausePrefix {
			clause[i] = string(v.Name())
		}
		if strings.Join(clause, " ") == strings.Join(stated, " ") {
			continue
		}
		shared := false
		for i := range prefix {
			for j := i + 1; j < len(prefix); j++ {
				if prefix[i].Type().Equals(prefix[j].Type()) {
					shared = true
				}
			}
		}
		if !shared {
			continue
		}
		t.Errorf("%s binds %s twice, its clause form reorders the prefix (stated (%s), clause (%s)) and two "+
			"prefix binders share a type: a partial witness tuple is read positionally against the clause "+
			"prefix and lands on the wrong binders in silence — bind the inner occurrence of %s under another "+
			"name (α-neutral; the key does not move)\n  statement: %s",
			e.Name, strings.Join(twice, " and "), strings.Join(stated, " "), strings.Join(clause, " "),
			strings.Join(twice, " / "), prop.PrintProp(stmt))
	}
}

// groundCiteSiteIndex counts the GROUND cites of the chapter sources —
// `At(`, `Cite(`, `CiteKeep(` or `Fact(` followed by a name and a comma,
// a witness tuple after the target — in ONE pass, so the census asks for
// an entry's count by lookup. A bare `Cite(X)` is not counted: with no
// witnesses there is no tuple to read in any order. A qualified site
// `Cite(pkg.Name,` counts under its qualifier wherever it appears; a bare
// site `Cite(Name,` counts under the package of the file it is in, since
// a bare name reads inside its own package. Approximate by construction
// — it is a census, and the number that matters is whether it is zero.
// Scanning the corpus once per entry instead was 318 whole-corpus regex
// passes (9 MB each) and 47 s of a 72 s lint battery.
type groundCiteSiteIndex struct {
	qualified map[string]int // "<pkg>.<Name>" → sites, any file
	bare      map[string]int // "<file package>.<Name>" → bare sites in that package's files
}

var (
	groundCiteSiteRe = regexp.MustCompile(
		`\b(?:At|Cite|CiteKeep|Fact)\(([A-Za-z_][A-Za-z0-9_]*)(?:\.([A-Za-z_][A-Za-z0-9_]*))?\s*,`)
	packageLineRe = regexp.MustCompile(`(?m)^package\s+([A-Za-z_][A-Za-z0-9_]*)`)
)

func newGroundCiteSiteIndex(chapterSrc map[string]string) *groundCiteSiteIndex {
	idx := &groundCiteSiteIndex{qualified: map[string]int{}, bare: map[string]int{}}
	for _, src := range chapterSrc {
		filePkg := ""
		if m := packageLineRe.FindStringSubmatch(src); m != nil {
			filePkg = m[1]
		}
		for _, m := range groundCiteSiteRe.FindAllStringSubmatch(src, -1) {
			switch {
			case m[2] != "":
				idx.qualified[m[1]+"."+m[2]]++
			case filePkg != "":
				idx.bare[filePkg+"."+m[1]]++
			}
		}
	}
	return idx
}

// sites is the number of ground-cite call sites that name the entry:
// qualified by its package anywhere, or bare inside its package.
func (idx *groundCiteSiteIndex) sites(entryName string) int {
	bare, pkg := entryName, ""
	if i := strings.LastIndex(entryName, "."); i >= 0 {
		bare = entryName[i+1:]
		pkg = entryName[:i]
		if j := strings.LastIndex(pkg, "/"); j >= 0 {
			pkg = pkg[j+1:]
		}
	}
	n := 0
	if pkg != "" {
		n += idx.qualified[pkg+"."+bare]
	}
	n += idx.bare[pkg+"."+bare]
	return n
}

// forallPrefixNamesForCensus mirrors prover/proof's forallPrefixNames
// (unexported there): leading ∀-binder names, outer to inner.
func forallPrefixNamesForCensus(t core.Term) []string {
	var names []string
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return names
		}
		names = append(names, string(abs.Var().Name()))
		t = abs.Body()
	}
}

// statementSlotOrderForCensus mirrors prover/proof's statementSlotOrder:
// reading positions of free variables (first occurrence) and quantifier
// binders (binding site), hyps before conclusion; dup marks names bound
// more than once.
func statementSlotOrderForCensus(ref core.Prop) (pos map[string]int, dup map[string]bool) {
	pos = map[string]int{}
	dup = map[string]bool{}
	next := 0
	bind := func(n string) {
		if _, ok := pos[n]; ok {
			dup[n] = true
			return
		}
		pos[n] = next
		next++
	}
	var walk func(t core.Term)
	walk = func(t core.Term) {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			bind(string(abs.Var().Name()))
			walk(abs.Body())
			return
		}
		if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
			bind(string(abs.Var().Name()))
			walk(abs.Body())
			return
		}
		switch tt := t.(type) {
		case core.VarTerm:
			if _, ok := pos[string(tt.Name())]; !ok {
				bind(string(tt.Name()))
			}
		case core.AppliedTerm:
			walk(tt.Fun())
			walk(tt.Arg())
		case core.AbsTerm:
			walk(tt.Body())
		}
	}
	pp := ref.AsProp()
	for i := 0; i < pp.NumHyps(); i++ {
		walk(pp.Hyp(i))
	}
	walk(pp.Conclusion())
	return pos, dup
}

// TestWitnessDecodingCommentCensus scans every proof file for
// comments that DECODE a machine witness order — "normalized … binder /
// prefix / slot" language adjacent to a ground cite. Since the
// witness-order landing (witnesses follow the dep's stated binder
// order; the engine permutes), such a comment is either stale doctrine
// or a site quietly re-paying the retired tax; the wave deleted the
// whole population, and this census keeps the count visible so a
// regression is one t.Logf away. Deliberate positional residue
// ([witness-unmapped] deps) states itself WITHOUT the word
// "normalized" — real_completeness.NaddComplete's note is the model.
func TestWitnessDecodingCommentCensus(t *testing.T) {
	decoding := regexp.MustCompile(`(?i)normalized[^\n]*(binder|prefix|slot)|witness order follows`)
	found := 0
	for _, path := range chapterProofFiles(t) {
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatalf("read %s: %v", path, err)
		}
		for i, line := range strings.Split(string(data), "\n") {
			if !strings.Contains(line, "//") {
				continue
			}
			comment := line[strings.Index(line, "//"):]
			if decoding.MatchString(comment) {
				found++
				t.Logf("[witness-decoding-comment] %s:%d: %s", path, i+1, strings.TrimSpace(comment))
			}
		}
	}
	t.Logf("witness-decoding-comment census: %d comment(s) decoding a machine witness order", found)
}

// ---------------------------------------------------------------------------
// A LIST SLOT ALREADY SEQUENCES. Chain composes several Actions into
// ONE, which is what a single-Action slot genuinely needs (Expect /
// Finally / CloseIfOpen, a helper's return, a variable). In a variadic
// `...Action` slot it composes nothing: the slot runs the identical
// `for … applyAction(s, node)` loop Chain runs, so the wrapper buys a
// pair of parentheses and an indent level and nothing else.
//
// The same rule for the branch verbs: a branch body is a list of
// Actions or ONE closure, so `a.When(l, Given(func…))` says with a
// wrapper what `a.When(l, func…)` says without one.
// ---------------------------------------------------------------------------

// actionListSlots maps a callee to the first argument index from which
// its parameters are a variadic `...Action`. Every entry is read off the
// constructor's own signature. `Do` is safe to list because a chapter
// proof file never holds a *GoalStackNode — its `.Do` is always
// Argument.Do (every receiver in the corpus is an Argument variable).
var actionListSlots = map[string]int{
	"Chain": 0, "Deduce": 0, "Do": 0, "Prove": 0,
	"Case": 1, "MakeCase": 1,
	"Show": 1, "Have": 2, "Obtain": 2, "Obtain2": 2, "Obtain3": 2, "Obtain4": 2, "Obtain5": 2,
	"Forward": 1, "Backward": 1, "BothHold": 1, "NeitherHolds": 1,
	"LeftHolds": 1, "RightHolds": 1,
	"FinalLeg": 1, "Leg": 2, "LeLeg": 2, "EqLeg": 2,
	"Assuming": 2, "Unless": 2, "Suffices": 2,
	"When": 1, "Otherwise": 1, "Base": 1, "Step": 1,
}

// branchVerbs are the verbs that claim a named branch of an open split
// (prover/proof/branch.go) plus the Chain-form ⇔ halves: each takes its
// body as a list of Actions or one closure.
var branchVerbs = map[string]bool{
	"When": true, "Otherwise": true, "Base": true, "Step": true,
	"Forward": true, "Backward": true, "BothHold": true, "NeitherHolds": true,
	"LeftHolds": true, "RightHolds": true,
}

func TestLintNoWrapperInActionList(t *testing.T) {
	fset := token.NewFileSet()
	for _, path := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, path, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", path, err)
		}
		ast.Inspect(af, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			name := verbName(call)
			from, listSlot := actionListSlots[name]
			if !listSlot || call.Ellipsis != token.NoPos {
				return true
			}
			for i := from; i < len(call.Args); i++ {
				inner, ok := call.Args[i].(*ast.CallExpr)
				if !ok {
					continue
				}
				switch calleeName(inner) {
				case "Chain":
					t.Errorf("%s: Chain inside %s's Action list — the slot already sequences; "+
						"drop the wrapper and list the steps",
						fset.Position(inner.Pos()), name)
				case "Given", "Derive":
					// Only the Argument METHODS take a closure. The
					// package-level Forward/Backward/BothHold/NeitherHolds
					// used inside a Chain-form SplitIff take `...Action`,
					// where Given(func…) is the only spelling there is —
					// telling the two apart is the call form.
					_, isMethod := call.Fun.(*ast.SelectorExpr)
					if isMethod && branchVerbs[name] && len(call.Args) == from+1 {
						t.Errorf("%s: %s inside %s's body — a branch body takes the closure "+
							"directly: %s(label, func(b *Argument%s) { … })",
							fset.Position(inner.Pos()), calleeName(inner), name, name,
							map[string]string{"Given": ", h Fact", "Derive": ""}[calleeName(inner)])
					}
				}
			}
			return true
		})
	}
}

// ---------------------------------------------------------------------------
// NO TrivialSimplify() AT A CLOSE SITE. `TrivialSimplify()` is the
// β-reduce / trivial-simplification ministep — a SHAPING action, which
// the manual's closers table marks "may not close". The closing verbs
// are `TrivialNormalized()` (the normalize-to-⊤ short-circuit, no CNF
// key), `Refl()`, and — for arithmetic — `ByArith(premises…)`. A leaf
// that ENDS on TrivialSimplify() replays green only
// because the action happened to close, so no gate ever said a word:
// the list chapter's consolidation found eight such leaves in files
// whose siblings end the identical job on TrivialNormalized(), and a
// reader could not learn the closing convention from the chapter.
// This lint is the observing step that rule
// lacked: a `TrivialSimplify()` that is the LAST action of an action
// list (the last argument of a call — Show / Case / Base / Step / Do /
// Chain / When / Otherwise / …) is refused, with the closer to spell.
//
// The allowlist below carries the pre-lint stock, file → EXACT count
// of terminal sites, a shrink-only ratchet as for the positional hyp
// addresses: a count above the entry fails (no new close sites), a
// count below fails too, telling you to lower the entry.
// ---------------------------------------------------------------------------

var terminalTrivialSimplifyAllowlist = map[string]int{}

func TestLintNoTerminalTrivialSimplify(t *testing.T) {
	fset := token.NewFileSet()
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		var sites []string
		endsOnTrivialSimplify := func(call *ast.CallExpr) bool {
			if len(call.Args) == 0 {
				return false
			}
			last, ok := call.Args[len(call.Args)-1].(*ast.CallExpr)
			if !ok || len(last.Args) != 0 {
				return false
			}
			id, ok := last.Fun.(*ast.Ident)
			return ok && id.Name == "TrivialSimplify"
		}
		isDo := func(call *ast.CallExpr) bool {
			sel, ok := call.Fun.(*ast.SelectorExpr)
			return ok && sel.Sel.Name == "Do"
		}
		ast.Inspect(af, func(n ast.Node) bool {
			switch node := n.(type) {
			case *ast.CallExpr:
				// The last action of an action list — a Case / Show /
				// Base / Step / Chain / … argument list. `a.Do(…)` is
				// the one verb whose list may END on a shaping action
				// and continue the block, so it is judged by position
				// in its closure instead (below).
				if !isDo(node) && endsOnTrivialSimplify(node) {
					pos := fset.Position(node.Args[len(node.Args)-1].Pos())
					sites = append(sites, fmt.Sprintf("%s:%d", f, pos.Line))
				}
			case *ast.FuncLit:
				// A closure body's LAST statement being `x.Do(…,
				// TrivialSimplify())` makes that action the block's
				// close (Derive / Given / a branch closure must close).
				if node.Body == nil || len(node.Body.List) == 0 {
					return true
				}
				if es, ok := node.Body.List[len(node.Body.List)-1].(*ast.ExprStmt); ok {
					if call, ok := es.X.(*ast.CallExpr); ok && isDo(call) && endsOnTrivialSimplify(call) {
						pos := fset.Position(call.Args[len(call.Args)-1].Pos())
						sites = append(sites, fmt.Sprintf("%s:%d", f, pos.Line))
					}
				}
			}
			return true
		})
		want := terminalTrivialSimplifyAllowlist[chapterRel(f)]
		if len(sites) > want {
			t.Errorf("%s: %d TrivialSimplify() close site(s), allowlist permits %d — "+
				"TrivialSimplify() shapes and MAY NOT close (manual: Closers); a leaf that ends on it "+
				"closes by accident. Spell the close: TrivialNormalized() (normalize-to-⊤, no CNF key), "+
				"Refl(), or ByArith(premises…) for an arithmetic close. Sites:\n  %s",
				f, len(sites), want, strings.Join(sites, "\n  "))
		} else if len(sites) < want {
			t.Errorf("%s: %d TrivialSimplify() close site(s) but the allowlist still says %d — "+
				"lower (or delete) its entry so the ratchet tracks reality",
				f, len(sites), want)
		}
	}
}
