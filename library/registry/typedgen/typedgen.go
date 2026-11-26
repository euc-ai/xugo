// Package typedgen renders a family's typed theorem-wrapper surface
// (zz_typed_thms_gen.go): one wrapper type per registered entry, its
// statement's ∀-chain as Typed parameters and its HOL type variables
// as Go type parameters (Go 1.27 generic methods). The gen_family
// command writes the rendering and, by default, wraps the bare
// `family.Add` vars in the member files in place (ApplyWraps); the
// drift gate (TestTypedGenCurrent) re-renders with the same code and
// compares against disk byte-for-byte. The design record is the
// typed-surface section of library/chapter_constitution.md.
//
// The file also carries the family package's doc comment, on its
// package clause: "Package <pkg> — <gloss>.", the title line of the
// chapter's README.md (registry.ChapterGloss) read as a sentence. It
// rides here because this is the one generated file every family has,
// and because a family's doc comment is never hand-written: the gloss
// has one home, the README's title, and the gates' package-doc lint
// (TestLintPackageDoc) refuses a family whose doc comment comes from
// any other file. The sentence is the line `go doc` opens on and the
// line pkg.go.dev prints beside the package, both of which take the
// FIRST sentence as go/doc cuts it — at a period followed by a space —
// so a gloss that go/doc would cut short is refused here, by name,
// and the title is reworded.
//
// The file reads framework names through library/authoring's existing
// aliases (Fact, Typed[Nat]), importing that surface only when used.
// Names outside that surface retain their qualifiers. Another chapter's
// phantom is aliased here for the family's proof files — each one a
// statement of the family names, and each one a proof file of it does
// (typedefsNamedIn) — and the phantom of each statement letter the
// family's statements bind beyond A–E is declared here
// (letter_phantoms.go).
package typedgen

import (
	"fmt"
	"go/ast"
	"go/doc"
	"go/format"
	"go/parser"
	"go/token"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// File is the product's file name, beside the family package it serves.
const File = "zz_typed_thms_gen.go"

// Rendered is one family's typed surface as the generator produces it.
type Rendered struct {
	Source   []byte   // the gofmt-formatted file
	Wrappers int      // wrapper types rendered
	Notes    []string // the bare wrappers and the letters with no phantom, one line each — the command prints them

	typeNames map[string]wrapTarget // bare entry name → its wrapper, for ApplyWraps
}

// Render produces zz_typed_thms_gen.go for fam in the Go package
// named pkg, whose files are in dir and whose chapter README glosses it
// as gloss (registry.ChapterGloss): the package's doc comment, the
// aliases of other chapters' typedef phantoms, the phantoms of the
// statement letters beyond A–E, then the wrappers. The wrappers are
// rendered in entry-NAME order, not registration
// order: registration order is Go's package initialization order,
// which a dependency edit inside one member moves silently, and the
// drift gate needs a rendering that only a statement change can move.
// The alias block is the one part read off the package's files as well
// as its statements: a phantom a proof file names bare keeps its alias
// when the last statement that named the type leaves the family.
func Render(fam *registry.Family, pkg, dir, gloss string) (*Rendered, error) {
	docComment, err := packageDoc(pkg, gloss)
	if err != nil {
		return nil, err
	}
	wrappers, namedTypedefs, notes, err := buildWrappers(fam)
	if err != nil {
		return nil, err
	}
	spelled, err := typedefsNamedIn(dir, chapterImportPath+familyDir(fam))
	if err != nil {
		return nil, err
	}
	for metatype := range spelled {
		namedTypedefs[metatype] = true
	}
	declared, unspelled := familyLetters(fam)
	if len(unspelled) > 0 {
		notes = append(notes, fmt.Sprintf("%s: statement %s %s without a phantom (typedgen.OwnerOfLetter)",
			fam.Name, plural(len(unspelled), "letter", "letters"), joinLetters(unspelled)))
	}
	src, err := renderTyped(pkg, docComment, fam, wrappers, namedTypedefs, declared, unspelled)
	if err != nil {
		return nil, err
	}
	formatted, err := format.Source([]byte(src))
	if err != nil {
		return nil, fmt.Errorf("typedgen: rendered source does not format (generator bug): %w\n%s", err, src)
	}
	names := map[string]wrapTarget{}
	for _, w := range wrappers {
		names[w.bareName] = wrapTarget{typeName: w.typeName, structure: w.structure}
	}
	return &Rendered{Source: formatted, Wrappers: len(wrappers), Notes: notes, typeNames: names}, nil
}

// packageDoc is the doc comment of the family package named pkg, whose
// chapter README glosses it as gloss: one sentence, the README's title
// line with "Package" for its "#". A gloss go/doc would end early is
// an error, because the sentence go/doc cuts is the one a reader of
// `go doc` and of pkg.go.dev's listing is shown.
func packageDoc(pkg, gloss string) (string, error) {
	sentence := fmt.Sprintf("Package %s — %s.", pkg, gloss)
	if shown := new(doc.Package).Synopsis(sentence); shown != sentence {
		return "", fmt.Errorf("typedgen: package %s: the README title's gloss %q does not read as one sentence of a doc comment — "+
			"go/doc ends a sentence at a period followed by a space, and shows %q. Reword the title line of the chapter's README.md",
			pkg, gloss, shown)
	}
	return "// " + sentence + "\n", nil
}

// ---------------------------------------------------------------------------
// Reading the statements
// ---------------------------------------------------------------------------

// witnessSlot is one ∀-binder of the statement's leading chain — a
// typed witness parameter of the generated At.
type witnessSlot struct {
	name    string // the statement's binder name, sanitized to a Go parameter
	phantom string // the binder's HOL type as a phantom spelling
	binder  string // the statement's binder name as stated
	typ     core.HolType

	// The dimension refinement (dimension_slots.go): a carrier-typed
	// binder every Dim-declared operation of the statement reads at ONE
	// dimension binder is a dimtypes.Vec parameter at that dimension's
	// phantom (vecDim names the dimension binder), and the dimension
	// binder's own slot is written off the vectors (elided). A
	// matrix-carrier binder read at one row binder and one column binder
	// is the same thing at two dimensions: a dimtypes.Mat parameter, both
	// binders elided. A map-carrier binder read at one source binder and
	// one target binder is a dimtypes.VecFun parameter the same way, the two
	// binders — or the one, for a map of a space into itself — elided.
	// inhabited marks a vector or matrix whose membership
	// is one of the statement's antecedents: the parameter is a
	// proof.Inhabited / proof.InhabitedMat and the cite bundles its
	// evidence. member marks a point whose membership in a COMPONENT
	// set of the structure a law is read at is one of the reading's
	// guards, at any level of its telescope: the parameter is a
	// proof.Member and the reading's cite bundles its evidence likewise.
	elem         string // the element phantom of a vector, matrix or map slot
	vecDim       string // the dimension binder a vector slot is read at ("" for a plain slot)
	matRows      string // the row-dimension binder a matrix slot is read at ("" for a non-matrix slot)
	matCols      string // the column-dimension binder a matrix slot is read at
	vecFunSource string // the dimension binder a map slot is read on ("" for a non-map slot)
	vecFunTarget string // the dimension binder a map slot's values are read at
	elided       bool   // a dimension binder written off its vectors, matrices or maps
	inhabited    bool   // the evidence of the slot's membership rides the cite
	member       bool   // the slot is a point with its membership in a component set
	// carrier is a member slot's carrier phantom: the reading's carrier
	// type parameter (Car0, Car1) where the law's structure has a phantom
	// and the set is one of its carriers, on.Any otherwise.
	carrier string
}

// typedefPhantom names a typedef's phantom and the package that owns
// it. The vocabulary is decentralized (ext/holtype_phantom.go): a
// phantom is DECLARED beside its type's mint, and this table is only
// the generator's map of where the mints are. A wrapper names a
// phantom minted below the chapters by its owner (dsl.Real); the
// family being generated references its own phantoms bare and aliases
// another chapter's (the alias block in the preamble). A metatype
// absent here still fails loudly in renderPhantom; landing the phantom
// beside the mint and adding its row IS the teaching the error asks
// for. A row whose phantom has gone is read by nothing here, and is
// TestTypedefPhantomsResolve's to report.
type typedefPhantom struct {
	name  string // the phantom's exported name at its home
	arity int
	home  string // import path of the declaring package
}

const chapterImportPath = "github.com/euc-ai/xugo/library/proofs/"

// aliasParams are the type parameters an alias of a phantom above
// arity 2 is spelled with; arities 1 and 2 keep X and X, Y.
var aliasParams = []string{"X", "Y", "Z", "W", "V", "T"}

var typedefPhantoms = map[string]typedefPhantom{
	"ind":                  {"Ind", 0, chapterImportPath + "nat_num/peano"},
	"real":                 {"Real", 0, "github.com/euc-ai/xugo/ext/dsl"},
	"int":                  {"Int", 0, "github.com/euc-ai/xugo/ext/dsl"},
	"hreal":                {"Hreal", 0, chapterImportPath + "real/tower/internal/nonneg_real"},
	"nadd":                 {"Nadd", 0, chapterImportPath + "real/tower/internal/eudoxus_slope"},
	"list":                 {"List", 1, chapterImportPath + "datatypes/list"},
	"option":               {"Option", 1, chapterImportPath + "datatypes/option"},
	"btree":                {"Btree", 1, chapterImportPath + "datatypes/tree"},
	"fo_formula":           {"Formula", 1, chapterImportPath + "datatypes/first_order"},
	"recspace":             {"Recspace", 1, chapterImportPath + "datatypes/datatype_universe"},
	"permutation":          {"Permutation", 1, chapterImportPath + "algebra/group/symmetric_group"},
	"free_group":           {"FreeGroup", 1, chapterImportPath + "algebra/group/free_group"},
	"complex":              {"Complex", 0, chapterImportPath + "complex/complex_field"},
	"extended_nonneg_real": {"ExtendedNonnegReal", 0, chapterImportPath + "real/extended_nonneg_real"},
	"group_ops":            {"GroupOps", 1, chapterImportPath + "algebra/group/group"},
	"field_ops":            {"FieldOps", 1, chapterImportPath + "algebra/field/field"},
	"ring_ops":             {"RingOps", 1, chapterImportPath + "algebra/module/module_record"},
	"module_ops":           {"ModuleOps", 2, chapterImportPath + "algebra/module/module_record"},
	"complex_ops":          {"ComplexOps", 2, chapterImportPath + "algebra/module/chain_complex"},
	"square_zero_ops":      {"SquareZeroOps", 4, chapterImportPath + "algebra/ring/square_zero_extension"},
	"module_extension_ops": {"ModuleExtensionOps", 4, chapterImportPath + "algebra/module/module_extension"},
	"category_ops":         {"CategoryOps", 2, chapterImportPath + "category/category"},
	"functor_ops":          {"FunctorOps", 4, chapterImportPath + "category/category"},
	"morphism_triple":      {"MorphismTriple", 2, chapterImportPath + "category/category"},
	"simplicial_ops":       {"SimplicialOps", 1, chapterImportPath + "simplicial/simplicial_set"},
	"bisimplicial_ops":     {"BisimplicialOps", 1, chapterImportPath + "simplicial/simplicial_homotopy"},
	"sobolev_localization": {"SobolevLocalization", 1, chapterImportPath + "manifold/sobolev_section"},
	"scm_model":            {"ScmModel", 3, chapterImportPath + "causal/structural_model"},
	"do_expr":              {"DoExpr", 1, chapterImportPath + "causal/do_derivation"},
	"fd_node":              {"FdNode", 0, chapterImportPath + "causal/identifiability"},
	"bow_node":             {"BowNode", 0, chapterImportPath + "causal/identifiability"},
}

// TypedefPhantom is the phantom a typedef's metatype is spelled by: the
// name its home package exports and the number of type arguments it
// takes, ok=false for a metatype the table has no row for. The emitter
// of session proofs (library/emit) spells an instance type through it,
// so a typedef has one phantom spelling in generated and emitted source
// alike.
func TypedefPhantom(metatype string) (name string, arity int, ok bool) {
	ph, ok := typedefPhantoms[metatype]
	return ph.name, ph.arity, ok
}

// mintedByAChapter reports whether the phantom's home is a chapter's
// package. A phantom minted below the chapters (ext, ext/dsl) is one
// library/authoring declares for every proof file.
func (ph typedefPhantom) mintedByAChapter() bool {
	return strings.HasPrefix(ph.home, chapterImportPath)
}

// spelling is the phantom's name as the generated file writes it:
// qualified by its owner for a phantom minted below the chapters, and
// bare for a chapter's — the family's own, or the preamble's alias of
// another chapter's.
func (ph typedefPhantom) spelling() string {
	if ph.mintedByAChapter() {
		return ph.name
	}
	return path.Base(ph.home) + "." + ph.name
}

// TypedefsInScope is the set of typedef metatypes whose phantom a
// proof file of fam names by its bare name once the family's typed
// surface is generated: a typedef minted below the chapters, whose
// phantom library/authoring declares for every proof file; a typedef
// whose phantom the family's own package declares; and another
// chapter's that a wrapper's signature names, which the generated
// preamble then aliases from its home (renderTyped) — the signature of
// an entry the family registers, or of a statement about to join it
// (joining). A phantom of any other typedef is undefined in the
// family's proof files. fam is nil for a chapter that registers
// nothing yet.
func TypedefsInScope(fam *registry.Family, joining ...core.Prop) map[string]bool {
	inScope := map[string]bool{}
	for metatype, ph := range typedefPhantoms {
		if !ph.mintedByAChapter() {
			inScope[metatype] = true
		}
	}
	if fam != nil {
		if _, named, _, err := buildWrappers(fam); err == nil {
			for metatype := range named {
				inScope[metatype] = true
			}
		}
		home := chapterImportPath + familyDir(fam)
		for metatype, ph := range typedefPhantoms {
			if ph.home == home {
				inScope[metatype] = true
			}
		}
	}
	for _, p := range joining {
		if p == nil {
			continue
		}
		named := map[string]bool{}
		if _, _, err := readSignature(p, named); err != nil {
			continue
		}
		for metatype := range named {
			inScope[metatype] = true
		}
	}
	return inScope
}

// memberFiles lists the hand-written Go files of the family package in
// dir, sorted: every .go file but the tests and the generated ones
// (zz_*). A directory that does not exist yet has none.
func memberFiles(dir string) ([]string, error) {
	files, err := filepath.Glob(filepath.Join(dir, "*.go"))
	if err != nil {
		return nil, fmt.Errorf("typedgen: glob: %w", err)
	}
	sort.Strings(files)
	var members []string
	for _, file := range files {
		base := filepath.Base(file)
		if strings.HasSuffix(base, "_test.go") || strings.HasPrefix(base, "zz_") {
			continue
		}
		members = append(members, file)
	}
	return members, nil
}

// typedefsNamedIn is the set of typedef metatypes of other chapters
// whose phantom a member file of the package in dir names bare: an
// identifier of the phantom's name that its file does not resolve —
// not a local, not the selector of a qualified name — and that no
// member file declares at package level. Such a name is the alias the
// generated preamble declares, or it is undefined; selfPath is the
// package's import path, whose own phantoms need no alias.
func typedefsNamedIn(dir, selfPath string) (map[string]bool, error) {
	byName := map[string]string{}
	for metatype, ph := range typedefPhantoms {
		if ph.mintedByAChapter() && ph.home != selfPath {
			byName[ph.name] = metatype
		}
	}
	files, err := memberFiles(dir)
	if err != nil {
		return nil, err
	}
	named, declared := map[string]bool{}, map[string]bool{}
	for _, file := range files {
		parsed, err := parser.ParseFile(token.NewFileSet(), file, nil, 0)
		if err != nil {
			return nil, fmt.Errorf("typedgen: parse %s: %w", file, err)
		}
		for _, ident := range parsed.Unresolved {
			if metatype, ok := byName[ident.Name]; ok {
				named[metatype] = true
			}
		}
		for _, decl := range parsed.Decls {
			switch decl := decl.(type) {
			case *ast.FuncDecl:
				if decl.Recv == nil {
					declared[decl.Name.Name] = true
				}
			case *ast.GenDecl:
				for _, spec := range decl.Specs {
					switch spec := spec.(type) {
					case *ast.TypeSpec:
						declared[spec.Name.Name] = true
					case *ast.ValueSpec:
						for _, name := range spec.Names {
							declared[name.Name] = true
						}
					}
				}
			}
		}
	}
	for name, metatype := range byName {
		if declared[name] {
			delete(named, metatype)
		}
	}
	return named, nil
}

// familyDir is the family's package directory under the chapter root.
func familyDir(fam *registry.Family) string {
	if fam.Dir != "" {
		return fam.Dir
	}
	return fam.Name
}

// wrapper is everything the renderer needs for one entry.
type wrapper struct {
	entry    *registry.ProofEntry
	bareName string // the Name the member file spells (Add prefixes the family)
	typeName string
	letters  []string // the statement's type variables, first-occurrence order
	slots    []witnessSlot

	// structure marks the definition entry of a structure the family
	// defines (DefineStructure): its var holds the *registry.Structure,
	// and the wrapper embeds it (registry.StructureLike), so the
	// structure's laws, axioms and fields read through the wrapped var.
	structure bool

	// The structure-law refinement: a statement `∀comps. S(comps) ⇒
	// body` whose leading binders are exactly the arguments of its
	// antecedent's predicate gets a Read(instance) — the law read at
	// an instance of S (proof.Read), its component slots gone. The
	// reading's At declares the law's type parameters its own slots
	// spell and no others: a letter only the components' types carry
	// is fixed by the instance, and Go infers no type parameter that
	// no argument mentions.
	components int // component slots; 0 for a statement that is not a law
	// readingSlots are the reading's own witness slots — the law's
	// beyond its components, in the statement's order, a binder bound
	// ahead of the components among them — with the membership
	// refinement read against the reading's statement: a membership
	// that was the law's second antecedent is the reading's first, and
	// a point's membership in a component becomes a Member slot. A
	// dimension binder only a component anchored is a parameter here
	// (keepUnanchoredDimensions).
	readingSlots []witnessSlot

	// The carrier refinement (structure_phantoms.go). law is the law's
	// structure where it has a phantom the family's file can name: the
	// Read is typed. projection is the structure fact a typed law's body
	// is, read as that structure's typed fact; closure, ≥ 0, is the
	// carrier a closure law's body puts a term of its points in, and
	// closureElem that term's phantom. instance marks a wrapper or
	// reading that may stand as an untyped instance of a typed Read: its
	// statement, or its body, is a structure's fact.
	law             *lawPhantom
	projection      *projection
	closure         int
	closureElem     string
	instance        bool
	readingInstance bool
	selfPath        string
}

func buildWrappers(fam *registry.Family) ([]wrapper, map[string]bool, []string, error) {
	var wrappers []wrapper
	var notes []string
	usedTypedefs := map[string]bool{}
	byTypeName := map[string]string{}
	prefix := path.Base(fam.Name) + "."
	selfPath := chapterImportPath + familyDir(fam)
	reach, err := reachable(fam)
	if err != nil {
		return nil, nil, nil, err
	}
	normalizeCarriers := recordCarrierNormalizer()
	structures := map[*registry.ProofEntry]bool{}
	for _, s := range fam.Structures() {
		structures[s.ProofEntry] = true
	}
	entries := append([]*registry.ProofEntry(nil), fam.Entries()...)
	sort.Slice(entries, func(i, j int) bool { return entries[i].Name < entries[j].Name })
	for _, e := range entries {
		bare := strings.TrimPrefix(e.Name, prefix)
		w := wrapper{entry: e, bareName: bare, typeName: wrapperTypeName(bare), closure: -1, selfPath: selfPath,
			structure: structures[e]}
		if prev, clash := byTypeName[w.typeName]; clash {
			return nil, nil, nil, fmt.Errorf("typedgen: entries %s and %s both render wrapper type %s", prev, e.Name, w.typeName)
		}
		byTypeName[w.typeName] = e.Name

		p := e.Statement().Prop
		var err error
		w.letters, w.slots, err = readSignature(p, usedTypedefs)
		if err != nil {
			return nil, nil, nil, fmt.Errorf("typedgen: entry %s: %w", e.Name, err)
		}
		// A law in the standard form is read as its telescope, the
		// shape the reading reads (prop.LawTelescope): same binders,
		// the structure's components and antecedent first, the other
		// binders after them in the statement's order.
		law := prop.LawTelescope(p)
		components := lawComponents(law)
		w.components = len(components)
		w.instance = isStructureFact(stripForAll(p.Conclusion()))
		if w.components > 0 {
			w.readingSlots = slotsBeyond(w.slots, components)
			keepUnanchoredDimensions(w.readingSlots)
			body := readingBody(law)
			markMemberships(w.readingSlots, antecedentConjuncts(body))
			markMembers(w.readingSlots, guardConjuncts(body), components)
			w.readingInstance = isStructureFact(body)
			if structure, ok := lawStructure(law); ok && reach[structure.ph.fam] {
				structure.normalize = normalizeCarriers
				w.law = structure
				refineCarriers(&w, body, reach, usedTypedefs)
			}
			markCarriers(w.readingSlots, guardConjuncts(body), w.law)
		}
		wrappers = append(wrappers, w)
	}
	return wrappers, usedTypedefs, notes, nil
}

func readSignature(p core.Prop, usedTypedefs map[string]bool) (letters []string, slots []witnessSlot, err error) {
	// Each statement letter is carried by the deliberately letter-free
	// type parameter Type0, Type1, … — the letter itself lives ONLY in
	// the binding the body states (InstSole needs none; a multi-letter
	// body says TypeBinder.BindA[Type0]()), never in a parameter name
	// that could be misread as the letter's phantom alias.
	letterParam := map[string]string{}
	paramNames := map[string]bool{}
	for i, v := range proof.OrderedPropTypeVars(p) {
		name := string(v.Name())
		if !isExportedIdent(name) {
			return nil, nil, fmt.Errorf("type variable %q is not a legal Go type parameter name", name)
		}
		letters = append(letters, name)
		letterParam[name] = fmt.Sprintf("Type%d", i)
		paramNames[letterParam[name]] = true
	}
	if len(letters) > 1 {
		for _, l := range letters {
			if !bindAlphabet[l] {
				return nil, nil, fmt.Errorf("type variable %q is outside the Bind alphabet — land the Bind%s method on proof's _TypeVarBinder beside its siblings (prover/proof/typed.go)", l, l)
			}
		}
	}

	seen := map[string]int{}
	t := p.Conclusion()
	for {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			v := abs.Var()
			phantom, err := renderPhantom(v.Type(), letterParam, usedTypedefs)
			if err != nil {
				return nil, nil, err
			}
			name := paramName(string(v.Name()), paramNames, seen)
			slots = append(slots, witnessSlot{name: name, phantom: phantom, binder: string(v.Name()), typ: v.Type()})
			t = abs.Body()
			continue
		}
		if _, concl, ok := ext.MatchesIMPLY(t); ok {
			t = concl
			continue
		}
		break
	}
	if err := refineDimensionSlots(p, slots, letterParam, usedTypedefs); err != nil {
		return nil, nil, err
	}
	return letters, slots, nil
}

// bindAlphabet is the letter set proof declares a BindX constructor
// for — the corpus's statement alphabet. A multi-letter statement
// binding a letter outside it fails loudly above; a SINGLE-letter
// statement needs no BindX (InstSole is name-free), so the alphabet
// constrains only the statements that actually pair.
var bindAlphabet = map[string]bool{
	"A": true, "B": true, "C": true, "D": true, "E": true, "F": true,
	"G": true, "H": true, "I": true, "M": true, "N": true, "U": true, "Z": true,
}

// BindLetter reports whether proof's TypeBinder has a Bind method for
// the type variable name: whether `TypeBinder.Bind<name>[T]()` is Go.
func BindLetter(name string) bool { return bindAlphabet[name] }

// lawComponents recognizes a structure law — `∀comps. S(comps) ⇒ body`,
// the leading ∀-binders exactly the arguments of the antecedent's
// predicate, each named once — and reports the names of its components.
// A statement of any other shape has none.
func lawComponents(p core.Prop) map[string]bool {
	t := p.Conclusion()
	var binders []core.VarTerm
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		binders = append(binders, abs.Var())
		t = abs.Body()
	}
	antecedent, _, ok := ext.MatchesIMPLY(t)
	if !ok || len(binders) == 0 {
		return nil
	}
	head, args := ext.MatchesApply(antecedent)
	if _, isConst := head.AsConst(); !isConst || len(args) != len(binders) {
		return nil
	}
	seen := map[string]bool{}
	for _, a := range args {
		v, isVar := a.AsVar()
		if !isVar || seen[string(v.Name())] {
			return nil
		}
		placed := false
		for _, b := range binders {
			if b.Equals(v) {
				placed = true
				break
			}
		}
		if !placed {
			return nil
		}
		seen[string(v.Name())] = true
	}
	return seen
}

// slotsBeyond is a law's slots without its components, in the
// statement's order. The telescope reads the components first, so they
// need not lead the statement's slots: a component is the first slot
// its name binds, the statement's leading ∀-block binding each name
// once.
func slotsBeyond(slots []witnessSlot, components map[string]bool) []witnessSlot {
	var rest []witnessSlot
	dropped := map[string]bool{}
	for _, s := range slots {
		if components[s.binder] && !dropped[s.binder] {
			dropped[s.binder] = true
			continue
		}
		rest = append(rest, s)
	}
	return rest
}

// renderPhantom spells a HOL type as a phantom type expression over
// the statement's type parameters (letterParam maps each letter to
// its Type0/Type1/… parameter). Sugar mirrors the vocabulary's own
// preferences: Set for X → bool, Op for the homogeneous binary
// operation, Fun2/Fun3 for the curried arities, and IntegerPolynomial
// for (num → num) → int, read as one type wherever it stands, a
// curried function's result among them (num → (num → num) → int is
// Fun[Nat, IntegerPolynomial]). A typedef renders as its owner's
// phantom (typedefPhantoms), recorded in usedTypedefs so the preamble
// can alias another chapter's from its home package. Framework names
// retain provider qualifiers here; bareAuthoring uses their existing
// aliases in the final declarations. IntegerPolynomial has no provider
// to qualify it by: it is library/authoring's own declaration, written
// bare, and the dot import follows from it as from every bare name.
func renderPhantom(t core.HolType, letterParam map[string]string, usedTypedefs map[string]bool) (string, error) {
	if v, ok := t.(core.VarType); ok {
		name := string(v.Name())
		param, ok := letterParam[name]
		if !ok {
			return "", fmt.Errorf("type variable %s not among the statement's type variables", name)
		}
		return param, nil
	}
	if t.Equals(core.TypeBool()) {
		return phantomBool, nil
	}
	if t.Equals(ext.NumType) {
		return "ext.Nat", nil
	}
	if t.Equals(integerPolynomialType) {
		return phantomIntegerPolynomial, nil
	}
	if c, ok := t.(core.CompositeType); ok && c.Meta().Equals(ext.MetaTypeProd) {
		left, err := renderPhantom(c.SubType(0), letterParam, usedTypedefs)
		if err != nil {
			return "", err
		}
		right, err := renderPhantom(c.SubType(1), letterParam, usedTypedefs)
		if err != nil {
			return "", err
		}
		return fmt.Sprintf("ext.Prod[%s, %s]", left, right), nil
	}
	if ext.IsFunType(t) {
		spine := funSpine(t)
		parts := make([]string, len(spine))
		for i, s := range spine {
			p, err := renderPhantom(s, letterParam, usedTypedefs)
			if err != nil {
				return "", err
			}
			parts[i] = p
		}
		args, result := parts[:len(parts)-1], parts[len(parts)-1]
		switch {
		case len(args) == 1 && result == phantomBool:
			return fmt.Sprintf("ext.Set[%s]", args[0]), nil
		case len(args) == 2 && args[0] == args[1] && args[1] == result:
			return fmt.Sprintf("ext.Op[%s]", result), nil
		case len(args) == 1:
			return fmt.Sprintf("ext.Fun[%s, %s]", args[0], result), nil
		case len(args) == 2:
			return fmt.Sprintf("ext.Fun2[%s, %s, %s]", args[0], args[1], result), nil
		case len(args) == 3:
			return fmt.Sprintf("ext.Fun3[%s, %s, %s, %s]", args[0], args[1], args[2], result), nil
		default:
			// Deeper arities nest: A → (rest), spelled at the logic's own
			// binary constructor.
			rest, err := renderPhantom(t.(core.CompositeType).SubType(1), letterParam, usedTypedefs)
			if err != nil {
				return "", err
			}
			return fmt.Sprintf("ext.Fun[%s, %s]", args[0], rest), nil
		}
	}
	if c, ok := t.(core.CompositeType); ok {
		if ph, known := typedefPhantoms[string(c.Meta().Name())]; known {
			if ph.arity != c.Meta().Arity() {
				return "", fmt.Errorf("metatype %s has arity %d but its phantom %s is declared at %d",
					c.Meta().Name(), c.Meta().Arity(), ph.name, ph.arity)
			}
			usedTypedefs[string(c.Meta().Name())] = true
			if ph.arity == 0 {
				return ph.spelling(), nil
			}
			subs := make([]string, ph.arity)
			for i := range subs {
				sub, err := renderPhantom(c.SubType(i), letterParam, usedTypedefs)
				if err != nil {
					return "", err
				}
				subs[i] = sub
			}
			return fmt.Sprintf("%s[%s]", ph.spelling(), strings.Join(subs, ", ")), nil
		}
	}
	return "", fmt.Errorf("no phantom spelling for type %s (declare the typedef's phantom in the minting family's vocab.go and add its typedefPhantoms row, or keep this entry's cites untyped)", ext.FormatType(t))
}

// phantomBool is the spelling of bool's phantom; renderPhantom reads a
// function into bool as a Set by it.
const phantomBool = "ext.Bool"

// phantomIntegerPolynomial is library/authoring's name for
// integerPolynomialType, the type of a first-order formula's atom.
const phantomIntegerPolynomial = "IntegerPolynomial"

// integerPolynomialType is (num → num) → int: a coefficient for every
// monomial, a monomial an exponent for every variable name.
var integerPolynomialType core.HolType = core.MakeFun(core.MakeFun(ext.NumType, ext.NumType), dsl.IntType)

// funSpine is a function type's argument types and its result, the
// arrows read to the right as ext.MatchesFun reads them, stopping at
// an integer polynomial, which is one type and not two more arguments.
func funSpine(t core.HolType) []core.HolType {
	var spine []core.HolType
	for ext.IsFunType(t) && !t.Equals(integerPolynomialType) {
		c := t.(core.CompositeType)
		spine = append(spine, c.SubType(0))
		t = c.SubType(1)
	}
	return append(spine, t)
}

// paramName sanitizes a statement binder name into a Go parameter
// that collides with neither the receiver, the type parameters, a
// package the generated file imports, nor an earlier binder.
func paramName(name string, typeParams map[string]bool, seen map[string]int) string {
	sanitized := strings.Map(func(r rune) rune {
		if unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' {
			return r
		}
		return '_'
	}, name)
	if sanitized == "" || unicode.IsDigit([]rune(sanitized)[0]) {
		sanitized = "w" + sanitized
	}
	if goKeywords[sanitized] || sanitized == "th" || importedNames[sanitized] || typeParams[sanitized] {
		sanitized += "_"
	}
	seen[sanitized]++
	if n := seen[sanitized]; n > 1 {
		sanitized = fmt.Sprintf("%s%d", sanitized, n)
	}
	return sanitized
}

var goKeywords = map[string]bool{
	"break": true, "case": true, "chan": true, "const": true, "continue": true,
	"default": true, "defer": true, "else": true, "fallthrough": true, "for": true,
	"func": true, "go": true, "goto": true, "if": true, "import": true,
	"interface": true, "map": true, "package": true, "range": true, "return": true,
	"select": true, "struct": true, "switch": true, "type": true, "var": true,
}

// importedNames are the packages a generated file names by qualifier,
// each by the name its import binds; preambleImports maps the name to
// the path. A statement binder of the same name would shadow the
// package inside the method that takes it.
var importedNames = map[string]bool{
	"core": true, "ext": true, "dsl": true, "dimtypes": true, "proof": true, "registry": true, "on": true,
}

var preambleImports = map[string]string{
	"core":     "github.com/euc-ai/xugo/core",
	"ext":      "github.com/euc-ai/xugo/ext",
	"dsl":      "github.com/euc-ai/xugo/ext/dsl",
	"dimtypes": "github.com/euc-ai/xugo/ext/dimtypes",
	"on":       "github.com/euc-ai/xugo/ext/on",
	"proof":    "github.com/euc-ai/xugo/prover/proof",
	"registry": "github.com/euc-ai/xugo/library/registry",
}

func wrapperTypeName(entryName string) string {
	r, size := utf8.DecodeRuneInString(entryName)
	return string(unicode.ToLower(r)) + entryName[size:] + "Thm"
}

func isExportedIdent(s string) bool {
	for i, r := range s {
		if i == 0 {
			if !unicode.IsUpper(r) {
				return false
			}
			continue
		}
		if !unicode.IsLetter(r) && !unicode.IsDigit(r) {
			return false
		}
	}
	return s != ""
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

func renderTyped(pkg, docComment string, fam *registry.Family, wrappers []wrapper, namedTypedefs map[string]bool, declaredLetters, unspelledLetters []string) (string, error) {
	// The typedef phantoms of OTHER chapters the signatures or the
	// family's proof files name (namedTypedefs), aliased from the
	// packages that own them. The family's own are already in scope
	// (their home is the package being written), and a phantom minted
	// below the chapters is named by its owner.
	selfPath := chapterImportPath + familyDir(fam)
	var aliased []string
	imports := map[string]bool{}
	for name := range namedTypedefs {
		ph := typedefPhantoms[name]
		if ph.home == selfPath || !ph.mintedByAChapter() {
			continue
		}
		aliased = append(aliased, name)
		imports[ph.home] = true
	}
	sort.Slice(aliased, func(i, j int) bool {
		return typedefPhantoms[aliased[i]].name < typedefPhantoms[aliased[j]].name
	})

	// The declarations first: the import block is read off what they
	// name.
	var body strings.Builder
	if len(aliased) > 0 {
		body.WriteString(`// The typedef phantoms of other chapters this family's statements or
// its proof files name, aliased from the packages that own them: a
// phantom is declared beside its type's mint (the vocabulary's
// decentralization rule, ext/holtype_phantom.go), and every other
// family reads it from there, so the Go type is ONE type wherever a
// signature spells it. A proof file of this family names them bare.
type (
`)
		for _, name := range aliased {
			ph := typedefPhantoms[name]
			qualifier := path.Base(ph.home)
			switch ph.arity {
			case 0:
				fmt.Fprintf(&body, "\t%s = %s.%s\n", ph.name, qualifier, ph.name)
			case 1:
				fmt.Fprintf(&body, "\t%s[X ext.TypePhantom] = %s.%s[X]\n", ph.name, qualifier, ph.name)
			case 2:
				fmt.Fprintf(&body, "\t%s[X, Y ext.TypePhantom] = %s.%s[X, Y]\n", ph.name, qualifier, ph.name)
			default:
				if ph.arity > len(aliasParams) {
					return "", fmt.Errorf("typedgen: typedef phantom %s: no alias shape for arity %d", ph.name, ph.arity)
				}
				params := strings.Join(aliasParams[:ph.arity], ", ")
				fmt.Fprintf(&body, "\t%s[%s ext.TypePhantom] = %s.%s[%s]\n", ph.name, params, qualifier, ph.name, params)
			}
		}
		body.WriteString(")\n\n")
	}
	renderLetterPhantoms(&body, declaredLetters, unspelledLetters)
	renderStructurePhantoms(&body, fam, selfPath)
	renderRecordFields(&body, wrappers)
	for _, w := range wrappers {
		renderWrapper(&body, w)
		if w.law != nil && w.law.ph.home != selfPath {
			imports[w.law.ph.home] = true
		}
		if w.projection != nil && w.projection.ph.home != selfPath {
			imports[w.projection.ph.home] = true
		}
	}
	declarations, authoring, err := bareAuthoring(pkg, body.String())
	if err != nil {
		return "", err
	}
	named, err := packagesNamed(pkg, declarations)
	if err != nil {
		return "", err
	}
	for name := range named {
		imports[preambleImports[name]] = true
	}
	if authoring {
		imports[authoringImportPath] = true
	}

	var b strings.Builder
	b.WriteString(`// Code generated by library/cmd/gen_family. DO NOT EDIT.
//
// Typed theorem wrappers. See engine/xugo-engine.md, "The generated wrappers".
// Regenerate with go generate ./library/proofs.
`)
	// Blank line: the banner is file provenance; the one comment
	// touching the package clause is the doc comment.
	fmt.Fprintf(&b, "\n%spackage %s\n\n", docComment, pkg)

	if len(imports) > 0 {
		paths := make([]string, 0, len(imports))
		for p := range imports {
			paths = append(paths, p)
		}
		sort.Strings(paths)
		b.WriteString("import (\n")
		for _, p := range paths {
			if p == authoringImportPath {
				fmt.Fprintf(&b, "\t. %q\n", p)
			} else {
				fmt.Fprintf(&b, "\t%q\n", p)
			}
		}
		b.WriteString(")\n\n")
	}
	b.WriteString(declarations)
	return b.String(), nil
}

// packagesNamed reads the rendered declarations for the packages they
// name by qualifier — the importedNames that stand left of a selector.
// The import block is written from this reading and never from a
// second account of what the renderer spells, so the two cannot
// disagree: an import the declarations do not use, or a qualifier
// with no import, is unrepresentable.
func packagesNamed(pkg, declarations string) (map[string]bool, error) {
	file, err := parser.ParseFile(token.NewFileSet(), File, "package "+pkg+"\n\n"+declarations, parser.SkipObjectResolution)
	if err != nil {
		return nil, fmt.Errorf("typedgen: rendered declarations do not parse (generator bug): %w\n%s", err, declarations)
	}
	named := map[string]bool{}
	ast.Inspect(file, func(n ast.Node) bool {
		if sel, ok := n.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok && importedNames[x.Name] {
				named[x.Name] = true
			}
		}
		return true
	})
	return named, nil
}

func renderWrapper(b *strings.Builder, w wrapper) {
	// self is the expression the methods read the entry through.
	self := "th.entry"
	if w.structure {
		fmt.Fprintf(b, "type %s struct{ *registry.Structure }\n\n", w.typeName)
		self = "th.ProofEntry"
	} else {
		fmt.Fprintf(b, "type %s struct{ entry *registry.ProofEntry }\n\n", w.typeName)
	}
	fmt.Fprintf(b, "func (th %s) Entry() *registry.ProofEntry { return %s }\n\n", w.typeName, self)
	fmt.Fprintf(b, "func (th %s) DepName() string { return %s.Name }\n\n", w.typeName, self)
	// The wrapper is the cite target the verbs take (proof.CiteTarget):
	// the fact it names, itself the dep.
	fmt.Fprintf(b, "func (th %s) AsFact() proof.Fact { return proof.NamedFact(th) }\n\n", w.typeName)
	// A definition a proof opens is the constant it defines
	// (proof.Definition), what Unfold and Unfolded take. A structure's
	// wrapper has the method from the *registry.Structure it embeds.
	if !w.structure && w.entry.Unfoldable() {
		fmt.Fprintf(b, "func (th %s) DefinedConstant() core.ConstTermMeta { return registry.DefinedConstant(th.entry) }\n\n", w.typeName)
	}
	if w.instance {
		renderUntypedInstance(b, w.typeName)
	}
	// Witnesses pass as the Typed values themselves: ext.Typed[T] embeds
	// Term, so the wrapper IS the witness and the install machinery
	// strips to the core term where it needs it — no .Core() noise.
	params := renderParams(w.slots)
	witnessArgs := renderWitnesses(w.slots)
	dimParams, hasInhabited := dimensionTypeParams(w.slots)

	// The letter-free type parameters Type0, Type1, … (the statement's
	// letters in first-occurrence order; the pairing lives in the
	// bindings alone) and the premise expression At builds on.
	typeParams := ""
	premise := ""
	if n := len(w.letters); n > 0 {
		names := make([]string, n)
		for i := range names {
			names[i] = fmt.Sprintf("Type%d", i)
		}
		typeParams = "[" + strings.Join(names, ", ") + " ext.TypePhantom" + dimParams + "]"
		if n == 1 {
			// A sole type variable has no pairing to state: name-free.
			fmt.Fprintf(b, "func (th %s) Inst[Type0 ext.TypePhantom]() proof.Fact {\n\treturn proof.InstSole[Type0](%s)\n}\n\n",
				w.typeName, self)
			premise = "th.Inst[Type0]()"
		} else {
			// Multi-letter: the instance is a list of named bindings —
			// no positional type-argument surface exists to re-pair.
			bindParams := make([]string, n)
			calls := make([]string, n)
			for i, l := range w.letters {
				bindParams[i] = "bind" + l
				calls[i] = fmt.Sprintf("proof.TypeBinder.Bind%s[Type%d]()", l, i)
			}
			fmt.Fprintf(b, "func (th %s) Inst(%s proof.TypeBinding) proof.Fact {\n\treturn proof.Inst(%s, %s)\n}\n\n",
				w.typeName, strings.Join(bindParams, ", "), self, strings.Join(bindParams, ", "))
			premise = fmt.Sprintf("th.Inst(%s)", strings.Join(calls, ", "))
		}
	}

	if len(w.letters) == 0 && dimParams != "" {
		typeParams = "[" + strings.TrimPrefix(dimParams, ", ") + "]"
	}
	if len(w.letters) == 0 {
		premise = self
	}
	if len(w.slots) > 0 {
		atBody := fmt.Sprintf("%s.At(%s)", premise, witnessArgs)
		if len(w.letters) == 0 {
			atBody = fmt.Sprintf("proof.At(%s, %s)", self, witnessArgs)
		}
		if hasInhabited {
			// The vectors travel with the instance as one premise group,
			// their evidence carried.
			var members []string
			for _, s := range w.slots {
				if s.inhabited {
					members = append(members, s.name)
				}
			}
			members = append(members, atBody)
			fmt.Fprintf(b, "func (th %s) At%s(%s) proof.PremiseGroup {\n\treturn proof.GroupPremises(%s)\n}\n\n",
				w.typeName, typeParams, params, strings.Join(members, ", "))
			return
		}
		fmt.Fprintf(b, "func (th %s) At%s(%s) proof.Fact {\n\treturn %s\n}\n\n", w.typeName, typeParams, params, atBody)
	}
	if w.components > 0 {
		renderReading(b, w)
	}
}

// renderRecordFields declares each record field's projection equation
// under its registered name, bound to the expression that reaches it
// through the datatype handle (`RingAddDef = ringAddDefThm{
// RingOpsData.Fields[0]}`): a Deps list, a Simp rule and a cite spell
// the name, and the field's position in the record stays here.
func renderRecordFields(b *strings.Builder, wrappers []wrapper) {
	var lines []string
	for _, w := range wrappers {
		if expr, ok := w.entry.RecordField(); ok {
			lines = append(lines, fmt.Sprintf("\t%s = %s{%s}\n", w.bareName, w.typeName, expr))
		}
	}
	if len(lines) == 0 {
		return
	}
	b.WriteString("// The record fields' projection equations, each under the name its\n" +
		"// field registers: what a Deps list, a Simp rule and a cite spell.\n" +
		"var (\n")
	for _, l := range lines {
		b.WriteString(l)
	}
	b.WriteString(")\n\n")
}

// renderReading renders a structure law's reading at an instance:
// the reading type over the Fact proof.Read builds, the law's Read
// method, and — where the law binds witnesses beyond its components —
// the reading's At over exactly those, the component slots gone. The
// At declares the law's type parameters its remaining slots spell
// (readingTypeParams): a letter only a component's type carries is
// fixed by the instance and would be one no call could infer.
func renderReading(b *strings.Builder, w wrapper) {
	if w.law != nil {
		renderTypedReading(b, w)
		return
	}
	readType := strings.TrimSuffix(w.typeName, "Thm") + "Reading"
	// The reading holds its Fact as a named field and declares the one
	// method the verbs read it through (proof.CiteTarget): embedding
	// would promote Fact's whole method set, compiled once per reading
	// type.
	fmt.Fprintf(b, "type %s struct{ fact proof.Fact }\n\n", readType)
	fmt.Fprintf(b, "func (th %s) AsFact() proof.Fact { return th.fact }\n\n", readType)
	if w.readingInstance {
		renderUntypedInstance(b, readType)
	}
	fmt.Fprintf(b, "func (th %s) Read(instance any) %s {\n\treturn %s{fact: proof.Read(th.entry, instance)}\n}\n\n",
		w.typeName, readType, readType)
	if len(w.slots) == w.components {
		return
	}
	renderReadingAt(b, w, readType)
}

// renderReadingAt renders a reading's At over the law's slots beyond its
// components, the membership refinement read against the reading's
// statement (buildWrappers) — a membership that was the law's SECOND
// antecedent is the reading's first.
func renderReadingAt(b *strings.Builder, w wrapper, readType string) {
	rest := w.readingSlots
	params := renderParams(rest)
	witnessArgs := renderWitnesses(rest)
	_, hasInhabited := dimensionTypeParams(rest)
	typeParams := readingTypeParams(len(w.letters), rest, params)
	// The receiver is `th`, as on the law's own wrapper: paramName
	// reserves that name, so no statement binder — a radius named r,
	// say — can shadow it.
	atBody := fmt.Sprintf("th.fact.At(%s)", witnessArgs)
	if w.closure >= 0 && closureElemInferred(w.closureElem, params) {
		member := fmt.Sprintf("*proof.Member[%s, Car%d]", w.closureElem, w.closure)
		fmt.Fprintf(b, "func (th %s) At%s(%s) %s {\n\treturn proof.ReadMember[%s, Car%d](th.entry.Statement().Prop, th.fact, th.instance, %s)\n}\n\n",
			readType, typeParams, params, member, w.closureElem, w.closure, witnessArgs)
		return
	}
	if hasInhabited {
		var members []string
		for _, s := range rest {
			if s.inhabited {
				members = append(members, s.name)
			}
		}
		fmt.Fprintf(b, "func (th %s) At%s(%s) proof.PremiseGroup {\n\treturn proof.WithMembers(%s, %s)\n}\n\n",
			readType, typeParams, params, atBody, strings.Join(members, ", "))
		return
	}
	fmt.Fprintf(b, "func (th %s) At%s(%s) proof.Fact {\n\treturn %s\n}\n\n", readType, typeParams, params, atBody)
}

// closureElemInferred reports whether every type parameter a closure
// law's member type spells is one the At's own parameters name, so a
// call infers it.
func closureElemInferred(elem, params string) bool {
	for _, name := range regexp.MustCompile(`\bType\d+\b`).FindAllString(elem, -1) {
		if !regexp.MustCompile(`\b` + name + `\b`).MatchString(params) {
			return false
		}
	}
	return true
}

// renderTypedReading renders the reading of a law whose structure has a
// phantom: Read infers the structure and its carriers from the instance
// (proof.Instance), a projection reads as the conclusion's typed fact,
// and a reading's members are members of its carriers.
func renderTypedReading(b *strings.Builder, w wrapper) {
	ph := w.law.ph
	q := ph.qualifier(w.selfPath)
	cars := w.law.carrierParams()
	instance := "proof.Instance"
	if len(cars) == 2 {
		instance = "proof.Instance2"
	}
	typeParams := fmt.Sprintf("[S interface {\n\tproof.StructurePhantom\n\t%s%s | proof.AnyStructure\n}, %s on.Carrier]",
		q, ph.typeName(), strings.Join(cars, ", "))
	instanceType := fmt.Sprintf("%s[S, %s]", instance, strings.Join(cars, ", "))

	if pr := w.projection; pr != nil {
		mapped := make([]string, len(pr.mapped))
		for i, k := range pr.mapped {
			mapped[i] = cars[k]
		}
		result := fmt.Sprintf("%s%s[%s]", pr.ph.qualifier(w.selfPath), pr.ph.factName(), strings.Join(mapped, ", "))
		readAs := "proof.ReadAs"
		if len(mapped) == 2 {
			readAs = "proof.ReadAs2"
		}
		fmt.Fprintf(b, "func (th %s) Read%s(instance %s) %s {\n\treturn %s(%s{}, th.entry, th.entry.Statement().Prop, instance)\n}\n\n",
			w.typeName, typeParams, instanceType, result, readAs, result)
		return
	}

	readType := strings.TrimSuffix(w.typeName, "Thm") + "Reading"
	carParams := strings.Join(cars, ", ")
	closure := w.closure >= 0 && closureElemInferred(w.closureElem, renderParams(w.readingSlots))
	if closure {
		fmt.Fprintf(b, "type %s[%s on.Carrier] struct {\n\tfact     proof.Fact\n\tentry    *registry.ProofEntry\n\tinstance any\n}\n\n", readType, carParams)
	} else {
		fmt.Fprintf(b, "type %s[%s on.Carrier] struct{ fact proof.Fact }\n\n", readType, carParams)
	}
	fmt.Fprintf(b, "func (th %s[%s]) AsFact() proof.Fact { return th.fact }\n\n", readType, carParams)
	if w.readingInstance {
		renderUntypedInstance(b, readType+"["+carParams+"]")
	}
	construct := fmt.Sprintf("%s[%s]{fact: proof.Read(th.entry, instance)}", readType, carParams)
	if closure {
		construct = fmt.Sprintf("%s[%s]{fact: proof.Read(th.entry, instance), entry: th.entry, instance: instance}", readType, carParams)
	}
	fmt.Fprintf(b, "func (th %s) Read%s(instance %s) %s[%s] {\n\treturn %s\n}\n\n",
		w.typeName, typeParams, instanceType, readType, carParams, construct)
	if len(w.slots) == w.components {
		return
	}
	if !closure {
		w.closure = -1
	}
	renderReadingAt(b, w, readType+"["+carParams+"]")
}

// renderUntypedInstance declares a type an untyped instance of a typed
// Read: its structure and carriers are not known before the proof runs.
func renderUntypedInstance(b *strings.Builder, typ string) {
	fmt.Fprintf(b, "func (th %s) InstanceOf(proof.AnyStructure, on.Any) {}\n\n", typ)
	fmt.Fprintf(b, "func (th %s) InstanceOf2(proof.AnyStructure, on.Any, on.Any) {}\n\n", typ)
}

// readingTypeParams spells a reading's At type parameters: of the law's
// letter-free parameters Type0 … Type(n−1), those the rendered slot
// list params names, then the dimension parameters of the slots
// themselves. A parameter no slot names would leave every call unable
// to infer it.
func readingTypeParams(letters int, slots []witnessSlot, params string) string {
	var kept []string
	for i := 0; i < letters; i++ {
		name := fmt.Sprintf("Type%d", i)
		if regexp.MustCompile(`\b` + name + `\b`).MatchString(params) {
			kept = append(kept, name)
		}
	}
	dimParams, _ := dimensionTypeParams(slots)
	switch {
	case len(kept) > 0:
		return "[" + strings.Join(kept, ", ") + " ext.TypePhantom" + dimParams + "]"
	case dimParams != "":
		return "[" + strings.TrimPrefix(dimParams, ", ") + "]"
	}
	return ""
}

// renderParams groups adjacent same-typed witness slots (`g, f
// ext.Typed[…]`), mirroring how a hand-written signature reads.
func renderParams(slots []witnessSlot) string {
	var groups []string
	for i := 0; i < len(slots); {
		if slots[i].elided {
			i++
			continue
		}
		j := i + 1
		for j < len(slots) && !slots[j].elided && slots[j].paramType() == slots[i].paramType() {
			j++
		}
		var names []string
		for _, s := range slots[i:j] {
			names = append(names, s.name)
		}
		groups = append(groups, fmt.Sprintf("%s %s", strings.Join(names, ", "), slots[i].paramType()))
		i = j
	}
	return strings.Join(groups, ", ")
}

// ---------------------------------------------------------------------------
// Wrapping the registration vars in place
// ---------------------------------------------------------------------------

// ApplyWraps rewrites `var X = family.Add(registry.ProofEntry{Name:
// "N", …})` to `var X = nThm{family.Add(…)}` in the member files under
// dir — the surgical two-token wrap that keeps registration, Deps
// reference and typed citation surface ONE name. A family.Define var
// takes the same wrap, and a family.DefineStructure var the wrap of
// its definition entry, which embeds the structure. A var already in
// its entry's wrapper is left alone; one in another wrapper — the type
// its entry's former name rendered, after a rename — is re-typed to
// its entry's; an Add whose entry the generator cannot identify
// (non-literal Name) is reported for hand-wrapping. The returned lines
// are the report, one per file touched or skipped, for the command to
// print.
func (r *Rendered) ApplyWraps(dir string) ([]string, error) {
	files, err := memberFiles(dir)
	if err != nil {
		return nil, err
	}
	var report []string
	for _, file := range files {
		lines, err := rewriteFile(file, r.typeNames)
		if err != nil {
			return nil, err
		}
		report = append(report, lines...)
	}
	return report, nil
}

// wrapTarget is the wrapper an entry's var takes: its type, and
// whether it is a structure's, embedding the *registry.Structure that
// family.DefineStructure returns rather than holding the entry.
type wrapTarget struct {
	typeName  string
	structure bool
}

// sourceEdit replaces the bytes [start, end) of a member file with
// text; a wrap is two insertions (start == end), a re-typing one
// replacement of the wrapper's name.
type sourceEdit struct {
	start, end int
	text       string
}

func rewriteFile(file string, byEntryName map[string]wrapTarget) ([]string, error) {
	src, err := os.ReadFile(file)
	if err != nil {
		return nil, fmt.Errorf("typedgen: read %s: %w", file, err)
	}
	fset := token.NewFileSet()
	parsed, err := parser.ParseFile(fset, file, src, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("typedgen: parse %s: %w", file, err)
	}

	var report []string
	var edits []sourceEdit
	wrapped, retyped := 0, 0
	for _, decl := range parsed.Decls {
		gen, ok := decl.(*ast.GenDecl)
		if !ok || gen.Tok != token.VAR {
			continue
		}
		for _, spec := range gen.Specs {
			vs, ok := spec.(*ast.ValueSpec)
			if !ok {
				continue
			}
			for _, value := range vs.Values {
				call, wrapper := registrationCall(value)
				if call == nil {
					continue // not a registration
				}
				name, ok := entryNameOf(call)
				if !ok {
					report = append(report, fmt.Sprintf("  %s: family.Add with a non-literal Name — wrap by hand", file))
					continue
				}
				target, ok := byEntryName[name]
				if !ok {
					report = append(report, fmt.Sprintf("  %s: entry %q not in this family's registry — wrap by hand", file, name))
					continue
				}
				// The wrapper's shape is the door's: a structure's embeds
				// the *registry.Structure DefineStructure returns.
				if door := call.Fun.(*ast.SelectorExpr).Sel.Name; (door == "DefineStructure") != target.structure {
					return nil, fmt.Errorf("typedgen: %s: entry %q is registered by family.%s, which its wrapper %s does not fit (generator bug)",
						file, name, door, target.typeName)
				}
				switch {
				case wrapper == nil:
					open, close := fset.Position(call.Pos()).Offset, fset.Position(call.End()).Offset
					edits = append(edits,
						sourceEdit{start: open, end: open, text: target.typeName + "{"},
						sourceEdit{start: close, end: close, text: "}"})
					wrapped++
				case wrapper.Name != target.typeName:
					edits = append(edits, sourceEdit{
						start: fset.Position(wrapper.Pos()).Offset,
						end:   fset.Position(wrapper.End()).Offset,
						text:  target.typeName,
					})
					retyped++
				}
			}
		}
	}
	if len(edits) == 0 {
		return report, nil
	}
	// Later spans first, so an applied edit moves no earlier offset.
	sort.SliceStable(edits, func(i, j int) bool { return edits[i].start > edits[j].start })
	for _, e := range edits {
		src = append(src[:e.start], append([]byte(e.text), src[e.end:]...)...)
	}
	formatted, err := format.Source(src)
	if err != nil {
		return nil, fmt.Errorf("typedgen: %s: wrapped source does not format (generator bug): %w", file, err)
	}
	if err := os.WriteFile(file, formatted, 0o644); err != nil {
		return nil, fmt.Errorf("typedgen: write %s: %w", file, err)
	}
	if wrapped > 0 {
		report = append(report, fmt.Sprintf("wrapped %d registration var(s) in %s", wrapped, file))
	}
	if retyped > 0 {
		report = append(report, fmt.Sprintf("re-typed %d wrapper(s) to the entry's name in %s", retyped, file))
	}
	return report, nil
}

// registrationCall reads a var's value as a registration: the bare
// `family.Add(…)` call, with no wrapper, or the call inside a wrapper
// literal `xThm{family.Add(…)}`, with the wrapper's name. nil for any
// other value.
func registrationCall(value ast.Expr) (call *ast.CallExpr, wrapper *ast.Ident) {
	if call, ok := familyAddCall(value); ok {
		return call, nil
	}
	lit, ok := value.(*ast.CompositeLit)
	if !ok || len(lit.Elts) != 1 {
		return nil, nil
	}
	wrapper, ok = lit.Type.(*ast.Ident)
	if !ok {
		return nil, nil
	}
	call, ok = familyAddCall(lit.Elts[0])
	if !ok {
		return nil, nil
	}
	return call, wrapper
}

// familyAddCall matches a bare `family.Add(…)`, `family.Define(…)` or
// `family.DefineStructure(…)` value expression.
func familyAddCall(value ast.Expr) (*ast.CallExpr, bool) {
	call, ok := value.(*ast.CallExpr)
	if !ok {
		return nil, false
	}
	sel, ok := call.Fun.(*ast.SelectorExpr)
	// Add registers a proof; Define registers a definition and returns
	// the same *ProofEntry, so its var takes the same wrapper — a
	// definition is the entry a chapter cites most, and a polymorphic
	// one has no Inst[τ]() spelling until it is wrapped. DefineStructure
	// returns the *Structure holding its definition entry, and its var
	// takes that entry's wrapper, rendered to embed the structure.
	// DefineType and DefineInductive return a struct of several entries
	// and are wrapped per field by hand.
	if !ok || (sel.Sel.Name != "Add" && sel.Sel.Name != "Define" && sel.Sel.Name != "DefineStructure") {
		return nil, false
	}
	recv, ok := sel.X.(*ast.Ident)
	if !ok || recv.Name != "family" {
		return nil, false
	}
	return call, true
}

func entryNameOf(call *ast.CallExpr) (string, bool) {
	if len(call.Args) != 1 {
		return "", false
	}
	lit, ok := call.Args[0].(*ast.CompositeLit)
	if !ok {
		return "", false
	}
	for _, elt := range lit.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok {
			continue
		}
		key, ok := kv.Key.(*ast.Ident)
		if !ok || key.Name != "Name" {
			continue
		}
		basic, ok := kv.Value.(*ast.BasicLit)
		if !ok || basic.Kind != token.STRING {
			return "", false
		}
		return strings.Trim(basic.Value, `"`), true
	}
	return "", false
}
