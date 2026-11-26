package typedgen

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/aliasgen"
	"github.com/euc-ai/xugo/prover/proof"
)

// A rendered file carries the package's doc comment on its package
// clause, names the proof surface through aliases, and imports exactly the
// packages its declarations name: a statement with a binder gives a
// wrapper over Typed and Fact, supplied by library/authoring, and every
// wrapper is a cite target through proof.NamedFact, which the authoring
// surface leaves out.
func TestRender_PackageDocAndBareNames(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_qualified", nil)
	fam.Add(registry.ProofEntry{
		Name:  "Member",
		Build: registry.BuildSpec{Headline: "∀p:bool. p ⇒ p", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err := Render(fam, "zz_typedgen_qualified", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	for _, want := range []string{
		"\n// Package zz_typedgen_qualified — a fixture chapter.\npackage zz_typedgen_qualified\n",
		"func (th memberThm) At(p Typed[Bool]) Fact {",
		"\treturn At(th.entry, p)",
		"func (th memberThm) AsFact() Fact { return proof.NamedFact(th) }",
		"\t. \"github.com/euc-ai/xugo/library/authoring\"\n",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("the rendered file lacks %q\n--- source: ---\n%s", want, src)
		}
	}
	for _, refused := range []string{"ext", "ext/dsl", "ext/dimtypes"} {
		if strings.Contains(src, "\""+"github.com/euc-ai/xugo/"+refused+"\"") {
			t.Errorf("the rendered file imports %s, which no declaration of it names\n--- source: ---\n%s", refused, src)
		}
	}
	if _, err := parser.ParseFile(token.NewFileSet(), File, rendered.Source, parser.AllErrors); err != nil {
		t.Errorf("the rendered file does not parse: %v", err)
	}

	// A chapter that registers nothing yet — the scaffold of a new
	// family, generated before its first member lands — is the doc
	// comment on a package clause, with no declaration and so no import.
	empty, err := Render(registry.NewFamily("zz_typedgen_scaffold", nil), "zz_typedgen_scaffold", t.TempDir(), "a chapter with no member yet")
	if err != nil {
		t.Fatalf("Render of an empty family: %v", err)
	}
	src = string(empty.Source)
	if !strings.HasSuffix(src, "\n// Package zz_typedgen_scaffold — a chapter with no member yet.\npackage zz_typedgen_scaffold\n") {
		t.Errorf("an empty family's file does not end at its package clause\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "\nimport ") {
		t.Errorf("an empty family's file imports a package it has no declaration to name\n--- source: ---\n%s", src)
	}
	if _, err := parser.ParseFile(token.NewFileSet(), File, empty.Source, parser.AllErrors); err != nil {
		t.Errorf("an empty family's file does not parse: %v", err)
	}
}

// The integer polynomial (num → num) → int is spelled by library/
// authoring's alias wherever it stands: a binder of the type, a
// curried function's result, a set's element. A type that only
// resembles it keeps its arrows.
func TestRender_IntegerPolynomialByItsAuthoringAlias(t *testing.T) {
	if got := ext.HolTypeOf[authoring.IntegerPolynomial](); !got.Equals(integerPolynomialType) {
		t.Fatalf("library/authoring's IntegerPolynomial is %s, the generator matches %s",
			ext.FormatType(got), ext.FormatType(integerPolynomialType))
	}
	if !aliasgen.OnSurface(phantomIntegerPolynomial) {
		t.Fatalf("%s is not on the authoring surface a generated file dot-imports", phantomIntegerPolynomial)
	}
	fam := registry.NewFamily("zz_typedgen_polynomial", nil)
	fam.Add(registry.ProofEntry{
		Name: "Member",
		Build: registry.BuildSpec{Headline: "∀p:(num → num) → int. ∀g:num → (num → num) → int. " +
			"∀s:((num → num) → int) → bool. ∀q:(num → num) → num. ∀r:(num → int) → int. " +
			"p ∈ s ∧ g(q(λi. i)) = p ∧ r = r ⇒ p ∈ s",
			Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err := Render(fam, "zz_typedgen_polynomial", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	want := "func (th memberThm) At(p Typed[IntegerPolynomial], g Typed[Fun[Nat, IntegerPolynomial]], " +
		"s Typed[Set[IntegerPolynomial]], q Typed[Fun[Fun[Nat, Nat], Nat]], r Typed[Fun[Fun[Nat, Int], Int]]) Fact {"
	if !strings.Contains(src, want) {
		t.Errorf("the rendered file lacks %q\n--- source: ---\n%s", want, src)
	}
	for _, refused := range []string{"Fun[Fun[Nat, Nat], Int]", "Fun2[Nat, Fun[Nat, Nat], Int]"} {
		if strings.Contains(src, refused) {
			t.Errorf("the rendered file spells %s, which library/authoring names IntegerPolynomial\n--- source: ---\n%s", refused, src)
		}
	}
	if !strings.Contains(src, "\t. \"github.com/euc-ai/xugo/library/authoring\"\n") {
		t.Errorf("the rendered file names IntegerPolynomial without the dot import that declares it\n--- source: ---\n%s", src)
	}
}

func TestBareAuthoring_LeavesEntryWrapperWithoutImport(t *testing.T) {
	const declaration = "type memberThm struct{ *registry.ProofEntry }\n"
	source, imported, err := bareAuthoring("fixture", declaration)
	if err != nil {
		t.Fatal(err)
	}
	if imported || source != declaration {
		t.Fatalf("a bare entry wrapper needs no authoring alias: %q", source)
	}
}

// The alias block is read off the proof files as well as the statements:
// a phantom of another chapter that a member file names bare is aliased
// though no statement of the family names its type, so the last such
// statement leaving the family does not take the alias with it. A name
// the file resolves itself, a qualified name, a name a member file
// declares, and the generated files do not count.
func TestRender_AliasesThePhantomsProofFilesName(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_file_aliases", nil)
	fam.Add(registry.ProofEntry{
		Name:  "Member",
		Build: registry.BuildSpec{Headline: "∀p:bool. p ⇒ p", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	const pkg = "zz_typedgen_file_aliases"
	render := func(files map[string]string) string {
		t.Helper()
		dir := t.TempDir()
		for name, src := range files {
			if err := os.WriteFile(filepath.Join(dir, name), []byte("package "+pkg+"\n\n"+src), 0o644); err != nil {
				t.Fatal(err)
			}
		}
		rendered, err := Render(fam, pkg, dir, "a fixture chapter")
		if err != nil {
			t.Fatalf("Render: %v", err)
		}
		if _, err := parser.ParseFile(token.NewFileSet(), File, rendered.Source, parser.AllErrors); err != nil {
			t.Fatalf("the rendered file does not parse: %v\n%s", err, rendered.Source)
		}
		return string(rendered.Source)
	}
	const ringAlias = "RingOps[X TypePhantom] = module_record.RingOps[X]"
	const moduleAlias = "ModuleOps[X, Y TypePhantom]"

	if src := render(nil); strings.Contains(src, "module_record") {
		t.Errorf("no statement and no file names a phantom, and the file aliases one:\n%s", src)
	}

	src := render(map[string]string{
		"member.go": "func build(R Typed[RingOps[A]]) {}\n",
		// A generated file's spelling is its generator's to keep.
		"zz_other_gen.go": "func other(M Typed[ModuleOps[A, B]]) {}\n",
		// A test file is no proof file.
		"member_test.go": "func helper(G Typed[GroupOps[A]]) {}\n",
	})
	if !strings.Contains(src, ringAlias) || !strings.Contains(src, "\"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record\"") {
		t.Errorf("member.go names RingOps bare, and the file does not alias it from its home:\n%s", src)
	}
	if strings.Contains(src, moduleAlias) || strings.Contains(src, "GroupOps") {
		t.Errorf("the file aliases a phantom only a generated file or a test names:\n%s", src)
	}

	for name, body := range map[string]string{
		"a qualified name":         "func build(R Typed[module_record.RingOps[A]]) {}\n",
		"a local of that name":     "func build() { RingOps := 0; _ = RingOps }\n",
		"a name the file declares": "type RingOps[X any] struct{}\n\nfunc build(R RingOps[int]) {}\n",
	} {
		if src := render(map[string]string{"member.go": body}); strings.Contains(src, ringAlias) {
			t.Errorf("%s is no bare use of the phantom, and the file aliases it:\n%s", name, src)
		}
	}
	// Declared in one member file, named in another: the package's own.
	src = render(map[string]string{
		"declares.go": "type RingOps[X any] struct{}\n",
		"names.go":    "func build(R RingOps[int]) {}\n",
	})
	if strings.Contains(src, ringAlias) {
		t.Errorf("a member file declares RingOps, and the file aliases the phantom over it:\n%s", src)
	}
}

func TestRender_ShadowedSurfaceNameStaysQualified(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_shadowed", nil)
	fam.Add(registry.ProofEntry{
		Name:  "Member",
		Build: registry.BuildSpec{Headline: "∀At:bool. At ⇒ At", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err := Render(fam, "zz_typedgen_shadowed", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatal(err)
	}
	source := string(rendered.Source)
	for _, want := range []string{"At Typed[Bool]", "return proof.At(th.entry, At)"} {
		if !strings.Contains(source, want) {
			t.Errorf("rendered file lacks %q:\n%s", want, source)
		}
	}
}

func TestBareAuthoring_UsesTheDeclaredAliasSource(t *testing.T) {
	const declarations = "type Fixture = proof.Case\n"
	source, imported, err := bareAuthoring("fixture", declarations)
	if err != nil {
		t.Fatal(err)
	}
	if imported || source != declarations {
		t.Fatalf("authoring.Case aliases a constructor, so proof.Case must retain its qualifier: %q", source)
	}
}

// A gloss go/doc would end early is refused by name: the sentence
// go/doc cuts is the line `go doc` and pkg.go.dev show for the package.
func TestRender_RefusesAGlossGoDocCutsShort(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_gloss", nil)
	if _, err := Render(fam, "zz_typedgen_gloss", t.TempDir(), "the interval m .. n of naturals"); err == nil ||
		!strings.Contains(err.Error(), "does not read as one sentence") {
		t.Errorf("a gloss holding a period followed by a space was not refused: %v", err)
	}
}

// TestTypedefsInScope: the phantom of a type minted below the chapters
// is in every proof file's scope, library/authoring declaring it; a
// chapter's is in a family's scope where a wrapper's signature names
// the type — here the signature of a statement about to join a chapter
// that registers nothing yet.
func TestTypedefsInScope(t *testing.T) {
	always := map[string]bool{}
	for metatype, ph := range typedefPhantoms {
		if !ph.mintedByAChapter() {
			always[metatype] = true
		}
	}
	if !always["real"] || !always["int"] || len(always) != 2 {
		t.Fatalf("the types minted below the chapters are real and int, got %v", always)
	}
	same := func(got, want map[string]bool) bool {
		if len(got) != len(want) {
			return false
		}
		for k := range want {
			if !got[k] {
				return false
			}
		}
		return true
	}

	x := ext.Var("x", dsl.RealType)
	overReals := prop.MakeProp(ext.ForAll(x)(core.Eq(x.Core(), x.Core())).Core())
	if in := TypedefsInScope(nil); !same(in, always) {
		t.Errorf("with no statement, exactly the types minted below the chapters are in scope, got %v", in)
	}
	if in := TypedefsInScope(nil, overReals, nil); !same(in, always) {
		t.Errorf("a statement over the reals adds nothing to %v, got %v", always, in)
	}

	// A chapter's typedef, read off a statement about to join: list is
	// minted by datatypes/list, and a statement binding a list puts it
	// in scope.
	listType := ext.MakeType("list", core.MakeVarType("A"))
	l := ext.Var("l", listType)
	overLists := prop.MakeProp(ext.ForAll(l)(core.Eq(l.Core(), l.Core())).Core())
	withList := map[string]bool{"list": true}
	for k := range always {
		withList[k] = true
	}
	if in := TypedefsInScope(nil, overLists); !same(in, withList) {
		t.Errorf("a statement binding a list adds list, got %v", in)
	}
}

// library/authoring DECLARES THE PHANTOM OF EVERY TYPE MINTED BELOW THE
// CHAPTERS, under the name its owner gives it. A proof file names such
// a phantom bare through its dot import, the generated wrappers name it
// by its owner, and TypedefsInScope tells the emitter it is in scope
// everywhere: all three read this table, so a row added here without
// its alias there is a proof file that does not compile, found at the
// first statement over the type.
func TestAuthoringDeclaresTheFrameworkPhantoms(t *testing.T) {
	const authoringFile = "../../authoring/authoring.go"
	af, err := parser.ParseFile(token.NewFileSet(), authoringFile, nil, parser.SkipObjectResolution)
	if err != nil {
		t.Fatalf("parse %s: %v", authoringFile, err)
	}
	// alias name → the "<qualifier>.<name>" it stands for.
	aliases := map[string]string{}
	ast.Inspect(af, func(n ast.Node) bool {
		spec, ok := n.(*ast.TypeSpec)
		if !ok || !spec.Assign.IsValid() {
			return true
		}
		if sel, ok := spec.Type.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok {
				aliases[spec.Name.Name] = x.Name + "." + sel.Sel.Name
			}
		}
		return false
	})
	if len(aliases) == 0 {
		t.Fatalf("%s declares no type alias — not library/authoring's hand-written file", authoringFile)
	}
	checked := 0
	for metatype, ph := range typedefPhantoms {
		if ph.mintedByAChapter() {
			if got, declared := aliases[ph.name]; declared && got != "" {
				t.Errorf("%s: library/authoring aliases %s as %s, but the type is minted by a chapter (%s) — "+
					"library/authoring imports no chapter", metatype, ph.name, got, ph.home)
			}
			continue
		}
		checked++
		if got := aliases[ph.name]; got != ph.spelling() {
			t.Errorf("%s: library/authoring declares %s = %q, want the alias %s = %s",
				metatype, ph.name, got, ph.name, ph.spelling())
		}
	}
	if checked == 0 {
		t.Fatal("no row of typedefPhantoms is minted below the chapters — the check read nothing")
	}
}

// A ROW OF typedefPhantoms NAMES A PHANTOM THAT EXISTS: its home
// package is on disk and declares the type, with the row's number of
// type parameters. The table is consulted only for a metatype some
// statement names, so a row whose type has retired — and whose home
// package may have gone with it — is read by nothing and fails
// nothing; this is what reads it.
func TestTypedefPhantomsResolve(t *testing.T) {
	// The module root, from this package's directory.
	const moduleRoot, modulePath = "../../..", "github.com/euc-ai/xugo/"
	if _, err := os.Stat(filepath.Join(moduleRoot, "go.mod")); err != nil {
		t.Fatalf("moduleRoot %q is not the module's root: %v", moduleRoot, err)
	}
	if len(typedefPhantoms) == 0 {
		t.Fatal("typedefPhantoms is empty")
	}
	fset := token.NewFileSet()
	for metatype, ph := range typedefPhantoms {
		rel, inModule := strings.CutPrefix(ph.home, modulePath)
		if !inModule {
			t.Errorf("%s: home %q is outside the module", metatype, ph.home)
			continue
		}
		dir := filepath.Join(moduleRoot, filepath.FromSlash(rel))
		files, err := os.ReadDir(dir)
		if err != nil {
			t.Errorf("%s: the row's home package %s is not on disk (%v) — the type's chapter has gone; delete the row", metatype, ph.home, err)
			continue
		}
		arity := -1
		for _, f := range files {
			if f.IsDir() || !strings.HasSuffix(f.Name(), ".go") || strings.HasSuffix(f.Name(), "_test.go") {
				continue
			}
			af, err := parser.ParseFile(fset, filepath.Join(dir, f.Name()), nil, parser.SkipObjectResolution)
			if err != nil {
				t.Fatalf("parse %s/%s: %v", dir, f.Name(), err)
			}
			ast.Inspect(af, func(n ast.Node) bool {
				spec, ok := n.(*ast.TypeSpec)
				if !ok || spec.Name.Name != ph.name {
					return true
				}
				arity = 0
				if spec.TypeParams != nil {
					for _, field := range spec.TypeParams.List {
						arity += len(field.Names)
					}
				}
				return false
			})
		}
		switch {
		case arity < 0:
			t.Errorf("%s: %s declares no type %s — the phantom was renamed or removed; fix or delete the row", metatype, ph.home, ph.name)
		case arity != ph.arity:
			t.Errorf("%s: %s.%s takes %d type parameters, the row says %d", metatype, ph.home, ph.name, arity, ph.arity)
		}
	}
}

// A structure law's reading holds its Fact as a named field and
// declares AsFact (proof.CiteTarget) itself: embedding the Fact would
// promote its whole method set, which Go compiles once per reading
// type — 528 of them across the corpus.
func TestRender_ReadingHoldsItsFact(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_reading", nil)
	fam.Add(registry.ProofEntry{
		Name:  "Law",
		Build: registry.BuildSpec{Headline: "∀x y:A. x = y ⇒ y = x", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err := Render(fam, "zz_typedgen_reading", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	for _, want := range []string{
		"type lawReading struct{ fact Fact }\n",
		"func (th lawReading) AsFact() Fact { return th.fact }\n",
		"\treturn lawReading{fact: Read(th.entry, instance)}\n",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("the rendered file lacks %q\n--- source: ---\n%s", want, src)
		}
	}
	if strings.Contains(src, "struct{ Fact }") {
		t.Errorf("a reading embeds its Fact\n--- source: ---\n%s", src)
	}
}

// A reading's At declares only the type parameters its slots spell: the
// law's component letter is fixed by the instance and occurs in no
// remaining slot, so declaring it would leave every call unable to
// infer it.
func TestRender_ReadingAtDeclaresOnlyItsSlotsLetters(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_reading_letters", nil)
	fam.Add(registry.ProofEntry{
		Name:  "Law",
		Build: registry.BuildSpec{Headline: "∀x y:A. x = y ⇒ ∀p q:B. p = q ⇒ q = p", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err := Render(fam, "zz_typedgen_reading_letters", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	if !strings.Contains(src, "func (th lawReading) At[Type1 TypePhantom](") {
		t.Errorf("the reading's At does not declare exactly the slots' letter Type1\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "func (th lawReading) At[Type0") {
		t.Errorf("the reading's At declares the component letter Type0, which no argument mentions\n--- source: ---\n%s", src)
	}
}

// A reading's point whose membership in a component is a guard takes a
// proof.Member, and the At bundles its evidence, wherever the guard sits
// along the body's ∀/⇒ telescope: with a second antecedent below it, or
// under a ∀ that follows an earlier antecedent. An ext.Typed slot there
// would take the Member, which embeds its term, and drop the evidence.
func TestRender_ReadingMemberGuardAtAnyLevel(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_reading_members", nil)
	for _, e := range []struct{ name, stmt string }{
		{"OneLevel", "∀c d:set(A). c = d ⇒ ∀x y:A. x ∈ c ∧ y ∈ c ⇒ y = x"},
		{"Nested", "∀c d:set(A). c = d ⇒ ∀x y:A. x ∈ c ∧ y ∈ c ⇒ x = y ⇒ y = x"},
		{"Telescope", "∀c d:set(A). c = d ⇒ ∀x:A. x ∈ c ⇒ ∀y:A. y ∈ d ⇒ y = x"},
	} {
		fam.Add(registry.ProofEntry{
			Name:  e.name,
			Build: registry.BuildSpec{Headline: e.stmt, Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
		})
	}
	rendered, err := Render(fam, "zz_typedgen_reading_members", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	for _, reading := range []string{"oneLevelReading", "nestedReading", "telescopeReading"} {
		want := "func (th " + reading + ") At[Type0 TypePhantom](x, y *Member[Type0, on.Any]) proof.PremiseGroup {\n" +
			"\treturn WithMembers(th.fact.At(x, y), x, y)\n}\n"
		if !strings.Contains(src, want) {
			t.Errorf("%s's At does not take Members and bundle their evidence; want\n%s\n--- source: ---\n%s", reading, want, src)
		}
	}
}

// A reading's slots are the law's binders that are not its components,
// wherever the statement binds them: a map bound ahead of the
// components stays a slot of the reading, in the statement's order, and
// a point's guard in a component that the telescope reads first still
// makes it a Member.
func TestRender_ReadingKeepsABinderAheadOfItsComponents(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_reading_prefix", nil)
	fam.Add(registry.ProofEntry{
		Name:  "Law",
		Build: registry.BuildSpec{Headline: "∀f:A → A. ∀c d:set(A). c = d ⇒ ∀x:A. x ∈ d ⇒ f(x) ∈ c", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err := Render(fam, "zz_typedgen_reading_prefix", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	want := "func (th lawReading) At[Type0 TypePhantom](f Typed[Fun[Type0, Type0]], x *Member[Type0, on.Any]) proof.PremiseGroup {\n" +
		"\treturn WithMembers(th.fact.At(f, x), x)\n}\n"
	if !strings.Contains(src, want) {
		t.Errorf("the reading's At does not take the prefix map and the guarded point; want\n%s\n--- source: ---\n%s", want, src)
	}
}

// A structure's definition entry is wrapped like any definition, and
// its wrapper embeds the *registry.Structure the var holds: the typed
// Inst / At read the definition entry through it, and the wrap
// applies to a family.DefineStructure var as to a family.Add var. A
// door the wrapper does not fit is refused.
func TestRender_StructureWrapperEmbedsTheStructure(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_structure", nil)
	fam.DefineStructure(registry.DefEntry{
		Name:      "Pointed",
		Const:     "zz_typedgen_pointed",
		Type:      "A → bool",
		Equations: []string{"∀e:A. zz_typedgen_pointed(e) ⇔ e = e"},
	})
	fam.Add(registry.ProofEntry{
		Name:  "Member",
		Build: registry.BuildSpec{Headline: "∀p:bool. p ⇒ p", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err := Render(fam, "zz_typedgen_structure", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	for _, want := range []string{
		"type pointedThm struct{ *registry.Structure }\n",
		"func (th pointedThm) Entry() *registry.ProofEntry { return th.ProofEntry }\n",
		"\treturn proof.InstSole[Type0](th.ProofEntry)\n",
		"type memberThm struct{ entry *registry.ProofEntry }\n",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("the rendered file lacks %q\n--- source: ---\n%s", want, src)
		}
	}

	dir := t.TempDir()
	member := filepath.Join(dir, "member.go")
	const file = `package zz_typedgen_structure

var Pointed = family.DefineStructure(registry.DefEntry{Name: "Pointed"})

var Member = family.Add(registry.ProofEntry{Name: "Member"})
`
	if err := os.WriteFile(member, []byte(file), 0o644); err != nil {
		t.Fatal(err)
	}
	if _, err := rendered.ApplyWraps(dir); err != nil {
		t.Fatalf("ApplyWraps: %v", err)
	}
	wrapped, err := os.ReadFile(member)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"var Pointed = pointedThm{family.DefineStructure(registry.DefEntry{Name: \"Pointed\"})}\n",
		"var Member = memberThm{family.Add(registry.ProofEntry{Name: \"Member\"})}\n",
	} {
		if !strings.Contains(string(wrapped), want) {
			t.Errorf("the wrapped file lacks %q\n--- source: ---\n%s", want, wrapped)
		}
	}

	misfit := filepath.Join(dir, "misfit.go")
	if err := os.WriteFile(misfit, []byte("package zz_typedgen_structure\n\nvar Pointed = family.Define(registry.DefEntry{Name: \"Pointed\"})\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.Remove(member); err != nil {
		t.Fatal(err)
	}
	if _, err := rendered.ApplyWraps(dir); err == nil || !strings.Contains(err.Error(), "does not fit") {
		t.Errorf("a family.Define var of a structure's entry was not refused: %v", err)
	}
}

// ApplyWraps wraps a bare registration var in its entry's wrapper and
// re-types one wrapped in another wrapper — the type a former name
// rendered, after a rename — leaving a var already in its entry's
// wrapper alone.
func TestApplyWraps_RetypesAStaleWrapper(t *testing.T) {
	dir := t.TempDir()
	src := "package zz\n\n" +
		"var X = xOldThm{family.Add(registry.ProofEntry{Name: \"X\"})}\n\n" +
		"var Y = family.Add(registry.ProofEntry{Name: \"Y\"})\n\n" +
		"var Z = zThm{family.DefineStructure(registry.ProofEntry{Name: \"Z\"})}\n"
	file := filepath.Join(dir, "member.go")
	if err := os.WriteFile(file, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	r := &Rendered{typeNames: map[string]wrapTarget{
		"X": {typeName: "xThm"}, "Y": {typeName: "yThm"}, "Z": {typeName: "zThm", structure: true}}}
	report, err := r.ApplyWraps(dir)
	if err != nil {
		t.Fatalf("ApplyWraps: %v", err)
	}
	out, err := os.ReadFile(file)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"var X = xThm{family.Add(registry.ProofEntry{Name: \"X\"})}",
		"var Y = yThm{family.Add(registry.ProofEntry{Name: \"Y\"})}",
		"var Z = zThm{family.DefineStructure(registry.ProofEntry{Name: \"Z\"})}",
	} {
		if !strings.Contains(string(out), want) {
			t.Errorf("the rewritten file lacks %q\n--- source: ---\n%s", want, out)
		}
	}
	joined := strings.Join(report, "\n")
	for _, want := range []string{"wrapped 1 registration var(s)", "re-typed 1 wrapper(s) to the entry's name"} {
		if !strings.Contains(joined, want) {
			t.Errorf("the report lacks %q: %q", want, joined)
		}
	}
}

// TestBindLetter_IsProofsTypeBinder: the letters BindLetter reports are
// the Bind methods prover/proof declares on its TypeBinder, no more and
// no fewer. A generated wrapper and an emitted member write
// `TypeBinder.Bind<letter>[T]()` on the alphabet's word, and a generic
// method is not one reflection lists, so the methods are read off the
// source that declares them.
func TestBindLetter_IsProofsTypeBinder(t *testing.T) {
	file, err := parser.ParseFile(token.NewFileSet(), filepath.Join("..", "..", "..", "prover", "proof", "typed.go"), nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	declared := map[string]bool{}
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Recv == nil || len(fn.Recv.List) != 1 {
			continue
		}
		recv, ok := fn.Recv.List[0].Type.(*ast.Ident)
		if !ok || recv.Name != "_TypeVarBinder" {
			continue
		}
		if letter, isBind := strings.CutPrefix(fn.Name.Name, "Bind"); isBind {
			declared[letter] = true
		}
	}
	if len(declared) == 0 {
		t.Fatal("prover/proof/typed.go declares no Bind method on _TypeVarBinder: the scan reads nothing")
	}
	for letter := range declared {
		if !BindLetter(letter) {
			t.Errorf("proof's TypeBinder has Bind%s, and the alphabet lacks %s", letter, letter)
		}
	}
	for letter := range bindAlphabet {
		if !declared[letter] {
			t.Errorf("the alphabet has %s, and proof's TypeBinder has no Bind%s", letter, letter)
		}
	}
}
