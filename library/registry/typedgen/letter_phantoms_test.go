package typedgen

import (
	"go/ast"
	"go/parser"
	"go/token"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/aliasgen"
	"github.com/euc-ai/xugo/prover/proof"
)

// A family's generated file declares a phantom for every letter its
// statements bind beyond A–E, hypotheses' letters included, under the
// shared letters' contract (Reify is MakeVarType of the letter's own
// name), M among them; a type variable whose bare name library/authoring
// exports under another meaning gets none, is named in a comment and in
// the notes, and stays out of LettersInScope.
func TestRender_DeclaresTheFamilyLetters(t *testing.T) {
	fam := registry.NewFamily("zz_typedgen_letters", nil)
	for _, e := range []struct{ name, stmt string }{
		{"Indexed", "∀x:I. ∀u:U. ∀a:A. x = x ∧ u = u ∧ a = a"},
		{"Morphism", "∀m:M. ∀z:Z. m = m ∧ z = z"},
		{"Vector", "∀v:var:Vec. v = v"},
	} {
		fam.Add(registry.ProofEntry{
			Name:  e.name,
			Build: registry.BuildSpec{Headline: e.stmt, Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
		})
	}
	rendered, err := Render(fam, "zz_typedgen_letters", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	src := string(rendered.Source)
	for _, want := range []string{
		"type (\n\tI struct{}\n\tM struct{}\n\tU struct{}\n\tZ struct{}\n)\n",
		"func (I) Reify() HolType { return MakeVarType(\"I\") }\n",
		"func (M) Reify() HolType { return MakeVarType(\"M\") }\n",
		"func (U) Reify() HolType { return MakeVarType(\"U\") }\n",
		"func (Z) Reify() HolType { return MakeVarType(\"Z\") }\n",
		"// The statement letter Vec has no phantom here:\n",
	} {
		if !strings.Contains(src, want) {
			t.Errorf("the rendered file lacks %q\n--- source: ---\n%s", want, src)
		}
	}
	for _, refused := range []string{"\tA struct{}", "\tVec struct{}", "type Vec struct{}", "Reify() HolType { return MakeVarType(\"Vec\") }"} {
		if strings.Contains(src, refused) {
			t.Errorf("the rendered file declares %q, a letter it has no phantom for\n--- source: ---\n%s", refused, src)
		}
	}
	if !strings.Contains(strings.Join(rendered.Notes, "\n"), "zz_typedgen_letters: statement letter Vec without a phantom") {
		t.Errorf("the notes do not name the letter Vec: %q", rendered.Notes)
	}
	if _, err := parser.ParseFile(token.NewFileSet(), File, rendered.Source, parser.AllErrors); err != nil {
		t.Errorf("the rendered file does not parse: %v", err)
	}

	var inScope []string
	for letter := range LettersInScope(fam) {
		inScope = append(inScope, letter)
	}
	sort.Strings(inScope)
	if got := strings.Join(inScope, " "); got != "A B C D E I M U Z" {
		t.Errorf("LettersInScope = %s, want the shared letters and I, M, U, Z", got)
	}
	if got := len(LettersInScope(nil)); got != len(sharedLetters) {
		t.Errorf("a chapter that registers nothing has %d letters in scope, want the %d shared ones", got, len(sharedLetters))
	}

	// One letter is one declaration, outside a group.
	single := registry.NewFamily("zz_typedgen_one_letter", nil)
	single.Add(registry.ProofEntry{
		Name:  "Member",
		Build: registry.BuildSpec{Headline: "∀x:G. x = x", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) { return nil, nil }},
	})
	rendered, err = Render(single, "zz_typedgen_one_letter", t.TempDir(), "a fixture chapter")
	if err != nil {
		t.Fatalf("Render: %v", err)
	}
	if !strings.Contains(string(rendered.Source), "\ntype G struct{}\n\nfunc (G) Reify() HolType { return MakeVarType(\"G\") }\n") {
		t.Errorf("a single letter is not declared on its own\n--- source: ---\n%s", rendered.Source)
	}
}

// The letter rule reads a letter's name alone: A–E are library/authoring's,
// a name the surface exports under another meaning or no exported Go
// identifier has no phantom, and any other letter is the family's — every
// capital beyond A–E, the surface spelling none (TestSurfaceSpellsNoOtherLetter).
func TestOwnerOfLetter(t *testing.T) {
	for letter, want := range map[string]LetterOwner{
		"A": LetterOfAuthoring, "E": LetterOfAuthoring,
		"G": LetterOfFamily, "I": LetterOfFamily, "U": LetterOfFamily, "Z": LetterOfFamily,
		"F": LetterOfFamily, "T": LetterOfFamily, "M": LetterOfFamily, "N": LetterOfFamily, "K": LetterOfFamily,
		"Vec": LetterWithoutPhantom, // the surface's vector type
		"a":   LetterWithoutPhantom, // not exported
	} {
		if got := OwnerOfLetter(letter); got != want {
			t.Errorf("OwnerOfLetter(%q) = %d, want %d", letter, got, want)
		}
	}
}

// THE SURFACE SPELLS NO OTHER LETTER: the capital letters
// library/authoring exports are exactly the shared statement letters
// A–E. Every other capital a family's statements bind is then the
// family's own phantom, under its own name, in every family alike; a
// truth constant or a dimension letter on the surface takes a full name
// (True, False, DimN).
func TestSurfaceSpellsNoOtherLetter(t *testing.T) {
	for c := 'A'; c <= 'Z'; c++ {
		letter := string(c)
		switch onSurface := aliasgen.OnSurface(letter); {
		case onSurface && !sharedLetters[letter]:
			t.Errorf("library/authoring exports %s, which is no shared statement letter: a family whose statements bind %s "+
				"could not declare its phantom. Give the declaration a full name", letter, letter)
		case !onSurface && sharedLetters[letter]:
			t.Errorf("library/authoring does not export the shared statement letter %s", letter)
		}
	}
}

// library/authoring DECLARES EXACTLY THE SHARED LETTERS: an alias
// `X = ext.X` whose ext type is a letter's phantom, its Reify
// MakeVarType("X"). A letter added there and not to sharedLetters
// would be declared a second time by every family binding it; one
// in sharedLetters and not there would have no phantom at all.
func TestAuthoringDeclaresTheSharedLetters(t *testing.T) {
	const authoringFile, extFile = "../../authoring/authoring.go", "../../../ext/holtype_phantom.go"
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, authoringFile, nil, parser.SkipObjectResolution)
	if err != nil {
		t.Fatalf("parse %s: %v", authoringFile, err)
	}
	ef, err := parser.ParseFile(fset, extFile, nil, parser.SkipObjectResolution)
	if err != nil {
		t.Fatalf("parse %s: %v", extFile, err)
	}
	// The ext types whose Reify is MakeVarType of their own name.
	letters := map[string]bool{}
	for _, decl := range ef.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Recv == nil || fn.Name.Name != "Reify" || fn.Body == nil || len(fn.Body.List) != 1 {
			continue
		}
		receiver, ok := fn.Recv.List[0].Type.(*ast.Ident)
		if !ok {
			continue
		}
		ret, ok := fn.Body.List[0].(*ast.ReturnStmt)
		if !ok || len(ret.Results) != 1 {
			continue
		}
		call, ok := ret.Results[0].(*ast.CallExpr)
		if !ok || len(call.Args) != 1 {
			continue
		}
		if callee, ok := call.Fun.(*ast.Ident); !ok || callee.Name != "MakeVarType" {
			continue
		}
		if lit, ok := call.Args[0].(*ast.BasicLit); ok {
			if name, err := strconv.Unquote(lit.Value); err == nil && name == receiver.Name {
				letters[name] = true
			}
		}
	}
	declared := map[string]bool{}
	ast.Inspect(af, func(n ast.Node) bool {
		spec, ok := n.(*ast.TypeSpec)
		if !ok || !spec.Assign.IsValid() {
			return true
		}
		if sel, ok := spec.Type.(*ast.SelectorExpr); ok {
			if x, ok := sel.X.(*ast.Ident); ok && x.Name == "ext" && sel.Sel.Name == spec.Name.Name && letters[spec.Name.Name] {
				declared[spec.Name.Name] = true
			}
		}
		return false
	})
	if len(declared) == 0 {
		t.Fatalf("%s aliases no letter phantom of %s — the check read nothing", authoringFile, extFile)
	}
	for letter := range declared {
		if !sharedLetters[letter] {
			t.Errorf("library/authoring aliases the letter %s = ext.%s, which sharedLetters lacks", letter, letter)
		}
	}
	for letter := range sharedLetters {
		if !declared[letter] {
			t.Errorf("sharedLetters holds %s, which library/authoring does not alias from ext", letter)
		}
	}
}
