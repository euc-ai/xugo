package gates

// TEXT DOORS READ ONE WAY. Every door that reads a statement or a claim
// text at a focus — the session's claim and lemma doors, the Go
// Script's statement and claim doors, the CLI's add-goal and
// parse-prop, emit's check that a rendered text reads back — reads it
// through dsl.ParsePropTextAtDoor, so a text cannot mean one thing in
// the session and another in the member emitted from it. A direct
// dsl.ParsePropTextInScope outside ext/dsl is refused, but in a
// definition door reading its own defining text, listed below with the
// reason; a listed file that no longer calls it is refused too, so the
// list cannot go stale.

import (
	"go/ast"
	"go/parser"
	"go/token"
	"io/fs"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

// textDoorExempt are the files that may parse a proposition text
// directly: definition doors, each reading the defining text of the
// constant it mints in a scope it builds for that text.
var textDoorExempt = map[string]string{
	"prover/proof/define.go":           "the definition door reads a defining equation",
	"prover/proof/define_spec.go":      "the specification door reads a specification",
	"prover/proof/define_inductive.go": "the inductive door reads a rule",
	"library/registry/define_data.go":  "the data door reads a constructor's extension",
}

const dslImportPath = "github.com/euc-ai/xugo/ext/dsl"

func TestLintTextDoorsReadOneWay(t *testing.T) {
	fset := token.NewFileSet()
	calling := map[string]bool{}
	err := filepath.WalkDir(moduleRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(moduleRoot, path)
		rel = filepath.ToSlash(rel)
		if d.IsDir() {
			if rel != "." && (rel == "ext/dsl" || strings.HasPrefix(d.Name(), ".") || d.Name() == "testdata") {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(path, ".go") || strings.HasSuffix(path, "_test.go") {
			return nil
		}
		f, err := parser.ParseFile(fset, path, nil, parser.SkipObjectResolution)
		if err != nil {
			return err
		}
		local := ""
		for _, imp := range f.Imports {
			if p, _ := strconv.Unquote(imp.Path.Value); p == dslImportPath {
				local = "dsl"
				if imp.Name != nil {
					local = imp.Name.Name
				}
			}
		}
		if local == "" {
			return nil
		}
		ast.Inspect(f, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || sel.Sel.Name != "ParsePropTextInScope" {
				return true
			}
			if pkg, ok := sel.X.(*ast.Ident); !ok || pkg.Name != local {
				return true
			}
			calling[rel] = true
			if _, exempt := textDoorExempt[rel]; !exempt {
				t.Errorf("%s:%d: a proposition text is parsed directly — read a statement or claim text through "+
					"dsl.ParsePropTextAtDoor, the doors' one reading; a definition door reading its own defining "+
					"text is listed in textDoorExempt with the reason", rel, fset.Position(call.Pos()).Line)
			}
			return true
		})
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	for file, why := range textDoorExempt {
		if !calling[file] {
			t.Errorf("%s is exempt (%s) but parses no proposition text directly any more — drop it from textDoorExempt", file, why)
		}
	}
}
