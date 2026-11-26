package gates

import (
	"go/ast"
	"go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/xugofmt"
)

// A README ROW THAT GIVES A CONSTANT'S TYPE GIVES THE DEFINITION'S. A
// chapter's definitions table may state a constant by its type,
// "| `XDef` | `const`: type |". Nothing else reads that column, so a
// definition whose `Type:` changes leaves the row describing a signature
// the code no longer has. The row is held to the definition: both sides
// are parsed as types and compared. A row whose text after the colon does
// not parse as a type describes the constant in words and is not read.
func TestLintReadmeDefinitionTypes(t *testing.T) {
	proofs := filepath.Join(moduleRoot, "library", "proofs")
	types := definitionTypes(t, proofs)
	row := regexp.MustCompile("^\\|\\s*`[A-Za-z0-9_]+`\\s*\\|\\s*`([a-z][a-z0-9_]*)`:\\s*(.+?)\\s*\\|\\s*$")
	err := filepath.WalkDir(proofs, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || d.Name() != "README.md" {
			return err
		}
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		rel, _ := filepath.Rel(moduleRoot, path)
		for i, line := range strings.Split(string(src), "\n") {
			m := row.FindStringSubmatch(line)
			if m == nil {
				continue
			}
			code, ok := types[m[1]]
			if !ok {
				continue
			}
			stated, err := dsl.ParseTypeText(m[2])
			if err != nil {
				continue
			}
			defined, err := dsl.ParseTypeText(code)
			if err != nil {
				continue
			}
			if !stated.Equals(defined) {
				t.Errorf("%s:%d: the row gives `%s` the type %s; its definition's Type is %s.\n"+
					"    Write the definition's type in the row.", rel, i+1, m[1], m[2], code)
			}
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
}

// definitionTypes reads every `registry.DefEntry{…}` literal of the proof
// files and returns its Const's Type text. A constant two literals define
// with two types is left out: the row cannot be held to either.
func definitionTypes(t *testing.T, root string) map[string]string {
	t.Helper()
	types := map[string]string{}
	twice := map[string]bool{}
	fset := token.NewFileSet()
	err := filepath.WalkDir(root, func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || !strings.HasSuffix(path, ".go") || strings.HasSuffix(path, "_test.go") {
			return err
		}
		file, err := parser.ParseFile(fset, path, nil, 0)
		if err != nil {
			return err
		}
		ast.Inspect(file, func(n ast.Node) bool {
			lit, ok := n.(*ast.CompositeLit)
			if !ok {
				return true
			}
			sel, ok := lit.Type.(*ast.SelectorExpr)
			if !ok || sel.Sel.Name != "DefEntry" {
				return true
			}
			var constant, typ string
			for _, elt := range lit.Elts {
				kv, ok := elt.(*ast.KeyValueExpr)
				if !ok {
					continue
				}
				key, ok := kv.Key.(*ast.Ident)
				text, isString := xugofmt.StringValue(kv.Value)
				if !ok || !isString {
					continue
				}
				switch key.Name {
				case "Const":
					constant = text
				case "Type":
					typ = dsl.OneLine(text)
				}
			}
			if constant == "" || typ == "" {
				return true
			}
			if prior, seen := types[constant]; seen && prior != typ {
				twice[constant] = true
			}
			types[constant] = typ
			return true
		})
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	for constant := range twice {
		delete(types, constant)
	}
	return types
}
