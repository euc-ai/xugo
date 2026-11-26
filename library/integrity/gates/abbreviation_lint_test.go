// abbreviation_lint_test.go — the statement rule on abbreviations
// (library/chapter_constitution.md, the statement paragraph): a table
// names compound terms, and a constant at a few plain arguments is
// written out where it is used.
package gates

import (
	"go/ast"
	"go/parser"
	"go/token"
	"path/filepath"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/xugofmt"
)

// TestLintAbbreviationIsCompound refuses an entry of any table a proof
// file declares — the chapter's (WithAbbrev), a member's Statement, a
// definition's, a section's lemma — whose text is one constant at
// dsl.WrittenOutArity or fewer arguments, each a name, a field of one
// or a numeral (dsl.IsShortConstantApplication): `polynomial_degree(p)`
// and `field_ring(L)` are written out at each use, never a «deg» or a
// «ring» declared for them. A constant at more arguments — the datum a
// chapter fixes at its six binders — may be named; whether the name
// earns its place is the review's call, not this gate's.
func TestLintAbbreviationIsCompound(t *testing.T) {
	offenders := 0
	for _, path := range chapterProofFiles(t) {
		if strings.HasPrefix(filepath.Base(path), "zz_") {
			continue
		}
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, path, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", path, err)
		}
		ast.Inspect(file, func(n ast.Node) bool {
			lit, ok := n.(*ast.CompositeLit)
			if !ok {
				return true
			}
			if id, ok := lit.Type.(*ast.Ident); !ok || id.Name != "Abbrev" {
				return true
			}
			for _, el := range lit.Elts {
				entry, ok := el.(*ast.CompositeLit)
				if !ok {
					continue
				}
				var name, text string
				for _, field := range entry.Elts {
					kv, ok := field.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					key, ok := kv.Key.(*ast.Ident)
					s, isString := xugofmt.StringValue(kv.Value)
					if !ok || !isString {
						continue
					}
					switch key.Name {
					case "Name":
						name = s
					case "Text":
						text = s
					}
				}
				short, err := dsl.IsShortConstantApplication(text)
				if err != nil {
					t.Errorf("%s: «%s»: the text does not parse: %v", fset.Position(entry.Pos()), name, err)
					continue
				}
				if short {
					offenders++
					t.Errorf("%s: «%s» ≔ %s is one constant at %d or fewer plain arguments: write the term out at each use and delete the entry",
						fset.Position(entry.Pos()), name, text, dsl.WrittenOutArity)
				}
			}
			return true
		})
	}
	if offenders > 0 {
		t.Logf("%d entr(y/ies) to write out", offenders)
	}
}
