// set_spelling_lint_test.go — the set(τ) spelling gate.
//
// The text DSL spells a set's type set(τ) and a predicate's τ → bool
// (ext/dsl/typenames.go, setspelling.go). The parser holds one
// direction at every door — a binder declared set(…) is never applied.
// This gate holds the other over the corpus: a binder declared
// `X → bool` that is never applied and stands under a set operator
// (∈ ⊆ ⊊ ∪ ∩ ∖, ⋃ ⋂, a Σ range, an equation with a set-shaped
// partner) is a set spelled as a predicate, and the finding names the
// spelling to write. A binder handed whole to a constant is the
// author's call — `finite(s)` reads either way — and stays unreported.
//
// The walker over the chapter files' statement-shaped literals is
// shared with the respelling sweep.
package gates

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
)

// dslPiece is one string literal of a chapter file: its content, where
// the content starts in the file, and where it sits in the joined text
// of the chain it belongs to. verbatim reports that the file spells the
// content byte for byte (no escapes), so a rewrite can splice into it.
type dslPiece struct {
	content   string
	fileStart int
	off       int
	verbatim  bool
}

// dslLiteral is a statement-shaped text of a chapter file: a string
// literal, or a `+` chain of literals and Go expressions, joined — each
// non-literal leaf stands as a placeholder identifier, so the chain
// still parses as the statement it spells.
type dslLiteral struct {
	file   string
	line   int
	text   string
	pieces []dslPiece
}

// walkDSLLiterals visits every literal of the chapter files (minus the
// construction chapters' internals) whose joined text satisfies want.
func walkDSLLiterals(t *testing.T, want func(string) bool, visit func(dslLiteral)) {
	t.Helper()
	fset := token.NewFileSet()
	for _, file := range chapterProofFiles(t) {
		src, err := os.ReadFile(file)
		if err != nil {
			t.Fatal(err)
		}
		if !want(string(src)) {
			continue
		}
		af, err := parser.ParseFile(fset, file, src, parser.ParseComments)
		if err != nil {
			t.Fatalf("%s: %v", file, err)
		}
		handled := map[ast.Node]bool{}
		var leaves func(e ast.Expr) ([]ast.Expr, bool)
		leaves = func(e ast.Expr) ([]ast.Expr, bool) {
			switch e := e.(type) {
			case *ast.ParenExpr:
				return leaves(e.X)
			case *ast.BinaryExpr:
				if e.Op == token.ADD {
					l, lok := leaves(e.X)
					r, rok := leaves(e.Y)
					if lok || rok {
						return append(l, r...), true
					}
				}
			case *ast.BasicLit:
				if e.Kind == token.STRING {
					return []ast.Expr{e}, true
				}
			}
			return []ast.Expr{e}, false
		}
		emit := func(exprs []ast.Expr) {
			var lit dslLiteral
			var joined strings.Builder
			holes := 0
			for _, e := range exprs {
				bl, ok := e.(*ast.BasicLit)
				if !ok || bl.Kind != token.STRING {
					fmt.Fprintf(&joined, "zzhole%d", holes)
					holes++
					continue
				}
				content, err := strconv.Unquote(bl.Value)
				if err != nil {
					return
				}
				pos := fset.Position(bl.Pos())
				if lit.file == "" {
					lit.file, lit.line = file, pos.Line
				}
				lit.pieces = append(lit.pieces, dslPiece{
					content:   content,
					fileStart: pos.Offset + 1,
					off:       joined.Len(),
					verbatim:  strings.HasPrefix(bl.Value, "`") || strconv.Quote(content) == bl.Value,
				})
				joined.WriteString(content)
			}
			lit.text = joined.String()
			if lit.file != "" && want(lit.text) {
				visit(lit)
			}
		}
		ast.Inspect(af, func(n ast.Node) bool {
			if handled[n] {
				return false
			}
			switch n := n.(type) {
			case *ast.BinaryExpr:
				if n.Op != token.ADD {
					return true
				}
				ls, anyLit := leaves(n)
				if !anyLit {
					return true
				}
				for _, l := range ls {
					handled[l] = true
				}
				emit(ls)
				return false
			case *ast.BasicLit:
				if n.Kind == token.STRING {
					emit([]ast.Expr{n})
				}
			}
			return true
		})
	}
}

func TestSetSpellingLint(t *testing.T) {
	var findings []string
	walkDSLLiterals(t, func(s string) bool { return strings.Contains(s, "→ bool") }, func(l dslLiteral) {
		rep := dsl.AnalyzeSetSpelling(l.text)
		if len(rep.Errors) > 0 {
			return // the parse gate (B0) owns unparseable texts
		}
		for _, b := range rep.Binders {
			if b.SpelledAsPredicate() {
				findings = append(findings, fmt.Sprintf("%s:%d: %s:%s stands under a set operator but is spelled as a predicate; write %s:%s",
					l.file, l.line, b.Name, b.TypeText, b.Name, b.Folded))
			}
		}
	})
	sort.Strings(findings)
	for _, f := range findings {
		t.Error(f)
	}
}
