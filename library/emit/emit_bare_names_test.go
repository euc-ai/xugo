package emit

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry/aliasgen"
)

// offSurfaceNames are the capitalized names the emitter's string
// literals write with no qualifier before them in the literal that are
// no name of library/authoring, each with why the rendered file still
// compiles — or is meant not to.
var offSurfaceNames = map[string]string{
	"SimpWith":        "written after the Script's `ctx.` (emitMiniStep's sx): a method",
	"SimpWithFlipped": "written after the Script's `ctx.` (emitMiniStep's sx): a method",
	"Obtain":          "written after the Argument's receiver (obtainVerbs): a method",
	"Obtain2":         "written after the Argument's receiver (obtainVerbs): a method",
	"Obtain3":         "written after the Argument's receiver (obtainVerbs): a method",
	"Obtain4":         "written after the Argument's receiver (obtainVerbs): a method",
	"Obtain5":         "written after the Argument's receiver (obtainVerbs): a method",
	"Denote":          "the search form of a recorded denote, retired from the surface (aliasgen): a landing names the term",
	"Denoted":         "the search form of a By's denote shaping, retired from the surface (aliasgen): a landing names the term",
}

// bareCall reads a capitalized Go name written bare — no qualifier, no
// receiver, no verb of the format string before it — where a call, an
// instantiation or a composite literal of it opens.
var bareCall = regexp.MustCompile(`(^|[^.\pL\pN_"%])(\p{Lu}[\pL\pN_]*)[(\[{]`)

// bareWord reads a text that is one capitalized Go name and nothing
// else.
var bareWord = regexp.MustCompile(`^\p{Lu}[\pL\pN_]*$`)

// bareNamesWritten are the capitalized names the string literals of the
// Go file at path write bare, each with the places that write it: a
// name heading a call, an instantiation or a composite literal inside
// a literal, and a literal that is one name and nothing else where the
// renderer holds it as a value to write — assigned, returned, appended
// to an argument list, an element of a table (`Raw`, `ByArith`,
// `Fact`). A literal that is one name as a `case` label, an operand of
// a comparison or an argument of another call names something read,
// not written. Literals joined by `+` are read as the one text they
// make.
func bareNamesWritten(t *testing.T, fset *token.FileSet, path string, found map[string][]string) {
	t.Helper()
	file, err := parser.ParseFile(fset, path, nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	// joined is the text of e where e is string literals joined by `+`.
	var joined func(e ast.Expr) (string, bool)
	joined = func(e ast.Expr) (string, bool) {
		switch x := e.(type) {
		case *ast.BasicLit:
			if x.Kind != token.STRING {
				return "", false
			}
			text, err := strconv.Unquote(x.Value)
			if err != nil {
				t.Fatalf("%s: %v", fset.Position(x.Pos()), err)
			}
			return text, true
		case *ast.BinaryExpr:
			if x.Op != token.ADD {
				return "", false
			}
			left, okLeft := joined(x.X)
			right, okRight := joined(x.Y)
			return left + right, okLeft && okRight
		case *ast.ParenExpr:
			return joined(x.X)
		}
		return "", false
	}
	note := func(name string, at token.Pos) {
		if len(found[name]) < 3 {
			found[name] = append(found[name], fset.Position(at).String())
		}
	}
	// held reports whether parent holds its child expression as a value
	// to write.
	held := func(parent ast.Node) bool {
		switch p := parent.(type) {
		case *ast.AssignStmt, *ast.ValueSpec, *ast.ReturnStmt, *ast.CompositeLit, *ast.KeyValueExpr:
			return true
		case *ast.CallExpr:
			fun, isIdent := p.Fun.(*ast.Ident)
			return isIdent && fun.Name == "append"
		}
		return false
	}
	var stack []ast.Node
	ast.Inspect(file, func(n ast.Node) bool {
		if n == nil {
			stack = stack[:len(stack)-1]
			return true
		}
		expr, isExpr := n.(ast.Expr)
		text, isText := "", false
		if isExpr {
			text, isText = joined(expr)
		}
		if !isText {
			stack = append(stack, n)
			return true
		}
		if bareWord.MatchString(text) && len(stack) > 0 && held(stack[len(stack)-1]) {
			note(text, n.Pos())
		}
		for _, m := range bareCall.FindAllStringSubmatch(text, -1) {
			note(m[2], n.Pos())
		}
		// The joined text is read whole: its literals are not read again.
		return false
	})
}

// TestEmit_BareNamesAreOnTheAuthoringSurface: a rendered proof file
// spells the prover's names bare and resolves them through its dot
// import of library/authoring, so a bare name the emitter writes that
// the surface lacks is a file that does not compile (`By(Raw, …)`
// where the surface declares no Raw). Every capitalized name a string
// literal of this package writes bare (bareNamesWritten) is a name of
// the surface's roster (aliasgen.OnSurface), or is listed in
// offSurfaceNames with the reason.
func TestEmit_BareNamesAreOnTheAuthoringSurface(t *testing.T) {
	files, err := os.ReadDir(".")
	if err != nil {
		t.Fatal(err)
	}
	found := map[string][]string{}
	fset := token.NewFileSet()
	for _, f := range files {
		if name := f.Name(); strings.HasSuffix(name, ".go") && !strings.HasSuffix(name, "_test.go") {
			bareNamesWritten(t, fset, name, found)
		}
	}
	// The scan reads the renderers: a By's shaping options are among
	// what it finds.
	for _, name := range []string{"By", "ByArith", "Raw", "PreNormalized", "Normalized", "Broadcast", "At", "ResidentHyp", "Fact"} {
		if _, written := found[name]; !written {
			t.Errorf("the scan does not find %s, which the emitter writes bare", name)
		}
	}
	var missing []string
	for name, at := range found {
		if aliasgen.OnSurface(name) {
			continue
		}
		if _, listed := offSurfaceNames[name]; listed {
			continue
		}
		missing = append(missing, name+" ("+strings.Join(at, ", ")+")")
	}
	sort.Strings(missing)
	for _, m := range missing {
		t.Errorf("the emitter writes a bare name the authoring surface lacks: %s", m)
	}
	for name := range offSurfaceNames {
		if _, written := found[name]; !written {
			t.Errorf("offSurfaceNames lists %s, which no literal of the emitter writes bare", name)
		}
		if aliasgen.OnSurface(name) {
			t.Errorf("offSurfaceNames lists %s, which the authoring surface declares", name)
		}
	}
}
