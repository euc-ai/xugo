package gates

import (
	"go/ast"
	"go/parser"
	"go/token"
	"testing"
)

// argumentDepthBound is the arguments a declaration may nest, one inside
// the other, a member's proof body the first.
const argumentDepthBound = 6

// TestLintArgumentDepth — a member's arguments nest at most
// argumentDepthBound deep (chapter_constitution.md, "Premise
// discipline"). An argument is a closure whose first parameter is an
// *Argument: a member's proof body, a section's, the proof of a Have, a
// case's, an induction step's. A closure bound to a name inside another
// is nested as it stands in the source. The argument one past the bound
// is the one reported, once for a declaration: it is the one to state as
// a section of the member (`ctx.Lemma`) and cite.
func TestLintArgumentDepth(t *testing.T) {
	deepest := 0
	for _, f := range chapterProofFiles(t) {
		fset := token.NewFileSet()
		file, err := parser.ParseFile(fset, f, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		for _, decl := range file.Decls {
			depth, past := argumentDepth(decl)
			if depth > deepest {
				deepest = depth
			}
			if depth > argumentDepthBound {
				t.Errorf("%s:%d: %s nests its arguments %d deep, past %d — state the argument that opens here "+
					"as a section of the member (ctx.Lemma) and cite it",
					f, fset.Position(past).Line, declaredName(decl), depth, argumentDepthBound)
			}
		}
	}
	if deepest < 2 {
		t.Fatalf("no argument read inside another (deepest %d) — the reader broke, the gate is vacuous", deepest)
	}
}

// argumentDepth is the deepest nesting of arguments in decl, and where
// the first argument one past argumentDepthBound opens.
func argumentDepth(decl ast.Decl) (deepest int, past token.Pos) {
	var opens []bool
	depth := 0
	ast.Inspect(decl, func(n ast.Node) bool {
		if n == nil {
			if opens[len(opens)-1] {
				depth--
			}
			opens = opens[:len(opens)-1]
			return true
		}
		lit, isLit := n.(*ast.FuncLit)
		argument := isLit && takesArgument(lit)
		if argument {
			depth++
			if depth > deepest {
				deepest = depth
			}
			if depth == argumentDepthBound+1 && !past.IsValid() {
				past = lit.Pos()
			}
		}
		opens = append(opens, argument)
		return true
	})
	return deepest, past
}

// takesArgument reports whether the first parameter of lit is an
// *Argument, under the bare name or a package's.
func takesArgument(lit *ast.FuncLit) bool {
	params := lit.Type.Params
	if params == nil || len(params.List) == 0 {
		return false
	}
	star, isStar := params.List[0].Type.(*ast.StarExpr)
	if !isStar {
		return false
	}
	switch x := star.X.(type) {
	case *ast.Ident:
		return x.Name == "Argument"
	case *ast.SelectorExpr:
		return x.Sel.Name == "Argument"
	}
	return false
}

// declaredName is the name decl declares: a function's, or the first of
// a var, const or type declaration's.
func declaredName(decl ast.Decl) string {
	switch decl := decl.(type) {
	case *ast.FuncDecl:
		return decl.Name.Name
	case *ast.GenDecl:
		for _, spec := range decl.Specs {
			switch spec := spec.(type) {
			case *ast.ValueSpec:
				return spec.Names[0].Name
			case *ast.TypeSpec:
				return spec.Name.Name
			}
		}
	}
	return "a declaration"
}
