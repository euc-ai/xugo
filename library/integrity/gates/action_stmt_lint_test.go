// action_stmt_lint_test.go — NO ACTION BUILT AND DROPPED. `f.Rw()`,
// `Unfold("c")`, `Simp(…)` and every other Action constructor RETURN a
// step; the step runs only inside an action list — `a.Do(f.Rw())`, a
// Show, a Case. Written as a bare statement the call compiles, builds
// the step and discards it, and the proof goes on as if the line were
// not there: the failure then surfaces steps later, as a leaf still
// carrying what the dropped rewrite was to remove (metric_space's
// subspace member, where `parts[0].Rw()` on its own line failed as
// "SetTacMembership failed" on a leaf still spelling t). Go's vet has
// no notion of which values are steps; this lint does — the package
// prover/proof's own exported constructors returning Action, and the
// Fact methods that do — and refuses an expression statement that is
// a call to one.

package gates

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"strings"
	"testing"
)

// actionSurface is the set of names whose call builds an Action: the
// package-level constructors of prover/proof (as the chapters' bare
// aliases spell them, or `proof.X`), and the methods on Fact.
type actionSurface struct {
	constructors map[string]bool
	factMethods  map[string]bool
}

// proverActionSurface reads the surface off prover/proof's own source:
// every exported function with the sole result type Action, and every
// method on a Fact receiver with it.
func proverActionSurface(t *testing.T) actionSurface {
	t.Helper()
	fset := token.NewFileSet()
	pkgs, err := parser.ParseDir(fset, proverSourceDir, func(fi os.FileInfo) bool {
		return !strings.HasSuffix(fi.Name(), "_test.go")
	}, 0)
	if err != nil {
		t.Fatalf("parse %s: %v", proverSourceDir, err)
	}
	out := actionSurface{constructors: map[string]bool{}, factMethods: map[string]bool{}}
	for _, pkg := range pkgs {
		for _, file := range pkg.Files {
			for _, decl := range file.Decls {
				fn, ok := decl.(*ast.FuncDecl)
				if !ok || !fn.Name.IsExported() || fn.Type.Results == nil || len(fn.Type.Results.List) != 1 {
					continue
				}
				res, ok := fn.Type.Results.List[0].Type.(*ast.Ident)
				if !ok || res.Name != "Action" {
					continue
				}
				if fn.Recv == nil {
					out.constructors[fn.Name.Name] = true
					continue
				}
				recv := fn.Recv.List[0].Type
				if star, ok := recv.(*ast.StarExpr); ok {
					recv = star.X
				}
				if id, ok := recv.(*ast.Ident); ok && id.Name == "Fact" {
					out.factMethods[fn.Name.Name] = true
				}
			}
		}
	}
	if len(out.constructors) == 0 || len(out.factMethods) == 0 {
		t.Fatalf("no Action surface read off %s — not the prover/proof directory?", proverSourceDir)
	}
	return out
}

// discardedActions lists every expression statement of the file that
// is a call building an Action and dropping it.
func discardedActions(fset *token.FileSet, af *ast.File, surface actionSurface) []string {
	var sites []string
	ast.Inspect(af, func(n ast.Node) bool {
		es, ok := n.(*ast.ExprStmt)
		if !ok {
			return true
		}
		call, ok := es.X.(*ast.CallExpr)
		if !ok {
			return true
		}
		var name string
		switch fun := call.Fun.(type) {
		case *ast.Ident:
			if surface.constructors[fun.Name] {
				name = fun.Name
			}
		case *ast.SelectorExpr:
			if pkg, ok := fun.X.(*ast.Ident); ok && pkg.Name == "proof" && surface.constructors[fun.Sel.Name] {
				name = "proof." + fun.Sel.Name
			} else if surface.factMethods[fun.Sel.Name] {
				name = "<fact>." + fun.Sel.Name
			}
		}
		if name != "" {
			sites = append(sites, fset.Position(es.Pos()).String()+": "+name)
		}
		return true
	})
	return sites
}

func TestLintNoDiscardedAction(t *testing.T) {
	surface := proverActionSurface(t)
	fset := token.NewFileSet()
	for _, path := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, path, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", path, err)
		}
		for _, site := range discardedActions(fset, af, surface) {
			t.Errorf("%s — an Action built as a statement and dropped: the step never runs; "+
				"put it in an action list (a.Do(…), a Show, a Case)", site)
		}
	}

	// The negative control: the lint fires on both spellings.
	const bad = `package x
func f(a *Argument, parts []Fact) {
	parts[0].Rw()
	Unfold("ball")
	a.Do(parts[0].Rw(), Unfold("ball"))
}
`
	af, err := parser.ParseFile(fset, "bad.go", bad, 0)
	if err != nil {
		t.Fatal(err)
	}
	sites := discardedActions(fset, af, surface)
	if len(sites) != 2 {
		t.Fatalf("negative control: want 2 sites, got %d: %v", len(sites), sites)
	}
}
