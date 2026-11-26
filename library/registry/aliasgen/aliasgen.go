// Package aliasgen renders the generated half of the bare-name surface
// proof bodies are written in — zz_constructors_gen.go of
// library/authoring, the package a proof file dot-imports — and holds
// the roster of the whole surface. It is a separate package so the
// gen_authoring command and the drift gate (TestAliasGenCurrent) share
// one renderer: what the gate compares against disk is byte-for-byte
// what the command would write, and a prover constructor added without
// a regeneration is a red test naming the command, not a name missing
// from the surface until an emitted body first spells it.
//
// library/authoring splits its surface across the hand-written
// authoring.go and the generated file: every exported prover
// constructor NOT already declared in the package. Hand-written
// declarations always win; redeclaration is impossible by construction.
//
// The roster (zz_surface_gen.go, in this package) is every name the
// two files declare, as data: OnSurface answers whether a name is one
// a proof file spells bare. A dot-imported name is in scope only in a
// file that carries the import and Go refuses an import a file does
// not use, so whoever writes a proof file by program — the emitter of
// session proofs — decides the import by reading its own output
// against the roster. The roster is rendered with the constructor file
// and held by the same gate.
//
// Selection rule (syntactic, no type-checking needed — constructors
// declare their result types by name): every exported top-level
// function in package prover/proof with no receiver whose single result
// type is one of resultTypes gets an alias line `Name = proof.Name`.
package aliasgen

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"os"
	"sort"
	"strings"
)

// The two products' file names: the constructor file in
// library/authoring, the roster in this package.
const (
	File        = "zz_constructors_gen.go"
	SurfaceFile = "zz_surface_gen.go"
)

// OnSurface reports whether name is one library/authoring declares: a
// name a proof file spells bare through its dot import.
func OnSurface(name string) bool { return surface[name] }

// OnSurfaceFrom reports whether the surface aliases owner.name under
// that same name. Renamed entries do not alias unrelated declarations
// that happen to share the surface spelling.
func OnSurfaceFrom(owner, name string) bool { return sameNamedSurface[owner+"."+name] }

// Rendered is the two generated files as the generator produces them.
type Rendered struct {
	Constructors []byte // zz_constructors_gen.go, for library/authoring
	Surface      []byte // zz_surface_gen.go, for this package
}

// resultTypes is the set of prover result-type names that mark a
// function as part of the Action/Step constructor surface.
var resultTypes = map[string]bool{
	"Action":        true,
	"Step":          true,
	"Case":          true,
	"SpecializeHyp": true,
	"CalcLeg":       true,
	"SimpRule":      true,
	"Fact":          true, // MakeFact / At — the fact-value constructors (fact.go)
	"ByShape":       true, // Denoted(n) — By's shaping options (fact.go)
	"PremiseGroup":  true, // GroupPremises / WithMembers — a fact with the facts it consumes (fact.go, member.go)

	// The ⇔-split halves (iff_direction.go). Each half is its own type
	// precisely so the two cannot be swapped, which means each also
	// needs its own row here.
	"IffForward":      true,
	"IffBackward":     true,
	"IffBothHold":     true,
	"IffNeitherHolds": true,
	// The ∨-split branches (disjunction_branches.go), typed apart for
	// the same reason.
	"DisjLeftHolds":  true,
	"DisjRightHolds": true,
	// The elementarity step's call (step_elementarity.go): an Action with its
	// fixed-parameter form .At.
	"ElementarityAction": true,
	// Generalizing(h…) — the hypotheses a ByInduction's predicate, read
	// from the goal, carries (induction_motive.go).
	"Generalization": true,
}

// retiredNames are prover constructors that are DELIBERATELY not part of
// the bare-name surface, even though they match the selection
// rule above. Emitting an alias for one of these would put a name in
// every proof file's scope that a proof must not use; leaving it
// out turns the misuse into a compile error at the call site, which is
// the loudest and cheapest check available.
//
// The three denote SEARCH forms live here. Their common defect is that
// they say HOW to find a term to abbreviate (a size threshold) instead
// of WHICH term is being abbreviated: the script tells the reader
// nothing, and the recorded step re-runs the heuristic at replay, so
// upstream drift silently changes the choice. The forms name the
// term — Argument.Denote / DenoteTerm / DenotedAs / DenoteRefuteAs.
//
// `Denote` additionally COLLIDES: in a proof file the name must mean
// Argument.Denote, the deduction verb, and nothing else.
//
// These stay exported from prover/proof: auto / expand run the search
// stage, and emit renders a recorded search-mode denote (a bare step,
// or a By's shaping) in the size form.
var retiredNames = map[string]string{
	"Denote":       "name the term: Argument.Denote(name, term) / DenoteTerm(name, term)",
	"Denoted":      "name the term: DenotedAs(name, term)",
	"DenoteRefute": "name the term: DenoteRefuteAs(name, term)",
	// The fact an entry or a generated wrapper reads as: the constructor
	// behind their AsFact, for the registry and the generator.
	"NamedFact": "pass the entry itself: it is a CiteTarget",
	// The def-expand step by the constant it opens: the engine's own
	// spelling, for the session and for a test that mints a constant.
	"DefExpandStep": "open the definition: Unfold(<the definition's entry>)",
	"DefinitionOf":  "name the definition's entry: its wrapper is a Definition",
}

// Render produces the two generated files from library/authoring's
// package directory dir: the scanned constructors (Constructors) minus
// every name the package already declares by hand, and the roster of
// both.
func Render(dir string, candidates map[string]bool) (*Rendered, error) {
	declared, err := declaredNamesInDir(dir, File)
	if err != nil {
		return nil, err
	}
	if len(declared) == 0 {
		return nil, fmt.Errorf("aliasgen: %s declares no name by hand — not library/authoring?", dir)
	}
	qualified, err := sameNamedAliasesInDir(dir, File)
	if err != nil {
		return nil, err
	}
	names := survivors(candidates, declared)
	if len(names) == 0 {
		return nil, errors.New("aliasgen: zero candidates survived — wrong directory?")
	}

	var b bytes.Buffer
	b.WriteString("// Code generated by library/cmd/gen_authoring. DO NOT EDIT.\n")
	b.WriteString("//\n")
	b.WriteString("// The scanned half of the bare-name surface: every exported\n")
	b.WriteString("// constructor of prover/proof that aliasgen's result-type rule\n")
	b.WriteString("// selects and the hand-written authoring.go does not already\n")
	b.WriteString("// declare. Regenerate after adding a prover constructor:\n")
	b.WriteString("//\n")
	b.WriteString("//\tgo generate ./library/authoring/\n")
	b.WriteString("//\n")
	b.WriteString("// TestAliasGenCurrent re-renders this file and fails while it is stale.\n")
	// Blank line: this banner is file provenance, not the package's
	// documentation. Attached to the package clause it would join the
	// package doc, which authoring.go alone carries.
	b.WriteString("\npackage authoring\n\n")
	b.WriteString("import \"github.com/euc-ai/xugo/prover/proof\"\n\n")
	b.WriteString("var (\n")
	for _, name := range names {
		fmt.Fprintf(&b, "\t%s = proof.%s\n", name, name)
		qualified["proof."+name] = true
	}
	b.WriteString(")\n")
	constructors, err := formatted(b.Bytes())
	if err != nil {
		return nil, err
	}

	roster := append([]string(nil), names...)
	for name := range declared {
		roster = append(roster, name)
	}
	sort.Strings(roster)
	b.Reset()
	b.WriteString("// Code generated by library/cmd/gen_authoring. DO NOT EDIT.\n")
	b.WriteString("//\n")
	b.WriteString("// The roster of the bare-name surface: every name library/authoring\n")
	b.WriteString("// declares, by hand or in its generated file. Regenerate after a\n")
	b.WriteString("// name joins or leaves either:\n")
	b.WriteString("//\n")
	b.WriteString("//\tgo generate ./library/authoring/\n")
	b.WriteString("//\n")
	b.WriteString("// TestAliasGenCurrent re-renders this file and fails while it is stale.\n")
	b.WriteString("\npackage aliasgen\n\n")
	b.WriteString("var surface = map[string]bool{\n")
	for _, name := range roster {
		fmt.Fprintf(&b, "\t%q: true,\n", name)
	}
	b.WriteString("}\n")
	qualifiedNames := make([]string, 0, len(qualified))
	for name := range qualified {
		qualifiedNames = append(qualifiedNames, name)
	}
	sort.Strings(qualifiedNames)
	b.WriteString("\nvar sameNamedSurface = map[string]bool{\n")
	for _, name := range qualifiedNames {
		fmt.Fprintf(&b, "\t%q: true,\n", name)
	}
	b.WriteString("}\n")
	surface, err := formatted(b.Bytes())
	if err != nil {
		return nil, err
	}
	return &Rendered{Constructors: constructors, Surface: surface}, nil
}

// sameNamedAliasesInDir reads aliases whose bare name is the qualified
// declaration's own name. A renamed surface entry such as Case =
// proof.MakeCase does not make the unrelated type proof.Case bare.
func sameNamedAliasesInDir(dir, skipFile string) (map[string]bool, error) {
	files, err := parser.ParseDir(token.NewFileSet(), dir, func(fi os.FileInfo) bool {
		return !strings.HasSuffix(fi.Name(), "_test.go") && fi.Name() != skipFile
	}, 0)
	if err != nil {
		return nil, fmt.Errorf("aliasgen: parse %s: %w", dir, err)
	}
	aliases := map[string]bool{}
	add := func(name string, target ast.Expr) {
		if sel, ok := target.(*ast.SelectorExpr); ok && sel.Sel.Name == name {
			if owner, ok := sel.X.(*ast.Ident); ok {
				aliases[owner.Name+"."+name] = true
			}
		}
	}
	for _, pkg := range files {
		for _, file := range pkg.Files {
			for _, decl := range file.Decls {
				gen, ok := decl.(*ast.GenDecl)
				if !ok {
					continue
				}
				for _, spec := range gen.Specs {
					switch spec := spec.(type) {
					case *ast.ValueSpec:
						if len(spec.Names) == 1 && len(spec.Values) == 1 {
							add(spec.Names[0].Name, spec.Values[0])
						}
					case *ast.TypeSpec:
						if !spec.Assign.IsValid() {
							continue
						}
						target := spec.Type
						switch app := target.(type) {
						case *ast.IndexExpr:
							target = app.X
						case *ast.IndexListExpr:
							target = app.X
						}
						add(spec.Name.Name, target)
					}
				}
			}
		}
	}
	return aliases, nil
}

// survivors is the sorted candidate list minus the names a package
// already declares.
func survivors(candidates, declared map[string]bool) []string {
	var names []string
	for name := range candidates {
		if !declared[name] {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	return names
}

func formatted(src []byte) ([]byte, error) {
	out, err := format.Source(src)
	if err != nil {
		return nil, fmt.Errorf("aliasgen: rendered source does not format (generator bug): %w", err)
	}
	return out, nil
}

// Constructors parses the prover package directory and returns the
// exported constructor names matching the selection rule — the
// candidate set both products are rendered from.
func Constructors(proverDir string) (map[string]bool, error) {
	fset := token.NewFileSet()
	pkgs, err := parser.ParseDir(fset, proverDir, func(fi os.FileInfo) bool {
		return !strings.HasSuffix(fi.Name(), "_test.go")
	}, 0)
	if err != nil {
		return nil, fmt.Errorf("aliasgen: parse %s: %w", proverDir, err)
	}
	out := map[string]bool{}
	for _, pkg := range pkgs {
		for _, file := range pkg.Files {
			for _, decl := range file.Decls {
				fn, ok := decl.(*ast.FuncDecl)
				if !ok || fn.Recv != nil || !fn.Name.IsExported() {
					continue
				}
				if fn.Type.TypeParams != nil {
					// A generic function cannot be bound un-instantiated
					// (utils/generic_test.go): where a bare
					// spelling is wanted it rides a VALUE with generic
					// methods (TypeBinder), never a var alias of the
					// function.
					continue
				}
				res := fn.Type.Results
				if res == nil || len(res.List) != 1 {
					continue
				}
				ident, ok := res.List[0].Type.(*ast.Ident)
				if !ok || !resultTypes[ident.Name] {
					continue
				}
				if _, retired := retiredNames[fn.Name.Name]; retired {
					continue
				}
				out[fn.Name.Name] = true
			}
		}
	}
	if len(out) == 0 {
		return nil, fmt.Errorf("aliasgen: no constructor in %s — not the prover/proof directory?", proverDir)
	}
	return out, nil
}

// declaredNamesInDir parses the package in dir minus the generated
// file and returns every package-level declared name — the exclusion
// set that lets hand-written declarations win.
func declaredNamesInDir(dir, skipFile string) (map[string]bool, error) {
	fset := token.NewFileSet()
	pkgs, err := parser.ParseDir(fset, dir, func(fi os.FileInfo) bool {
		return !strings.HasSuffix(fi.Name(), "_test.go") && fi.Name() != skipFile
	}, 0)
	if err != nil {
		return nil, fmt.Errorf("aliasgen: parse %s: %w", dir, err)
	}
	out := map[string]bool{}
	for _, pkg := range pkgs {
		for _, file := range pkg.Files {
			collectDeclaredNames(file, out)
		}
	}
	return out, nil
}

func collectDeclaredNames(file *ast.File, out map[string]bool) {
	for _, decl := range file.Decls {
		switch d := decl.(type) {
		case *ast.FuncDecl:
			if d.Recv == nil {
				out[d.Name.Name] = true
			}
		case *ast.GenDecl:
			for _, spec := range d.Specs {
				switch s := spec.(type) {
				case *ast.ValueSpec:
					for _, n := range s.Names {
						out[n.Name] = true
					}
				case *ast.TypeSpec:
					out[s.Name.Name] = true
				}
			}
		}
	}
}
