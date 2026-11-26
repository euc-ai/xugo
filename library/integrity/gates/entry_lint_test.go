// entry_lint_test.go — entry-DECLARATION lints: the one-declaration-
// per-entry shape.
//
// E0 — ENTRY VAR NAME IS THE ENTRY NAME. Every family member is
// declared as `var <V> = family.Add(registry.ProofEntry{Name: "<N>",
// …})`, and V == N: the Go variable a consumer cites and the
// registered (bare) name are the same word, so jump-to-definition,
// grep and the registry never disagree about what a member is called.
// Gated — the corpus measures zero mismatches. `family.Add` calls
// outside the single-var form are census-only (there are none).
//
// E1 — BUILD IS INLINE (the migration ratchet). One declaration per
// entry: the Build constructor call lives inside the entry literal
// (metadata fields first, Build last), never in a separate
// `var Build_X = family.Theorem(…)` the entry references by name. The
// split two-var ceremony was dissolved corpus-wide; this ratchet keeps
// the migrated class from regrowing. Scope is exactly that class: a
// `Build:` field whose value is an identifier resolving to a SAME-FILE
// package-level single-spec var whose initializer is a family
// constructor call (Theorem / Sections / Derived / Lifted).
// `registry.Bare(fn)` wrapping a hand-written build func
// stays legal, as does any shape the migration skipped.
//
// E2 — A FAMILY'S cards.go HOLDS CARDS ONLY. cards.go is the file a
// family's cards are laid in ahead of their proofs, so it shows what is
// still open (chapter_constitution.md, "Families: a theory chapter as a
// sub-package"): every declaration in it is a card's entry. A card
// filled there moves, entry and comment, to the proof file of its
// subject; a skeleton's definitions stand in definitions.go; and the
// blank imports that link the family's vocabulary stand in
// definitions.go or family.go, so the file is deleted with its last
// card and takes no link with it.
package gates

import (
	"go/ast"
	"go/parser"
	"go/token"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Shared collection
// ---------------------------------------------------------------------------

// entryCtorNames: the family Build constructors — the class the inline
// migration moved and the E1 ratchet guards.
var entryCtorNames = map[string]bool{
	"Theorem": true, "Sections": true, "Derived": true,
	"Lifted": true,
}

// inductiveKindFields are the handle fields an inductive door exposes,
// each a registered entry (registry.InductiveEntries).
var inductiveKindFields = map[string]bool{"Rules": true, "Induct": true, "Cases": true}

type entrySite struct {
	file    string
	dir     string
	line    int
	varName string
	nameLit string // the Name field's string literal
	// handleName is the var name a multi-entry door's site must carry
	// — DefineType's `<Name>Def`, whose literal registers two entries
	// (`<Name>Retraction`, `<Name>Membership`), one site each;
	// DefineData's `<Name>Data`, whose literal registers the datatype's
	// derived principles (`<Name>Induct`, `<Name>Recursion`, and
	// `<Name>Inj` / `<Name>Distinct` when the constructors give them).
	handleName string
	entry      *registry.ProofEntry
	decl       *ast.GenDecl
	lit        *ast.CompositeLit
	buildKV    *ast.KeyValueExpr
}

type entryCollection struct {
	fset   *token.FileSet
	asts   map[string]*ast.File // proof file → AST
	sites  []*entrySite
	census map[string]int
}

// authoringImportPath is the package a proof file dot-imports for the
// bare-name proof surface; its directory is authoringDir.
const authoringImportPath = "github.com/euc-ai/xugo/library/authoring"

func collectEntrySites(t *testing.T) *entryCollection {
	t.Helper()
	famByDir := claimFamilyByDir()
	col := &entryCollection{
		fset:   token.NewFileSet(),
		asts:   map[string]*ast.File{},
		census: map[string]int{},
	}
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(col.fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		col.asts[f] = af
	}
	// Entry sites.
	files := make([]string, 0, len(col.asts))
	for f := range col.asts {
		files = append(files, f)
	}
	sort.Strings(files)
	for _, f := range files {
		af := col.asts[f]
		dir := path.Dir(filepath.ToSlash(f))
		fam := famByDir[dir]
		addCalls := 0
		ast.Inspect(af, func(n ast.Node) bool {
			if call, ok := n.(*ast.CallExpr); ok {
				if sel, ok := call.Fun.(*ast.SelectorExpr); ok &&
					(sel.Sel.Name == "Add" || sel.Sel.Name == "Define" || sel.Sel.Name == "DefineStructure") && len(call.Args) == 1 {
					if _, ok := call.Args[0].(*ast.CompositeLit); ok {
						addCalls++
					}
				}
			}
			return true
		})
		varForm := 0
		// dataHandles: the file's DefineData vars → the datatype's
		// registered principle names by handle field (Induct /
		// Recursion / Inj / Distinct), read off the literal's
		// Principles, for the principle aliases declared after them.
		dataHandles := map[string]map[string]string{}
		for _, d := range af.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.VAR {
				continue
			}
			for _, spec := range gd.Specs {
				vs, ok := spec.(*ast.ValueSpec)
				if !ok || len(vs.Names) != 1 || len(vs.Values) != 1 {
					continue
				}
				val := vs.Values[0]
				// A datatype door's principle under a chapter name —
				// `var Induction = listInductThm{ListData.Induct}` (the
				// typed wrapper around the handle's field) — is the
				// derived entry the field holds, under the word the door
				// registered for it.
				if handle, field, isAlias := dataHandleSelector(val); isAlias {
					if x := handle; x != nil {
						if names, ok := dataHandles[x.Name]; ok {
							registered := names[field]
							// The alias IS the door's name for that principle:
							// `var NilNotCons = nilNotConsThm{ListData.Distinct}`
							// carries the word Principles registered, so a
							// session key, a brief and a cite spell one name.
							if registered != vs.Names[0].Name {
								t.Errorf("%s:%d: the principle alias %q is registered as %q (DataEntry.Principles) — "+
									"the Go variable and the registered (bare) name must be the same word",
									f, col.fset.Position(vs.Pos()).Line, vs.Names[0].Name, registered)
							}
							continue
						}
					}
				}
				// A typed theorem wrapper declares the same entry one
				// level deep — `var Sing = singThm{family.Add(…)}` —
				// and IS the member declaration. Unwrap to the call.
				if wl, ok := val.(*ast.CompositeLit); ok && len(wl.Elts) == 1 {
					if inner, ok := wl.Elts[0].(*ast.CallExpr); ok {
						val = inner
					}
					// An inductive door's hand-wrapped face — `var FiniteInduct =
					// finiteInductThm{finite.Induct}` — is not a declaration site:
					// the door's literal registers the three entries.
					if field, ok := wl.Elts[0].(*ast.SelectorExpr); ok {
						if _, isIdent := field.X.(*ast.Ident); isIdent && inductiveKindFields[field.Sel.Name] && fam != nil {
							continue
						}
					}
				}
				call, ok := val.(*ast.CallExpr)
				if !ok {
					continue
				}
				sel, ok := call.Fun.(*ast.SelectorExpr)
				if !ok || (sel.Sel.Name != "Add" && sel.Sel.Name != "Define" &&
					sel.Sel.Name != "DefineStructure" && sel.Sel.Name != "DefineSpec" &&
					sel.Sel.Name != "DefineType" && sel.Sel.Name != "DefineInductive" && sel.Sel.Name != "DefineData" &&
					sel.Sel.Name != "DefineQuotient") || len(call.Args) != 1 {
					continue
				}
				// A define-door site (`family.Define(registry.DefEntry{…})` /
				// `family.DefineStructure(registry.DefEntry{…})` /
				// `family.DefineSpec(registry.SpecEntry{…})`) registers an
				// entry like Add does; its literal carries
				// Name/Const(s)/Spec/Equations, no Build key — the
				// build-shaped rules skip it via the nil buildKV.
				cl, ok := call.Args[0].(*ast.CompositeLit)
				if !ok {
					continue
				}
				varForm++
				s := &entrySite{
					file: f, dir: dir, varName: vs.Names[0].Name,
					line: col.fset.Position(vs.Pos()).Line,
					decl: gd, lit: cl,
				}
				for _, elt := range cl.Elts {
					kv, ok := elt.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					key, ok := kv.Key.(*ast.Ident)
					if !ok {
						continue
					}
					switch key.Name {
					case "Name":
						if lit, ok := kv.Value.(*ast.BasicLit); ok && lit.Kind == token.STRING {
							if v, err := strconv.Unquote(lit.Value); err == nil {
								s.nameLit = v
							}
						}
					case "Build":
						s.buildKV = kv
					}
				}
				// A type-definition site registers two entries under
				// derived names; the var is the definition's handle.
				sites := []*entrySite{s}
				if sel.Sel.Name == "DefineType" && s.nameLit != "" {
					base := s.nameLit
					retraction, membership := *s, *s
					retraction.nameLit, retraction.handleName = base+"Retraction", base+"Def"
					membership.nameLit, membership.handleName = base+"Membership", base+"Def"
					sites = []*entrySite{&retraction, &membership}
					varForm++
				}
				// A quotient-definition site registers seven entries under
				// derived names; the var is the definition's handle.
				if sel.Sel.Name == "DefineQuotient" && s.nameLit != "" {
					base := s.nameLit
					sites = nil
					for _, suffix := range []string{"Surjectivity", "Induct", "Sound", "Exact", "Eq", "ForallOnImage", "ExistsOnImage"} {
						derived := *s
						derived.nameLit, derived.handleName = base+suffix, base+"Def"
						sites = append(sites, &derived)
					}
					varForm += len(sites) - 1
				}
				// An inductive-definition site registers three entries under
				// derived names; the var is the definition's handle, the
				// Name with its first letter lowered (`finite` for "Finite"),
				// whose exported faces are the hand-wrapped vars above.
				if sel.Sel.Name == "DefineInductive" && s.nameLit != "" {
					base := s.nameLit
					handle := strings.ToLower(base[:1]) + base[1:]
					sites = nil
					// The strengthened induction is registered only where a
					// rule has a premise to strengthen, so the site list is
					// read off the registry rather than assumed.
					for _, suffix := range []string{"Rules", "Induct", "Cases", "InductStrong"} {
						if fam == nil {
							break
						}
						if _, ok := registry.ByName(path.Base(fam.Name) + "." + base + suffix); !ok {
							continue
						}
						derived := *s
						derived.nameLit, derived.handleName = base+suffix, handle
						sites = append(sites, &derived)
					}
					varForm += len(sites) - 1
				}
				// A datatype site registers the derived principles under
				// derived names — Induct and Recursion always, Inj when a
				// constructor takes arguments, Distinct when there are two
				// or more constructors (registry.DefineData) — and the var
				// is the datatype's handle.
				if sel.Sel.Name == "DefineData" && s.nameLit != "" {
					base := s.nameLit
					names := dataPrincipleNames(cl)
					dataHandles[s.varName] = names
					kinds := []string{"Induct", "Recursion"}
					ctors, anyArgs := dataConstructorShape(cl)
					if anyArgs {
						kinds = append(kinds, "Inj")
					}
					if ctors >= 2 {
						kinds = append(kinds, "Distinct")
					}
					// A record's parts register under their own names, and
					// its extensionality under Principles.Extensionality.
					partNames := dataFieldNames(cl)
					if len(partNames) > 0 {
						kinds = append(kinds, "Ext")
					}
					for i, n := range partNames {
						names["Fields["+strconv.Itoa(i)+"]"] = n
					}
					sites = nil
					for _, kind := range kinds {
						derived := *s
						derived.nameLit, derived.handleName = names[kind], base+"Data"
						sites = append(sites, &derived)
					}
					for _, n := range partNames {
						derived := *s
						derived.nameLit, derived.handleName = n, base+"Data"
						sites = append(sites, &derived)
					}
					varForm += len(sites) - 1
				}
				for _, s := range sites {
					if fam != nil && s.nameLit != "" {
						if e, ok := registry.ByName(path.Base(fam.Name) + "." + s.nameLit); ok {
							s.entry = e
						}
					}
					col.sites = append(col.sites, s)
				}
			}
		}
		if addCalls > varForm {
			col.census["family.Add call outside the single-var form"] += addCalls - varForm
		}
	}
	return col
}

// ---------------------------------------------------------------------------
// E0 — entry var name == entry Name
// ---------------------------------------------------------------------------

func TestEntryLintNameMatchesVar(t *testing.T) {
	col := collectEntrySites(t)

	// Instrument guard 1: the harvest sees every registered entry —
	// a collector matching nothing proves nothing.
	if got, want := len(col.sites), len(registry.All()); got != want {
		t.Fatalf("instrument guard: harvested %d entry declarations but the registry holds %d entries "+
			"— the collector's shape assumptions no longer match the corpus", got, want)
	}
	// Instrument guard 2: the mismatch detector fires on a synthetic site.
	probe := &entrySite{varName: "LessEqRefl", nameLit: "LessEqReflex"}
	if probe.varName == probe.nameLit {
		t.Fatalf("instrument guard: probe mismatch not detectable")
	}

	mismatches := 0
	for _, s := range col.sites {
		if s.nameLit == "" {
			col.census["entry literal without a static Name string"]++
			continue
		}
		want := s.nameLit
		if s.handleName != "" {
			want = s.handleName
		}
		if s.varName != want {
			mismatches++
			t.Errorf("%s:%d: entry var %q registers Name %q — the Go variable and the registered "+
				"(bare) name must be the same word (a type definition's var is its handle, %q)",
				s.file, s.line, s.varName, s.nameLit, want)
		}
	}
	for class, n := range col.census {
		t.Logf("E0 census: %-58s %4d", class, n)
	}
	t.Logf("E0: %d entry declarations checked, %d mismatches", len(col.sites), mismatches)
}

// ---------------------------------------------------------------------------
// E1 — inline-Build ratchet
// ---------------------------------------------------------------------------

// splitBuildVars indexes, per FILE, the package-level single-spec vars
// whose initializer is a family constructor call — the migrated class.
func splitBuildVars(af *ast.File) map[string]bool {
	out := map[string]bool{}
	for _, d := range af.Decls {
		gd, ok := d.(*ast.GenDecl)
		if !ok || gd.Tok != token.VAR {
			continue
		}
		for _, spec := range gd.Specs {
			vs, ok := spec.(*ast.ValueSpec)
			if !ok || len(vs.Names) != 1 || len(vs.Values) != 1 {
				continue
			}
			call, ok := vs.Values[0].(*ast.CallExpr)
			if !ok {
				continue
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || !entryCtorNames[sel.Sel.Name] {
				continue
			}
			if _, ok := sel.X.(*ast.Ident); ok {
				out[vs.Names[0].Name] = true
			}
		}
	}
	return out
}

func TestEntryLintInlineBuild(t *testing.T) {
	col := collectEntrySites(t)

	// Instrument guard: the split shape must be detected.
	src := `package p
var X = family.Add(registry.ProofEntry{Name: "X", Build: Build_X})
var Build_X = family.Theorem("stmt", nil)
`
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, "probe.go", src, 0)
	if err != nil {
		t.Fatalf("instrument guard: probe parse: %v", err)
	}
	if !splitBuildVars(af)["Build_X"] {
		t.Fatalf("instrument guard: splitBuildVars missed the probe's constructor var")
	}

	checked := 0
	for _, s := range col.sites {
		if s.buildKV == nil {
			continue
		}
		id, ok := s.buildKV.Value.(*ast.Ident)
		if !ok {
			continue // inline constructor or registry.Bare(…) — the target shape
		}
		checked++
		if splitBuildVars(col.asts[s.file])[id.Name] {
			pos := col.fset.Position(s.buildKV.Pos())
			t.Errorf("%s:%d: entry %s spells Build as a reference to the separate constructor var %s — "+
				"inline the constructor call into the entry literal (metadata fields first, Build last); "+
				"the split two-var ceremony is retired", s.file, pos.Line, s.varName, id.Name)
		}
	}
	t.Logf("E1: %d entry declarations scanned, %d Build-by-identifier sites examined", len(col.sites), checked)
}

// ---------------------------------------------------------------------------
// E2 — a family's cards.go holds cards only
// ---------------------------------------------------------------------------

func TestLintCardsFileHoldsCards(t *testing.T) {
	col := collectEntrySites(t)
	// The entries of each cards.go, by the var that declares them: each
	// is judged here, and the declaration walk below reads the rest.
	entryVars := map[string]map[string]bool{}
	cards := 0
	for _, s := range col.sites {
		if filepath.Base(s.file) != "cards.go" {
			continue
		}
		if entryVars[s.file] == nil {
			entryVars[s.file] = map[string]bool{}
		}
		entryVars[s.file][s.varName] = true
		if s.entry == nil || !s.entry.IsCard() {
			what := "an entry the registry does not hold"
			switch {
			case s.entry != nil && s.entry.DepsRecorded():
				what = "proved"
			case s.entry != nil:
				what = "not a card"
			}
			t.Errorf("%s:%d: %s is %s and stands in its family's cards.go, which holds cards only — "+
				"a filled card moves, its comment with it, to the proof file of its subject (a new file "+
				"named for the subject when no file's subject fits), a definition to definitions.go; "+
				"a cards.go left with no entry is deleted", s.file, s.line, s.nameLit, what)
			continue
		}
		cards++
	}
	files := 0
	for f, af := range col.asts {
		if filepath.Base(f) != "cards.go" {
			continue
		}
		files++
		for _, imp := range af.Imports {
			if imp.Name != nil && imp.Name.Name == "_" {
				t.Errorf("%s:%d: cards.go carries the blank import %s — a family's links stand in "+
					"definitions.go or family.go, so its cards.go goes with its last card and takes no "+
					"link with it", f, col.fset.Position(imp.Pos()).Line, imp.Path.Value)
			}
		}
		for _, d := range af.Decls {
			gd, ok := d.(*ast.GenDecl)
			if ok && gd.Tok == token.IMPORT {
				continue
			}
			isEntry := ok && gd.Tok == token.VAR && len(gd.Specs) > 0
			if isEntry {
				for _, spec := range gd.Specs {
					vs, ok := spec.(*ast.ValueSpec)
					if !ok || len(vs.Names) != 1 || !entryVars[f][vs.Names[0].Name] {
						isEntry = false
					}
				}
			}
			if !isEntry {
				t.Errorf("%s:%d: cards.go holds a declaration that is no card's entry — it belongs in "+
					"another file of the family", f, col.fset.Position(d.Pos()).Line)
			}
		}
	}
	// Instrument guard: the harvest reaches the cards files — a lint
	// that reads none of them refuses nothing.
	if cards == 0 || files == 0 {
		t.Fatalf("instrument guard: %d card(s) harvested from %d cards.go — the collector no longer reads them",
			cards, files)
	}
	t.Logf("E2: %d card(s) in %d cards.go files", cards, files)
}

// ---------------------------------------------------------------------------
// Datatype door sites — the shapes collectEntrySites reads a DefineData
// literal and its principle aliases by
// ---------------------------------------------------------------------------

// dataHandleSelector reads a principle-alias declaration's value —
// `wrapper{Handle.Field}` or a bare `Handle.Field` — as the selector it
// names, or nil for any other shape.
func dataHandleSelector(val ast.Expr) (*ast.Ident, string, bool) {
	if wl, ok := val.(*ast.CompositeLit); ok && len(wl.Elts) == 1 {
		val = wl.Elts[0]
	}
	// A record's part: `Handle.Fields[i]`, keyed "Fields[i]".
	if ix, ok := val.(*ast.IndexExpr); ok {
		sel, ok := ix.X.(*ast.SelectorExpr)
		lit, isLit := ix.Index.(*ast.BasicLit)
		if !ok || !isLit || sel.Sel.Name != "Fields" {
			return nil, "", false
		}
		handle, ok := sel.X.(*ast.Ident)
		if !ok {
			return nil, "", false
		}
		return handle, "Fields[" + lit.Value + "]", true
	}
	sel, ok := val.(*ast.SelectorExpr)
	if !ok {
		return nil, "", false
	}
	switch sel.Sel.Name {
	case "Induct", "Recursion", "Inj", "Distinct", "Ext",
		"Surjectivity", "Sound", "Exact", "Eq", "ForallOnImage", "ExistsOnImage":
		handle, ok := sel.X.(*ast.Ident)
		if !ok {
			return nil, "", false
		}
		return handle, sel.Sel.Name, true
	}
	return nil, "", false
}

// dataFieldNames reads a DataEntry literal's Fields — the registered
// name of each part, in order — or nil when it declares none.
func dataFieldNames(cl *ast.CompositeLit) []string {
	var out []string
	for _, elt := range cl.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok {
			continue
		}
		if key, ok := kv.Key.(*ast.Ident); !ok || key.Name != "Fields" {
			continue
		}
		list, ok := kv.Value.(*ast.CompositeLit)
		if !ok {
			continue
		}
		for _, fe := range list.Elts {
			fl, ok := fe.(*ast.CompositeLit)
			if !ok {
				continue
			}
			for _, pe := range fl.Elts {
				pkv, ok := pe.(*ast.KeyValueExpr)
				if !ok {
					continue
				}
				if pkey, ok := pkv.Key.(*ast.Ident); !ok || pkey.Name != "Name" {
					continue
				}
				if lit, ok := pkv.Value.(*ast.BasicLit); ok && lit.Kind == token.STRING {
					if v, err := strconv.Unquote(lit.Value); err == nil {
						out = append(out, v)
					}
				}
			}
		}
	}
	return out
}

// dataPrincipleNames reads a DataEntry literal's Principles — the
// registered name per derived kind, keyed by the handle's field name
// (Induct / Recursion / Inj / Distinct) so an alias's selector reads
// its own name off it. A kind the literal does not name maps to "".
func dataPrincipleNames(cl *ast.CompositeLit) map[string]string {
	out := map[string]string{}
	fields := map[string]string{"Induction": "Induct", "Recursion": "Recursion", "Injective": "Inj", "Distinct": "Distinct", "Extensionality": "Ext"}
	for _, elt := range cl.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok {
			continue
		}
		if key, ok := kv.Key.(*ast.Ident); !ok || key.Name != "Principles" {
			continue
		}
		inner, ok := kv.Value.(*ast.CompositeLit)
		if !ok {
			continue
		}
		for _, pe := range inner.Elts {
			pkv, ok := pe.(*ast.KeyValueExpr)
			if !ok {
				continue
			}
			pkey, ok := pkv.Key.(*ast.Ident)
			if !ok {
				continue
			}
			if lit, ok := pkv.Value.(*ast.BasicLit); ok && lit.Kind == token.STRING {
				if v, err := strconv.Unquote(lit.Value); err == nil {
					out[fields[pkey.Name]] = v
				}
			}
		}
	}
	return out
}

// dataConstructorShape reads a DataEntry literal's Constructors: how
// many there are, and whether any takes arguments.
func dataConstructorShape(cl *ast.CompositeLit) (ctors int, anyArgs bool) {
	for _, elt := range cl.Elts {
		kv, ok := elt.(*ast.KeyValueExpr)
		if !ok {
			continue
		}
		if key, ok := kv.Key.(*ast.Ident); !ok || key.Name != "Constructors" {
			continue
		}
		list, ok := kv.Value.(*ast.CompositeLit)
		if !ok {
			continue
		}
		for _, c := range list.Elts {
			ctors++
			spec, ok := c.(*ast.CompositeLit)
			if !ok {
				continue
			}
			for _, f := range spec.Elts {
				if fkv, ok := f.(*ast.KeyValueExpr); ok {
					if fkey, ok := fkv.Key.(*ast.Ident); ok && fkey.Name == "Args" {
						anyArgs = true
					}
				}
			}
		}
	}
	return ctors, anyArgs
}
