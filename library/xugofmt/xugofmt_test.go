package xugofmt

import (
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
)

// The narration verbs are read off the proof language itself: an
// exported function or method of prover/proof with a parameter named
// label or labels, a string or a ...string, and a name library/authoring
// gives one (`Case = proof.MakeCase`). A verb added to the language with
// a label is a verb this table misses until it is listed.
func TestNarrationVerbsAreTheLabelTakers(t *testing.T) {
	holdTable(t, "NarrationVerbs", NarrationVerbs, languageVerbs(t, takesALabel),
		"each takes a label and is not laid out one argument to a line",
		"which take no label")
}

// The list verbs are read off the proof language the same way: an
// exported function or method of prover/proof whose last parameter is a
// list of premises, rules or facts (`premises ...`, `rules ...`,
// `facts ...`) and that takes no label, and a name library/authoring
// gives one.
func TestListVerbsAreTheListTakers(t *testing.T) {
	lists := func(fn *ast.FuncDecl) bool { return takesAList(fn) && !takesALabel(fn) }
	holdTable(t, "listVerbs", listVerbs, languageVerbs(t, lists),
		"each ends in a list of premises or rules and is not fitted to a line",
		"which take no list of premises or rules")
}

// languageVerbs are the names of the exported functions and methods of
// prover/proof that verb holds of, and the names library/authoring
// gives them.
func languageVerbs(t *testing.T, verb func(*ast.FuncDecl) bool) map[string]bool {
	derived := map[string]bool{}
	fset := token.NewFileSet()
	for _, file := range parseDir(t, fset, "../../prover/proof") {
		for _, decl := range file.Decls {
			if fn, isFunc := decl.(*ast.FuncDecl); isFunc && fn.Name.IsExported() && verb(fn) {
				derived[fn.Name.Name] = true
			}
		}
	}
	for _, file := range parseDir(t, fset, "../authoring") {
		ast.Inspect(file, func(n ast.Node) bool {
			spec, isValue := n.(*ast.ValueSpec)
			if !isValue {
				return true
			}
			for i, value := range spec.Values {
				if sel, isSel := value.(*ast.SelectorExpr); isSel && derived[sel.Sel.Name] && i < len(spec.Names) {
					derived[spec.Names[i].Name] = true
				}
			}
			return true
		})
	}
	return derived
}

// holdTable reports the names derived has and table lacks, and the
// names table lists and derived has not.
func holdTable(t *testing.T, name string, table, derived map[string]bool, lacksWhy, extraWhy string) {
	t.Helper()
	var missing, extra []string
	for verb := range derived {
		if !table[verb] {
			missing = append(missing, verb)
		}
	}
	for verb := range table {
		if !derived[verb] {
			extra = append(extra, verb)
		}
	}
	slices.Sort(missing)
	slices.Sort(extra)
	if len(missing) > 0 {
		t.Errorf("%s lacks %v: %s", name, missing, lacksWhy)
	}
	if len(extra) > 0 {
		t.Errorf("%s lists %v, %s", name, extra, extraWhy)
	}
}

// takesALabel reports whether fn has a parameter named label or labels,
// a string or a ...string.
func takesALabel(fn *ast.FuncDecl) bool {
	for _, field := range fn.Type.Params.List {
		for _, name := range field.Names {
			if (name.Name == "label" || name.Name == "labels") && isStringParam(field.Type) {
				return true
			}
		}
	}
	return false
}

// takesAList reports whether fn's last parameter is variadic and named
// premises, rules or facts.
func takesAList(fn *ast.FuncDecl) bool {
	params := fn.Type.Params.List
	if len(params) == 0 {
		return false
	}
	last := params[len(params)-1]
	if _, isVariadic := last.Type.(*ast.Ellipsis); !isVariadic || len(last.Names) == 0 {
		return false
	}
	name := last.Names[len(last.Names)-1].Name
	return name == "premises" || name == "rules" || name == "facts"
}

func isStringParam(expr ast.Expr) bool {
	if ellipsis, isEllipsis := expr.(*ast.Ellipsis); isEllipsis {
		expr = ellipsis.Elt
	}
	ident, isIdent := expr.(*ast.Ident)
	return isIdent && ident.Name == "string"
}

func parseDir(t *testing.T, fset *token.FileSet, dir string) []*ast.File {
	t.Helper()
	entries, err := os.ReadDir(dir)
	if err != nil {
		t.Fatalf("read %s: %v", dir, err)
	}
	var files []*ast.File
	for _, entry := range entries {
		name := entry.Name()
		if !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			continue
		}
		file, err := parser.ParseFile(fset, filepath.Join(dir, name), nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", name, err)
		}
		files = append(files, file)
	}
	return files
}

func TestSourceLayout(t *testing.T) {
	cases := []struct{ name, in, want string }{{
		name: "each argument on its own line, the first one included",
		in: `	c.Show("i < j ≤ 1 is the pair (0, 1)", ByArith(bound, zero))
`,
		want: `	c.Show(
		"i < j ≤ 1 is the pair (0, 1)",
		ByArith(bound, zero))
`,
	}, {
		name: "a laid-out call is its own fixed point",
		in: `	c.Show(
		"i < j ≤ 1 is the pair (0, 1)",
		ByArith(bound, zero))
`,
		want: `	c.Show(
		"i < j ≤ 1 is the pair (0, 1)",
		ByArith(bound, zero))
`,
	}, {
		name: "a break already there stays, and a trailing comma keeps its closing line",
		in: `	x := a.Have("label", "claim",
		By(h),
	)
`,
		want: `	x := a.Have(
		"label",
		"claim",
		By(h),
	)
`,
	}, {
		name: "a comment in a gap leaves that gap alone",
		in: `	a.Show("label", // the one step
		By(h))
`,
		want: `	a.Show(
		"label", // the one step
		By(h))
`,
	}, {
		name: "the arguments of a call that is no narration verb stay; a narration verb inside one is laid out",
		in: `	a.Do(Simp(Fwd(Def)), By(a.Have("label", "claim", By(h))))
`,
		want: `	a.Do(Simp(Fwd(Def)), By(a.Have(
		"label",
		"claim",
		By(h))))
`,
	}, {
		name: "a one-argument call stays",
		in: `	a.Show(By(h))
`,
		want: `	a.Show(By(h))
`,
	}, {
		name: "a generic verb is laid out by its name",
		in: `	x, fact := a.ObtainAs[Nat]("label", "∃x:num. P(x)", By(h))
`,
		want: `	x, fact := a.ObtainAs[Nat](
		"label",
		"∃x:num. P(x)",
		By(h))
`,
	}, {
		name: "a function literal argument moves whole, its body indented under it",
		in: `	a.When("label", func(b *Argument, zero Fact) {
		b.Show("done", By(zero))
	})
`,
		want: `	a.When(
		"label",
		func(b *Argument, zero Fact) {
			b.Show(
				"done",
				By(zero))
		})
`,
	}, {
		name: "a list call that fits is joined onto one line",
		in: `	x := By(Normalized, scalarField,
		primeModule, h)
`,
		want: `	x := By(Normalized, scalarField, primeModule, h)
`,
	}, {
		name: "a list call that ends on its own line is joined without its trailing comma",
		in: `	x := Simp(
		Fwd(regularDef),
		Fwd(fieldRingDef),
	)
`,
		want: `	x := Simp(Fwd(regularDef), Fwd(fieldRingDef))
`,
	}, {
		name: "a list call that does not fit takes one argument to a line",
		in: `	x := By(Normalized, scalarFieldDef, scalarRingDef, regularModule, primeData,
		field.SubfieldSubring.Read(k).At(C))
`,
		want: `	x := By(
		Normalized,
		scalarFieldDef,
		scalarRingDef,
		regularModule,
		primeData,
		field.SubfieldSubring.Read(k).At(C))
`,
	}, {
		name: "a list call inside a laid-out one is measured on its own line",
		in: `	x := ByArith(firstPremiseOfTheStep, secondPremiseOfTheStep, Simp(Fwd(firstDefinition),
		Fwd(secondDefinition)))
`,
		want: `	x := ByArith(
		firstPremiseOfTheStep,
		secondPremiseOfTheStep,
		Simp(Fwd(firstDefinition), Fwd(secondDefinition)))
`,
	}, {
		name: "an elementarity call that does not fit takes one fact to a line, its At left on the last",
		in: `	a.Show("the property transfers", ByElementarity(real_polynomial_geometry.BrouwerSource, closedF, real_closed_instance.RealClosed, polynomials, keepsCube).At(P))
`,
		want: `	a.Show(
		"the property transfers",
		ByElementarity(
			real_polynomial_geometry.BrouwerSource,
			closedF,
			real_closed_instance.RealClosed,
			polynomials,
			keepsCube).At(P))
`,
	}, {
		name: "a list call holding a comment does not join, and keeps the comment",
		in: `	x := By(h, // the hypothesis
		k)
`,
		want: `	x := By(
		h, // the hypothesis
		k)
`,
	}}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got, err := Source([]byte("package p\n\nfunc f() {\n" + c.in + "}\n"))
			if err != nil {
				t.Fatal(err)
			}
			want := "package p\n\nfunc f() {\n" + c.want + "}\n"
			if string(got) != want {
				t.Errorf("got\n%s\nwant\n%s", got, want)
			}
		})
	}
}

// Over every chapter file: Source changes no token but a string's
// layout, a string read with the strings joined to it by `+` and on one
// line (dsl.OneLine); it keeps the comments in their order, one that
// ended a line of code moving to the line above; and it is its own
// fixed point.
func TestSourceKeepsTheTokens(t *testing.T) {
	err := filepath.WalkDir("../proofs", func(path string, d fs.DirEntry, err error) error {
		if err != nil || d.IsDir() || !strings.HasSuffix(path, ".go") {
			return err
		}
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		once, err := Source(src)
		if err != nil {
			t.Errorf("%s: %v", path, err)
			return nil
		}
		code, comments := tokens(src)
		formattedCode, formattedComments := tokens(once)
		if !slices.Equal(code, formattedCode) {
			t.Errorf("%s: Source changed a token", path)
		}
		if !slices.Equal(comments, formattedComments) {
			t.Errorf("%s: Source changed a comment", path)
		}
		twice, err := Source(once)
		if err != nil {
			t.Errorf("%s: the formatted file does not parse: %v", path, err)
			return nil
		}
		if string(twice) != string(once) {
			t.Errorf("%s: Source is not its own fixed point", path)
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
}

// tokens is src's token stream and its comments, each in order, the
// semicolons a newline inserts and the commas before a closing bracket
// left out; a string and the strings `+` joins to it are one token, its
// text on one line.
func tokens(src []byte) (out, comments []string) {
	fset := token.NewFileSet()
	file := fset.AddFile("", fset.Base(), len(src))
	var s scanner.Scanner
	s.Init(file, src, nil, scanner.ScanComments)
	var chain *strings.Builder // the strings joined so far, while the last tokens are a chain of them
	joined := false            // the token before is a `+` after a chain
	flush := func() {
		if chain != nil {
			out = append(out, "STRING "+dsl.OneLine(chain.String()))
			chain = nil
		}
		if joined {
			out = append(out, token.ADD.String()+" ")
			joined = false
		}
	}
	for {
		_, tok, lit := s.Scan()
		if tok == token.EOF {
			flush()
			return out, comments
		}
		if tok == token.SEMICOLON && lit == "\n" {
			continue
		}
		if tok == token.COMMENT {
			comments = append(comments, strings.TrimSpace(lit))
			continue
		}
		switch {
		case tok == token.STRING && (chain == nil || joined):
			value, err := strconv.Unquote(lit)
			if err != nil {
				value = lit
			}
			if chain == nil {
				chain = &strings.Builder{}
			}
			chain.WriteString(value)
			joined = false
			continue
		case tok == token.ADD && chain != nil && !joined:
			joined = true
			continue
		}
		flush()
		if (tok == token.RPAREN || tok == token.RBRACK || tok == token.RBRACE) && len(out) > 0 && out[len(out)-1] == token.COMMA.String()+" " {
			out = out[:len(out)-1]
		}
		out = append(out, tok.String()+" "+strings.TrimSpace(lit))
	}
}

// A `//line` directive gives the lines after it another file's line
// numbers, and with no column leaves their columns unknown: those are
// the positions a compiler reports, and a layout is of the source's own
// lines. Each case is formatted bare and under a directive of each
// form, and has the one layout. The directive names line 1, so the
// lines after it are numbered as the lines above it are.
func TestSourceLaysOutUnderALineDirective(t *testing.T) {
	directives := []struct{ name, text string }{
		{"no directive", ""},
		{"a directive of a line", "//line other.go:1\n"},
		{"a directive of a line and a column", "//line other.go:1:1\n"},
		{"a directive in a general comment", "/*line other.go:1*/\n"},
	}
	pastTheWidth := "// " + strings.Repeat("a", LineWidth+1) + "\n"
	cases := []struct{ name, in, want string }{{
		name: "a comment after the directive, in a file with a line nothing breaks",
		in:   "// a comment\n\n" + pastTheWidth,
		want: "// a comment\n\n" + pastTheWidth,
	}, {
		name: "the comment ending the line past the width moves, and no other",
		in: `func f() {
	scaled := SmulIn.Read(module).At(cR, fx) // c • F(x): the module M is closed under scaling by the ring's elements
	y := g(b)
	z := g(c)
	x := g(a) // a short comment
}
`,
		want: `func f() {
	// c • F(x): the module M is closed under scaling by the ring's elements
	scaled := SmulIn.Read(module).At(cR, fx)
	y := g(b)
	z := g(c)
	x := g(a) // a short comment
}
`,
	}, {
		name: "the line past the width is broken at its list, and no other",
		in: `func f() {
	x := polynomial.PolynomialOverMap.At(firstArgument, a.TermAs[A]("field_of_fractions.zero"), a.TermAs[B]("target_ring.zero"), secondArgument)
	y := g(b)
	z := g(c)
	w := g(d)
}
`,
		want: `func f() {
	x := polynomial.PolynomialOverMap.At(
		firstArgument,
		a.TermAs[A]("field_of_fractions.zero"),
		a.TermAs[B]("target_ring.zero"),
		secondArgument)
	y := g(b)
	z := g(c)
	w := g(d)
}
`,
	}, {
		name: "a list call past the width is laid out and one that fits is joined",
		in: `func f() {
	By(Normalized, scalarFieldDefinition, field.SubfieldSubring.Read(k).At(C), module.ModuleRestrictScalars.At(originalRing, V, C))
	By(
		Normalized,
		h)
}
`,
		want: `func f() {
	By(
		Normalized,
		scalarFieldDefinition,
		field.SubfieldSubring.Read(k).At(C),
		module.ModuleRestrictScalars.At(originalRing, V, C))
	By(Normalized, h)
}
`,
	}, {
		name: "a text past the width is a chain of literals, and a chain that fits is one",
		in: `func f() {
	a.Show(
		"so the composite of the two maps carries every point of the first space into the third one, as the goal asks",
		By(h))
	a.Show(
		"so the composite "+
			"is continuous",
		By(h))
}
`,
		want: `func f() {
	a.Show(
		"so the composite of the two maps carries every point "+
			"of the first space into the third one, as the goal asks",
		By(h))
	a.Show(
		"so the composite is continuous",
		By(h))
}
`,
	}}
	for _, c := range cases {
		for _, directive := range directives {
			t.Run(c.name+", under "+directive.name, func(t *testing.T) {
				got, err := Source([]byte("package p\n\n" + directive.text + c.in))
				if err != nil {
					t.Fatal(err)
				}
				want := "package p\n\n" + directive.text + c.want
				if string(got) != want {
					t.Errorf("got\n%s\nwant\n%s", got, want)
				}
				again, err := Source(got)
				if err != nil || string(again) != string(got) {
					t.Errorf("the layout of its layout is\n%s", again)
				}
			})
		}
	}
}

// Every position the package reads is read by inSource. A call of
// Position or of Line, on a file set or on one of its files, reads the
// position a `//line` directive gives, and the package makes none.
func TestPositionsAreReadInTheSource(t *testing.T) {
	fset := token.NewFileSet()
	for _, file := range parseDir(t, fset, ".") {
		ast.Inspect(file, func(n ast.Node) bool {
			call, isCall := n.(*ast.CallExpr)
			if !isCall {
				return true
			}
			method, isMethod := call.Fun.(*ast.SelectorExpr)
			if isMethod && (method.Sel.Name == "Position" || method.Sel.Name == "Line") {
				t.Errorf("%s: a call of %s reads the position a //line directive gives; inSource reads the source's",
					fset.Position(call.Pos()), method.Sel.Name)
			}
			return true
		})
	}
}
