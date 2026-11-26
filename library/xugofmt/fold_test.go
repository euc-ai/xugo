package xugofmt

import (
	"go/ast"
	"go/token"
	"reflect"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
)

// The math arguments are read off the proof language: each parameter of
// an exported function or method of prover/proof or library/registry
// whose name mathParameters lists and that takes a string or any, by
// its position, and the names library/authoring gives such a function.
// A function added with such a parameter is one this table misses until
// it is listed.
func TestMathArgumentsAreTheTextReaders(t *testing.T) {
	derived := map[string]map[int]bool{}
	fset := token.NewFileSet()
	files := append(parseDir(t, fset, "../../prover/proof"), parseDir(t, fset, "../registry")...)
	for _, file := range files {
		for _, decl := range file.Decls {
			fn, isFunc := decl.(*ast.FuncDecl)
			if !isFunc || !fn.Name.IsExported() {
				continue
			}
			i := 0
			for _, field := range fn.Type.Params.List {
				if len(field.Names) == 0 {
					i++
					continue
				}
				for _, name := range field.Names {
					if mathParameters[name.Name] && readsAText(field.Type) {
						if derived[fn.Name.Name] == nil {
							derived[fn.Name.Name] = map[int]bool{}
						}
						derived[fn.Name.Name][i] = true
					}
					i++
				}
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
				if sel, isSel := value.(*ast.SelectorExpr); isSel && derived[sel.Sel.Name] != nil && i < len(spec.Names) {
					derived[spec.Names[i].Name] = derived[sel.Sel.Name]
				}
			}
			return true
		})
	}
	var wrong []string
	for name, at := range derived {
		var want []int
		for i := range at {
			want = append(want, i)
		}
		sort.Ints(want)
		if !reflect.DeepEqual(mathArguments[name], want) {
			wrong = append(wrong, name)
		}
	}
	for name := range mathArguments {
		if derived[name] == nil {
			wrong = append(wrong, name)
		}
	}
	sort.Strings(wrong)
	for _, name := range wrong {
		t.Errorf("mathArguments[%q] = %v; the language reads a text at %v", name, mathArguments[name], derived[name])
	}
}

// readsAText reports whether a parameter of type expr takes a string
// literal: a string or any.
func readsAText(expr ast.Expr) bool {
	ident, isIdent := expr.(*ast.Ident)
	return isIdent && (ident.Name == "string" || ident.Name == "any")
}

// Each math field is a field of a Statement or of a definition entry
// that holds a string or a list of them: the parts of a statement, and
// a definition's type, equations and measure.
func TestMathFieldsAreTextFields(t *testing.T) {
	holders := []reflect.Type{reflect.TypeOf(dsl.Statement{}), reflect.TypeOf(registry.DefEntry{})}
	for name := range mathFields {
		found := false
		for _, holder := range holders {
			if field, ok := holder.FieldByName(name); ok {
				kind := field.Type.Kind()
				found = found || kind == reflect.String || kind == reflect.Slice && field.Type.Elem().Kind() == reflect.String
			}
		}
		if !found {
			t.Errorf("mathFields lists %s, which no Statement or DefEntry field of strings is", name)
		}
	}
	entry := reflect.TypeOf(dsl.Abbreviation{})
	if field, ok := entry.FieldByName("Text"); !ok || field.Type.Kind() != reflect.String {
		t.Errorf("an abbreviation entry's Text is no string field")
	}
}

func TestFoldTextLayout(t *testing.T) {
	cases := []struct {
		name        string
		text        string
		first, rest int
		want        []string
	}{{
		name:  "a text that fits is one line, its blanks single and none inside brackets",
		text:  "f( x,  y )   ∧\n\tg(x)",
		first: 40, rest: 40,
		want: []string{"f(x, y) ∧ g(x)"},
	}, {
		name:  "a chain breaks at its loosest operator, the operator ending each line",
		text:  "p(x) ∧ q(x) ⇒ r(x) ∧ s(x)",
		first: 16, rest: 16,
		want: []string{"p(x) ∧ q(x) ⇒ ", "r(x) ∧ s(x)"},
	}, {
		name:  "each operand of the broken layer takes a line",
		text:  "a(1) ∧ b(2) ∧ c(3) ∧ d(4)",
		first: 20, rest: 20,
		want: []string{"a(1) ∧ ", "b(2) ∧ ", "c(3) ∧ ", "d(4)"},
	}, {
		name:  "the binders end a line and the scope stands four spaces in",
		text:  "∀x:A. ∀y:A. p(x) ∧ q(y)",
		first: 14, rest: 20,
		want: []string{"∀x:A. ∀y:A. ", "    p(x) ∧ q(y)"},
	}, {
		name:  "a group breaks at its commas, later lines four spaces in",
		text:  "f(alpha, beta, gamma)",
		first: 12, rest: 12,
		want: []string{"f(alpha, ", "    beta, ", "    gamma)"},
	}, {
		name:  "content that does not fit after the opener starts the next line",
		text:  "function_name(argument_one)",
		first: 16, rest: 40,
		want: []string{"function_name( ", "    argument_one)"},
	}, {
		name:  "a binder inside parentheses alone takes the one step in",
		text:  "a ∧ (∀x:A. p(x) ⇒ q(x))",
		first: 14, rest: 12,
		want: []string{"a ∧ ", "(∀x:A. ", "    p(x) ⇒ ", "    q(x))"},
	}, {
		name:  "a group's fields stay on its last line",
		text:  "f(alpha, beta).carrier = S",
		first: 12, rest: 22,
		want: []string{"f(alpha, ", "    beta).carrier = ", "S"},
	}, {
		name:  "a binder inside a member of a group reaches only to the member's end",
		text:  "f(λc:A. c, second_argument, λd:A. d)",
		first: 20, rest: 20,
		want: []string{"f(λc:A. c, ", "    second_argument, ", "    λd:A. d)"},
	}, {
		name:  "binders the text ends in have no scope and stand one to a line",
		text:  "∀x:A. ∀y:B. ∀z:C.",
		first: 12, rest: 12,
		want: []string{"∀x:A. ", "∀y:B. ", "∀z:C."},
	}, {
		name:  "a group that is a member of a group breaks at its own commas, four spaces in",
		text:  "f(a, (alpha_one, beta_two), c)",
		first: 20, rest: 20,
		want: []string{"f(a, ", "    (alpha_one, ", "        beta_two), ", "    c)"},
	}, {
		name:  "an abbreviation is one token, its blanks its own",
		text:  "«a b» ∧ «c d»",
		first: 6, rest: 6,
		want: []string{"«a b» ∧ ", "«c d»"},
	}}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got, laid := foldText(c.text, c.first, c.rest, -3)
			if !laid || !reflect.DeepEqual(got, c.want) {
				t.Fatalf("got %q, want %q", got, c.want)
			}
			again, _ := foldText(strings.Join(got, ""), c.first, c.rest, -3)
			if !reflect.DeepEqual(again, got) {
				t.Errorf("the layout of its layout is %q", again)
			}
		})
	}
}

func TestSourceLaysOutMathTexts(t *testing.T) {
	cases := []struct{ name, in, want string }{{
		name: "a conclusion past the width is a chain of literals, one line each",
		in: `	s := Statement{
		Binders:    "∀x:A.",
		Conclusion: "first_predicate(x, alpha) ∧ second_predicate(x, beta) ∧ third_predicate(x, gamma) ∧ fourth_predicate(x, delta)",
	}
`,
		want: `	s := Statement{
		Binders: "∀x:A.",
		Conclusion: "first_predicate(x, alpha) ∧ " +
			"second_predicate(x, beta) ∧ " +
			"third_predicate(x, gamma) ∧ " +
			"fourth_predicate(x, delta)",
	}
`,
	}, {
		name: "a chain that fits is joined into one literal",
		in: `	s := Statement{
		Conclusion: "p(x) ∧ " +
			"q(x)",
	}
`,
		want: `	s := Statement{
		Conclusion: "p(x) ∧ q(x)",
	}
`,
	}, {
		name: "a statement on one line past the width takes a field to a line",
		in: `	a.Have(
		"label",
		Statement{Binders: "∀x:A.", Hypotheses: []string{"x ∈ S"}, Conclusion: "a_long_predicate_name(x, S) ∧ p(x)"},
		By(h))
`,
		want: `	a.Have(
		"label",
		Statement{
			Binders:    "∀x:A.",
			Hypotheses: []string{"x ∈ S"},
			Conclusion: "a_long_predicate_name(x, S) ∧ p(x)",
		},
		By(h))
`,
	}, {
		name: "a claim on its own line is laid out under its label",
		in: `	a.Have(
		"label",
		"∀x:A. x ∈ S ⇒ first_predicate(x, alpha) ∧ second_predicate(x, beta) ∧ third_predicate(x, gamma) ∧ fourth_predicate(x, delta)",
		By(h))
`,
		want: `	a.Have(
		"label",
		"∀x:A. "+
			"    x ∈ S ⇒ "+
			"    first_predicate(x, alpha) ∧ "+
			"    second_predicate(x, beta) ∧ "+
			"    third_predicate(x, gamma) ∧ "+
			"    fourth_predicate(x, delta)",
		By(h))
`,
	}, {
		name: "a text on a line of code that a line of its own would hold stays one literal",
		in: `	x := ByArith(someFactNameHere, anotherFactName, a.TermAs[Nat]("first_function(x, y) + second_function(y, z)"))
`,
		want: `	x := ByArith(
		someFactNameHere,
		anotherFactName,
		a.TermAs[Nat]("first_function(x, y) + second_function(y, z)"))
`,
	}, {
		name: "an abbreviation entry lays its Text out after its Name",
		in: `	t := Abbrev{
		{Name: "entry", Text: "λf:M. λg:M. COND(f = g, first_value(f, g, alpha), second_value(g, f, beta))"},
	}
`,
		want: `	t := Abbrev{
		{Name: "entry", Text: "λf:M. λg:M. " +
			"    COND(f = g, first_value(f, g, alpha), second_value(g, f, beta))"},
	}
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
