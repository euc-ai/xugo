package dsl

import (
	"maps"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Dimensions in a head's ⟨…⟩ (dimension.go), pinned on a toy vector
// chapter at the reals: `vec` and `matrix` behind an implicit zero,
// `dot` behind two operations and with a notation, and `vec_dist` under
// the word `dist` it shares with `real_dist`.

func dimensionTestScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{
		"vec":       core.MakeConstMeta("vec", typ("A → num → (num → A) → bool")),
		"matrix":    core.MakeConstMeta("matrix", typ("A → num → num → (num → num → A) → bool")),
		"dot":       core.MakeConstMeta("dot", typ("(A → A → A) → (A → A → A) → num → (num → A) → (num → A) → A")),
		"vec_dist":  core.MakeConstMeta("vec_dist", typ("num → (num → real) → (num → real) → real")),
		"real_dist": core.MakeConstMeta("real_dist", typ("real → real → real")),
		"real_add":  core.MakeConstMeta("real_add", typ("real → real → real")),
		"real_mul":  core.MakeConstMeta("real_mul", typ("real → real → real")),
		"rzero":     core.MakeConstMeta("rzero", typ("real")),
	}
	scope := &ParseScope{
		ConstMetas: metas,
		Vars: map[string]core.HolType{
			"u": typ("num → real"), "v": typ("num → real"), "M": typ("num → num → real"),
			"n": NumType, "m": NumType, "x": RealType, "y": RealType,
		},
		Syntax: testSyntax{
			"vec":       {Implicit: []string{"zero"}, Dims: 1},
			"matrix":    {Implicit: []string{"zero"}, Dims: 2},
			"dot":       {Implicit: []string{"add", "mul"}, Dims: 1, Outfix: &Outfix{Open: "⟪", Close: "⟫", Body: []int{1, 2}, Sub: 0}},
			"vec_dist":  {Dims: 1, Overload: &Overload{Word: "dist", Arity: 3, Type: metas["vec_dist"].AbsType()}},
			"real_dist": {Overload: &Overload{Word: "dist", Arity: 2, Type: metas["real_dist"].AbsType()}},
		},
		StrictResolution: true,
		CoerceDomain:     RealType,
	}
	scope.ImplicitBindings = map[string]core.Term{}
	for name, constant := range map[string]string{"zero": "rzero", "add": "real_add", "mul": "real_mul"} {
		scope.ImplicitBindings[name] = ParseTermTextInScope(constant, nil, scope, nil).Term
	}
	return scope
}

// undimensioned is scope with no constant declaring a dimension: the
// scope a plain application of every argument parses in, which is the
// kernel term a ⟨…⟩ text must build.
func undimensioned(scope *ParseScope) *ParseScope {
	plain := *scope
	table := testSyntax{}
	for name, s := range scope.Syntax.(testSyntax) {
		c := *s
		c.Dims = 0
		table[name] = &c
	}
	plain.Syntax = table
	plain.Vars = maps.Clone(scope.Vars)
	return &plain
}

func TestDimension_Parse(t *testing.T) {
	scope := dimensionTestScope(t)
	plain := undimensioned(scope)
	same := func(text, kernel string) {
		t.Helper()
		a, b := parseImplicit(t, scope, text), parseImplicit(t, plain, kernel)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", text, kernel, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	// The scope's components stand before the dimension.
	same("vec⟨n⟩(u)", "vec(rzero, n, u)")
	same("vec⟨n + 1⟩(u) ⇒ vec⟨n⟩(u)", "vec(rzero, n + 1, u) ⇒ vec(rzero, n, u)")
	same("matrix⟨n, m⟩(M)", "matrix(rzero, n, m, M)")
	same("dot⟨n⟩(u, v) = dot⟨n⟩(v, u)", "dot(real_add, real_mul, n, u, v) = dot(real_add, real_mul, n, v, u)")
	// So does a prefix the parentheses spell — by the component's name,
	// by a bound variable's type, by the instance's own constant.
	same("vec⟨n⟩(rzero, u)", "vec(rzero, n, u)")
	same("∀z:real. vec⟨n⟩(z, u)", "∀z:real. vec(z, n, u)")
	same("∀zero:real. vec⟨n⟩(zero, u)", "∀zero:real. vec(zero, n, u)")
	same("dot⟨n⟩(real_mul, real_add, u, v) = x", "dot(real_mul, real_add, n, u, v) = x")
	// A type letter beside the dimension, in either order.
	same("vec⟨A:real, n⟩(u)", "vec(rzero, n, u)")
	same("vec⟨n, A:real⟩(u)", "vec(rzero, n, u)")
	// The notation's subscript is the same argument.
	same("⟪u, v⟫_n = dot⟨n⟩(u, v)", "dot(real_add, real_mul, n, u, v) = dot(real_add, real_mul, n, u, v)")
	// The overloaded word reads its dimension where its constant does.
	same("dist⟨n⟩(u, v) = dist(x, y)", "vec_dist(n, u, v) = real_dist(x, y)")
	same("vec_dist⟨n⟩(u, v) = x", "vec_dist(n, u, v) = x")
	// A constant applied to its dimensions alone is a value.
	same("vec_dist⟨n⟩ = vec_dist⟨m⟩", "vec_dist(n) = vec_dist(m)")
	same("matrix⟨n⟩ = matrix⟨m⟩", "matrix(rzero, n) = matrix(rzero, m)")
	// A further argument group applies the application.
	same("vec_dist⟨n⟩(u)(v) = x", "vec_dist(n, u, v) = x")
	// The term path.
	term := ParseTermTextInScope("dot⟨n⟩(u)", nil, scope, nil)
	if len(term.Errors) > 0 {
		t.Fatalf("term: %s", term.Errors[0].Message)
	}
	kernel := ParseTermTextInScope("dot(real_add, real_mul, n, u)", nil, plain, nil)
	if !term.Term.Equals(kernel.Term) {
		t.Fatalf("term differs from its kernel application")
	}
}

func TestDimension_Refusals(t *testing.T) {
	scope := dimensionTestScope(t)
	refused := func(text, want string) {
		t.Helper()
		res := ParsePropTextInScope(text, scope)
		if len(res.Errors) == 0 {
			t.Fatalf("%q: expected a refusal, parsed %s", text, prop.PrintProp(res.Prop))
		}
		if !strings.Contains(res.Errors[0].Message, want) {
			t.Fatalf("%q: refusal %q lacks %q", text, res.Errors[0].Message, want)
		}
	}
	// A dimension in the parentheses, short and with the prefix spelled:
	// the refusal names the text to write.
	refused("vec(n, u)", "write vec⟨n⟩(u)")
	refused("vec(rzero, n, u)", "write vec⟨n⟩(rzero, u)")
	refused("matrix(n, m, M)", "write matrix⟨n, m⟩(M)")
	refused("dot(n, u, v) = x", "write dot⟨n⟩(u, v)")
	refused("vec_dist(n, u, v) = x", "write vec_dist⟨n⟩(u, v)")
	refused("vec_dist(n) = vec_dist(n)", "write vec_dist⟨n⟩")
	refused("dist(n, u, v) = x", "write dist⟨…⟩(…)")
	// A suffix the name has no use for.
	refused("vec⟨n, m⟩(u)", "takes 1 dimension(s)")
	refused("real_dist⟨n⟩(x, y) = x", "declares no dimension")
	// The word with a dimension is the constant that declares one, and
	// its operands are read at that constant's domains.
	refused("dist⟨n⟩(x, y) = x", "does not match domain")
	refused("dist⟨n, m⟩(u, v) = x", "dist takes no 4 arguments")
	refused("∀f:(num → (num → real) → bool). f⟨n⟩(u)", "f is a variable here")
	// A prefix spelled in part cannot stand before the dimension.
	refused("∀z:real. dot⟨n⟩(real_add, u, v) = z", "dot")
	// No table, no dimension.
	bare := *scope
	bare.Syntax = nil
	res := ParsePropTextInScope("vec⟨n⟩(rzero, u)", &bare)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "no syntax table") {
		t.Fatalf("a ⟨…⟩ dimension without a syntax table must be refused: %+v", res.Errors)
	}
}

func TestDimension_ChapterSpelling(t *testing.T) {
	scope := dimensionTestScope(t)
	plain := undimensioned(scope)
	decls := "u:(num → real), v:(num → real), M:(num → num → real), n:num, m:num ⊢ "
	spell := func(kernel string, fragments ...string) {
		t.Helper()
		out, err := ChapterSpelling(decls+kernel, scope.Syntax, scope.ImplicitBindings)
		if err != nil {
			t.Fatalf("%q: %v", kernel, err)
		}
		for _, frag := range fragments {
			if !strings.Contains(out, frag) {
				t.Errorf("chapter spelling of %q lacks %q: %s", kernel, frag, out)
			}
		}
		a, b := parseImplicit(t, scope, out), parseImplicit(t, plain, decls+kernel)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("chapter spelling parses to a different statement: %s", out)
		}
	}
	spell("vec(rzero, n, u) ∧ matrix(rzero, n, m + 1, M)", "vec⟨n⟩(u)", "matrix⟨n, m + 1⟩(M)")
	// The notation takes a full application; the suffix what is left.
	spell("dot(real_add, real_mul, n, u, v) = dot(real_add, real_mul, n, u, v)", "⟪u, v⟫_n")
	spell("dot(real_add, real_mul, n, u) = dot(real_add, real_mul, n, v)", "dot⟨n⟩(u) = dot⟨n⟩(v)")
	// The word keeps the suffix; a value has no parentheses.
	spell("vec_dist(n, u, v) = vec_dist(m, v, u)", "dist⟨n⟩(u, v) = dist⟨m⟩(v, u)")
	spell("vec_dist(n) = vec_dist(m)", "vec_dist⟨n⟩ = vec_dist⟨m⟩")
	// A prefix the scope does not read back stays, behind the suffix.
	spell("∀z:real. vec(z, n, u)", "vec⟨n⟩(z, u)")
	spell("dot(real_mul, real_add, n, u, v) = dot(real_mul, real_add, n, v, u)", "dot⟨n⟩(real_mul, real_add, u, v)")
	// A text already in the form keeps it, and drops a prefix the scope reads.
	out, err := ChapterSpelling(decls+"vec⟨n⟩(rzero, u) ∧ vec⟨m⟩(v)", scope.Syntax, scope.ImplicitBindings)
	if err != nil || !strings.Contains(out, "vec⟨n⟩(u) ∧ vec⟨m⟩(v)") {
		t.Fatalf("re-spelling a ⟨…⟩ text: %q (%v)", out, err)
	}
	// The scope-free formatter round-trips the suffix as an AST.
	formatted, err := FormatStmtText("∀u:(num → real). vec⟨A:real, n+1⟩(u) ⇒ matrix⟨n,m⟩(M) ∧ vec_dist⟨n⟩ = vec_dist⟨n⟩")
	if err != nil || !strings.Contains(formatted, "vec⟨A:real, n + 1⟩(u) ⇒ matrix⟨n, m⟩(M) ∧ vec_dist⟨n⟩ = vec_dist⟨n⟩") {
		t.Fatalf("FormatStmtText: %q (%v)", formatted, err)
	}
}

// An abbreviation whose text is a constant at its dimensions — alone or
// at further arguments — applied, is the one application its text and
// the arguments write out, the dimensions still the suffix's; and the
// output door's fold of that application reads back as the term.
func TestDimension_Abbreviation(t *testing.T) {
	scope := dimensionTestScope(t)
	plain := undimensioned(scope)
	table, err := ParseAbbreviations(Abbrev{
		{Name: "V", Text: "vec⟨n⟩"},
		{Name: "D", Text: "vec_dist⟨n⟩(u)"},
		{Name: "Mat", Text: "matrix⟨n, m⟩"},
		{Name: "Dot", Text: "dot⟨n⟩(u)"},
		{Name: "W", Text: "dist⟨n⟩(u)"},
	})
	if err != nil {
		t.Fatal(err)
	}
	scope.Abbreviations = table
	for _, c := range []struct{ short, written, kernel string }{
		// The scope's components stand before the entry's dimension.
		{"«V»(u)", "vec⟨n⟩(u)", "vec(rzero, n, u)"},
		{"«Mat»(M)", "matrix⟨n, m⟩(M)", "matrix(rzero, n, m, M)"},
		{"«Dot»(v) = x", "dot⟨n⟩(u, v) = x", "dot(real_add, real_mul, n, u, v) = x"},
		// So does a prefix the use's parentheses spell.
		{"«V»(rzero, u)", "vec⟨n⟩(rzero, u)", "vec(rzero, n, u)"},
		{"∀z:real. «V»(z, u)", "∀z:real. vec⟨n⟩(z, u)", "∀z:real. vec(z, n, u)"},
		// A constant of no prefix, and the word it answers to.
		{"«D»(v) = x", "vec_dist⟨n⟩(u, v) = x", "vec_dist(n, u, v) = x"},
		{"«W»(v) = x", "dist⟨n⟩(u, v) = x", "vec_dist(n, u, v) = x"},
	} {
		short, written := parseImplicit(t, scope, c.short), parseImplicit(t, scope, c.written)
		kernel := parseImplicit(t, plain, c.kernel)
		if short.AlphaKey() != written.AlphaKey() || short.AlphaKey() != kernel.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", c.short, c.written, prop.PrintProp(short), prop.PrintProp(kernel))
		}
	}
	// The other direction: the kernel's application, folded into the
	// entries and spelled as the door spells it, is the applied
	// abbreviation, and that text is the term again.
	terms := table.Terms(scope.Vars, scope)
	for _, c := range []struct{ kernel, folded string }{
		{"vec(rzero, n, u)", "«V»(u)"},
		{"matrix(rzero, n, m, M)", "«Mat»(M)"},
		{"dot(real_add, real_mul, n, u, v)", "«Dot»(v)"},
		{"vec_dist(n, u, v)", "«D»(v)"},
	} {
		kernel := ParseTermTextInScope(c.kernel, nil, plain, nil)
		if len(kernel.Errors) > 0 {
			t.Fatalf("%q: %s", c.kernel, kernel.Errors[0].Message)
		}
		printed := DisplaySpelling(ext.PrintTerm(FoldAbbreviations(kernel.Term, terms)), scope.Syntax, scope.ImplicitBindings)
		if printed != c.folded {
			t.Fatalf("%q folds to %q, want %q", c.kernel, printed, c.folded)
		}
		back := ParseTermTextInScope(printed, nil, scope, nil)
		if len(back.Errors) > 0 {
			t.Fatalf("the fold %q of %q does not read back: %s", printed, c.kernel, back.Errors[0].Message)
		}
		if !back.Term.Equals(kernel.Term) {
			t.Fatalf("the fold %q of %q reads back as %s", printed, c.kernel, ext.PrintTerm(back.Term))
		}
	}
}

func TestDimension_Definiendum(t *testing.T) {
	scope := dimensionTestScope(t)
	plain := undimensioned(scope)
	typ, err := ParseTypeText("A → num → (num → A) → bool")
	if err != nil {
		t.Fatal(err)
	}
	// The equation declares its definiendum as a variable; its
	// dimension is written as the constant's will be.
	scope.Vars["padded"] = typ
	plain.Vars["padded"] = typ
	scope.Definiendum = &Definiendum{Name: "padded", Implicit: []string{"zero"}, Dims: 1}
	equation := "∀zero:A. ∀n:num. ∀u:(num → A). padded⟨n⟩(zero, u) ⇔ (∀i:num. n ≤ i ⇒ u(i) = zero)"
	kernel := "∀zero:A. ∀n:num. ∀u:(num → A). padded(zero, n, u) ⇔ (∀i:num. n ≤ i ⇒ u(i) = zero)"
	a, b := parseImplicit(t, scope, equation), parseImplicit(t, plain, kernel)
	if a.AlphaKey() != b.AlphaKey() {
		t.Fatalf("definiendum: %s ≠ %s", prop.PrintProp(a), prop.PrintProp(b))
	}
	res := ParsePropTextInScope(kernel, scope)
	if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "write padded⟨n⟩(zero, u)") {
		t.Fatalf("a definiendum's dimension in parentheses must be refused: %+v", res.Errors)
	}
}
