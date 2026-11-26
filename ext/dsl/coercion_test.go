package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// A declared coercion: `zz_lift : real → complex` marked as the
// embedding of the real line into ℂ. `&` lifts a real through it, and
// a num through the real line, wherever ℂ is expected or a partner is
// complex; the chapter spelling writes the application back as `&`.
func coercionTestScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{}
	for name, ty := range map[string]string{
		"zz_lift": "real → complex",
		"zz_i":    "complex",
		"zz_add":  "complex → complex → complex",
		"zz_mul":  "complex → complex → complex",
		"zz_neg":  "complex → complex",
		"zz_exp":  "complex → complex",
		"zz_cexp": "complex → complex",
		"zz_pi":   "real",
		// A polynomial's evaluation over its ring's operations, the two
		// leading ones implicit, and a conditional: the polymorphic
		// slots a lift stands in.
		"zz_poly": "(A → A → A) → A → (num → A) → A → A",
		"zz_cond": "bool → A → A → A",
	} {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
	}
	return &ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta { return metas[name] },
		Syntax: coercionTestSyntax{testSyntax{
			"zz_lift": {Coercion: &Coercion{Into: typ("complex")}},
			"zz_poly": {Implicit: []string{"add", "zero"}},
			"zz_mul":  {Operator: &Operator{Symbol: "*", Args: []int{0, 1}}},
			"zz_cexp": {Overload: &Overload{Word: "cexp", Arity: 1}},
		}, metas},
		Vars:             map[string]core.HolType{"x": RealType, "z": typ("complex")},
		StrictResolution: true,
		CoerceDomain:     RealType,
	}
}

// coercionTestSyntax is testSyntax with the constants' metas, which the
// chapter spelling reads a position's type from (coercion.go).
type coercionTestSyntax struct {
	testSyntax
	metas map[string]core.ConstTermMeta
}

func (s coercionTestSyntax) ConstMeta(name string) core.ConstTermMeta { return s.metas[name] }

func TestCoercion_LiftsWhereComplexIsAsked(t *testing.T) {
	scope := coercionTestScope(t)
	same := func(short, long string) {
		t.Helper()
		a, b := parseImplicit(t, scope, short), parseImplicit(t, scope, long)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", short, long, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	// An argument position of type complex: a real variable, a numeral
	// through the real line.
	same("zz_add(zz_i, &x) = z", "zz_add(zz_i, zz_lift(x)) = z")
	same("zz_add(zz_i, &1) = z", "zz_add(zz_i, zz_lift(&1)) = z")
	// A partner that is complex: the equation's other side, an
	// operator's other operand.
	same("z = &1", "z = zz_lift(&1)")
	same("zz_exp(zz_i) = &0", "zz_exp(zz_i) = zz_lift(&0)")
	same("zz_add(z, &zz_pi) = &1", "zz_add(z, zz_lift(zz_pi)) = zz_lift(&1)")
	// No complex around: `&` is the chapter's declared real, as before.
	same("&0 ≤ x", "real_of_num(0) ≤ x")
	same("&0 ≤ &1", "real_of_num(0) ≤ real_of_num(1)")
	// A genuine real beside a complex is still a mismatch.
	if res := ParsePropTextInScope("z = x", scope); len(res.Errors) == 0 {
		t.Fatal("a real variable beside a complex must still be refused")
	}
	// A real operand with nothing to lift it is refused, naming why.
	if res := ParsePropTextInScope("&x = &x", scope); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "lifts it") {
		t.Fatalf("& of a real with no lifting domain must be refused: %v", res.Errors)
	}
}

// The chapter spelling writes the lift as `&` exactly where the build
// types the `&` by its position (coercion.go), and the spelled text
// reads back at the real domain, where a `&` no position types is a
// real: a slot of the codomain, a slot an earlier argument pins to it,
// a partner of the codomain, the body of a λ at such a position. A
// slot the text leaves open, a lift under an overloaded word and the
// second of two lifts facing each other keep the application spelled.
func TestCoercion_ChapterSpelling(t *testing.T) {
	scope := coercionTestScope(t)
	for _, tc := range []struct{ raw, want string }{
		{"x:real, z:complex ⊢ zz_add(zz_i, zz_lift(x)) = z", "zz_add(zz_i, &x) = z"},
		{"z:complex ⊢ zz_exp(zz_add(zz_i, zz_lift(&1))) = zz_lift(&0)", "zz_exp(zz_add(zz_i, &1)) = &0"},
		// A slot the operation before it pins to ℂ; a slot nothing pins.
		{"p:(num → complex), z:complex ⊢ zz_poly(zz_add, zz_lift(&0), p, z) = z", "zz_poly(zz_add, &0, p, z) = z"},
		{"b:bool, x:real, z:complex ⊢ zz_cond(b, zz_lift(x), zz_lift(&0)) = z", "zz_cond(b, zz_lift(x), &0) = z"},
		{"b:bool, z:complex ⊢ zz_cond(b, zz_lift(&1), zz_cond(b, zz_neg(z), zz_lift(&0))) = z", "zz_cond(b, zz_lift(&1), zz_cond(b, zz_neg(z), &0)) = z"},
		// The body of a λ at a pinned slot, and against a partner.
		{"p:(num → complex), z:complex ⊢ zz_poly(zz_add, zz_lift(&0), λn:num. zz_lift(&1), z) = z", "zz_poly(zz_add, &0, λn:num. &1, z) = z"},
		{"x:real, f:(num → complex) ⊢ (λn:num. zz_lift(x)) = f", "(λn:num. &x) = f"},
		// An operator's partner; two lifts facing each other.
		{"x:real, z:complex ⊢ zz_mul(zz_lift(x), z) = z", "&x * z = z"},
		{"x:real, y:real ⊢ zz_mul(zz_lift(x), zz_lift(y)) = zz_i", "zz_lift(x) * &y = zz_i"},
		{"x:real, y:real ⊢ zz_lift(x) = zz_lift(y)", "zz_lift(x) = &y"},
		// Under an overloaded word the operand's own type picks the
		// constant, so the lift stays spelled on both sides.
		{"zz_cexp(zz_lift(&0)) = zz_lift(&1)", "cexp(zz_lift(&0)) = zz_lift(&1)"},
	} {
		out, err := ChapterSpelling(tc.raw, scope.Syntax, nil)
		if err != nil || !strings.Contains(out, tc.want) {
			t.Errorf("ChapterSpelling(%q) = %q (%v), want %q", tc.raw, out, err, tc.want)
			continue
		}
		if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, tc.raw).AlphaKey() {
			t.Errorf("%q does not parse back to %q", out, tc.raw)
		}
	}
}

// A partner whose arrows end in ℂ types the `&` at the result of a λ on
// the other side, whichever side it stands on and however many λs
// stand between: the chapter spelling folds the lift there, and the
// build reads the folded text back as the statement it came from. A λ
// whose body is a genuine real stays a mismatch beside a complex-valued
// function — nothing inserts a lift the text does not spell — and a
// real-valued equation reads its `&` on the real line as before.
func TestCoercion_PartnerTypesLambdaBody(t *testing.T) {
	scope := coercionTestScope(t)
	for _, tc := range []struct{ raw, want string }{
		{"f:(num → complex) ⊢ f = (λn:num. zz_lift(&0))", "f = λn:num. &0"},
		{"f:(num → complex) ⊢ (λn:num. zz_lift(&0)) = f", "(λn:num. &0) = f"},
		{"f:(num → complex) ⊢ f ≠ (λn:num. zz_lift(&0))", "f ≠ λn:num. &0"},
		{"g:(num → num → complex) ⊢ g = (λn:num. λm:num. zz_lift(&0))", "g = λn:num. λm:num. &0"},
		{"g:(num → num → complex) ⊢ (λn:num. λm:num. zz_lift(&0)) = g", "(λn:num. λm:num. &0) = g"},
		{"g:(num → num → complex) ⊢ g(0) = (λm:num. zz_lift(&1))", "g(0) = λm:num. &1"},
		{"z:complex ⊢ (λn:num. zz_i) = (λn:num. zz_lift(&1))", "(λn:num. zz_i) = λn:num. &1"},
		{"f:((num → real) → complex) ⊢ f = (λx:(num → real). zz_lift(&0))", "f = λx:(num → real). &0"},
	} {
		out, err := ChapterSpelling(tc.raw, scope.Syntax, nil)
		if err != nil || !strings.Contains(out, tc.want) {
			t.Errorf("ChapterSpelling(%q) = %q (%v), want %q", tc.raw, out, err, tc.want)
			continue
		}
		res := ParsePropTextInScope(out, scope)
		if len(res.Errors) > 0 {
			t.Errorf("%q does not read back: %s", out, res.Errors[0].Message)
			continue
		}
		if res.Prop.AlphaKey() != parseImplicit(t, scope, tc.raw).AlphaKey() {
			t.Errorf("%q reads back as %s, not as %q", out, prop.PrintProp(res.Prop), tc.raw)
		}
	}

	same := func(short, long string) {
		t.Helper()
		a, b := parseImplicit(t, scope, short), parseImplicit(t, scope, long)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", short, long, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	decls := "f:(num → complex), g:(num → num → complex), h:(num → real) ⊢ "
	// A binder the text leaves unannotated takes the partner's domain.
	same(decls+"f = (λn. &0)", decls+"f = (λn:num. zz_lift(&0))")
	// A real-valued function's λ is read on the real line.
	same(decls+"h = (λn:num. &0)", decls+"h = (λn:num. real_of_num(0))")
	for _, text := range []string{
		"f = (λn:num. x)",
		"(λn:num. x) = f",
		"f = (λn:num. x + &1)",
		"g = (λn:num. λm:num. x)",
		"f ≠ (λn:num. x)",
		"f = &0",
		"h = (λn:num. zz_lift(&0))",
	} {
		if res := ParsePropTextInScope(decls+text, scope); len(res.Errors) == 0 {
			t.Errorf("%q must stay a type mismatch, read as %s", text, prop.PrintProp(res.Prop))
		}
	}
}

// A `&` in a slot whose type the application's other arguments decide
// is read after them, at the type they give the slot: a conditional's
// branch beside a complex or an integer one is the same term whichever
// branch it stands in. A `&` beside a real, or beside another `&`, is
// read on the real line as before, and a genuine real beside a complex
// stays a mismatch.
func TestCoercion_ArgumentTypedByItsSiblings(t *testing.T) {
	scope := coercionTestScope(t)
	same := func(short, long string) {
		t.Helper()
		res := ParsePropTextInScope(short, scope)
		if len(res.Errors) > 0 {
			t.Errorf("%q: %s", short, res.Errors[0].Message)
			return
		}
		if b := parseImplicit(t, scope, long); res.Prop.AlphaKey() != b.AlphaKey() {
			t.Errorf("%q ≠ %q:\n  %s\n  %s", short, long, prop.PrintProp(res.Prop), prop.PrintProp(b))
		}
	}
	decls := "b:bool, k:int, p:(num → complex) ⊢ "
	same(decls+"zz_cond(b, &0, z) = z", decls+"zz_cond(b, zz_lift(&0), z) = z")
	same(decls+"zz_cond(b, z, &0) = z", decls+"zz_cond(b, z, zz_lift(&0)) = z")
	same(decls+"zz_cond(b, &0, zz_cond(b, &1, z)) = z", decls+"zz_cond(b, zz_lift(&0), zz_cond(b, zz_lift(&1), z)) = z")
	same(decls+"zz_cond(b, &x, z) = z", decls+"zz_cond(b, zz_lift(x), z) = z")
	same(decls+"zz_cond(b, &0, k) = k", decls+"zz_cond(b, int_of_num(0), k) = k")
	same(decls+"zz_cond(b, &0, x) = x", decls+"zz_cond(b, real_of_num(0), x) = x")
	same(decls+"zz_cond(b, &0, &1) = x", decls+"zz_cond(b, real_of_num(0), real_of_num(1)) = x")
	for _, text := range []string{
		"zz_cond(b, x, z) = z",
		"zz_cond(b, z, x) = z",
		"zz_cond(b, &0, b) = b",
	} {
		if res := ParsePropTextInScope(decls+text, scope); len(res.Errors) == 0 {
			t.Errorf("%q must stay a type mismatch, read as %s", text, prop.PrintProp(res.Prop))
		}
	}
}

// The prefix `-` a chapter declares at ℂ passes the partner's ℂ to its
// operand inside a λ body as it does outside one.
func TestCoercion_PartnerTypesNegatedLambdaBody(t *testing.T) {
	scope := coercionTestScope(t)
	base := scope.Syntax.(coercionTestSyntax)
	syntax := testSyntax{}
	for name, s := range base.testSyntax {
		syntax[name] = s
	}
	syntax["zz_neg"] = &ConstSyntax{Operator: &Operator{Symbol: "-", Args: []int{0}}}
	scope.Syntax = coercionTestSyntax{syntax, base.metas}
	raw := "f:(num → complex) ⊢ f = (λn:num. zz_neg(zz_lift(&1)))"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	if err != nil || !strings.Contains(out, "f = λn:num. -&1") {
		t.Fatalf("ChapterSpelling(%q) = %q (%v)", raw, out, err)
	}
	if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
		t.Fatalf("%q does not parse back to %q", out, raw)
	}
}

// A `&` standing in an implicit slot that an earlier argument made the
// lift's codomain spells that component explicitly, as a real or an
// int in a real or int slot does (implicit.go, spellsPrefix): with the
// components in scope the completion keeps the written prefix instead
// of inserting the scope's in front of it.
func TestCoercion_ExplicitImplicitSlot(t *testing.T) {
	scope := coercionTestScope(t)
	same := func(short, long string) {
		t.Helper()
		a, b := parseImplicit(t, scope, short), parseImplicit(t, scope, long)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", short, long, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	components := "add:(complex → complex → complex), zero:complex, p:(num → complex), z:complex ⊢ "
	same(components+"zz_poly(zz_add, &0, p, z) = z", components+"zz_poly(zz_add, zz_lift(&0), p, z) = z")
	same(components+"zz_poly(p, z) = z", components+"zz_poly(add, zero, p, z) = z")
}

// A chapter that declared the lift's codomain as its domain: `&` of a
// real lifts with nothing else around, a num under `&` is still read
// on the real line, and a declared domain nothing lifts into is
// refused at the first `&` that reads it (a chapter declares its
// domain before it mints the lift, so no earlier).
func TestCoercion_DeclaredDomain(t *testing.T) {
	scope := coercionTestScope(t)
	complexType, _ := ParseTypeText("complex")
	scope.CoerceDomain = complexType
	same := func(short, long string) {
		t.Helper()
		a, b := parseImplicit(t, scope, short), parseImplicit(t, scope, long)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", short, long, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same("zz_exp(&x) = &x", "zz_exp(zz_lift(x)) = zz_lift(x)")
	same("&zz_pi = z", "zz_lift(zz_pi) = z")
	same("z = &1", "z = zz_lift(&1)")
	same("&0 ≤ x", "real_of_num(0) ≤ x")
	same("&0 ≤ &1", "real_of_num(0) ≤ real_of_num(1)")
	same("zz_add(zz_i, &1) = &0", "zz_add(zz_i, zz_lift(&1)) = zz_lift(&0)")
	// The folded spelling of an unanchored lift parses back only here.
	raw := "x:real ⊢ zz_exp(zz_lift(x)) = zz_lift(x)"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	if err != nil || !strings.Contains(out, "zz_exp(&x) = &x") {
		t.Fatalf("ChapterSpelling(%q) = %q (%v)", raw, out, err)
	}
	if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
		t.Fatalf("%q does not parse back to %q", out, raw)
	}
	// A declared domain no constant lifts into is refused by the
	// unanchored `&` that reads it; an anchored `&` and a text with none
	// read.
	scope.Syntax = testSyntax{}
	if res := ParsePropTextInScope("&0 ≤ &1", scope); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "declared coercion into") {
		t.Fatalf("a declared domain with no lift must be refused: %v", res.Errors)
	}
	for _, text := range []string{"&0 ≤ x", "x ≤ x"} {
		if res := ParsePropTextInScope(text, scope); len(res.Errors) > 0 {
			t.Fatalf("%q reads under any declared domain: %v", text, res.Errors)
		}
	}
}

// A relation between `&` numerals alone is typed by the scope's domain
// and by nothing in the text, and the parse says so in a warning: the
// type it was read at and what decided it. Under a declared ℂ a bare
// numeral stays on the real line, so `&2 ≠ &0` is a statement about
// reals. A relation one side of which names a type is not reported, nor
// one whose numerals a partner retargets.
func TestCoercion_RelationBetweenNumeralsIsReported(t *testing.T) {
	scope := coercionTestScope(t)
	complexType, _ := ParseTypeText("complex")
	scope.CoerceDomain = complexType
	scope.Vars["k"] = IntType
	numeral := func(text string) []InputDiagnostic {
		t.Helper()
		res := ParsePropTextInScope(text, scope)
		if len(res.Errors) > 0 {
			t.Fatalf("%q: %v", text, res.Errors)
		}
		var out []InputDiagnostic
		for _, w := range res.Warnings {
			if w.Code == CodeNumeralDomain {
				out = append(out, w)
			}
		}
		return out
	}
	for _, text := range []string{"&2 ≠ &0", "&1 + &1 = &2", "&0 < &1", "-(&1) ≤ &2 * &3"} {
		ws := numeral(text)
		if len(ws) != 1 {
			t.Fatalf("%q: want one numeral warning, got %v", text, ws)
		}
		if !strings.Contains(ws[0].Message, "stands between numerals alone and is read at real") ||
			!strings.Contains(ws[0].Message, "the scope's `&` domain is complex, under which a bare numeral stays on the real line") {
			t.Fatalf("%q: %s", text, ws[0].Message)
		}
		if ws[0].Suggestion != "to state it at complex, lift one side, `zz_lift(&…)`: the other side follows it" {
			t.Fatalf("%q: %s", text, ws[0].Suggestion)
		}
	}
	if ws := numeral("&2 ≠ &0 ∧ (x = &1 ∨ &3 = &4)"); len(ws) != 2 || ws[0].Position >= ws[1].Position {
		t.Fatalf("two relations between numerals, in the text's order: %v", ws)
	}
	for _, text := range []string{
		"x ≠ &0",                // a real variable types the relation
		"x + &1 = &2",           // and types the sum it stands in
		"z = &1",                // a complex partner lifts the numeral
		"&2 = k",                // an int partner retargets it
		"zz_add(zz_i, &1) = &0", // the left side is complex by its constant
		"1 + 1 = 2",             // no coercion at all
	} {
		if ws := numeral(text); len(ws) != 0 {
			t.Fatalf("%q names a type: %v", text, ws)
		}
	}

	// With a declared ℝ or ℤ the reason names it, and with none declared
	// a text not read strictly is read at real by default.
	scope.CoerceDomain = RealType
	if ws := numeral("&2 ≠ &0"); len(ws) != 1 || !strings.Contains(ws[0].Message, "the scope's `&` domain is real") {
		t.Fatalf("declared real: %v", ws)
	}
	scope.CoerceDomain = IntType
	if ws := numeral("&2 ≠ &0"); len(ws) != 1 || !strings.Contains(ws[0].Message, "is read at int") {
		t.Fatalf("declared int: %v", ws)
	}
	scope.CoerceDomain, scope.StrictResolution = nil, false
	if ws := numeral("&2 ≠ &0"); len(ws) != 1 || !strings.Contains(ws[0].Message, "the scope declares no `&` domain") {
		t.Fatalf("no domain: %v", ws)
	}
}
