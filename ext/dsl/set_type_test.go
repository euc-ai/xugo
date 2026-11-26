package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
)

// The set(τ) alias, the applied-set check, the type vocabulary check
// and the fold rule (typenames.go, setspelling.go).

func mustType(t *testing.T, text string) core.HolType {
	t.Helper()
	ty, err := ParseTypeText(text)
	if err != nil {
		t.Fatalf("ParseTypeText(%q): %v", text, err)
	}
	return ty
}

func TestSetAliasLowersToArrow(t *testing.T) {
	for _, c := range []struct{ alias, arrow string }{
		{"set(A)", "A → bool"},
		{"set(set(A))", "(A → bool) → bool"},
		{"set(A) → bool", "(A → bool) → bool"},
		{"A → set(B)", "A → B → bool"},
		{"set(prod(A, B))", "prod(A, B) → bool"},
		{"list(set(A))", "list(A → bool)"},
	} {
		if got, want := mustType(t, c.alias), mustType(t, c.arrow); !got.Equals(want) {
			t.Errorf("%s lowers to %v, want %v (%s)", c.alias, got, want, c.arrow)
		}
	}
}

func TestSetAliasArity(t *testing.T) {
	if _, err := ParseTypeText("set(A, B)"); err == nil {
		t.Fatal("set(A, B) parsed")
	}
	res := ParsePropText("∀s:set(A, B). ⊤")
	if len(res.Errors) == 0 || res.Errors[0].Code != CodeArityMismatch {
		t.Fatalf("expected an arity error, got %+v", res.Errors)
	}
	if _, err := ParseTypeText("set"); err == nil {
		t.Fatal("bare set parsed: the alias takes one argument")
	}
}

func TestSetSpellingIsTheSameStatement(t *testing.T) {
	a := ParsePropText("∀s:set(set(A)). ∀u:set(A). u ∈ s ⇒ ∀x:A. x ∈ u ⇒ x ∈ ⋃s")
	b := ParsePropText("∀s:((A → bool) → bool). ∀u:(A → bool). u ∈ s ⇒ ∀x:A. x ∈ u ⇒ x ∈ ⋃s")
	requireParses(t, a)
	requireParses(t, b)
	if !a.Prop.Conclusion().AlphaEquals(b.Prop.Conclusion()) {
		t.Fatalf("the two spellings build different terms:\n%v\n%v", a.Prop, b.Prop)
	}
}

func requireCode(t *testing.T, res ParseResult, code string) {
	t.Helper()
	if len(res.Errors) == 0 {
		t.Fatalf("expected a %s error, parsed: %v", code, res.Prop)
	}
	if res.Errors[0].Code != code {
		t.Fatalf("expected a %s error, got %s: %s", code, res.Errors[0].Code, res.Errors[0].Message)
	}
}

func TestAppliedSetRefused(t *testing.T) {
	requireCode(t, ParsePropText("∀s:set(A). ∀x:A. s(x)"), CodeSetApplied)
	requireCode(t, ParsePropText("s:set(A) ⊢ ∀x:A. s(x)"), CodeSetApplied)
	requireCode(t, ParsePropText("∀t:(A → set(B)). ∀x:A. ∀y:B. t(x)(y)"), CodeSetApplied)
	requireCode(t, ParsePropText("∀t:(A → set(B)). ∀x:A. ∀y:B. t(x, y)"), CodeSetApplied)
	requireCode(t, ParseTermText("λs:set(A). λx:A. s(x)", nil, nil), CodeSetApplied)
	requireParses(t, ParsePropText("∀s:set(A). ∀x:A. x ∈ s"))
	requireParses(t, ParsePropText("∀t:(A → set(B)). ∀x:A. ∀y:B. y ∈ t(x)"))
	requireParses(t, ParsePropText("∀P:(A → bool). ∀x:A. P(x)"))
	requireParses(t, ParsePropText("∀P:(set(A) → bool). ∀s:set(A). P(s)"))
	// An inner binder shadows: the applied s is the predicate.
	requireParses(t, ParsePropText("∀s:set(A). ∀s:(A → bool). ∀x:A. s(x)"))
}

func vocab(names map[string]int) *ParseScope {
	return &ParseScope{TypeResolver: func(name string) (int, bool) {
		a, ok := names[name]
		return a, ok
	}}
}

func TestUnknownTypeRefusedUnderAVocabulary(t *testing.T) {
	scope := vocab(map[string]int{"num": 0, "list": 1})
	requireParses(t, ParsePropTextInScope("∀n:num. n = n", scope))
	requireParses(t, ParsePropTextInScope("∀l:list(A). l = l", scope))
	requireParses(t, ParsePropTextInScope("∀s:set(num). ∀n:num. n ∈ s", scope))
	requireParses(t, ParsePropTextInScope("∀x:var:Repty. x = x", scope))
	requireCode(t, ParsePropTextInScope("∀n:nat. n = n", scope), CodeUnknownType)
	requireCode(t, ParsePropTextInScope("∀l:lst(A). l = l", scope), CodeUnknownType)
	requireCode(t, ParsePropTextInScope("∀l:list. l = l", scope), CodeArityMismatch)
	requireCode(t, ParsePropTextInScope("∀b:bool(A). b", scope), CodeArityMismatch)
	requireCode(t, ParsePropTextInScope("∀p:prod(A). p = p", scope), CodeArityMismatch)
	// The engine's own types are known under any vocabulary.
	requireParses(t, ParsePropTextInScope("∀p:prod(num, real). ∀i:int. p = p ∧ i = i", vocab(map[string]int{})))
	requireCode(t, ParsePropTextInScope("∀l:list(A). ∀x:A. x = x ∧ ∀m:lst(A). m = m", scope), CodeUnknownType)
	requireCode(t, ParseTermTextInScope("λn:nat. n", nil, scope, nil), CodeUnknownType)
	if _, err := ParseTypeTextInScope("nat → num", scope); err == nil {
		t.Fatal("nat accepted under the vocabulary")
	}
	// No vocabulary: loose, as a bare parse has always been.
	requireParses(t, ParsePropText("∀n:nat. n = n"))
}

func TestRespellSets(t *testing.T) {
	for _, c := range []struct{ in, want string }{
		{"∀s:(A → bool). ∀x:A. x ∈ s", "∀s:set(A). ∀x:A. x ∈ s"},
		{"∀s:set(A). ∀x:A. x ∈ s", "∀s:set(A). ∀x:A. x ∈ s"},
		{"∀P:(A → bool). ∀x:A. P(x)", "∀P:(A → bool). ∀x:A. P(x)"},
		{"∀T:((A → bool) → bool). ∀u:(A → bool). u ∈ T", "∀T:set(set(A)). ∀u:set(A). u ∈ T"},
		{"∀P:((A → bool) → bool). ∀s:(A → bool). P(s)", "∀P:(set(A) → bool). ∀s:set(A). P(s)"},
		{"∀t:(A → B → bool). ∀x:A. ∀y:B. y ∈ t(x)", "∀t:(A → set(B)). ∀x:A. ∀y:B. y ∈ t(x)"},
		{"∀R:(A → A → bool). ∀x y:A. R(x, y)", "∀R:(A → A → bool). ∀x y:A. R(x, y)"},
		{"∀R:(A → A → bool). wellfounded(R)", "∀R:(A → A → bool). wellfounded(R)"},
		{"∀s t:(A → bool). s ⊆ t", "∀s t:set(A). s ⊆ t"},
		{"∀s t:(A → bool). ∀x:A. s(x) ∧ x ∈ t", "∀s t:(A → bool). ∀x:A. s(x) ∧ x ∈ t"},
		{"∀op:(bool → bool). ∀b:bool. op(b) = b", "∀op:(bool → bool). ∀b:bool. op(b) = b"},
		{"s:(A → bool) ⊢ ∀x:A. x ∈ s", "s:set(A) ⊢ ∀x:A. x ∈ s"},
		{"λt₁:(A → bool). λt₂:(A → bool). t₁ ⊊ t₂ ∧ t₂ ⊆ s", "λt₁:set(A). λt₂:set(A). t₁ ⊊ t₂ ∧ t₂ ⊆ s"},
		{"∀s:(A -> bool). ∀x:A. x ∈ s", "∀s:(A -> bool). ∀x:A. x ∈ s"},
		{"∀s:(A → bool). finite(s)", "∀s:set(A). finite(s)"},
		{"∀s:(A → bool). s = ∅", "∀s:set(A). s = ∅"},
		{"∀s:(prod(A, B) → bool). ∀p:prod(A, B). p ∈ s", "∀s:set(prod(A, B)). ∀p:prod(A, B). p ∈ s"},
		{"∀s:(A → bool). {x:A | x ∈ s} = s", "∀s:set(A). {x:A | x ∈ s} = s"},
		{"image:((A → B) → (A → bool) → B → bool) ⊢ ∀f:(A → B). ∀s:(A → bool). ∀y:B. y ∈ image(f, s)",
			"image:((A → B) → set(A) → set(B)) ⊢ ∀f:(A → B). ∀s:set(A). ∀y:B. y ∈ image(f, s)"},
		{"∀s:((A → A → bool) → bool). ∀R:(A → A → bool). R ∈ s", "∀s:set(A → A → bool). ∀R:(A → A → bool). R ∈ s"},
		{"∀f:((A, B) → bool). ∀a:A. ∀b:B. f(a, b)", "∀f:((A, B) → bool). ∀a:A. ∀b:B. f(a, b)"},
	} {
		got, rep := RespellSets(c.in)
		if len(rep.Errors) > 0 {
			t.Errorf("%s: %s", c.in, rep.Errors[0].Message)
			continue
		}
		if got != c.want {
			t.Errorf("RespellSets(%s)\n got  %s\n want %s", c.in, got, c.want)
		}
		// The respelling is the same statement (a λ claim is a term).
		parse := func(s string) ParseResult {
			if strings.HasPrefix(s, "λ") {
				free := map[string]core.HolType{"s": core.MakeFun(core.MakeVarType("A"), core.TypeBool())}
				return ParseTermText(s, free, nil)
			}
			return ParsePropText(s)
		}
		a, b := parse(c.in), parse(got)
		if a.Term != nil && b.Term != nil {
			if !a.Term.AlphaEquals(b.Term) {
				t.Errorf("%s: the respelling builds a different term", c.in)
			}
			continue
		}
		if len(a.Errors) > 0 || len(b.Errors) > 0 {
			t.Errorf("%s: before %v / after %v", c.in, a.Errors, b.Errors)
			continue
		}
		if !a.Prop.Conclusion().AlphaEquals(b.Prop.Conclusion()) {
			t.Errorf("%s: the respelling builds a different term", c.in)
		}
	}
}

func TestSpelledAsPredicateFinding(t *testing.T) {
	find := func(text, name string) SetBinder {
		t.Helper()
		rep := AnalyzeSetSpelling(text)
		if len(rep.Errors) > 0 {
			t.Fatalf("%s: %s", text, rep.Errors[0].Message)
		}
		for _, b := range rep.Binders {
			if b.Name == name {
				return b
			}
		}
		t.Fatalf("%s: no binder %s", text, name)
		return SetBinder{}
	}
	if b := find("∀s:(A → bool). ∀x:A. x ∈ s", "s"); !b.SpelledAsPredicate() {
		t.Errorf("s used with ∈ is a set spelled as a predicate: %+v", b)
	}
	if b := find("∀P:(A → bool). ∀x:A. P(x)", "P"); b.SpelledAsPredicate() {
		t.Errorf("P applied is a predicate: %+v", b)
	}
	if b := find("∀s:(A → bool). finite(s)", "s"); b.SpelledAsPredicate() || b.Evidence != "constant:finite" {
		t.Errorf("s handed to a constant is the author's call, evidence %q: %+v", b.Evidence, b)
	}
	if b := find("∀s:(num → bool). Σ_{i∈s} i = 0", "s"); !b.SpelledAsPredicate() {
		t.Errorf("a Σ range is a set position: %+v", b)
	}
	if b := find("∀s:set(A). ∀x:A. x ∈ s", "s"); b.SpelledAsPredicate() || b.Folded != "" {
		t.Errorf("already spelled: %+v", b)
	}
}
