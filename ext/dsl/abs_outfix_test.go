package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// `|x|`: one pair of delimiters shared by several constants under one
// overloaded word — a toy real and int magnitude, both `|x|` and both
// the word `zz_abs` — read by the body's type as the word is, and
// never confused with the set-builder's `|`. The scope has a chapter's
// shape: the engine's built-in constants (the set-builder's among
// them) resolve as scope constants and meta letters are freshened.
func absOutfixTestScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{}
	for name, ty := range map[string]string{"zz_rabs": "real → real", "zz_iabs": "int → int"} {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
	}
	bars := func(ty string) *ConstSyntax {
		return &ConstSyntax{
			Outfix:   &Outfix{Open: "|", Close: "|", Body: []int{0}, Sub: -1},
			Overload: &Overload{Word: "zz_abs", Arity: 1, Type: typ(ty)},
		}
	}
	return &ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if m, ok := metas[name]; ok {
				return m
			}
			if m, ok := ext.InitConstMetaMap().Load(core.TermName(name)); ok {
				return m
			}
			return core.ConstTermMeta{}
		},
		Syntax:             testSyntax{"zz_rabs": bars("real → real"), "zz_iabs": bars("int → int")},
		Vars:               map[string]core.HolType{"x": RealType, "y": RealType, "a": IntType, "s": typ("real → bool"), "P": core.TypeBool()},
		StrictResolution:   true,
		FreshenMetaLetters: true,
		CoerceDomain:       RealType,
	}
}

func TestAbsOutfix_Parse(t *testing.T) {
	scope := absOutfixTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	// The body's type picks the constant, as it does for the word.
	same("|x| = zz_rabs(x)", "zz_abs(x) = zz_rabs(x)")
	same("|a| = zz_iabs(a)", "zz_abs(a) = zz_iabs(a)")
	same("|x - y| = |y - x|", "zz_rabs(x - y) = zz_rabs(y - x)")
	same("-|x| ≤ x", "-zz_rabs(x) ≤ x")
	// Nested and negated: `||` and `|-` are not ASCII aliases.
	same("||x|| = |x|", "zz_rabs(zz_rabs(x)) = zz_rabs(x)")
	same("|-x| = |x|", "zz_rabs(-x) = zz_rabs(x)")
	same("|&1| = &1", "zz_rabs(&1) = &1")
	// Beside the set-builder's separator, in every position the two can meet.
	same("{x | x ∈ s ∧ |x| < &1} = s", "{x | x ∈ s ∧ zz_rabs(x) < &1} = s")
	same("{x:real | |x| < &1} = s", "{x:real | zz_rabs(x) < &1} = s")
	// The binder is typed by its first use: the membership comes first.
	same("{x | x ∈ s ∧ |x| < &1} = {x | x ∈ s ∧ &0 < |x|}", "{x | x ∈ s ∧ zz_rabs(x) < &1} = {x | x ∈ s ∧ &0 < zz_rabs(x)}")
	same("|x| ∈ {y | y ∈ s ∧ |y| < &1}", "zz_rabs(x) ∈ {y | y ∈ s ∧ zz_rabs(y) < &1}")
	// A body no sharer takes is refused, naming the word.
	if res := ParsePropTextInScope("|P| = |P|", scope); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "zz_abs") {
		t.Fatalf("a body of no candidate's type must be refused by the word: %v", res.Errors)
	}
	// With no sharer in scope the delimiters are nobody's.
	if res := ParsePropTextInScope("|x| = x", &ParseScope{Vars: scope.Vars, Syntax: testSyntax{}}); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "no constant in scope declares") {
		t.Fatalf("|…| with no declaring constant must be refused: %v", res.Errors)
	}
}

func TestAbsOutfix_ChapterSpelling(t *testing.T) {
	scope := absOutfixTestScope(t)
	raw := "x:real, a:int, s:(real → bool) ⊢ zz_rabs(x - x) = zz_rabs(x) ∧ zz_iabs(a) = a ∧ {y | y ∈ s ∧ zz_rabs(y) < &1} = s ∧ zz_rabs(zz_rabs(x)) = x ∧ zz_rabs(-x) = x"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{"|x - x| = |x|", "|a| = a", "{y | y ∈ s ∧ |y| < &1} = s", "||x|| = x", "|-x| = x"} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
		t.Fatalf("the spelling parses to a different statement: %s", out)
	}
	// The scope-free formatter keeps the bars as written.
	for in, want := range map[string]string{
		"|x| = x":                 "|x| = x",
		"-|x - y| ≤ |x|":          "-|x - y| ≤ |x|",
		"{x | |x| < &1} = s":      "{x | |x| < &1} = s",
		"{ |x| | x | x ∈ s } = s": "{|x| | x | x ∈ s} = s",
		"||x|| = x":               "||x|| = x",
		"|-x| = x":                "|-x| = x",
	} {
		got, err := FormatStmtText(in)
		if err != nil || !strings.Contains(got, want) {
			t.Errorf("FormatStmtText(%q) = %q (%v), want %q", in, got, err, want)
		}
	}
}
