package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// `⁅x⁆`: the class delimiters a quotient's class map declares, shared
// by every quotient under the one word `class` — read by the body's
// type as `|x|` is, and spelled back by the chapter spelling. Two toy
// class maps stand in for two quotients.
func classOutfixTestScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	metas := map[string]core.ConstTermMeta{}
	for name, ty := range map[string]string{"zz_nclass": "num → num", "zz_rclass": "real → real"} {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
	}
	brackets := func(ty string) *ConstSyntax {
		return &ConstSyntax{
			Outfix:   &Outfix{Open: "⁅", Close: "⁆", Body: []int{0}, Sub: -1},
			Overload: &Overload{Word: "class", Arity: 1, Type: typ(ty)},
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
		Syntax:             testSyntax{"zz_nclass": brackets("num → num"), "zz_rclass": brackets("real → real")},
		Vars:               map[string]core.HolType{"n": ext.NumType, "m": ext.NumType, "x": RealType},
		StrictResolution:   true,
		FreshenMetaLetters: true,
		CoerceDomain:       RealType,
	}
}

func TestClassOutfix_Parse(t *testing.T) {
	scope := classOutfixTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same("⁅n⁆ = zz_nclass(n)", "class(n) = zz_nclass(n)")
	same("⁅x⁆ = zz_rclass(x)", "class(x) = zz_rclass(x)")
	same("⁅n + m⁆ = ⁅m + n⁆", "zz_nclass(n + m) = zz_nclass(m + n)")
	same("⁅⁅n⁆⁆ = ⁅n⁆", "zz_nclass(zz_nclass(n)) = zz_nclass(n)")
	if res := ParsePropTextInScope("⁅n⁆ = n", &ParseScope{Vars: scope.Vars, Syntax: testSyntax{}}); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "no constant in scope declares") {
		t.Fatalf("⁅…⁆ with no declaring constant must be refused: %v", res.Errors)
	}
}

func TestClassOutfix_ChapterSpelling(t *testing.T) {
	scope := classOutfixTestScope(t)
	raw := "n:num, x:real ⊢ zz_nclass(n + n) = zz_nclass(n) ∧ zz_rclass(x) = zz_rclass(-x)"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{"⁅n + n⁆ = ⁅n⁆", "⁅x⁆ = ⁅-x⁆"} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
		t.Fatalf("the spelling parses to a different statement: %s", out)
	}
	got, err := FormatStmtText("⁅n⁆ = ⁅m⁆")
	if err != nil || !strings.Contains(got, "⁅n⁆ = ⁅m⁆") {
		t.Errorf("FormatStmtText keeps the brackets: %q (%v)", got, err)
	}
}
