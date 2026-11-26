package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// A type with an order of its own and a lift for numerals alone — the
// shape of [0, ∞]: `zz_le` and `zz_lt` declare `≤` and `<`, `zz_add`
// declares `+`, and `zz_of : real → zz_e` is the `&` of a num, which
// embeds the nonnegative line only and so lifts no real.
func declaredOrderTestScope(t *testing.T) *ParseScope {
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
		"zz_le":  "zz_e → zz_e → bool",
		"zz_lt":  "zz_e → zz_e → bool",
		"zz_add": "zz_e → zz_e → zz_e",
		"zz_of":  "real → zz_e",
		"zz_mu":  "set(real) → zz_e",
	} {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
	}
	return &ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta { return metas[name] },
		Syntax: coercionTestSyntax{testSyntax{
			"zz_le":  {Operator: &Operator{Symbol: "≤", Args: []int{0, 1}}},
			"zz_lt":  {Operator: &Operator{Symbol: "<", Args: []int{0, 1}}},
			"zz_add": {Operator: &Operator{Symbol: "+", Args: []int{0, 1}}},
			"zz_of":  {Coercion: &Coercion{Into: typ("zz_e"), NumeralsOnly: true}},
		}, metas},
		Vars:             map[string]core.HolType{"x": RealType, "n": NumType, "s": typ("set(real)"), "t": typ("set(real)")},
		StrictResolution: true,
		CoerceDomain:     RealType,
	}
}

func TestDeclaredOrder_Parse(t *testing.T) {
	scope := declaredOrderTestScope(t)
	same := func(short, long string) {
		t.Helper()
		a, b := parseImplicit(t, scope, short), parseImplicit(t, scope, long)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", short, long, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same("zz_mu(s) ≤ zz_mu(t)", "zz_le(zz_mu(s), zz_mu(t))")
	same("zz_mu(s) < zz_mu(t) + zz_mu(s)", "zz_lt(zz_mu(s), zz_add(zz_mu(t), zz_mu(s)))")
	// A numeral beside the type is its lift; a num term likewise.
	same("&0 ≤ zz_mu(s)", "zz_le(zz_of(&0), zz_mu(s))")
	same("zz_mu(s) < &1", "zz_lt(zz_mu(s), zz_of(&1))")
	same("zz_mu(s) ≤ &n", "zz_le(zz_mu(s), zz_of(&n))")
	same("zz_mu(s) + &1 = zz_mu(t)", "zz_add(zz_mu(s), zz_of(&1)) = zz_mu(t)")
	// The real line keeps its own order and numerals.
	same("&0 ≤ x", "real_of_num(0) ≤ x")
	// The lift takes no real: `&x` beside the type is refused, naming
	// the lift, and the constant applied to a real reads as written.
	if res := ParsePropTextInScope("&x ≤ zz_mu(s)", scope); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "lifts numerals only") {
		t.Fatalf("& of a real into a numerals-only lift must be refused: %v", res.Errors)
	}
	same("zz_of(x) ≤ zz_mu(s)", "zz_le(zz_of(x), zz_mu(s))")
	if res := ParsePropTextInScope("zz_mu(s) ≤ x", scope); len(res.Errors) == 0 {
		t.Fatal("a real beside the declared type must still be refused")
	}
	if res := ParsePropTextInScope("zz_mu(s) ≥ zz_mu(t)", scope); len(res.Errors) == 0 {
		t.Fatal("≥ is declared by no constant here and must be refused")
	}
}

// The chapter spelling writes the declared order as `≤` and `<`, and
// the numerals-only lift as `&` exactly where its operand is the `&` of
// a num; at a real the lift keeps its name.
func TestDeclaredOrder_ChapterSpelling(t *testing.T) {
	scope := declaredOrderTestScope(t)
	for _, tc := range []struct{ raw, want string }{
		{"s:set(real), t:set(real) ⊢ zz_le(zz_mu(s), zz_mu(t))", "zz_mu(s) ≤ zz_mu(t)"},
		{"s:set(real) ⊢ zz_le(zz_mu(s), zz_of(&0))", "zz_mu(s) ≤ &0"},
		{"s:set(real) ⊢ zz_lt(zz_of(&1), zz_mu(s))", "&1 < zz_mu(s)"},
		{"s:set(real), t:set(real) ⊢ zz_lt(zz_add(zz_mu(s), zz_of(&1)), zz_mu(t))", "zz_mu(s) + &1 < zz_mu(t)"},
		{"n:num, s:set(real) ⊢ zz_le(zz_of(&n), zz_mu(s))", "&n ≤ zz_mu(s)"},
		{"x:real, s:set(real) ⊢ zz_le(zz_of(x), zz_mu(s))", "zz_of(x) ≤ zz_mu(s)"},
		{"x:real, s:set(real) ⊢ zz_add(zz_mu(s), zz_of(x)) = zz_of(&0)", "zz_mu(s) + zz_of(x) = &0"},
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
	if !OperatorSymbolOK("≤", 2) || !OperatorSymbolOK("<", 2) || OperatorSymbolOK("≥", 2) {
		t.Error("the define door takes ≤ and < at arity 2, and no other comparison")
	}
}
