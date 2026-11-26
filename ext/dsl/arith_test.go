// Round-trip tests for arith / numeric-literal lowering: parse a
// human-friendly text rendering of a corpus theorem, normalize the
// resulting prop, and check the AlphaKey against the theorem's
// normalized key. The keys are hard-coded fixtures so the test runs
// without the registry.
//
// A mismatch here means one of:
//   - the const-meta types in arith.go drifted from the registry
//   - the lexer / parser / lowering changed structural shape
//   - prop.Normalize changed its canonical form (in which case the
//     fixtures need refreshing — that's a separate signal, but the
//     test still flags it)
//
// Lives in package ext_test (black-box) so we can import ext/prop
// without an import cycle.

package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// corpusFixture pairs an agent-friendly text rendering of a corpus
// theorem with its normalized key (alpha-key of the canonical
// form). The fixture comment shows the printed normalized form for
// reference.
type corpusFixture struct {
	name        string // theorem name (for test reporting)
	text        string // agent-friendly text
	normalized  string // printed normalized form (comment only)
	expectedKey core.PropKey
}

// 12 nat-arith corpus theorems covering +, -, *, <, ≤, ≠, suc,
// numeric literals, and combinations.
var corpusFixtures = []corpusFixture{
	{
		name:        "nat_arith.AddZero",
		text:        "∀m:num. m + 0 = m",
		normalized:  "∀m. m = m + 0",
		expectedKey: "prop_bdab6326259f3ff0",
	},
	{
		name:        "nat_arith.AddSym",
		text:        "∀m:num. ∀n:num. m + n = n + m",
		normalized:  "∀m. ∀n. (m + n) = (n + m)",
		expectedKey: "prop_db75c36bf81c6d32",
	},
	{
		name:        "nat_arith.AddAssoc",
		text:        "∀m:num. ∀n:num. ∀p:num. m + (n + p) = (m + n) + p",
		normalized:  "∀m. ∀n. ∀p. (m + (n + p)) = ((m + n) + p)",
		expectedKey: "prop_5ae355304538196a",
	},
	{
		name:        "nat_arith.MulZero",
		text:        "∀m:num. m * 0 = 0",
		normalized:  "∀m. 0 = (m * 0)",
		expectedKey: "prop_7c79be931ec6d39b",
	},
	{
		name:        "nat_arith.MulSuc",
		text:        "∀m:num. ∀n:num. m * suc(n) = m + m * n",
		normalized:  "∀m. ∀n. (m * suc(n)) = (m + (m * n))",
		expectedKey: "prop_404b4440c26a3475",
	},
	{
		name:        "nat_arith.MulSym",
		text:        "∀m:num. ∀n:num. m * n = n * m",
		normalized:  "∀m. ∀n. (m * n) = (n * m)",
		expectedKey: "prop_4b12272f28f2d0c9",
	},
	{
		name:        "nat_order.ZeroLessEq",
		text:        "∀n:num. 0 ≤ n",
		normalized:  "∀n. 0 ≤ n",
		expectedKey: "prop_a9a4c6302ce129b9",
	},
	{
		name:        "nat_order.ZeroLessThanSuc",
		text:        "∀n:num. 0 < suc(n)",
		normalized:  "∀n. 0 < suc(n)",
		expectedKey: "prop_c9f52f32a3a0f07",
	},
	{
		name:        "nat_order.LessEqRefl",
		text:        "∀n:num. n ≤ n",
		normalized:  "∀n. n ≤ n",
		expectedKey: "prop_c1df2bc9f509331f",
	},
	{
		// Outer parens required: tight-binding ∀ only scopes the
		// relational body, so the ⇔ needs an explicit grouping.
		name:        "nat_order.PosIffNonzero",
		text:        "∀n:num. ((n ≠ 0) ⇔ (0 < n))",
		normalized:  "∀n. (n ≠ 0) ⇔ (0 < n)",
		expectedKey: "prop_1633d223328d3761",
	},
	{
		name:        "nat_monus.subZero",
		text:        "∀m:num. ((m = m - 0) ∧ (0 = 0 - m))",
		normalized:  "∀m. (m = m - 0) ∧ (0 = 0 - m)",
		expectedKey: "prop_6031cc0b343b0aa8",
	},
	{
		name:        "nat_order.LessEqTrans",
		text:        "∀m:num. ∀p:num. ∀n:num. (¬(m ≤ p) ∨ ¬(p ≤ n) ∨ (m ≤ n))",
		normalized:  "∀m. ∀p. ∀n. ¬(m ≤ p) ∨ ¬(p ≤ n) ∨ (m ≤ n)",
		expectedKey: "prop_e42ad3f6745873e7",
	},
}

func TestArith_CorpusRoundTrip(t *testing.T) {
	for _, f := range corpusFixtures {
		t.Run(f.name, func(t *testing.T) {
			res := ParsePropText(f.text)
			if len(res.Errors) > 0 {
				t.Fatalf("parse failed for %q:\n  errors: %v", f.text, res.Errors)
			}
			if res.Prop == nil {
				t.Fatalf("parse returned nil prop for %q", f.text)
			}

			normalized, _ := prop.Normalize(res.Prop)
			got := normalized.AlphaKey()
			if got != f.expectedKey {
				t.Errorf("alpha-key mismatch for %s\n  text:           %q\n  normalized form (expected): %s\n  got AlphaKey:   %s\n  want AlphaKey:  %s",
					f.name, f.text, f.normalized, got, f.expectedKey)
			}
		})
	}
}

// TestArith_BareNumberLiteral spot-checks that a standalone numeric
// literal lowers to the engine-canonical bare bit-tree (`_0`, `bit1(_0)`,
// …).
func TestArith_BareNumberLiteral(t *testing.T) {
	cases := []struct {
		text string
		// expected: hand-built equivalent using core APIs (bare bit-tree).
		expected core.Term
	}{
		{"x:num ⊢ x = 0", ZeroMeta.Term()},
		{"x:num ⊢ x = 1", coreApp(Bit1Meta.Term(), ZeroMeta.Term())},
		{"x:num ⊢ x = 2", coreApp(Bit0Meta.Term(),
			coreApp(Bit1Meta.Term(), ZeroMeta.Term()))},
		{"x:num ⊢ x = 5", coreApp(Bit1Meta.Term(),
			coreApp(Bit0Meta.Term(),
				coreApp(Bit1Meta.Term(), ZeroMeta.Term())))},
	}
	for _, c := range cases {
		t.Run(c.text, func(t *testing.T) {
			res := ParsePropText(c.text)
			if len(res.Errors) > 0 {
				t.Fatalf("parse failed: %v", res.Errors)
			}
			// Conclusion is (x = <literal>); pull out the rhs.
			concl := res.Prop.Conclusion()
			_, rhs, ok := core.MatchesEQ(concl)
			if !ok {
				t.Fatalf("conclusion not an equality: %s", concl.AlphaKey())
			}
			if rhs.AlphaKey() != c.expected.AlphaKey() {
				t.Errorf("literal mismatch for %q\n  got:  %s\n  want: %s",
					c.text, rhs.AlphaKey(), c.expected.AlphaKey())
			}
		})
	}
}

func coreApp(f core.Term, args ...core.Term) core.Term {
	r := f
	for _, a := range args {
		r = core.Apply(r, a)
	}
	return r
}

func parseReal(t *testing.T, s string, vars map[string]core.HolType, expected core.HolType) (core.Term, []InputDiagnostic) {
	t.Helper()
	r := ParseTermTextInScope(s, vars, &ParseScope{}, expected)
	return r.Term, r.Errors
}

// lit parses a bare real literal `&n` (also exercising the `&` prefix alone).
func lit(t *testing.T, s string) core.Term {
	tm, errs := parseReal(t, s, nil, RealType)
	if len(errs) > 0 {
		t.Fatalf("parse %q: %v", s, errs)
	}
	return tm
}

func TestRealParse_AmpAndOverload(t *testing.T) {
	x := core.Var("x", RealType)

	// `&2 * x + &3` builds at type real, dispatching + and * to the real
	// instances and `&n` to real_of_num(<bit-tree n>).
	want := ext.Apply(RealPlusMeta.Term(),
		ext.Apply(RealStarMeta.Term(), lit(t, "&2"), x),
		lit(t, "&3"),
	)
	got, errs := parseReal(t, "&2 * x + &3", map[string]core.HolType{"x": RealType}, RealType)
	if len(errs) > 0 {
		t.Fatalf("parse errors: %v", errs)
	}
	if !got.Type().Equals(RealType) {
		t.Errorf("type = %s, want real", ext.FormatType(got.Type()))
	}
	if !got.AlphaEquals(want) {
		t.Errorf("parse(&2 * x + &3) = %v, want %v", got, want)
	}
}

func TestRealParse_ComparisonIsBool(t *testing.T) {
	// `x < &2` is a real comparison ⇒ bool, head is the real `<`.
	want := ext.Apply(RealLtMeta.Term(), core.Var("x", RealType), lit(t, "&2"))
	got, errs := parseReal(t, "x < &2", map[string]core.HolType{"x": RealType}, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("parse errors: %v", errs)
	}
	if !got.AlphaEquals(want) {
		t.Errorf("parse(x < &2) = %v, want real-< form", got)
	}
}

func TestRealParse_OverloadByType(t *testing.T) {
	// The SAME text dispatches to num or real by operand type.
	numT, errs := parseReal(t, "a + b", map[string]core.HolType{"a": NumType, "b": NumType}, NumType)
	if len(errs) > 0 {
		t.Fatalf("num parse errors: %v", errs)
	}
	if !numT.Type().Equals(NumType) {
		t.Errorf("num: type = %s, want num", ext.FormatType(numT.Type()))
	}
	realT, errs := parseReal(t, "a + b", map[string]core.HolType{"a": RealType, "b": RealType}, RealType)
	if len(errs) > 0 {
		t.Fatalf("real parse errors: %v", errs)
	}
	if !realT.Type().Equals(RealType) {
		t.Errorf("real: type = %s, want real", ext.FormatType(realT.Type()))
	}
}

func TestRealParse_MixedOperandsRejected(t *testing.T) {
	// One real, one num operand ⇒ no dispatch, parse error.
	_, errs := parseReal(t, "x + a", map[string]core.HolType{"x": RealType, "a": NumType}, nil)
	if len(errs) == 0 {
		t.Errorf("mixed real+num operands should error, got none")
	}
}

// TestRealPrint_InfixRoundTrip pins the PRINT side of the real agent surface:
// the const metas carry the REGISTRY names (real_add/real_lt/…, arith.go), but
// applied terms print as the overloaded infix symbols + the `&` coercion
// prefix (ext/format.go's real_* initConstFmt entries + the arity-1 template
// branch of formatTermImpl), and the printed text re-parses alpha-equal — the
// parser re-resolves each symbol to the real instance by operand type, the
// inverse of the dispatch the TestRealParse_* cases above pin.
func TestRealPrint_InfixRoundTrip(t *testing.T) {
	scope := map[string]core.HolType{"x": RealType, "y": RealType, "k": NumType}
	cases := []struct {
		text string
		typ  core.HolType
		want string // exact FormatTermForParser output — the agent surface
	}{
		{"&2 * x + &3", RealType, "(&2 * x) + &3"},
		{"x + y", RealType, "x + y"},
		{"x < y", core.TypeBool(), "x < y"},
		{"x <= &5", core.TypeBool(), "x ≤ &5"},
		{"x > y", core.TypeBool(), "x > y"},
		{"x >= y", core.TypeBool(), "x ≥ y"},
		{"&k + x", RealType, "&k + x"},             // coerced num VAR
		{"&(k + 2) * x", RealType, "&(k + 2) * x"}, // coerced compound num term
	}
	for _, c := range cases {
		orig, errs := parseReal(t, c.text, scope, c.typ)
		if len(errs) > 0 {
			t.Fatalf("parse %q: %v", c.text, errs)
		}
		printed := ext.FormatTermForParser(orig)
		if printed != c.want {
			t.Errorf("%q prints as %q, want %q", c.text, printed, c.want)
		}
		back, errs := parseReal(t, printed, scope, c.typ)
		if len(errs) > 0 {
			t.Fatalf("re-parse %q: %v", printed, errs)
		}
		if !back.AlphaEquals(orig) {
			t.Errorf("round-trip broke: %q → %q → %v (≠ original)", c.text, printed, back)
		}
	}
}

// The int (ℤ) half of the DSL surface: three-way operator dispatch (the int
// instance joins num/real), the unary `-` negation prefix (int_neg/real_neg),
// and the type-directed `&` coercion (`&n` resolves int_of_num vs real_of_num by
// context). Mirrors the real-surface tests in arith_test.go. Subtraction is
// real_sub/int_sub (TOTAL), distinct from num's monus.

// ilit parses an int literal `&n` (forcing the int target via the expected type)
// — the int twin of arith_test.go's real `lit`.
func ilit(t *testing.T, s string) core.Term {
	t.Helper()
	tm, errs := parseReal(t, s, nil, IntType)
	if len(errs) > 0 {
		t.Fatalf("parse %q (int): %v", s, errs)
	}
	return tm
}

func TestIntParse_OperatorsAndNeg(t *testing.T) {
	sc := map[string]core.HolType{"x": IntType, "y": IntType}
	x := core.Var("x", IntType)
	y := core.Var("y", IntType)
	cases := []struct {
		text string
		typ  core.HolType
		want core.Term
	}{
		{"x + y", IntType, ext.Apply(IntPlusMeta.Term(), x, y)},
		{"x - y", IntType, ext.Apply(IntSubMeta.Term(), x, y)}, // TOTAL int_sub, not monus
		{"x * y", IntType, ext.Apply(IntStarMeta.Term(), x, y)},
		{"x <= y", core.TypeBool(), ext.Apply(IntLeMeta.Term(), x, y)},
		{"x < y", core.TypeBool(), ext.Apply(IntLtMeta.Term(), x, y)},
		{"x >= y", core.TypeBool(), ext.Apply(IntGeMeta.Term(), x, y)},
		{"x > y", core.TypeBool(), ext.Apply(IntGtMeta.Term(), x, y)},
		{"-x", IntType, ext.Apply(IntNegMeta.Term(), x)},
		{"x - &2", IntType, ext.Apply(IntSubMeta.Term(), x, ilit(t, "&2"))},
		{"-x + y", IntType, ext.Apply(IntPlusMeta.Term(), ext.Apply(IntNegMeta.Term(), x), y)},
	}
	for _, c := range cases {
		got, errs := parseReal(t, c.text, sc, c.typ)
		if len(errs) > 0 {
			t.Fatalf("parse %q: %v", c.text, errs)
		}
		if !got.AlphaEquals(c.want) {
			t.Errorf("parse %q = %v, want %v", c.text, got, c.want)
		}
	}
}

// TestIntParse_TypeDirectedAmp pins the type-directed `&`: a bare `&n` defaults
// to real_of_num, but resolves to int_of_num when its sibling operand (or an
// int expected type) fixes the domain.
func TestIntParse_TypeDirectedAmp(t *testing.T) {
	sc := map[string]core.HolType{"x": IntType}
	x := core.Var("x", IntType)

	// Anchored by an int sibling, in either order, and across a comparison.
	anchored := []struct {
		text string
		typ  core.HolType
		want core.Term
	}{
		{"x + &2", IntType, ext.Apply(IntPlusMeta.Term(), x, ilit(t, "&2"))},
		{"&2 + x", IntType, ext.Apply(IntPlusMeta.Term(), ilit(t, "&2"), x)},
		{"x <= &3", core.TypeBool(), ext.Apply(IntLeMeta.Term(), x, ilit(t, "&3"))},
	}
	for _, c := range anchored {
		got, errs := parseReal(t, c.text, sc, c.typ)
		if len(errs) > 0 {
			t.Fatalf("parse %q: %v", c.text, errs)
		}
		if !got.AlphaEquals(c.want) {
			t.Errorf("parse %q = %v, want int_of_num form %v", c.text, got, c.want)
		}
	}

	// All-literal under an int expectation: the int domain threads down through
	// the nested sum, so both `&` resolve to int_of_num.
	gotInt, errs := parseReal(t, "&2 + &3", nil, IntType)
	if len(errs) > 0 {
		t.Fatalf("parse &2+&3 (int): %v", errs)
	}
	wantInt := ext.Apply(IntPlusMeta.Term(), ilit(t, "&2"), ilit(t, "&3"))
	if !gotInt.AlphaEquals(wantInt) {
		t.Errorf("&2+&3 at int = %v, want int_of_num form", gotInt)
	}

	// All-literal with NO int context defaults to real (backward-compatible).
	gotReal, errs := parseReal(t, "&2 + &3", nil, RealType)
	if len(errs) > 0 {
		t.Fatalf("parse &2+&3 (real): %v", errs)
	}
	if !gotReal.Type().Equals(RealType) {
		t.Errorf("&2+&3 with no context: type %s, want real (default)", ext.FormatType(gotReal.Type()))
	}
}

// TestIntParse_ExplicitOfNum: the explicit `int_of_num(n)` literal form (the
// printed, round-trip-safe shape) parses without an int anchor — int_of_num is
// in the default scope.
func TestIntParse_ExplicitOfNum(t *testing.T) {
	got, errs := parseReal(t, "int_of_num(2) + int_of_num(3)", nil, IntType)
	if len(errs) > 0 {
		t.Fatalf("parse explicit int_of_num: %v", errs)
	}
	want := ext.Apply(IntPlusMeta.Term(), ilit(t, "&2"), ilit(t, "&3"))
	if !got.AlphaEquals(want) {
		t.Errorf("explicit int_of_num sum = %v, want %v", got, want)
	}
}

// TestIntPrint_InfixRoundTrip: int terms print as the overloaded infix symbols
// with int literals as the EXPLICIT `int_of_num(n)` (not `&n`, which re-parses
// to real), and the printed text re-parses alpha-equal.
func TestIntPrint_InfixRoundTrip(t *testing.T) {
	sc := map[string]core.HolType{"x": IntType, "y": IntType}
	cases := []struct {
		text string
		typ  core.HolType
		want string
	}{
		{"x + y", IntType, "x + y"},
		{"x - y", IntType, "x - y"},
		{"-x", IntType, "-x"},
		{"x + &2", IntType, "x + int_of_num(2)"}, // int literal prints explicit
		{"x <= &3", core.TypeBool(), "x ≤ int_of_num(3)"},
		{"x > y", core.TypeBool(), "x > y"},
		// all-literal int (no var anchor) — explicit int_of_num keeps it
		// unambiguous on re-parse where infix `&` would default to real.
		{"int_of_num(2) + int_of_num(3)", IntType, "int_of_num(2) + int_of_num(3)"},
	}
	for _, c := range cases {
		orig, errs := parseReal(t, c.text, sc, c.typ)
		if len(errs) > 0 {
			t.Fatalf("parse %q: %v", c.text, errs)
		}
		printed := ext.FormatTermForParser(orig)
		if printed != c.want {
			t.Errorf("%q prints as %q, want %q", c.text, printed, c.want)
		}
		back, errs := parseReal(t, printed, sc, c.typ)
		if len(errs) > 0 {
			t.Fatalf("re-parse %q: %v", printed, errs)
		}
		if !back.AlphaEquals(orig) {
			t.Errorf("round-trip broke: %q → %q → %v (≠ original)", c.text, printed, back)
		}
	}
}

// TestIntPrint_QuantifiedStatementShape: int statements quantify their
// vars (`∀y:int.∀x:int. …`), so the typed binders anchor the infix re-parse.
// Pins that a full int prop in the int_lt/int_le shape round-trips through the
// infix printer (the emit concern the README flags).
func TestIntPrint_QuantifiedStatementShape(t *testing.T) {
	// int_lt's normalized statement, written at the agent surface (≤/< infix).
	text := "∀y:int.∀x:int. (¬(y <= x) ⇔ (x < y))"
	res := ParsePropText(text)
	if len(res.Errors) > 0 {
		t.Fatalf("parse %q: %v", text, res.Errors)
	}
	orig := res.Prop.Conclusion()
	printed := ext.FormatTermForParser(orig)
	back := ParsePropText(printed)
	if len(back.Errors) > 0 {
		t.Fatalf("re-parse %q: %v", printed, back.Errors)
	}
	if !back.Prop.Conclusion().AlphaEquals(orig) {
		t.Errorf("quantified int round-trip broke:\n  %q\n→ %q\n→ not alpha-equal", text, printed)
	}
}

// TestRealSubNeg_Surface: the symmetric real_sub/real_neg surface (added with
// the int work). `-` on real is real_sub (TOTAL), the unary `-` is real_neg, and
// both round-trip.
func TestRealSubNeg_Surface(t *testing.T) {
	sc := map[string]core.HolType{"x": RealType, "y": RealType}
	x := core.Var("x", RealType)
	y := core.Var("y", RealType)
	cases := []struct {
		text string
		typ  core.HolType
		want core.Term
		show string
	}{
		{"x - y", RealType, ext.Apply(RealSubMeta.Term(), x, y), "x - y"},
		{"-x", RealType, ext.Apply(RealNegMeta.Term(), x), "-x"},
		{"x - &2", RealType, ext.Apply(RealSubMeta.Term(), x, lit(t, "&2")), "x - &2"},
	}
	for _, c := range cases {
		got, errs := parseReal(t, c.text, sc, c.typ)
		if len(errs) > 0 {
			t.Fatalf("parse %q: %v", c.text, errs)
		}
		if !got.AlphaEquals(c.want) {
			t.Errorf("parse %q = %v, want %v", c.text, got, c.want)
		}
		if printed := ext.FormatTermForParser(got); printed != c.show {
			t.Errorf("%q prints as %q, want %q", c.text, printed, c.show)
		}
	}
}

// TestNumMinus_StillMonus: num `-` is unchanged (truncated monus / NatMinusMeta),
// NOT routed to the new total-subtraction handling.
func TestNumMinus_StillMonus(t *testing.T) {
	sc := map[string]core.HolType{"a": NumType, "b": NumType}
	got, errs := parseReal(t, "a - b", sc, NumType)
	if len(errs) > 0 {
		t.Fatalf("parse num a-b: %v", errs)
	}
	want := ext.Apply(NatMinusMeta.Term(), core.Var("a", NumType), core.Var("b", NumType))
	if !got.AlphaEquals(want) {
		t.Errorf("num a-b = %v, want monus NatMinus form", got)
	}
}

// TestDividesInfix pins the `∣` (U+2223) divisibility surface: dispatched
// to nat_divides / int_divides by operand type (arithOperator), relational
// precedence (`d ∣ m * n` is `d ∣ (m * n)`), rejected for real operands,
// and round-trips through the printer's infix template. NOT the ASCII
// pipe: `|` stays the set-builder separator.
func TestDividesInfix(t *testing.T) {
	d := core.Var("d", NumType)
	n := core.Var("n", NumType)
	xi := core.Var("x", IntType)
	yi := core.Var("y", IntType)

	// num operands → nat_divides.
	got, errs := parseReal(t, "d ∣ n",
		map[string]core.HolType{"d": NumType, "n": NumType}, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("num ∣ parse: %v", errs)
	}
	if want := ext.Apply(NatDividesMeta.Term(), d, n); !got.AlphaEquals(want) {
		t.Errorf("num ∣ built %v, want %v", got, want)
	}

	// int operands → int_divides.
	got, errs = parseReal(t, "x ∣ y",
		map[string]core.HolType{"x": IntType, "y": IntType}, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("int ∣ parse: %v", errs)
	}
	if want := ext.Apply(IntDividesMeta.Term(), xi, yi); !got.AlphaEquals(want) {
		t.Errorf("int ∣ built %v, want %v", got, want)
	}

	// Relational precedence: `d ∣ m * n` = nat_divides(d, m*n).
	m := core.Var("m", NumType)
	got, errs = parseReal(t, "d ∣ m * n",
		map[string]core.HolType{"d": NumType, "m": NumType, "n": NumType}, core.TypeBool())
	if len(errs) > 0 {
		t.Fatalf("precedence parse: %v", errs)
	}
	if want := ext.Apply(NatDividesMeta.Term(), d,
		ext.Apply(NatStarMeta.Term(), m, n)); !got.AlphaEquals(want) {
		t.Errorf("precedence built %v, want %v", got, want)
	}

	// Real operands rejected (no real instance registered).
	_, errs = parseReal(t, "a ∣ b",
		map[string]core.HolType{"a": RealType, "b": RealType}, core.TypeBool())
	if len(errs) == 0 {
		t.Errorf("real ∣ must be rejected")
	}

	// Print → parse round-trips (num, int, and inside a set-builder —
	// the ∣/| codepoint split keeps the brace grammar unambiguous). The
	// set-builder binder carries `:num`: an UNANNOTATED binder under an
	// arith-op predicate is a pre-existing inference boundary (`{k | k <
	// n}` fails identically) — untyped-binder inference doesn't flow
	// through the arithOperator dispatch, only through polymorphic-meta
	// unification (∈-family).
	assertRoundTrip(t, "∀d:num.∀n:num.(d ∣ n)")
	assertRoundTrip(t, "∀x:int.∀y:int.((x ∣ y) ⇒ (x ∣ y))")
	assertRoundTrip(t, "∀n:num.∀s:(num → bool).(s = {d:num | d ∣ n})")
}
