package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
)

func TestChapterSpelling_IntegerLiteralBesideAPartnerThatTypesIt(t *testing.T) {
	// The parser-faithful printers write an integer literal
	// `int_of_num(n)`; the chapter's spelling is `&n` wherever the
	// operator's other operand is int by its own text, and the short
	// text reads back as the statement the long one is.
	syntax := implicitTestScope(t).Syntax
	for _, tc := range []struct{ long, short string }{
		{"∀u:(num → int). int_of_num(0) ≤ u(0)", "∀u:(num → int). &0 ≤ u(0)"},
		{"∀x:int. x + int_of_num(1) ≤ int_of_num(5)", "∀x:int. x + &1 ≤ &5"},
		// Through the sum and the negation a rebuild at int reaches.
		{"∀x:int. int_of_num(1) + int_of_num(2) ≤ x", "∀x:int. &1 + &2 ≤ x"},
		{"∀x:int. -int_of_num(3) + x = int_of_num(0)", "∀x:int. -&3 + x = &0"},
		// The embedding of a num that is not a numeral.
		{"∀x:int. ∀n:num. x * int_of_num(n + 1) ≠ int_of_num(n)", "∀x:int. ∀n:num. x * &(n + 1) ≠ &n"},
		{"∀x:int. int_of_num(2) ∣ x", "∀x:int. &2 ∣ x"},
		{"∀x:int. x ≤ int_of_num(0) ∧ int_of_num(0) ≤ x", "∀x:int. x ≤ &0 ∧ &0 ≤ x"},
		// The base of a power, whose exponent is a num either way.
		{"∀x:int. ∀n:num. x = int_of_num(1) - int_of_num(2) ^ n * int_of_num(n)", "∀x:int. ∀n:num. x = &1 - &2 ^ n * &n"},
		{"∀x:int. ∀n:num. x ^ n ≤ int_of_num(2) ^ n", "∀x:int. ∀n:num. x ^ n ≤ &2 ^ n"},
		// A congruence is never read over ℝ: its literals need no partner.
		{"∀x y n:num. int_of_num(x) ≡ int_of_num(y) (mod int_of_num(n))", "∀x y n:num. &x ≡ &y (mod &n)"},
		{"∀x:int. ∀n:num. x ≡ -int_of_num(1) (mod int_of_num(2) ^ n)", "∀x:int. ∀n:num. x ≡ -&1 (mod &2 ^ n)"},
		// A declared free variable is a partner as a bound one is.
		{"x:int ⊢ x ≤ int_of_num(0)", "x : int ⊢ x ≤ &0"},
		// An argument position is not an operand: only the equation's
		// right side has a partner.
		{"∀f:(int → int). f(int_of_num(0)) = int_of_num(0)", "∀f:(int → int). f(int_of_num(0)) = &0"},
	} {
		long := ParsePropText(tc.long)
		if len(long.Errors) > 0 {
			t.Fatalf("%q: %s", tc.long, long.Errors[0].Message)
		}
		got, err := ChapterSpelling(tc.long, syntax, nil)
		if err != nil {
			t.Fatalf("ChapterSpelling(%q): %v", tc.long, err)
		}
		if got != tc.short {
			t.Errorf("ChapterSpelling(%q) = %q, want %q", tc.long, got, tc.short)
			continue
		}
		back := ParsePropText(got)
		if len(back.Errors) > 0 {
			t.Errorf("%q does not read back: %s", got, back.Errors[0].Message)
			continue
		}
		if !back.Prop.AlphaEquals(long.Prop) {
			t.Errorf("%q reads back as another statement than %q", got, tc.long)
		}
	}
}

func TestChapterSpelling_IntegerLiteralWithNoPartnerKeepsTheLongForm(t *testing.T) {
	// `&0 < &1` is a statement about reals: two literals facing each
	// other have no partner to type them, and neither has a literal
	// under a power or one that is an argument.
	syntax := implicitTestScope(t).Syntax
	for _, text := range []string{
		"int_of_num(0) < int_of_num(1)",
		"int_of_num(1) + int_of_num(2) = int_of_num(3)",
		"∀n:num. ∀w:num. int_of_num(w) ^ n ≤ int_of_num(2) ^ n",
		"∀x:int. ∀n:num. int_rem(x, int_of_num(2) ^ n) = x",
		"∀f:(int → bool). f(int_of_num(0))",
	} {
		got, err := ChapterSpelling(text, syntax, nil)
		if err != nil {
			t.Fatalf("ChapterSpelling(%q): %v", text, err)
		}
		if strings.Contains(got, "&") {
			t.Errorf("ChapterSpelling(%q) = %q: an unanchored literal must stay int_of_num(…)", text, got)
		}
		long, back := ParsePropText(text), ParsePropText(got)
		if len(long.Errors) > 0 || len(back.Errors) > 0 || !back.Prop.AlphaEquals(long.Prop) {
			t.Errorf("%q does not read back as %q", got, text)
		}
	}
}

func TestChapterSpelling_IntegerLiteralBesideAScopeTypedVariable(t *testing.T) {
	// A text printed without declarations leaves its free variables to
	// the scope that reads it; the variable is the literal's partner
	// there as a declared one is.
	syntax := implicitTestScope(t).Syntax
	scope := &ParseScope{Syntax: syntax, Vars: map[string]core.HolType{"x": IntType}}
	const text = "x ≤ int_of_num(0)"
	got, err := ChapterSpelling(text, syntax, nil)
	if err != nil {
		t.Fatalf("ChapterSpelling: %v", err)
	}
	if got != "x ≤ &0" {
		t.Fatalf("ChapterSpelling(%q) = %q, want %q", text, got, "x ≤ &0")
	}
	long, back := ParsePropTextInScope(text, scope), ParsePropTextInScope(got, scope)
	if len(long.Errors) > 0 || len(back.Errors) > 0 || !back.Prop.AlphaEquals(long.Prop) {
		t.Fatalf("%q does not read back as %q under the scope that types x", got, text)
	}
}

func TestChapterSpelling_AVariableNamedAsTheEmbeddingIsNotALiteral(t *testing.T) {
	syntax := implicitTestScope(t).Syntax
	const text = "∀int_of_num:(num → int). ∀x:int. x ≤ int_of_num(0)"
	got, err := ChapterSpelling(text, syntax, nil)
	if err != nil {
		t.Fatalf("ChapterSpelling: %v", err)
	}
	if strings.Contains(got, "&") {
		t.Fatalf("ChapterSpelling(%q) = %q: the bound variable's application is not the embedding", text, got)
	}
}
