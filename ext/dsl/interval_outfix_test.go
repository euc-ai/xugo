package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The intervals: `⟦a, b⟧`, `⟬a, b⟭`, `⟦a, b⟭` and `⟬a, b⟧` — the white
// square brackets and the white tortoise shell brackets, each opening
// closed by either closing, four delimiter pairs and four notations, two
// body holes and no subscript. Toy constants stand in for the intervals.
func intervalOutfixTestScope(t *testing.T) *ParseScope {
	t.Helper()
	ty, err := ParseTypeText("real → real → set(real)")
	if err != nil {
		t.Fatal(err)
	}
	pairs := map[string][2]string{
		"zz_icc": {"⟦", "⟧"},
		"zz_ioo": {"⟬", "⟭"},
		"zz_ico": {"⟦", "⟭"},
		"zz_ioc": {"⟬", "⟧"},
	}
	metas := map[string]core.ConstTermMeta{}
	syntax := testSyntax{}
	for name, pair := range pairs {
		metas[name] = core.MakeConstMeta(core.TermName(name), ty)
		syntax[name] = &ConstSyntax{Outfix: &Outfix{Open: pair[0], Close: pair[1], Body: []int{0, 1}, Sub: -1}}
	}
	setOfReal, err := ParseTypeText("set(real)")
	if err != nil {
		t.Fatal(err)
	}
	return &ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if meta, ok := metas[name]; ok {
				return meta
			}
			if m, ok := ext.InitConstMetaMap().Load(core.TermName(name)); ok {
				return m
			}
			return core.ConstTermMeta{}
		},
		Syntax:             syntax,
		Vars:               map[string]core.HolType{"a": RealType, "b": RealType, "x": RealType, "s": setOfReal},
		StrictResolution:   true,
		FreshenMetaLetters: true,
		CoerceDomain:       RealType,
	}
}

func TestIntervalOutfix_Parse(t *testing.T) {
	scope := intervalOutfixTestScope(t)
	same := func(sugar, plain string) {
		t.Helper()
		a, b := parseImplicit(t, scope, sugar), parseImplicit(t, scope, plain)
		if a.AlphaKey() != b.AlphaKey() {
			t.Fatalf("%q ≠ %q:\n  %s\n  %s", sugar, plain, prop.PrintProp(a), prop.PrintProp(b))
		}
	}
	same("x ∈ ⟦a, b⟧", "x ∈ zz_icc(a, b)")
	same("⟦&0, &1⟧ ⊆ ⟦a - &1, b + &1⟧", "zz_icc(&0, &1) ⊆ zz_icc(a - &1, b + &1)")
	same("s = ⟦-a, a * b⟧", "s = zz_icc(-a, a * b)")
	same("{x | x ∈ ⟦a, b⟧} = ⟦a, b⟧", "{x | x ∈ zz_icc(a, b)} = zz_icc(a, b)")
	// The open interval and the two half-open ones: a notation is its
	// delimiter pair, so one opening delimiter begins two notations.
	same("x ∈ ⟬a, b⟭", "x ∈ zz_ioo(a, b)")
	same("x ∈ ⟦a, b⟭", "x ∈ zz_ico(a, b)")
	same("x ∈ ⟬a, b⟧", "x ∈ zz_ioc(a, b)")
	same("⟬a, b⟭ ⊆ ⟦a, b⟭ ∧ ⟦a, b⟭ ⊆ ⟦a, b⟧ ∧ ⟬a, b⟧ ⊆ ⟦a, b⟧", "zz_ioo(a, b) ⊆ zz_ico(a, b) ∧ zz_ico(a, b) ⊆ zz_icc(a, b) ∧ zz_ioc(a, b) ⊆ zz_icc(a, b)")
	// The round parentheses stay the pair.
	if res := ParseTermTextInScope("(a, b)", nil, scope, nil); len(res.Errors) > 0 || res.Term.Type().Equals(scope.Vars["s"]) {
		t.Fatalf("(a, b) is the pair: %v", res.Errors)
	}
	for _, bad := range []string{"x ∈ ⟦a, b", "x ∈ a, b⟧", "x ∈ ⟦a, b)", "x ∈ ⟬a, b)", "x ∈ (a, b⟭", "x ∈ ⟬a, b⟫"} {
		if res := ParsePropTextInScope(bad, scope); len(res.Errors) == 0 {
			t.Errorf("%q must be refused", bad)
		}
	}
	// The textbook brackets are not lexed; the refusal names the four
	// spellings.
	for _, textbook := range []string{"x ∈ [a, b]", "x ∈ [a, b)", "x ∈ (a, b]", "x ∈ ⟮a, b⟯"} {
		res := ParsePropTextInScope(textbook, scope)
		if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "the intervals are written ⟦a, b⟧, ⟬a, b⟭, ⟦a, b⟭ and ⟬a, b⟧") {
			t.Errorf("%q: the refusal does not name the interval spellings: %v", textbook, res.Errors)
		}
	}
	if res := ParsePropTextInScope("x ∈ ⟦a, b⟧", &ParseScope{Vars: scope.Vars, Syntax: testSyntax{}}); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "no constant in scope declares") {
		t.Fatalf("⟦…⟧ with no declaring constant must be refused: %v", res.Errors)
	}
	// A pair no constant declares is refused though its opening
	// delimiter begins another constant's notation.
	only := &ParseScope{Vars: scope.Vars, ConstResolver: scope.ConstResolver,
		Syntax: testSyntax{"zz_icc": scope.Syntax.ConstSyntax("zz_icc")}}
	if res := ParsePropTextInScope("x ∈ ⟦a, b⟭", only); len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, "⟦…⟭: no constant in scope declares") {
		t.Fatalf("⟦…⟭ beside ⟦a, b⟧ alone must be refused: %v", res.Errors)
	}
}

func TestIntervalOutfix_ChapterSpelling(t *testing.T) {
	scope := intervalOutfixTestScope(t)
	raw := "a:real, b:real, x:real ⊢ x ∈ zz_icc(a, b) ∧ zz_icc(&0, b + &1) = zz_icc(a, a) ∧ " +
		"x ∈ zz_ioo(a, b) ∧ zz_ico(a, b) ⊆ zz_ioc(a, b)"
	out, err := ChapterSpelling(raw, scope.Syntax, nil)
	if err != nil {
		t.Fatal(err)
	}
	for _, frag := range []string{"x ∈ ⟦a, b⟧", "⟦&0, b + &1⟧ = ⟦a, a⟧", "x ∈ ⟬a, b⟭", "⟦a, b⟭ ⊆ ⟬a, b⟧"} {
		if !strings.Contains(out, frag) {
			t.Errorf("chapter spelling lacks %q: %s", frag, out)
		}
	}
	if parseImplicit(t, scope, out).AlphaKey() != parseImplicit(t, scope, raw).AlphaKey() {
		t.Fatalf("the spelling parses to a different statement: %s", out)
	}
	for _, text := range []string{"x ∈ ⟦a, b⟧", "x ∈ ⟬a, b⟭", "x ∈ ⟦a, b⟭", "x ∈ ⟬a, b⟧"} {
		got, err := FormatStmtText(text)
		if err != nil || !strings.Contains(got, text) {
			t.Errorf("FormatStmtText keeps the delimiters: %q (%v)", got, err)
		}
	}
}

// A pair of reals where a set is expected is refused with the open
// interval's spelling: `(a, b)` stays the pair. Another mismatch keeps
// its refusal as it was.
func TestIntervalOutfix_PairWhereASetIsExpected(t *testing.T) {
	scope := intervalOutfixTestScope(t)
	hint := "(a, b) is a pair: the open interval is written ⟬a, b⟭"
	for _, text := range []string{"x ∈ (a, b)", "(a, b) ⊆ s", "s = (a, b)", "(&0, &1) ≠ s", "∀y:real. y ∈ (a, b) ⇒ y < b"} {
		res := ParsePropTextInScope(text, scope)
		if len(res.Errors) == 0 || !strings.Contains(res.Errors[0].Message, hint) {
			t.Errorf("%q: the refusal does not name the open interval: %v", text, res.Errors)
		}
	}
	for _, text := range []string{"x ∈ (0, 1)", "x ∈ a", "s = (a, b, x)"} {
		res := ParsePropTextInScope(text, scope)
		if len(res.Errors) == 0 {
			t.Fatalf("%q must be refused", text)
		}
		if strings.Contains(res.Errors[0].Message, hint) {
			t.Errorf("%q is no pair of reals where a set is expected: %v", text, res.Errors)
		}
	}
}
