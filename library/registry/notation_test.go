package registry

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
)

// parseNotation (define.go): the declared pattern is read over the
// constant's explicit binders — an outfix, an infix or a prefix — and
// every way of getting it wrong is refused at the definition.
func TestParseNotation(t *testing.T) {
	explicit := []string{"n", "u"}
	o, _, err := parseNotation("‖u‖_n", explicit)
	if err != nil {
		t.Fatal(err)
	}
	if o.Open != "‖" || o.Close != "‖" || len(o.Body) != 1 || o.Body[0] != 1 || o.Sub != 0 || o.Arity() != 2 {
		t.Fatalf("‖u‖_n read as %+v", o)
	}
	o, _, err = parseNotation("⟪u, n⟫", explicit)
	if err != nil {
		t.Fatal(err)
	}
	if o.Open != "⟪" || o.Close != "⟫" || len(o.Body) != 2 || o.Body[0] != 1 || o.Body[1] != 0 || o.Sub != -1 {
		t.Fatalf("⟪u, n⟫ read as %+v", o)
	}
	// The infix reads its holes in the constant's argument order; the
	// prefix takes the one explicit binder.
	_, op, err := parseNotation("u + n", explicit)
	if err != nil {
		t.Fatal(err)
	}
	if op.Symbol != "+" || op.Arity() != 2 || op.Args[0] != 1 || op.Args[1] != 0 {
		t.Fatalf("u + n read as %+v", op)
	}
	_, op, err = parseNotation("n • u", explicit)
	if err != nil || op.Symbol != "•" || op.Args[0] != 0 || op.Args[1] != 1 {
		t.Fatalf("n • u read as %+v (%v)", op, err)
	}
	_, op, err = parseNotation("-u", []string{"u"})
	if err != nil || op.Symbol != "-" || op.Arity() != 1 || op.Args[0] != 0 {
		t.Fatalf("-u read as %+v (%v)", op, err)
	}
	// A pointwise definition binds the point after the operation's own
	// arguments; the notation spells the leading binders and leaves it.
	_, op, err = parseNotation("u + v", []string{"u", "v", "i"})
	if err != nil || op.Symbol != "+" || op.Arity() != 2 {
		t.Fatalf("u + v over [u v i] read as %+v (%v)", op, err)
	}
	if _, _, err := parseNotation("u + i", []string{"u", "v", "i"}); err == nil || !strings.Contains(err.Error(), "v is missing") {
		t.Fatalf("u + i over [u v i]: got %v", err)
	}
	// The limit mixfix: `⟶` with its point clause, arity three, the holes
	// read in the notation's order against the constant's own.
	_, op, err = parseNotation("f ⟶ l (at c)", []string{"f", "c", "l"})
	if err != nil || op.Symbol != "⟶" || op.Arity() != 3 || op.Args[0] != 0 || op.Args[1] != 2 || op.Args[2] != 1 {
		t.Fatalf("f ⟶ l (at c) read as %+v (%v)", op, err)
	}
	for pattern, want := range map[string]string{
		"f ⟶ l (at x)":  "not one of the constant's explicit binders",
		"f ⟶ l (mod c)": "limit mixfix",
		"f + l (at c)":  "limit mixfix",
		"f ⟶ l (at f)":  "used twice",
	} {
		if _, _, err := parseNotation(pattern, []string{"f", "c", "l"}); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%q: got %v, want %q", pattern, err, want)
		}
	}
	// The class brackets are an outfix pair: a quotient's class map
	// declares `⁅x⁆`.
	if outfix, _, err := parseNotation("⁅u⁆", []string{"u"}); err != nil || outfix == nil || outfix.Open != "⁅" || outfix.Close != "⁆" {
		t.Fatalf("⁅u⁆ read as %+v (%v)", outfix, err)
	}
	// The white square brackets are an outfix pair, two holes: a closed
	// interval declares `⟦a, b⟧`.
	if outfix, _, err := parseNotation("⟦a, b⟧", []string{"a", "b"}); err != nil || outfix == nil || outfix.Open != "⟦" || outfix.Close != "⟧" || len(outfix.Body) != 2 || outfix.Sub != -1 {
		t.Fatalf("⟦a, b⟧ read as %+v (%v)", outfix, err)
	}
	// The white tortoise shell brackets are an outfix pair, and each of
	// `⟦` and `⟬` closes with `⟧` or `⟭`: the open interval and the two
	// half-open ones are notations of their own, the pair read at the
	// first closing delimiter.
	for pattern, pair := range map[string][2]string{
		"⟬a, b⟭": {"⟬", "⟭"},
		"⟦a, b⟭": {"⟦", "⟭"},
		"⟬a, b⟧": {"⟬", "⟧"},
	} {
		outfix, _, err := parseNotation(pattern, []string{"a", "b"})
		if err != nil || outfix == nil || outfix.Open != pair[0] || outfix.Close != pair[1] || len(outfix.Body) != 2 || outfix.Sub != -1 {
			t.Fatalf("%s read as %+v (%v)", pattern, outfix, err)
		}
	}
	if _, _, err := parseNotation("⟬a, b⟫", []string{"a", "b"}); err == nil || !strings.Contains(err.Error(), "no closing ⟭ or ⟧") {
		t.Fatalf("⟬a, b⟫: got %v", err)
	}
	// The order is an infix a type declares: `x ≤ y`, `x < y`.
	for _, symbol := range []string{"≤", "<"} {
		if _, op, err := parseNotation("x "+symbol+" y", []string{"x", "y"}); err != nil || op == nil || op.Symbol != symbol || op.Args[0] != 0 || op.Args[1] != 1 {
			t.Fatalf("x %s y read as %+v (%v)", symbol, op, err)
		}
	}
	if _, _, err := parseNotation("x ≥ y", []string{"x", "y"}); err == nil {
		t.Fatal("x ≥ y: ≥ is no declarable symbol")
	}
	for pattern, want := range map[string]string{
		"«u»_n":   "outfix",
		"‖u‖":     "leading explicit binders",
		"‖u‖_x":   "not one of the constant's explicit binders",
		"‖u‖_u":   "used twice",
		"‖u‖ n":   "only a `_binder` subscript may follow",
		"‖u, ‖_n": "empty hole",
		"u ∘ n":   "outfix",
		"u + u":   "used twice",
		"u + x":   "not one of the constant's explicit binders",
		"-u":      "n is missing",
	} {
		if _, _, err := parseNotation(pattern, explicit); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%q: got %v, want %q", pattern, err, want)
		}
	}
}

// bigOpOf (define.go): a big operator is declared on a fold over a
// carrier and nothing else.
func TestBigOpOf(t *testing.T) {
	typ := func(text string) core.HolType {
		ty, err := dsl.ParseTypeText(text)
		if err != nil {
			t.Fatalf("type %q: %v", text, err)
		}
		return ty
	}
	b, err := bigOpOf("Σ", typ("(A → bool) → (A → real) → real"))
	if err != nil || b.Symbol != "Σ" || !b.Carrier.Equals(dsl.RealType) {
		t.Fatalf("Σ on sum read as %+v (%v)", b, err)
	}
	if _, err := bigOpOf("Π", typ("(A → bool) → (A → num) → num")); err != nil {
		t.Fatal(err)
	}
	for text, want := range map[string]string{
		"(A → bool) → (A → B) → B":               "type variables",
		"(A → bool) → (B → real) → real":         "not a fold",
		"(A → A → A) → (B → bool) → (B → A) → A": "not a fold",
		"real → real": "not a fold",
	} {
		if _, err := bigOpOf("Σ", typ(text)); err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%s: got %v, want %q", text, err, want)
		}
	}
	if _, err := bigOpOf("∫", typ("(A → bool) → (A → real) → real")); err == nil || !strings.Contains(err.Error(), "not a big operator") {
		t.Errorf("∫: got %v", err)
	}
}

// overloadOf (define.go): a word is a lowercase identifier other than
// the constant's own name, on a constant with no implicit arguments;
// its arity is the constant's full application — zero for a nullary
// constant, whose word is its symbol (`π`).
func TestCoercionOf(t *testing.T) {
	typ := func(text string) core.HolType {
		ty, err := dsl.ParseTypeText(text)
		if err != nil {
			t.Fatal(err)
		}
		return ty
	}
	c, err := coercionOf(typ("real → zz_c"), nil)
	if err != nil || !c.Into.Equals(typ("zz_c")) {
		t.Fatalf("real → zz_c read as %+v (%v)", c, err)
	}
	for _, r := range []struct {
		ty       string
		implicit []string
		want     string
	}{
		{"num → zz_c", nil, "exactly a real"},
		{"zz_c", nil, "exactly a real"},
		{"real → real", nil, "other than real"},
		{"real → real → zz_c", nil, "no further argument"},
		{"real → zz_c", []string{"op"}, "implicit arguments"},
	} {
		if _, err := coercionOf(typ(r.ty), r.implicit); err == nil || !strings.Contains(err.Error(), r.want) {
			t.Errorf("%s %v: got %v, want %q", r.ty, r.implicit, err, r.want)
		}
	}
}

func TestOverloadOf(t *testing.T) {
	ty, err := dsl.ParseTypeText("(A → bool) → (A → real) → real")
	if err != nil {
		t.Fatal(err)
	}
	o, err := overloadOf("sum", "real_sum", ty, nil)
	if err != nil || o.Word != "sum" || o.Arity != 2 || !o.Type.Equals(ty) {
		t.Fatalf("sum on real_sum read as %+v (%v)", o, err)
	}
	real, _ := dsl.ParseTypeText("real")
	if o, err := overloadOf("π", "pi", real, nil); err != nil || o.Arity != 0 || o.Word != "π" {
		t.Fatalf("π on pi read as %+v (%v)", o, err)
	}
	for _, c := range []struct {
		word, name string
		ty         core.HolType
		implicit   []string
		want       string
	}{
		{"Sum", "real_sum", ty, nil, "lowercase identifier"},
		{"real_sum", "real_sum", ty, nil, "own name"},
		{"sum", "real_sum", ty, []string{"add"}, "implicit arguments"},
	} {
		if _, err := overloadOf(c.word, c.name, c.ty, c.implicit); err == nil || !strings.Contains(err.Error(), c.want) {
			t.Errorf("%s on %s: got %v, want %q", c.word, c.name, err, c.want)
		}
	}
}
