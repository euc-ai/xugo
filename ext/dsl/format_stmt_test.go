package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
)

// termText renders a built conclusion name-faithfully — binder names
// included, so the comparison is exact, not just α-equal.
func termText(res ParseResult) string {
	if res.Prop == nil {
		return "<no prop>"
	}
	return ext.FormatTermForParserInConflictsNameFaithful(res.Prop.Conclusion(), nil)
}

// TestGroupedBinderParse: the grouped multi-binder form desugars to the
// identical proposition as the nested single-binder spelling — same
// binder names, same structure, so downstream Skolem naming and keys
// cannot move.
func TestGroupedBinderParse(t *testing.T) {
	cases := []struct{ grouped, nested string }{
		{"∀m n:num. m + n = n + m",
			"∀m:num.∀n:num.((m + n) = (n + m))"},
		{"∀m n. suc(m) ≤ suc(n) ⇔ m ≤ n",
			"∀m.∀n.((suc(m) ≤ suc(n)) ⇔ (m ≤ n))"},
		{"∃x y:num. x < y",
			"∃x:num.∃y:num.(x < y)"},
		{"∀n m:num. m ≤ n ⇔ ∃d:num. n = m + d",
			"∀n:num.∀m:num.((m ≤ n) ⇔ (∃d:num.(n = (m + d))))"},
	}
	for _, c := range cases {
		g := ParsePropText(c.grouped)
		n := ParsePropText(c.nested)
		if g.Prop == nil {
			t.Fatalf("grouped %q: %v", c.grouped, g.Errors)
		}
		if n.Prop == nil {
			t.Fatalf("nested %q: %v", c.nested, n.Errors)
		}
		gs, ns := termText(g), termText(n)
		if gs != ns {
			t.Errorf("grouped %q ≠ nested %q:\n got  %s\n want %s", c.grouped, c.nested, gs, ns)
		}
	}
}

// TestGroupedBinderEpsilonRejected: ε stays single-binder.
func TestGroupedBinderEpsilonRejected(t *testing.T) {
	res := ParsePropText("∀y:num. (εx z:num. x = z) = y")
	if len(res.Errors) == 0 {
		t.Fatal("εx z. … should be a parse error")
	}
}

// TestFormatStmtText: corpus-representative spellings and their
// canonical forms.
func TestFormatStmtText(t *testing.T) {
	cases := []struct{ in, want string }{
		// Grouped binders + minimal parens + subscripts.
		{"∀m:num.∀n:num.((m + n) = (n + m))",
			"∀m n:num. m + n = n + m"},
		{"∀n:num.∀m:num.((m ≤ n) ⇔ (∃d:num.(n = (m + d))))",
			"∀n m:num. m ≤ n ⇔ ∃d:num. n = m + d"},
		{"∀m:num.∀n:num.∀p:num.(((m + n) ≤ (m + p)) ⇔ (n ≤ p))",
			"∀m n p:num. m + n ≤ m + p ⇔ n ≤ p"},
		{"∀m:num.((m ≤ 0) ⇔ (m = 0))",
			"∀m:num. m ≤ 0 ⇔ m = 0"},
		{"∀m:num.(¬(m < 0))",
			"∀m:num. ¬(m < 0)"},
		// Mixed types don't group; function-type annotations keep parens.
		{"∀P:(num → num).((∃B:num.∀n:num.(P(n) ≤ B)) ⇔ (∃A:num.∃B:num.∀n:num.((n * P(n)) ≤ ((A * n) + B))))",
			"∀P:(num → num). (∃B:num. ∀n:num. P(n) ≤ B) ⇔ ∃A B:num. ∀n:num. n * P(n) ≤ A * n + B"},
		// A ⇒-chain keeps disambiguating parens (parser warns otherwise).
		{"∀m:num.∀p:num.∀n:num.((m ≤ p) ⇒ ((m + n) ≤ (p + n)))",
			"∀m p n:num. m ≤ p ⇒ m + n ≤ p + n"},
		// Conjunction / disjunction precedence.
		{"∀m:num.∀n:num.(((m + n) = 0) ⇔ ((m = 0) ∧ (n = 0)))",
			"∀m n:num. m + n = 0 ⇔ m = 0 ∧ n = 0"},
		{"∀b:num.∀x:num.((x = 0) ∨ (b ≤ (b * x)))",
			"∀b x:num. x = 0 ∨ b ≤ b * x"},
		// ∧ as the right operand of ∨ keeps its parens (warning-free).
		{"∀x:num.((x = 0) ∨ ((0 < x) ∧ (0 ≤ x)))",
			"∀x:num. x = 0 ∨ (0 < x ∧ 0 ≤ x)"},
		// Pair arguments.
		{"∀m:num.∀n:num.(nat_dist((m, n)) = nat_dist((n, m)))",
			"∀m n:num. nat_dist((m, n)) = nat_dist((n, m))"},
		// Composition: right-associative, tighter than `*`; a left
		// grouping keeps its parens.
		{"∀f:(A → A).∀g:(A → A).∀h:(A → A).(((f ∘ (g ∘ h)) = ((f ∘ g) ∘ h)))",
			"∀f g h:(A → A). f ∘ g ∘ h = (f ∘ g) ∘ h"},
		// Subscripted frees in a claim text.
		{"(B_0 ≤ (B_0 * (m_0 + n_0)))",
			"B₀ ≤ B₀ * (m₀ + n₀)"},
		// Sequent form.
		{"(x_0 ≤ y_0), (y_0 ≤ z_0) ⊢ (x_0 ≤ z_0)",
			"x₀ ≤ y₀, y₀ ≤ z₀ ⊢ x₀ ≤ z₀"},
		// Quantifier as a non-tail operand keeps parens.
		{"((∀n:num.((A_0 * n) ≤ B_0)) ⇔ (A_0 = 0))",
			"(∀n:num. A₀ * n ≤ B₀) ⇔ A₀ = 0"},
		// λ binder body.
		{"(mk_real(λu:prod(hreal, hreal).treal_eq(x, u)) = y)",
			"mk_real(λu:prod(hreal, hreal). treal_eq(x, u)) = y"},
		// Idempotence on already-canonical text.
		{"∀m n:num. m + n = n + m",
			"∀m n:num. m + n = n + m"},
	}
	for _, c := range cases {
		got, err := FormatStmtText(c.in)
		if err != nil {
			t.Errorf("FormatStmtText(%q): %v", c.in, err)
			continue
		}
		if got != c.want {
			t.Errorf("FormatStmtText(%q):\n got  %q\n want %q", c.in, got, c.want)
		}
		// The canonical form is a fixed point.
		again, err := FormatStmtText(got)
		if err != nil {
			t.Errorf("FormatStmtText fixed-point (%q): %v", got, err)
		} else if again != got {
			t.Errorf("not idempotent: %q → %q", got, again)
		}
	}
}

// TestFormatStmtTextSemanticIdentity: for corpus-shaped inputs the
// formatted text builds the SAME proposition (exact term print, not
// just α-equal — binder names feed Skolem naming downstream).
func TestFormatStmtTextSemanticIdentity(t *testing.T) {
	inputs := []string{
		"∀m:num.∀n:num.((m + n) = (n + m))",
		"∀n:num.∀m:num.((m < n) ⇔ (∃d:num.(n = (m + suc(d)))))",
		"∀m:num.∀n:num.(((m + n) = 0) ⇔ ((m = 0) ∧ (n = 0)))",
		"∀A:num.∀B:num.((∀n:num.((A * n) ≤ B)) ⇔ (A = 0))",
	}
	for _, in := range inputs {
		out, err := FormatStmtText(in)
		if err != nil {
			t.Errorf("FormatStmtText(%q): %v", in, err)
			continue
		}
		a, b := ParsePropText(in), ParsePropText(out)
		if a.Prop == nil || b.Prop == nil {
			t.Errorf("build failed: %q → %q (%v %v)", in, out, a.Errors, b.Errors)
			continue
		}
		as, bs := termText(a), termText(b)
		if as != bs {
			t.Errorf("semantic drift:\n in   %q → %s\n out  %q → %s", in, as, out, bs)
		}
	}
}

// TestFormatStmtTextSetSugar pins the printer's re-sugaring of the set
// constants the PARSER lowers to bare names. The lowering is total —
// `∅` and a literal `empty_set` parse to the identical node — so without
// re-sugaring the "canonical" form of a set-theory statement spelled
// its constants out, and running the formatter over a set chapter
// turned its mathematics into constant names. Every case here is a
// FIXED POINT: canonical set text must survive formatting unchanged.
func TestFormatStmtTextSetSugar(t *testing.T) {
	fixed := []string{
		"∀s:(A → bool). ∅ ⊆ s",
		"∀s:(A → bool). s ⊆ ∅ ⇔ s = ∅",
		"∀s:(A → bool). s ⊆ 𝕌",
		"∀u:((A → bool) → bool). ∀s:(A → bool). ¬(u = ∅) ∧ (∀t:(A → bool). t ∈ u ⇒ t ⊆ s) ⇒ ⋂u ⊆ s",
		"⋃∅ = ∅",
		"∀s:(A → bool). ⋃{s} = s",
		"∀a b:A. {a, b} = {b, a}",
		"∀n:num. {n} ⊆ 𝕌",
		// insert over a VARIABLE tail is the add-an-element idiom, not a
		// brace literal — it must keep its call form. The empty_set tail is
		// the whole distinction.
		"∀a:A. ∀s:(A → bool). a ∈ insert(a, s)",
		"∀a:A. ∀s t:(A → bool). a ∉ s ∪ t ⇔ a ∉ s ∧ a ∉ t",
		"∀a:A. ∀s:(A → bool). ¬(a ∈ s) ⇒ a ∉ s",
		"∀a:A. ∀s:(A → bool). insert(a, s) = {a} ∪ s",
	}
	for _, in := range fixed {
		got, err := FormatStmtText(in)
		if err != nil {
			t.Errorf("FormatStmtText(%q): %v", in, err)
			continue
		}
		if got != in {
			t.Errorf("set sugar not preserved:\n got  %q\n want %q", got, in)
		}
	}

	// Lowered spellings canonicalize INTO the sugar. `{}` is the parser's
	// own alias for a bare empty_set, so it canonicalizes to `∅`.
	rewrites := []struct{ in, want string }{
		{"∀s:(A → bool). empty_set ⊆ s", "∀s:(A → bool). ∅ ⊆ s"},
		{"∀s:(A → bool). s ⊆ universe", "∀s:(A → bool). s ⊆ 𝕌"},
		{"∀u:((A → bool) → bool). big_intersection(u) ⊆ 𝕌", "∀u:((A → bool) → bool). ⋂u ⊆ 𝕌"},
		{"∀a:A. insert(a, empty_set) = {a}", "∀a:A. {a} = {a}"},
		{"∀s:(A → bool). {} = ∅", "∀s:(A → bool). ∅ = ∅"},
	}
	for _, c := range rewrites {
		got, err := FormatStmtText(c.in)
		if err != nil {
			t.Errorf("FormatStmtText(%q): %v", c.in, err)
			continue
		}
		if got != c.want {
			t.Errorf("FormatStmtText(%q):\n got  %q\n want %q", c.in, got, c.want)
		}
	}

	// An operand the prefix sugar cannot carry keeps the call form:
	// parseSetPrefixOp takes one SPINE and never a parenthesized
	// expression, so `⋃(s ∪ t)` is not a spelling of big_union(s ∪ t).
	got, err := FormatStmtText("∀s t:(A → bool). ⋃(s ∪ t) = ⋃s ∪ ⋃t")
	if err != nil {
		t.Fatalf("FormatStmtText: %v", err)
	}
	if want := "∀s t:(A → bool). big_union(s ∪ t) = ⋃s ∪ ⋃t"; got != want {
		t.Errorf("big-op fallback:\n got  %q\n want %q", got, want)
	}
}

// TestFormatStmtTextQuantifiedConjunct pins the one place the formatter
// deliberately spends a paren against pure minimality: a quantifier that
// is an OPERAND of ∧/∨. The parser does not need it — ∀ binds as far
// right as it can either way — but a reader of a chained `A ∧ B` cannot
// otherwise tell that the binders belong to the last operand rather than
// to the whole conjunction, and proofs reason about exactly that
// grouping (a conjunction pack whose ∀s live under one conjunct is
// name-mapped by that conjunct's binders).
func TestFormatStmtTextQuantifiedConjunct(t *testing.T) {
	cases := []struct{ in, want, why string }{
		{"(finite(e) ∧ (∀x:A.∀s:(A → bool).(finite(s) ⇒ finite(i(x, s)))))",
			"finite(e) ∧ (∀x:A. ∀s:(A → bool). finite(s) ⇒ finite(i(x, s)))",
			"∀ as the right operand of ∧ keeps its parens"},
		{"((s = e) ∨ (∃x:A.∃t:(A → bool).((s = i(x, t)) ∧ finite(t))))",
			"s = e ∨ (∃x:A. ∃t:(A → bool). s = i(x, t) ∧ finite(t))",
			"∃ as the right operand of ∨ keeps its parens"},
		// The boundary: ⇒ and ⇔ are directional, so "everything to the
		// right" is already how their RHS reads. A trailing quantifier
		// there stays bare, as before.
		{"∀P:((A → bool) → bool).(P(e) ⇒ (∀t:(A → bool).(finite(t) ⇒ P(t))))",
			"∀P:((A → bool) → bool). P(e) ⇒ ∀t:(A → bool). finite(t) ⇒ P(t)",
			"∀ trailing a ⇒ stays bare"},
		{"∀s:(A → bool).(finite(s) ⇔ (∀t:(A → bool).(finite(t) ⇒ finite(s))))",
			"∀s:(A → bool). finite(s) ⇔ ∀t:(A → bool). finite(t) ⇒ finite(s)",
			"∀ trailing a ⇔ stays bare"},
	}
	for _, c := range cases {
		got, err := FormatStmtText(c.in)
		if err != nil {
			t.Errorf("FormatStmtText(%q) [%s]: %v", c.in, c.why, err)
			continue
		}
		if got != c.want {
			t.Errorf("FormatStmtText(%q) [%s]\n got: %s\nwant: %s", c.in, c.why, got, c.want)
		}
	}
}

// TestFormatStmtTextSetBuilder: set-builder literals keep (or regain)
// their surface sugar. The lowered form's λ-binder name is
// position-derived (`GEN%PVAR%<open-pos>`), so re-spelling moves it;
// the round-trip comparison canonicalizes exactly that name class and
// no other (canonGenPVars), per parser.go's own α contract for it.
func TestFormatStmtTextSetBuilder(t *testing.T) {
	cases := []struct{ in, want string }{
		// Identity form, typed — the num_segment corpus shape.
		{"∀n:num. {x:num | x ≤ n} = 0 .. n",
			"∀n:num. {x:num | x ≤ n} = 0 .. n"},
		// Identity form, untyped.
		{"∀n:num. {x | x < n} = 0 .. (n - 1)",
			"∀n:num. {x | x < n} = 0 .. n - 1"},
		// Sugar inside an application argument — a binary expansion
		// (comprehension as nat_sum's range).
		{"∀n k:num. nat_mod(n, nat_pow(2, k)) = nat_sum({i:num | i < k}, λi:num. nat_pow(2, i) * nat_mod(nat_div(n, nat_pow(2, i)), 2))",
			"∀n k:num. nat_mod(n, nat_pow(2, k)) = nat_sum({i:num | i < k}, λi:num. nat_pow(2, i) * nat_mod(nat_div(n, nat_pow(2, i)), 2))"},
		// Machine form REGAINS the sugar: the expansion re-sugars, and
		// the re-parse's differently-numbered GEN%PVAR% binder is
		// absorbed by the canonicalized comparison.
		{"finite(set_comprehension(λGEN%PVAR%182:num. ∃m:num. comprehension_spec(GEN%PVAR%182, m < n, m)))",
			"finite({m:num | m < n})"},
		// General three-part form.
		{"{2 * x | x:num | x < n} = s",
			"{2 * x | x:num | x < n} = s"},
	}
	for _, c := range cases {
		got, err := FormatStmtText(c.in)
		if err != nil {
			t.Errorf("FormatStmtText(%q): %v", c.in, err)
			continue
		}
		if got != c.want {
			t.Errorf("FormatStmtText(%q):\n got  %q\n want %q", c.in, got, c.want)
		}
	}
}

// TestFormatStmtTextSetBuilderHandNamed: a set_comprehension whose λ-binder is NOT
// parser-synthesized is outside the α-free class — the matcher declines,
// the raw application form prints, and the comparison stays name-exact.
func TestFormatStmtTextSetBuilderHandNamed(t *testing.T) {
	in := "finite(set_comprehension(λv:num. ∃m:num. comprehension_spec(v, m < n, m)))"
	got, err := FormatStmtText(in)
	if err != nil {
		t.Fatalf("FormatStmtText(%q): %v", in, err)
	}
	if !strings.Contains(got, "set_comprehension") {
		t.Errorf("hand-named λ-binder must keep the raw form, got %q", got)
	}
}

// A field written on a name is one identifier, `M_0.carrier`, and its
// receiver carries the subscript before the dot: the printer renders
// every segment, so a Skolem spells `M₀` whether it stands alone or
// heads a field, and the lexer reads the rendering back.
func TestFormatStmtText_FieldOnASubscriptedName(t *testing.T) {
	cases := []struct{ in, want string }{
		{"∀u:B. M_0.add(u, x_0) = x_0 ∧ N_0 ⊆ M_0.carrier",
			"∀u:B. M₀.add(u, x₀) = x₀ ∧ N₀ ⊆ M₀.carrier"},
		{"P_1(n).zero ∈ S_12.inner.carrier", "P₁(n).zero ∈ S₁₂.inner.carrier"},
	}
	for _, c := range cases {
		got, err := FormatStmtText(c.in)
		if err != nil {
			t.Fatalf("FormatStmtText(%q): %v", c.in, err)
		}
		if got != c.want {
			t.Errorf("FormatStmtText(%q):\n got  %q\n want %q", c.in, got, c.want)
		}
	}
}

// TestFormatStmtTextNestedCoerce: a coercion of a coercion keeps the
// inner one bracketed. Printed bare, `&&n` reads back as `∧` (the ASCII
// rule for `&&`), so the canonical form of a statement holding a real
// number read in ℂ, `&(&n)`, would not parse.
func TestFormatStmtTextNestedCoerce(t *testing.T) {
	for in, want := range map[string]string{
		"&(&n) * y = z":       "&(&n) * y = z",
		"&(&(n + 1)) * y = z": "&(&(n + 1)) * y = z",
		"&(&(-n)) = z":        "&(&(-n)) = z",
	} {
		got, err := FormatStmtText(in)
		if err != nil || got != want {
			t.Errorf("FormatStmtText(%q) = %q (%v), want %q", in, got, err, want)
			continue
		}
		if again, err := FormatStmtText(got); err != nil || again != got {
			t.Errorf("not a fixed point: %q → %q (%v)", got, again, err)
		}
	}
}
