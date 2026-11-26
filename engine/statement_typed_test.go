package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
)

// TestFormatStatementTyped_RoundTrip pins the statement_typed contract:
// for goals built from fully-annotated text-DSL input, the parse-faithful
// rendering must (a) be produced (ok=true) and (b) re-parse — in the
// scope add-goal's text path parses with — to an α-equal prop.
//
// The case list deliberately includes the class the field exists for:
// two type variables, polymorphic set_member/subset/card/image at mixed
// instantiations, and free variables whose types only the declaration
// prefix can pin. The plain `statement` display drops binder types and
// the declaration prefix, and the single-pass parser then rejects
// `y ∈ t`-shaped applications — statement_typed is the surface that
// round-trips.
func TestFormatStatementTyped_RoundTrip(t *testing.T) {

	cases := []struct {
		name string
		text string
	}{
		{
			name: "two-type-var sequent (SIIG injImpliesSurj class)",
			text: "s:(var:A → bool), t:(var:B → bool), f:(var:A → var:B), y:var:B, finite(s), finite(t), ∀x2:var:A.∀y2:var:A.(((x2 ∈ s) ∧ ((y2 ∈ s) ∧ (f(x2) = f(y2)))) ⇒ (x2 = y2)), card(s) = card(t), y ∈ t, image(f, s) ⊆ t ⊢ ∃x:var:A.((x ∈ s) ∧ (f(x) = y))",
		},
		{
			name: "closed prenex formula with inner quantifiers (SIIG surjImpliesInj class)",
			text: "∀t:(var:B → bool).∀s:(var:A → bool).∀f:(var:A → var:B).∀x:var:A.∀y:var:A.(¬finite(s) ∨ ¬finite(t) ∨ (card(s) ≠ card(t)) ∨ ¬(image(f, s) ⊆ t) ∨ ¬(∀y2:var:B.((y2 ∈ t) ⇒ (∃x2:var:A.((x2 ∈ s) ∧ (f(x2) = y2))))) ∨ ¬(x ∈ s) ∨ ¬(y ∈ s) ∨ (f(x) ≠ f(y)) ∨ (x = y))",
		},
		{
			name: "monomorphic num arithmetic",
			text: "∀m:num.∀n:num.((m + n) = (n + m))",
		},
		{
			name: "free num vars need the declaration prefix",
			text: "a:num, b:num, a = b ⊢ b = a",
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			p := parseEMatchGoal(t, tc.text)

			typed, ok := FormatStatementTyped(p)
			require.True(t, ok, "round-trip must close; renderer output rejected for: %s", tc.text)
			require.NotEmpty(t, typed)

			// Re-read at the add-goal text path's own scope (the
			// statement door of a session bound to no family).
			res := dsl.ParsePropTextInScope(typed, StatementDoorScope(nil))
			require.Empty(t, res.Errors, "statement_typed failed to re-parse: %s", typed)
			require.Equal(t, p.AlphaKey(), res.Prop.AlphaKey(),
				"statement_typed re-parsed to a different α-class:\n  typed: %s", typed)
		})
	}
}

// Record fields remain visible when a symbol would lose its owner,
// and expression receivers survive the session's typed output door.
func TestFormatStatementTyped_RecordFields(t *testing.T) {
	for _, tc := range []struct{ text, reads string }{
		{"∀M N:module_ops(A, B). ∀x y:B. mod_add(M, x, y) = mod_add(N, y, x)",
			"M.add(x, y) = N.add(y, x)"},
		{"∀R:ring_ops(real). ∀x y:real. ring_add(R, x, y) = x + y ∧ ring_neg(R, x) = -x",
			"R.add(x, y) = x + y ∧ R.neg(x) = -x"},
		{"∀P:(num → module_ops(A, B)). ∀n:num. mod_zero(P(n + 1)) ∈ mod_carrier(P(n + 1))",
			"P(n + 1).zero ∈ P(n + 1).carrier"},
		{"∀P:(num → module_ops(A, B)). ∀n:num. ∀x y:B. mod_add(P(n), x, y) = mod_zero(P(n))",
			"P(n).add(x, y) = P(n).zero"},
	} {
		p := parseEMatchGoal(t, tc.text)
		typed, ok := FormatStatementTyped(p)
		require.True(t, ok, tc.text)
		require.Contains(t, typed, tc.reads)
		res := dsl.ParsePropTextInScope(typed, StatementDoorScope(nil))
		require.Empty(t, res.Errors, typed)
		require.Equal(t, p.AlphaKey(), res.Prop.AlphaKey(), typed)
	}
}

// A derived law passes constructor fields as explicit structure
// components; implicit completion must see their types before building.
func TestFormatStatementTyped_RecordReading(t *testing.T) {
	root, ok := registry.ByName("module.RegularModuleOn")
	require.True(t, ok)
	count := 0
	for _, r := range registry.Readables() {
		if r.Root() != root || r.Law.Name != "quotient_group.FirstIsomorphism" {
			continue
		}
		scope := StatementDoorScope(root.Family())
		out, err := dsl.ChapterSpelling(prop.FormatPropForParser(r.Statement), constSyntax(), scope.ImplicitBindings)
		require.NoError(t, err)
		back := dsl.ParsePropTextInScope(out, scope)
		require.Empty(t, back.Errors, out)
		require.Equal(t, r.Statement.AlphaKey(), back.Prop.AlphaKey(), out)
		require.NotContains(t, root.Family().SpellStatement(r.Statement), "var:")
		count++
	}
	require.Positive(t, count, "missing readable FirstIsomorphism")
}

// TestFormatStatementTyped_FoldsTheEncodings: a set-builder and a paired
// lambda read as written, never as the encoding they lower to — also
// where the comprehension's constant carries a type annotation, the
// shape the chapter spelling does not fold back from the machine form
// (`set_comprehension⟨A:B⟩(λGEN%PVAR%35:B. …)`). The text is the goal's
// α-class: it parses back to the goal, the encoding's own binder
// renamed.
func TestFormatStatementTyped_FoldsTheEncodings(t *testing.T) {
	cases := []struct{ name, text, reads string }{
		{
			name:  "three-part set-builder at a second type instance",
			text:  "∀f:(var:A → var:B).∀P:(var:A → bool).({f(x):var:B | x:var:A | P(x)} = image(f, {x:var:A | P(x)}))",
			reads: "{f(x):B | x:A | P(x)} = image(f, {x:A | P(x)})",
		},
		{
			name:  "set-builder under free variables",
			text:  "s:(var:A → bool), f:(var:A → var:B), t:(var:B → bool) ⊢ {x:var:A | (x ∈ s) ∧ (f(x) ∈ t)} ⊆ s",
			reads: "{x:A | x ∈ s ∧ f(x) ∈ t} ⊆ s",
		},
		{
			name:  "paired lambda as an operand",
			text:  "∀g:(var:A → (var:B → var:C)).((λ(x:var:A, y:var:B).g(x, y)) = (λp:prod(var:A, var:B).g(fst(p), snd(p))))",
			reads: "(λ(x:A, y:B). g(x, y)) = ",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			p := parseEMatchGoal(t, tc.text)
			typed, ok := FormatStatementTyped(p)
			require.True(t, ok, "round-trip must close for: %s", tc.text)
			require.Contains(t, typed, tc.reads)
			for _, machine := range []string{"GEN%PVAR", "set_comprehension", "comprehension_spec", "pattern_abstraction"} {
				require.NotContains(t, typed, machine)
			}
			res := dsl.ParsePropTextInScope(typed, StatementDoorScope(nil))
			require.Empty(t, res.Errors, "statement_typed failed to re-parse: %s", typed)
			require.Equal(t, p.AlphaKey(), res.Prop.AlphaKey(), "statement_typed re-parsed to a different α-class: %s", typed)
		})
	}
}

// TestFormatStatementTyped_ConstantLettersAreItsOwn: a statement whose
// own type variable is named like a constant's type letter, with the
// constant at an instance over that variable — composition's letters
// are A, B, C, and `g ∘ f` here is at (num → A) for each of them. The
// door freshens a constant's letters at every occurrence, so it reads
// the print; a check reading them unfreshened takes composition's A
// for the statement's (`arg type … does not match domain`) and would
// serve no text for a statement the door reads.
func TestFormatStatementTyped_ConstantLettersAreItsOwn(t *testing.T) {
	cases := []struct{ name, text string }{
		{
			name: "composition over maps of sequences in the statement's A",
			text: "∀f:((num → var:A) → (num → var:A)).∀g:((num → var:A) → (num → var:A)).(g ∘ f = g ∘ f)",
		},
		{
			name: "composition into the statement's A from a sequence in it",
			text: "∀f:(var:A → var:B).∀x:(num → var:A).∀y:(num → var:B).(f ∘ x = y ⇒ y = f ∘ x)",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			door := dsl.ParsePropTextInScope(tc.text, StatementDoorScope(nil))
			require.Empty(t, door.Errors, "the statement door reads the text")
			typed, ok := FormatStatementTyped(door.Prop)
			require.True(t, ok, "a statement the door reads has a typed text")
			back := dsl.ParsePropTextInScope(typed, StatementDoorScope(nil))
			require.Empty(t, back.Errors, "statement_typed failed to re-parse: %s", typed)
			require.Equal(t, door.Prop.AlphaKey(), back.Prop.AlphaKey(), "statement_typed re-parsed to a different α-class: %s", typed)

			// The reason the scope freshens: read with composition's
			// letters as written, the print does not type.
			unfreshened := StatementDoorScope(nil)
			unfreshened.FreshenMetaLetters = false
			require.NotEmpty(t, dsl.ParsePropTextInScope(prop.FormatPropForParser(door.Prop), unfreshened).Errors,
				"the case no longer exercises the letter collision")
		})
	}
}

// TestFormatStatementTyped_OperatorsAsValues: an operator constant
// standing as a value prints bare — `word_bitwise_binary(k, ∧, x, y)`,
// `word_bitwise_unary(n, ¬, x)`, `insert(s, ∃)` — and a partial
// application of one prints as a prefix call, `*(k)`; the statement
// door reads each as the constant, so the typed text serves and reads
// back. Measured on the whole replay before the parser read them: 114
// goals of the words, binomial, slope and nat_sum chapters had no text.
func TestFormatStatementTyped_OperatorsAsValues(t *testing.T) {
	cases := []struct{ name, text, prints string }{
		{
			name:   "a connective as an argument",
			text:   "∀op:(bool → (bool → bool)).((op = (∧)) ⇒ (op(⊤, ⊤) ⇔ ⊤))",
			prints: "op = ∧",
		},
		{
			name:   "negation as an argument",
			text:   "∀op:(bool → bool).((op = (¬)) ⇒ (op(⊥) ⇔ ⊤))",
			prints: "op = ¬",
		},
		{
			name:   "the quantifier constant as a set of sets",
			text:   "∀s:((real → bool) → bool).((s = (∃)) ⇒ ((λx:real.⊤) ∈ s))",
			prints: "s = ∃",
		},
		{
			name:   "a partial application of multiplication",
			text:   "∀k:num.∀f:(num → num).((f = (*)(k)) ⇒ (f(2) = (k * 2)))",
			prints: "f = *(k)",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			door := dsl.ParsePropTextInScope(tc.text, StatementDoorScope(nil))
			require.Empty(t, door.Errors, "the statement door reads the text: %v", door.Errors)
			typed, ok := FormatStatementTyped(door.Prop)
			require.True(t, ok, "a statement the door reads has a typed text")
			require.Contains(t, typed, tc.prints)
			back := dsl.ParsePropTextInScope(typed, StatementDoorScope(nil))
			require.Empty(t, back.Errors, "statement_typed failed to re-parse: %s", typed)
			require.Equal(t, door.Prop.AlphaKey(), back.Prop.AlphaKey(), "statement_typed re-parsed to a different α-class: %s", typed)
		})
	}
}

// TestFormatStatementTyped_ServedIsWhatTheDoorReads: the check is the
// door's own scope under the same family, so a text is served exactly
// where a session bound to that family reads it. `&0 < &1` has no
// operand that says which domain `&` embeds into: a session bound to no
// family refuses it, and no typed text is served there; one bound to a
// chapter that declares ℝ reads it, and it is served.
func TestFormatStatementTyped_ServedIsWhatTheDoorReads(t *testing.T) {
	var realChapter *registry.Family
	for _, f := range registry.Families() {
		if f.Name == "real/real_order_field" {
			realChapter = f
		}
	}
	require.NotNil(t, realChapter, "real/real_order_field is not registered")
	require.NotNil(t, realChapter.CoerceDomain(), "the chapter declares its numeric domain")

	goal := parseEMatchGoal(t, "real_of_num(0) < real_of_num(1)")
	const text = "&0 < &1"

	require.NotEmpty(t, dsl.ParsePropTextInScope(text, StatementDoorScope(nil)).Errors,
		"a session bound to no family refuses an unanchored `&`")
	typed, ok := FormatStatementTypedUnder(goal, nil)
	require.False(t, ok, "no typed text where the door reads none: %q", typed)

	read := dsl.ParsePropTextInScope(text, StatementDoorScope(realChapter))
	require.Empty(t, read.Errors, "a session bound to a chapter declaring ℝ reads it")
	require.Equal(t, goal.AlphaKey(), read.Prop.AlphaKey())
	typed, ok = FormatStatementTypedUnder(goal, realChapter)
	require.True(t, ok)
	require.Equal(t, text, typed)
}

// TestFormatStatementTyped_NilGoal pins the nil-safety contract.
func TestFormatStatementTyped_NilGoal(t *testing.T) {
	typed, ok := FormatStatementTyped(nil)
	require.False(t, ok)
	require.Empty(t, typed)
}

// A record projection on a Skolem prints its head under the Skolem's
// own spelling — `M₀.carrier`, never `M_0.carrier` beside an `M₀` in
// the same text — in the display, in the typed text and in a
// hypothesis as new_hyps serves it, and M₀'s addition, the one holder
// of `+`, prints as `u + v`; the typed text reads back.
func TestFormatStatementTyped_ProjectionOnASkolem(t *testing.T) {
	goal := parseEMatchGoal(t, "M_0:module_ops(A, B), N_0:set(B), mod_zero(M_0) ∈ N_0 ⊢ N_0 ⊆ mod_carrier(M_0) ∧ (∀u v:B. mod_add(M_0, u, v) ∈ N_0)")
	door := &Spelling{}
	display := door.Prop(goal)
	for _, frag := range []string{"M₀.zero ∈ N₀ ⊢", "N₀ ⊆ M₀.carrier", "u + v ∈ N₀"} {
		require.Contains(t, display, frag, display)
	}
	require.NotContains(t, display, "M_0", display)
	typed, ok := FormatStatementTyped(goal)
	require.True(t, ok)
	require.Contains(t, typed, "M₀.carrier", typed)
	require.NotContains(t, typed, "M_0", typed)
	res := dsl.ParsePropTextInScope(typed, StatementDoorScope(nil))
	require.Empty(t, res.Errors, typed)
	require.Equal(t, goal.AlphaKey(), res.Prop.AlphaKey(), typed)
	require.Equal(t, "M₀.zero ∈ N₀", door.Term(goal.Hyp(0)))
}

// A record's field is printed under its symbol only where the parser
// reads the symbol back as that field. With group_on(G) and
// comm_ring_on(R) resident, G a group on B and R a ring on A, the
// display — whose Skolems carry no types — prints R.add's `+`, which it
// alone holds, and spells R.mul and G.mul, which share `*`, by name;
// the typed text, where the carriers are spelled, gives each its `*`.
// With both records on one carrier (a group beside a field on A) `*`
// would be refused back as bound by two records, and both texts spell
// F.mul and G.mul by name. Every text parses back to its goal in the
// scope a pasted claim is read in.
func TestFormatStatementTyped_SymbolHeldByTwoComponents(t *testing.T) {
	readsBack := func(t *testing.T, goal core.Prop, text string) {
		t.Helper()
		scope := StatementDoorScope(nil)
		scope.Vars = map[string]core.HolType{}
		for _, h := range goal.Hyps() {
			for _, v := range h.Frees(nil) {
				scope.Vars[string(v.Name())] = v.Type()
			}
		}
		scope.ResidentFacts = goal.Hyps()
		res := dsl.ParsePropTextInScope(strings.TrimPrefix(text, "⊢ "), scope)
		require.Empty(t, res.Errors, text)
		require.Equal(t, goal.AlphaKey(), res.Prop.AlphaKey(), text)
	}
	door := &Spelling{}
	two := parseEMatchGoal(t, "G:group_ops(B), R:ring_ops(A), group_on(G), comm_ring_on(R) ⊢ "+
		"∀a b:A. ∀u v:B. ring_add(R, a, b) = ring_add(R, b, a) ∧ ring_mul(R, a, b) = ring_mul(R, b, a) ∧ group_mul(G, u, v) = group_mul(G, v, u)")
	display := door.Prop(two)
	for _, frag := range []string{"a + b = b + a", "R.mul(a, b) = R.mul(b, a)", "G.mul(u, v) = G.mul(v, u)"} {
		require.Contains(t, display, frag, display)
	}
	require.NotContains(t, display, "*", display)
	readsBack(t, two, display)
	typed, ok := FormatStatementTyped(two)
	require.True(t, ok)
	for _, frag := range []string{"a + b = b + a", "a * b = b * a", "u * v = v * u"} {
		require.Contains(t, typed, frag, typed)
	}
	readsBack(t, two, typed)

	one := parseEMatchGoal(t, "G:group_ops(A), F:field_ops(A), group_on(G), field_on(F) ⊢ ∀x y:A. x ∈ group_carrier(G) ∧ y ∈ group_carrier(G) ⇒ "+
		"field_add(F, x, y) = field_add(F, y, x) ∧ field_mul(F, x, y) = field_mul(F, y, x) ∧ group_mul(G, x, y) = group_mul(G, y, x)")
	for _, text := range []string{door.Prop(one), mustTyped(t, one)} {
		for _, frag := range []string{"x + y = y + x", "F.mul(x, y) = F.mul(y, x)", "G.mul(x, y) = G.mul(y, x)"} {
			require.Contains(t, text, frag, text)
		}
		require.NotContains(t, text, "*", text)
		readsBack(t, one, text)
	}
}

func mustTyped(t *testing.T, goal core.Prop) string {
	t.Helper()
	typed, ok := FormatStatementTyped(goal)
	require.True(t, ok)
	return typed
}

// TestFormatStatementTyped_LiftWhereThePositionTypesIt: the chapter
// spelling writes a declared coercion as `&` exactly where the
// statement door types the `&` by its position (ext/dsl/coercion.go),
// and the door's implicit completion lets a `&` stand in a slot an
// earlier argument made the codomain (implicit.go, spellsPrefix) — so
// the served typed text is the chapter's spelling, not the parser
// print, for the shapes the Weil chapters state: a zero and a one
// under a record binder, a lift in a COND branch, a lift under an
// overloaded word.
func TestFormatStatementTyped_LiftWhereThePositionTypesIt(t *testing.T) {
	cases := []struct{ name, text, reads string }{
		{
			name:  "zero and one of polynomial_eval under a field binder",
			text:  "∀M:field_ops(var:A).∀z:complex.(polynomial_eval(complex_add, complex_of_real(&0), complex_mul, complex_of_real(&1), λn:num.complex_of_real(&0), z) = complex_of_real(&0))",
			reads: "polynomial_eval(complex_add, &0, complex_mul, &1, λn:num. &0, z) = &0",
		},
		{
			name:  "a COND branch the text leaves open keeps the lift, the pinned one folds",
			text:  "∀z:complex.∀x:real.(COND(0 < 1, complex_of_real(x), complex_of_real(&0)) = z)",
			reads: "COND(0 < 1, complex_of_real(x), &0) = z",
		},
		{
			name:  "a lift under an overloaded word stays spelled",
			text:  "complex_exp(complex_of_real(&0)) = complex_of_real(&1)",
			reads: "exp(complex_of_real(&0)) = complex_of_real(&1)",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			p := parseEMatchGoal(t, tc.text)
			typed, ok := StatementTypedUnder(p, nil)
			require.True(t, ok, "round-trip must close for: %s", tc.text)
			require.True(t, typed.ChapterSpelling, "the chapter's spelling is served, not the print: %s", typed.Text)
			require.Contains(t, typed.Text, tc.reads)
			res := dsl.ParsePropTextInScope(typed.Text, StatementDoorScope(nil))
			require.Empty(t, res.Errors, "statement_typed failed to re-parse: %s", typed.Text)
			require.Equal(t, p.AlphaKey(), res.Prop.AlphaKey(), "statement_typed re-parsed to a different α-class: %s", typed.Text)
		})
	}
}
