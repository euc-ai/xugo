// Tests for the abbreviation table (abbreviation.go): the «Name»
// lexeme, expansion before name resolution, the capture refusal and
// the leading-binder exemption.
package dsl

import (
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func mustTable(t *testing.T, abbrs Abbrev) *AbbreviationTable {
	t.Helper()
	table, err := ParseAbbreviations(abbrs)
	require.NoError(t, err)
	return table
}

// propOf parses text with no abbreviations, as the comparison target.
func propOf(t *testing.T, text string) core.Prop {
	t.Helper()
	res := ParsePropText(text)
	require.Empty(t, res.Errors, "%s", text)
	return res.Prop
}

func TestAbbreviationExpandsInStatement(t *testing.T) {
	table := mustTable(t, Abbrev{{Name: "R", Text: "x + 1"}})
	scope := &ParseScope{Abbreviations: table, AbbreviationBinders: map[string]bool{"x": true}}
	res := ParsePropTextInScope("∀x:num. «R» = x + 1", scope)
	require.Empty(t, res.Errors)
	assert.True(t, res.Prop.AlphaEquals(propOf(t, "∀x:num. x + 1 = x + 1")))
}

func TestAbbreviationNestedEntries(t *testing.T) {
	table := mustTable(t, Abbrev{
		{Name: "S", Text: "suc(x)"},
		{Name: "R", Text: "«S» + «S»"},
	})
	scope := &ParseScope{Abbreviations: table, AbbreviationBinders: map[string]bool{"x": true}}
	res := ParsePropTextInScope("∀x:num. «R» = «R»", scope)
	require.Empty(t, res.Errors)
	assert.True(t, res.Prop.AlphaEquals(propOf(t, "∀x:num. suc(x) + suc(x) = suc(x) + suc(x)")))
	assert.Equal(t, []string{"S", "R"}, table.Names())
}

func TestAbbreviationAsHeadAndField(t *testing.T) {
	// An abbreviation is an atom: applied, juxtaposed, a field read off it.
	table := mustTable(t, Abbrev{{Name: "f", Text: "suc"}})
	scope := &ParseScope{Abbreviations: table}
	res := ParseTermTextInScope("«f»(«f»(x))", map[string]core.HolType{"x": NumType}, scope, nil)
	require.Empty(t, res.Errors)
	want := ParseTermText("suc(suc(x))", map[string]core.HolType{"x": NumType}, nil)
	require.Empty(t, want.Errors)
	assert.True(t, res.Term.Equals(want.Term))
}

// Join reads two tables as one: an entry both hold, one name with one
// text however it is laid out over lines, is read once, where the
// first table has it; an entry of the second may spell the first's; one
// name with two texts is refused. Extend, a table read under another,
// refuses a name both declare whatever its text.
func TestAbbreviationTableJoin(t *testing.T) {
	parent := Abbrev{{Name: "S", Text: "suc(x)"}}
	left := mustTable(t, append(parent, Abbreviation{Name: "L", Text: "«S» + 1"}))
	right := append(Abbrev{{Name: "S", Text: "suc(\n\tx)"}}, Abbreviation{Name: "R", Text: "«S» + «L»"})

	joined, err := left.Join(right)
	require.NoError(t, err)
	assert.Equal(t, []string{"S", "L", "R"}, joined.Names())
	res := ParseTermTextInScope("«R»", map[string]core.HolType{"x": NumType}, &ParseScope{Abbreviations: joined}, nil)
	require.Empty(t, res.Errors)
	want := ParseTermText("suc(x) + (suc(x) + 1)", map[string]core.HolType{"x": NumType}, nil)
	require.Empty(t, want.Errors)
	assert.True(t, res.Term.Equals(want.Term))

	same, err := left.Join(parent)
	require.NoError(t, err)
	assert.Same(t, left, same, "a table that adds nothing is the table")

	var none *AbbreviationTable
	alone, err := none.Join(parent)
	require.NoError(t, err)
	assert.Equal(t, []string{"S"}, alone.Names())

	_, err = left.Join(Abbrev{{Name: "S", Text: "x"}})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "abbreviation «S» is declared by two of the tables read, as `suc(x)` and as `x`")

	_, err = left.Extend(parent)
	require.Error(t, err)
	assert.Contains(t, err.Error(), "declared twice")
}

func TestAbbreviationTableRefusals(t *testing.T) {
	_, err := ParseAbbreviations(Abbrev{{Name: "R", Text: "«S» + 1"}, {Name: "S", Text: "x"}})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "«R» spells «S», which is not declared before it")

	_, err = ParseAbbreviations(Abbrev{{Name: "R", Text: "x"}, {Name: "R", Text: "y"}})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "declared twice")

	_, err = ParseAbbreviations(Abbrev{{Name: "", Text: "x"}})
	require.Error(t, err)

	_, err = ParseAbbreviations(Abbrev{{Name: "R", Text: "x +"}})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "abbreviation «R»")
}

func TestAbbreviationShortConstantApplication(t *testing.T) {
	for text, want := range map[string]bool{
		"polynomial_degree(p)":                  true,
		"free_algebra(ι, R)":                    true,
		"left_cosets(G.carrier, n)":             true,
		"monoid_pow(R.mul, R.one, 2)":           true,
		"lattice_pair(R, A₀, A₁, V)":            false,
		"curve_over_line(L, k, t, A₀, A₁, A₀₁)": false,
		"restrict_ring(field_ring(L), k)":       false,
		"restrict_ring(«ring», k)":              false,
		"x + y":                                 false,
		"R":                                     false,
		"𝕌⟨A:num⟩":                              false,
		"{x:num | x < n}":                       false,
		"λr:num. r * r":                         false,
	} {
		got, err := IsShortConstantApplication(text)
		require.NoError(t, err, text)
		assert.Equal(t, want, got, text)
	}
	_, err := IsShortConstantApplication("f(x,")
	require.Error(t, err)
}

func TestAbbreviationUnknownName(t *testing.T) {
	res := ParsePropText("∀x:num. «R» = x")
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "no abbreviation table is in scope")

	table := mustTable(t, Abbrev{{Name: "S", Text: "x"}})
	res = ParsePropTextInScope("∀x:num. «R» = x", &ParseScope{Abbreviations: table})
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "«R» is not an abbreviation of this statement (declared: «S»)")
}

func TestAbbreviationCaptureRefused(t *testing.T) {
	table := mustTable(t, Abbrev{{Name: "R", Text: "x + 1"}})
	// The claim door: no leading binder is the statement's, so a text
	// that binds x rebinds what «R» spells.
	res := ParsePropTextInScope("∀x:num. «R» = x", &ParseScope{Abbreviations: table})
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "«R» spells x, which a binder of this text rebinds")

	// The statement door: its own leading ∀x is what R is written over.
	statement := &ParseScope{Abbreviations: table, AbbreviationBinders: map[string]bool{"x": true}}
	res = ParsePropTextInScope("∀x:num. ∀y:num. «R» = y", statement)
	require.Empty(t, res.Errors)
	// An inner binder of the same name is a capture even there.
	res = ParsePropTextInScope("∀x:num. ∃x:num. «R» = x", statement)
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "rebinds")
	// A leading binder the statement does not own is not exempt.
	res = ParsePropTextInScope("∀y:num. ∀x:num. «R» = y", &ParseScope{Abbreviations: table, AbbreviationBinders: map[string]bool{"y": true}})
	require.NotEmpty(t, res.Errors)
}

func TestAbbreviationNameIsVerbatim(t *testing.T) {
	// A keyword, a subscript: nothing inside the guillemets is rewritten.
	table := mustTable(t, Abbrev{{Name: "and", Text: "x"}, {Name: "R₀", Text: "suc(x)"}})
	scope := &ParseScope{Abbreviations: table, AbbreviationBinders: map[string]bool{"x": true}}
	res := ParsePropTextInScope("∀x:num. «and» = x ∧ «R₀» = suc(x)", scope)
	require.Empty(t, res.Errors)
	assert.True(t, res.Prop.AlphaEquals(propOf(t, "∀x:num. x = x ∧ suc(x) = suc(x)")))
}

func TestAbbreviationLexErrors(t *testing.T) {
	res := ParsePropText("∀x:num. «R = x")
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "unterminated abbreviation")
	res = ParsePropText("∀x:num. «» = x")
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "empty abbreviation")
}

func TestFormatStmtTextKeepsAbbreviation(t *testing.T) {
	got, err := FormatStmtText("∀x:num.((«R» + 1) = x)")
	require.NoError(t, err)
	assert.Equal(t, "∀x:num. «R» + 1 = x", got)
	got, err = FormatStmtText("«f»(x, «g».add)")
	require.NoError(t, err)
	assert.Equal(t, "«f»(x, «g».add)", got)
}

// An abbreviation of a partial application, applied, expands to the
// one application the author would have written out, and the output
// door folds it back.
func TestAbbreviationPartialApplication(t *testing.T) {
	table := Abbrev{{Name: "Pair", Text: "g(r, a)"}}
	fn := core.MakeFun(NumType, core.MakeFun(NumType, core.MakeFun(NumType, NumType)))
	ctx := map[string]core.HolType{"g": fn, "r": NumType, "a": NumType, "m": NumType}
	parsed, err := ParseAbbreviations(table)
	require.NoError(t, err)
	short := ParseTermTextInScope("«Pair»(m)", ctx, &ParseScope{Abbreviations: parsed}, nil)
	long := ParseTermText("g(r, a, m)", ctx, nil)
	require.Empty(t, short.Errors)
	require.Empty(t, long.Errors)
	assert.True(t, short.Term.Equals(long.Term))
	assert.Equal(t, "«Pair»(m)", ext.PrintTerm(FoldAbbreviations(long.Term, parsed.Terms(ctx, nil))))
}

// An abbreviation whose text is a λ, applied, reads as the body at the
// arguments — the term the author abbreviated, written out at them —
// and the output door folds the instance back to the application.
func TestAbbreviationLambdaApplication(t *testing.T) {
	pred := core.MakeFun(NumType, core.TypeBool())
	ctx := map[string]core.HolType{"P": pred, "J": pred, "m": NumType, "w": NumType}
	parsed, err := ParseAbbreviations(Abbrev{
		{Name: "HasPP", Text: "λH:(num → bool). ∃x:num. H(x) ∧ P(x)"},
		{Name: "Both", Text: "λa:num. λb:num. P(a) ∧ J(b)"},
	})
	require.NoError(t, err)
	scope := &ParseScope{Abbreviations: parsed}
	short := ParseTermTextInScope("«HasPP»(J)", ctx, scope, nil)
	long := ParseTermText("∃x:num. J(x) ∧ P(x)", ctx, nil)
	require.Empty(t, short.Errors)
	require.Empty(t, long.Errors)
	assert.True(t, short.Term.AlphaEquals(long.Term), "got %s", ext.PrintTerm(short.Term))
	// The capture-avoiding substitution: the argument spells the body's
	// binder; the λ argument is applied where the body applies H, so no
	// redex is left.
	captured := ParseTermTextInScope("«HasPP»(λx:num. x = m)", ctx, scope, nil)
	require.Empty(t, captured.Errors)
	want := ParseTermText("∃y:num. y = m ∧ P(y)", ctx, nil)
	require.Empty(t, want.Errors)
	assert.True(t, captured.Term.AlphaEquals(want.Term), "got %s", ext.PrintTerm(captured.Term))
	// A redex the text spells is kept as written.
	written := ParseTermTextInScope("(λx:num. x = m)(w)", ctx, scope, nil)
	require.Empty(t, written.Errors)
	_, isApp := written.Term.AsAppliedTerm()
	assert.True(t, isApp, "got %s", ext.PrintTerm(written.Term))
	// Two λ-binders, two arguments; an argument order the body does not
	// take is still the body's.
	both := ParseTermTextInScope("«Both»(m, w)", ctx, scope, nil)
	require.Empty(t, both.Errors)
	wantBoth := ParseTermText("P(m) ∧ J(w)", ctx, nil)
	require.Empty(t, wantBoth.Errors)
	assert.True(t, both.Term.AlphaEquals(wantBoth.Term), "got %s", ext.PrintTerm(both.Term))
	// The fold reads the instances back, a reduced λ argument among them.
	terms := parsed.Terms(ctx, nil)
	assert.Equal(t, "«HasPP»(J)", ext.PrintTerm(FoldAbbreviations(long.Term, terms)))
	assert.Equal(t, "«HasPP»(λy.(y = m))", ext.PrintTerm(FoldAbbreviations(want.Term, terms)))
	assert.Equal(t, "«Both»(m, w)", ext.PrintTerm(FoldAbbreviations(wantBoth.Term, terms)))
	// Not an instance: another predicate in the body's place, a binder
	// mapped to two terms.
	other := ParseTermText("∃x:num. J(x) ∧ J(x)", ctx, nil)
	require.Empty(t, other.Errors)
	assert.Equal(t, ext.PrintTerm(other.Term), ext.PrintTerm(FoldAbbreviations(other.Term, terms)))
	twice := ParseTermText("P(m) ∧ J(m)", ctx, nil)
	require.Empty(t, twice.Errors)
	assert.Equal(t, "«Both»(m, m)", ext.PrintTerm(FoldAbbreviations(twice.Term, terms)))
}

// A fold is made only where it reads back. An entry whose text is a λ,
// applied, reads as its body at the arguments; so the λ a term applies
// as written, the head of a redex, is not folded into the entry's name
// — `«through»(a)` would read as `f(a)` — while the same λ handed whole
// is the name, and the redex's other subterms fold as they do anywhere.
func TestAbbreviationFoldKeepsAnAppliedLambda(t *testing.T) {
	fun := core.MakeFun(core.TypeA(), core.TypeA())
	ctx := map[string]core.HolType{"a": core.TypeA(), "f": fun, "g": core.MakeFun(fun, core.TypeA())}
	table := mustTable(t, Abbrev{
		{Name: "through", Text: "λx:A. f(x)"},
		{Name: "twice", Text: "f(f(a))"},
	})
	scope := &ParseScope{Abbreviations: table}
	terms := table.Terms(ctx, nil)
	readsBack := func(text string) (string, core.Term) {
		t.Helper()
		written := ParseTermText(text, ctx, nil)
		require.Empty(t, written.Errors, "%s", text)
		folded := ext.FormatTermForParser(FoldAbbreviations(written.Term, terms))
		read := ParseTermTextInScope(folded, ctx, scope, nil)
		require.Empty(t, read.Errors, "%s", folded)
		assert.True(t, read.Term.AlphaEquals(written.Term), "%s folds to %s, which reads as %s", text, folded, ext.PrintTerm(read.Term))
		return folded, written.Term
	}

	redex, _ := readsBack("(λx:A. f(x))(a)")
	assert.NotContains(t, redex, "«through»(a)", "the applied λ is not its name applied")

	// The λ handed whole is its name, beside the redex and inside it.
	whole, _ := readsBack("g(λx:A. f(x))")
	assert.Equal(t, "g(«through»)", whole)
	mixed, _ := readsBack("(λx:A. f(x))(f(f(a))) = g(λx:A. f(x))")
	assert.Contains(t, mixed, "«twice»")
	assert.Contains(t, mixed, "g(«through»)")
}

// An entry is generic in the letters it is written at: each use reads
// them afresh, at the types the text around it gives, at the types its
// tie gives, or at the written letters where nothing fixes them.
func TestAbbreviationGenericLetters(t *testing.T) {
	table := mustTable(t, Abbrev{
		{Name: "mem", Text: "λs:(A → bool). λx:A. s(x)"},
		{Name: "memAt", Text: "λx:A. «mem»(λy:A. y = x, x)"},
	})
	generic := &ParseScope{Abbreviations: table, FreshenMetaLetters: true}
	read := func(text string) core.Prop {
		t.Helper()
		res := ParsePropTextInScope(text, generic)
		require.Empty(t, res.Errors, "%s", text)
		return res.Prop
	}
	// One entry at two type pairs, the arguments fixing each use.
	assert.True(t, read("∀s:(A → bool). ∀x:A. ∀r:(B → bool). ∀y:B. «mem»(s, x) ∧ «mem»(r, y)").AlphaEquals(
		propOf(t, "∀s:(A → bool). ∀x:A. ∀r:(B → bool). ∀y:B. s(x) ∧ r(y)")))
	assert.True(t, read("∀n:num. ∀b:bool. «memAt»(n) ∧ «memAt»(b)").AlphaEquals(
		propOf(t, "∀n:num. ∀b:bool. n = n ∧ b = b")))
	// A use nothing fixes reads at the written letter; a tie reads it at
	// the tie's type.
	assert.True(t, read("«mem» = «mem»").AlphaEquals(
		propOf(t, "(λs:(A → bool). λx:A. s(x)) = (λs:(A → bool). λx:A. s(x))")))
	assert.True(t, read("«mem»⟨A:B⟩ = «mem»⟨A:B⟩").AlphaEquals(
		propOf(t, "(λs:(B → bool). λx:B. s(x)) = (λs:(B → bool). λx:B. s(x))")))
	assert.True(t, read("«mem»⟨A:num⟩ = (λs:(num → bool). λx:num. s(x))").AlphaEquals(
		propOf(t, "(λs:(num → bool). λx:num. s(x)) = (λs:(num → bool). λx:num. s(x))")))
	// A tie naming a letter the entry is not written at is refused.
	res := ParsePropTextInScope("«mem»⟨C:num⟩ = «mem»", generic)
	require.NotEmpty(t, res.Errors)
	assert.Contains(t, res.Errors[0].Message, "the entry is written at the letters A, not C")
	// Without FreshenMetaLetters an entry reads at its written letters.
	res = ParsePropTextInScope("∀n:num. «mem»(λy:num. y = n, n)", &ParseScope{Abbreviations: table})
	require.NotEmpty(t, res.Errors)
}

// The fold reads an instance at other letters back, tied where its
// arguments do not fix the letter, and the folded text reads back as the
// term.
func TestAbbreviationFoldGenericLetters(t *testing.T) {
	table := mustTable(t, Abbrev{{Name: "mem", Text: "λs:(A → bool). λx:A. s(x)"}})
	ctx := map[string]core.HolType{
		"r": core.MakeFun(core.MakeVarType("B"), core.TypeBool()),
		"y": core.MakeVarType("B"),
	}
	scope := &ParseScope{Abbreviations: table, FreshenMetaLetters: true}
	terms := table.Terms(ctx, scope)
	applied := ParseTermText("r(y)", ctx, nil)
	require.Empty(t, applied.Errors)
	assert.Equal(t, "«mem»(r, y)", ext.PrintTerm(FoldAbbreviations(applied.Term, terms)))
	bare := ParseTermTextInScope("«mem»⟨A:B⟩", ctx, scope, nil)
	require.Empty(t, bare.Errors)
	folded := ext.PrintTerm(FoldAbbreviations(bare.Term, terms))
	assert.Equal(t, "«mem»⟨A:var:B⟩", folded)
	back := ParseTermTextInScope(folded, ctx, scope, nil)
	require.Empty(t, back.Errors)
	assert.True(t, back.Term.AlphaEquals(bare.Term))
}

func TestAbbreviationFoldRejectsDifferentArgumentTypes(t *testing.T) {
	table := mustTable(t, Abbrev{
		{Name: "Mapped", Text: "λh:(num → num). λp:(bool → num). λi:bool. h(p(i))"},
	})
	ctx := map[string]core.HolType{
		"g": core.MakeFun(core.TypeBool(), NumType),
		"P": core.MakeFun(NumType, core.TypeBool()),
		"n": NumType,
	}
	term := ParseTermText("g(P(n))", ctx, nil)
	require.Empty(t, term.Errors)
	var folded core.Term
	require.NotPanics(t, func() {
		folded = FoldAbbreviations(term.Term, table.Terms(ctx, nil))
	})
	assert.True(t, folded.AlphaEquals(term.Term))
}

// Extend reads entries under a table: the outer entries first, an inner
// entry spelling an outer one, a name both declare refused, and a nil
// outer table the entries alone.
func TestAbbreviationTable_Extend(t *testing.T) {
	outer, err := ParseAbbreviations(Abbrev{{Name: "R", Text: "f(x)"}})
	if err != nil {
		t.Fatal(err)
	}
	merged, err := outer.Extend(Abbrev{{Name: "S", Text: "g(«R»)"}})
	if err != nil {
		t.Fatal(err)
	}
	if got := merged.Names(); len(got) != 2 || got[0] != "R" || got[1] != "S" {
		t.Errorf("merged names %v, want [R S]", got)
	}
	if same, err := outer.Extend(nil); err != nil || same != outer {
		t.Errorf("no entries: want the outer table itself, got %v, %v", same, err)
	}
	if _, err := outer.Extend(Abbrev{{Name: "R", Text: "x"}}); err == nil || !strings.Contains(err.Error(), "one name, one meaning") {
		t.Errorf("a redeclared name: want the refusal, got %v", err)
	}
	var none *AbbreviationTable
	alone, err := none.Extend(Abbrev{{Name: "S", Text: "g(x)"}})
	if err != nil || !alone.Has("S") {
		t.Errorf("a nil outer table: want the entries alone, got %v, %v", alone, err)
	}
}

// An extended table holds the outer table's entries themselves and
// reads only the new ones. What it reads is what one table of all the
// entries reads — the same texts, free names and letters — and the
// outer table is left as it was. A refusal numbers an entry by its
// place in the whole table.
func TestAbbreviationTable_ExtendSharesTheOuterEntries(t *testing.T) {
	outerEntries := Abbrev{{Name: "R", Text: "f(x,\n  y)"}, {Name: "Q", Text: "g(«R», λv:A. v)"}}
	innerEntries := Abbrev{{Name: "S", Text: "h(«Q»,\n  w)"}, {Name: "T", Text: "k(«S», «R», λu:B. u)"}}
	outer, err := ParseAbbreviations(outerEntries)
	require.NoError(t, err)
	merged, err := outer.Extend(innerEntries)
	require.NoError(t, err)
	whole, err := ParseAbbreviations(append(slices.Clone(outerEntries), innerEntries...))
	require.NoError(t, err)

	require.Len(t, merged.entries, 4)
	for i, e := range outer.entries {
		require.Same(t, e, merged.entries[i], "«%s» is the outer table's entry", e.Name)
		require.Same(t, e, merged.byName[e.Name])
	}
	require.Equal(t, whole.Entries(), merged.Entries())
	for i, e := range whole.entries {
		assert.Equal(t, e.frees, merged.entries[i].frees, "«%s»: free names", e.Name)
		assert.Equal(t, e.letters, merged.entries[i].letters, "«%s»: letters", e.Name)
	}
	assert.Equal(t, []string{"R", "Q"}, outer.Names(), "the outer table is left as it was")
	assert.False(t, outer.Has("S"))

	_, err = outer.Extend(Abbrev{{Name: "S", Text: "x"}, {Name: " ", Text: "y"}})
	require.EqualError(t, err, "abbreviation 4 has no name")
	_, err = outer.Extend(Abbrev{{Name: "S", Text: "«U»"}})
	require.ErrorContains(t, err, "«S» spells «U», which is not declared before it")
}
