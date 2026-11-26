// Tests for the canonical type-variable spelling: bare single
// uppercase letters (`M`) are the canonical DSL form, and the parser
// normalizes the `var:M` spelling to it at AST construction
// (normalizeTypeVarName in parser.go). Both spellings therefore
// produce IDENTICAL ASTs and identical core props, and the statement
// formatter outputs the bare form. Multi-letter names (`var:Repty`),
// Skolem type-vars (`var:?94099` / bare `?94099`) and non-uppercase
// names (`var:a`) are NOT normalized and keep their spelling.
package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// assertParseIdentical parses both spellings scope-free and asserts
// they are the SAME statement at every level: identical AST
// (astPropEqual — the normalization point works), identical
// name-faithful rendering, and exactly-equal conclusions (Term.Equals,
// not merely α-equal).
func assertParseIdentical(t *testing.T, canonical, variant string) {
	t.Helper()

	astC, err := parseStmtAST(canonical)
	require.NoError(t, err, "canonical %q", canonical)
	astV, err := parseStmtAST(variant)
	require.NoError(t, err, "variant %q", variant)
	assert.True(t, astPropEqual(astC, astV),
		"ASTs differ: %q vs %q", canonical, variant)

	resC := ParsePropText(canonical)
	require.Empty(t, resC.Errors, "canonical %q: %v", canonical, resC.Errors)
	resV := ParsePropText(variant)
	require.Empty(t, resV.Errors, "variant %q: %v", variant, resV.Errors)
	assert.Equal(t, termText(resC), termText(resV),
		"name-faithful renderings differ: %q vs %q", canonical, variant)
	assert.True(t, resC.Prop.Conclusion().Equals(resV.Prop.Conclusion()),
		"conclusions not exactly equal: %q vs %q", canonical, variant)
	require.Equal(t, resC.Prop.NumHyps(), resV.Prop.NumHyps())
	for i := 0; i < resC.Prop.NumHyps(); i++ {
		assert.True(t, resC.Prop.Hyp(i).Equals(resV.Prop.Hyp(i)),
			"hyp %d not exactly equal: %q vs %q", i, canonical, variant)
	}
}

// TestTypeVarNormalizeParseEquivalence: `var:M` and bare `M` produce
// identical ASTs and props in every type position — decl ascription,
// binder ascription, function type, composite-type argument.
func TestTypeVarNormalizeParseEquivalence(t *testing.T) {
	cases := []struct{ canonical, variant string }{
		// Decl (⊢) type ascription.
		{"x:M ⊢ P(x)", "x:var:M ⊢ P(x)"},
		// Binder ascription + function type.
		{"∀f:(M → N).∀x:M.(f(x) = f(x))",
			"∀f:(var:M → var:N).∀x:var:M.(f(x) = f(x))"},
		// Composite-type argument.
		{"∀l:list(A).(l = l)", "∀l:list(var:A).(l = l)"},
		// Mixed spellings in one statement still normalize to one AST.
		{"∀f:(M → N).∀x:M.(f(x) = f(x))",
			"∀f:(var:M → N).∀x:M.(f(x) = f(x))"},
	}
	for _, c := range cases {
		assertParseIdentical(t, c.canonical, c.variant)
	}
}

// TestTypeVarNormalizeAnnotation: the `⟨V:T⟩` annotation RHS is a full
// type expression, so `C⟨A:var:M⟩` and `C⟨A:M⟩` build exactly the same
// term (same const meta instantiation).
func TestTypeVarNormalizeAnnotation(t *testing.T) {
	typeM := core.MakeVarType("M")
	scope := polyScope()
	ctx := map[string]core.HolType{
		"s": core.MakeFun(typeM, core.TypeBool()),
		"m": NumType,
	}
	resBare := ParseTermTextInScope("has_size⟨A:M⟩(s, m)", ctx, scope, core.TypeBool())
	require.Empty(t, resBare.Errors, "bare: %v", resBare.Errors)
	resVar := ParseTermTextInScope("has_size⟨A:var:M⟩(s, m)", ctx, scope, core.TypeBool())
	require.Empty(t, resVar.Errors, "var-prefixed: %v", resVar.Errors)
	assert.True(t, resBare.Term.Equals(resVar.Term),
		"annotated terms not exactly equal")

	c := findConstOfName(resVar.Term, "has_size")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	assert.True(t, subs[0].HolType.Equals(typeM))
}

// TestTypeVarNormalizeFormat: the statement formatter outputs the bare
// spelling for single-letter type vars — and its internal round-trip
// check (print → re-parse → identical AST) stays green, which
// FormatStmtText returning nil error certifies.
func TestTypeVarNormalizeFormat(t *testing.T) {
	// Expected spellings follow the printer's house style: mixed-type
	// binders don't group; function-type annotations keep their parens.
	cases := []struct{ in, want string }{
		{"∀x:var:M.(x = x)", "∀x:M. x = x"},
		{"∀f:(var:M → var:N).∀x:var:M.(f(x) = f(x))",
			"∀f:(M → N). ∀x:M. f(x) = f(x)"},
		{"∀l:list(var:A).(l = l)", "∀l:list(A). l = l"},
		{"C⟨A:var:M,B:var:N⟩ ⊢ C⟨A:var:M,B:var:N⟩",
			"C⟨A:M, B:N⟩ ⊢ C⟨A:M, B:N⟩"},
	}
	for _, c := range cases {
		got, err := FormatStmtText(c.in)
		require.NoError(t, err, "FormatStmtText(%q)", c.in)
		assert.Equal(t, c.want, got, "FormatStmtText(%q)", c.in)
		assert.NotContains(t, got, "var:", "single-letter var: must canonicalize away")
	}
}

// TestTypeVarPreserveNonCanonical: spellings OUTSIDE the single-
// uppercase-letter form are untouched — multi-letter type vars keep
// the required `var:` prefix, Skolem `?`-named type vars keep their
// (synthesized) `var:?N` form, and lowercase `var:a` is not
// respelled (bare `a` would mean a nullary composite type).
func TestTypeVarPreserveNonCanonical(t *testing.T) {
	cases := []struct{ in, want string }{
		{"∀x:var:Repty.(x = x)", "∀x:var:Repty. x = x"},
		{"∀x:var:?94099.(x = x)", "∀x:var:?94099. x = x"},
		// Bare `?94099` lexes as the synthesized ident `var:?94099`
		// (lex.go's `?` concession) — formatter surfaces that form.
		{"∀x:?94099.(x = x)", "∀x:var:?94099. x = x"},
		{"∀x:var:a.(x = x)", "∀x:var:a. x = x"},
	}
	for _, c := range cases {
		got, err := FormatStmtText(c.in)
		require.NoError(t, err, "FormatStmtText(%q)", c.in)
		assert.Equal(t, c.want, got, "FormatStmtText(%q)", c.in)
	}
	// The two Skolem spellings remain the same statement.
	assertParseIdentical(t, "∀x:var:?94099.(x = x)", "∀x:?94099.(x = x)")
	// var:Repty must NOT parse identically to bare Repty (type var vs
	// nullary composite type) — the normalization is single-letter only.
	varForm := ParsePropText("∀x:var:Repty.(x = x)")
	require.Empty(t, varForm.Errors)
	bareForm := ParsePropText("∀x:Repty.(x = x)")
	require.Empty(t, bareForm.Errors)
	assert.False(t, varForm.Prop.Conclusion().Equals(bareForm.Prop.Conclusion()),
		"var:Repty (type var) must stay distinct from bare Repty (composite)")
}

// TestTypeVarSkolemAnnotationEquivalence extends the existing Skolem
// annotation coverage (TestParseAngleBracket_HasSizeSkolemVar): the
// bare `?83621` and explicit `var:?83621` spellings in annotation TYPE
// position build exactly the same term, before and after the
// single-letter normalization (which must not touch them).
func TestTypeVarSkolemAnnotationEquivalence(t *testing.T) {
	scope := polyScope()
	ctx := map[string]core.HolType{"m": NumType}
	bare := ParseTermTextInScope(
		"has_size⟨A:?83621⟩(universe⟨A:?83621⟩, m)", ctx, scope, core.TypeBool())
	require.Empty(t, bare.Errors, "bare: %v", bare.Errors)
	explicit := ParseTermTextInScope(
		"has_size⟨A:var:?83621⟩(universe⟨A:var:?83621⟩, m)", ctx, scope, core.TypeBool())
	require.Empty(t, explicit.Errors, "explicit: %v", explicit.Errors)
	assert.True(t, bare.Term.Equals(explicit.Term))

	c := findConstOfName(explicit.Term, "has_size")
	require.False(t, c.IsZero())
	subs := c.TypeSubsts()
	require.Len(t, subs, 1)
	assert.True(t, subs[0].HolType.Equals(core.MakeVarType("?83621")))
}

// TestNormalizeTypeVarName pins the helper's exact boundary.
func TestNormalizeTypeVarName(t *testing.T) {
	cases := map[string]string{
		"var:M":      "M",
		"var:A":      "A",
		"var:Z":      "Z",
		"var:Repty":  "var:Repty",  // multi-letter: prefix required
		"var:?94099": "var:?94099", // Skolem
		"var:a":      "var:a",      // lowercase: bare `a` ≠ type var
		"var:Œ":      "var:Œ",      // non-ASCII uppercase: excluded
		"M":          "M",
		"num":        "num",
		"var:":       "var:",
	}
	for in, want := range cases {
		if got := normalizeTypeVarName(in); got != want {
			t.Errorf("normalizeTypeVarName(%q) = %q, want %q", in, got, want)
		}
	}
}
