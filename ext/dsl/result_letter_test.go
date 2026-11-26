package dsl

// A polymorphic constant whose letter occurs only in its result type —
// `zz_tag : num → U → U` applied to its number, `zz_embed : A → U`,
// `zz_names : num → U → bool` — is pinned by nothing but the slot it
// stands in. Each test reads the untied text beside the text that ties
// the letter with ⟨⟩, and asks for the same statement.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

func resultLetterScope(t *testing.T) *ParseScope {
	t.Helper()
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err, text)
		return ty
	}
	metas := map[string]core.ConstTermMeta{}
	for name, ty := range map[string]string{
		"zz_univ":  "A → bool",
		"zz_tag":   "num → U → U",
		"zz_embed": "A → U",
		"zz_names": "num → U → bool",
		"zz_inj":   "(A → bool) → (A → B) → bool",
		"zz_hom":   "(U → bool) → (U → bool) → (U → U) → bool",
		"zz_aug":   "A → U → A → bool",
		"zz_zero":  "A → D → A",
		"zz_mem":   "A → (A → bool) → bool",
		"zz_pair":  "A → zz_box(A)",
		"zz_free":  "num → zz_ops(U)",
		"zz_op":    "zz_ops(A) → A → A → A",
	} {
		metas[name] = core.MakeConstMeta(core.TermName(name), typ(ty))
	}
	return &ParseScope{
		ConstMetas: metas,
		Syntax: structFieldsSyntax{SyntaxTable: testSyntax{}, metas: metas, structs: map[string]*StructSyntax{
			"zz_ops": {Fields: []StructField{{Name: "op", Const: "zz_op"}}},
		}},
		StrictResolution:   true,
		FreshenMetaLetters: true,
	}
}

// assertReadsAsTied parses the untied text and the tied one and
// requires one statement, with no stand-in left in it.
func assertReadsAsTied(t *testing.T, scope *ParseScope, untied, tied string) {
	t.Helper()
	want := parseImplicit(t, scope, tied)
	got := parseImplicit(t, scope, untied)
	require.Empty(t, UnpinnedLetters(got), "no stand-in survives: %s", prop.PrintProp(got))
	require.Equal(t, want.AlphaKey(), got.AlphaKey(),
		"the slot pins the letter as the tie does:\n  got  %s\n  want %s", prop.PrintProp(got), prop.PrintProp(want))
}

// In an argument slot: the slot's type is fixed by the head — a
// constant whose earlier argument instantiated it, or a variable typed
// by its binder — and the argument's result-only letter reads at it.
func TestResultLetter_ArgumentSlot(t *testing.T) {
	scope := resultLetterScope(t)
	// The head's domain `U → ?B` and the argument's `?U → ?U` meet only
	// by unifying both sides: neither is an instance of the other.
	assertReadsAsTied(t, scope,
		"∀i:num. zz_inj(zz_univ⟨A:U⟩, zz_tag(i))",
		"∀i:num. zz_inj(zz_univ⟨A:U⟩, zz_tag⟨U:U⟩(i))")
	// The argument's result a set over the author's letter: the slot's
	// open `B` takes `set(A)` while the argument's `U` takes the slot's.
	assertReadsAsTied(t, scope,
		"∀a:A. zz_inj(zz_univ⟨A:U⟩, zz_aug(a))",
		"∀a:A. zz_inj(zz_univ⟨A:U⟩, zz_aug⟨U:U⟩(a))")
	// A variable head: its domain is the binder's type.
	assertReadsAsTied(t, scope,
		"∀P:((U → U) → bool). ∀i:num. P(zz_tag(i))",
		"∀P:((U → U) → bool). ∀i:num. P(zz_tag⟨U:U⟩(i))")
	assertReadsAsTied(t, scope,
		"∀g:(U → B). ∀b:B. ∀x:A. g(zz_embed(x)) = b",
		"∀g:(U → B). ∀b:B. ∀x:A. g(zz_embed⟨U:U⟩(x)) = b")
}

// As the receiver of a field: the field's operands fix the record's
// carrier.
func TestResultLetter_FieldReceiver(t *testing.T) {
	scope := resultLetterScope(t)
	assertReadsAsTied(t, scope,
		"∀n:num. ∀q:U. zz_free(n).op(q, q) = q",
		"∀n:num. ∀q:U. zz_free⟨U:U⟩(n).op(q, q) = q")
	// The field spelling and the projection spelling are one reading.
	assertReadsAsTied(t, scope,
		"∀n:num. ∀q:U. zz_free(n).op(q, q) = q",
		"∀n:num. ∀q:U. zz_op(zz_free(n), q, q) = q")
}

// Two sibling arguments at one letter, neither pinned, and a later
// argument that pins it: the binding the later argument makes reaches
// both.
func TestResultLetter_UnpinnedSiblings(t *testing.T) {
	scope := resultLetterScope(t)
	assertReadsAsTied(t, scope,
		"∀n:num. ∀φ:(V → V). zz_hom(zz_names(n), zz_names(n + 1), φ)",
		"∀n:num. ∀φ:(V → V). zz_hom(zz_names⟨U:V⟩(n), zz_names(n + 1), φ)")
}

// A slot the argument cannot take is refused by name, before the
// kernel sees the application; a letter nothing pins stays the
// statement door's to report.
func TestResultLetter_Refusals(t *testing.T) {
	scope := resultLetterScope(t)
	res := ParsePropTextInScope("∀P:(num → bool). ∀i:num. P(zz_tag(i))", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "does not match domain num")
	require.NotContains(t, res.Errors[0].Message, "ill-typed")

	res = ParsePropTextInScope("∀n:num. ∀q:num. zz_free⟨U:U⟩(n).op(q, q) = q", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "argument type num does not match domain")
	require.NotContains(t, res.Errors[0].Message, "ill-typed")

	// A variable its first use typed at a constant's letter is not
	// retyped at one occurrence: its binder would no longer bind it.
	res = ParsePropTextInScope("∀x. zz_univ(x) ∧ (∀P:(U → bool). P(x))", scope)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "x took the type")
	require.Contains(t, res.Errors[0].Message, "write its type at its binder")
	assertReadsAsTied(t, scope,
		"∀x:U. zz_univ(x) ∧ (∀P:(U → bool). P(x))",
		"∀x:U. zz_univ⟨A:U⟩(x) ∧ (∀P:(U → bool). P(x))")

	res = ParsePropTextInScope("∀i:num. zz_inj(zz_univ, zz_tag(i))", scope)
	requireParses(t, res)
	require.NotEmpty(t, UnpinnedLetters(res.Prop), "nothing pins the letter: %s", prop.PrintProp(res.Prop))
}

// At a term door the expected type is the slot: a witness or a TermAs
// text reads a result-only letter at it, as the tie would.
func TestResultLetter_TermDoor(t *testing.T) {
	scope := resultLetterScope(t)
	U := core.MakeVarType("U")
	want := ParseTermTextInScope("zz_tag⟨U:U⟩(0)", nil, scope, core.MakeFun(U, U))
	require.Empty(t, want.Errors)
	got := ParseTermTextInScope("zz_tag(0)", nil, scope, core.MakeFun(U, U))
	require.Empty(t, got.Errors)
	require.True(t, got.Term.Equals(want.Term), "got %s, want %s",
		ext.FormatTerm(got.Term, false), ext.FormatTerm(want.Term, false))

	res := ParseTermTextInScope("zz_tag(0)", nil, scope, NumType)
	require.NotEmpty(t, res.Errors)
	require.Contains(t, res.Errors[0].Message, "but expected num")
}
