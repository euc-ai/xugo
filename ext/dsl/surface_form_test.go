package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// SurfaceForm puts a printed statement in the chapter's spelling: set
// binders `set(τ)`, and the instance ties its arguments fix dropped — a
// tie stays where the text would not read back without it.
func TestSurfaceForm_SetsAndTies(t *testing.T) {
	scope := &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{
			"finite": core.MakeConstMeta("finite", mustType(t, "(A → bool) → bool")),
			"card":   core.MakeConstMeta("card", mustType(t, "(A → bool) → num")),
			"none":   core.MakeConstMeta("none", mustType(t, "A → bool")),
		},
		StrictResolution: true, StrictMint: true, FreshenMetaLetters: true,
	}
	const printed = "∀s:(A → bool). ∀t:(B → bool). finite⟨A:A⟩(s) ∧ finite⟨A:B⟩(t) ⇒ card⟨A:A⟩(none⟨A:A⟩) = card⟨A:A⟩(s)"
	stated := ParsePropTextInScope(printed, scope)
	if len(stated.Errors) > 0 {
		t.Fatalf("the printed text: %s", stated.Errors[0].Message)
	}
	reads := func(text string) bool {
		res := ParsePropTextInScope(text, scope)
		return len(res.Errors) == 0 && res.Prop.AlphaKey() == stated.Prop.AlphaKey()
	}
	got := SurfaceForm(printed, reads)
	const want = "∀s:set(A). ∀t:set(B). finite(s) ∧ finite(t) ⇒ card⟨A:A⟩(none) = card(s)"
	if got != want {
		t.Fatalf("surface form\n got: %s\nwant: %s", got, want)
	}
	if !reads(got) {
		t.Fatalf("the surface form does not read back: %s", got)
	}
}

func TestSurfaceForm_NumericEmbeddings(t *testing.T) {
	scope := &ParseScope{
		ConstMetas: map[string]core.ConstTermMeta{
			"fun_support": core.MakeConstMeta("fun_support", mustType(t, "A → (B → A) → (B → bool)")),
		},
		StrictResolution: true, FreshenMetaLetters: true,
	}
	const prefix = "∀a b:num. ∀z:int. "
	for _, tc := range []struct{ name, printed, want string }{
		{"variable", prefix + "int_of_num(a) = z", prefix + "a = z"},
		{"literal", prefix + "z + int_of_num(2) = z", prefix + "z + 2 = z"},
		{"monus", prefix + "int_of_num(a - b) = z", prefix + "a - b = z"},
		{"precedence", prefix + "z + int_of_num(a - b) = z", prefix + "z + (a - b) = z"},
		{"integer subtraction", prefix + "int_of_num(a) - int_of_num(b) = z", prefix + "&a - b = z"},
		{"integer multiplication", prefix + "int_of_num(a) * int_of_num(b) = z", prefix + "&a * b = z"},
		{"chapter ampersands", prefix + "z + &a = z + &b", prefix + "z + a = z + b"},
		{"integer anchor", "int_of_num(0) = int_of_num(1)", "int_of_num(0) = 1"},
		{"integer congruence", "∀a b p:num. int_of_num(a) ≡ int_of_num(b) (mod int_of_num(p))", "∀a b p:num. &a ≡ b (mod p)"},
		{"polymorphic zero", "∀f:(num → int). fun_support(int_of_num(0), f) = fun_support(int_of_num(0), f)", "∀f:(num → int). fun_support(&0, f) = fun_support(&0, f)"},
		{"shadowed head", "∀int_of_num:(num → int). ∀a:num. ∀z:int. int_of_num(a) = z", "∀int_of_num:(num → int). ∀a:num. ∀z:int. int_of_num(a) = z"},
		{"real embedding", "∀x:real. x + &1 = x", "∀x:real. x + &1 = x"},
		{"printed name", "∀a₀:num. ∀z:int. int_of_num(a₀) = z", "∀a₀:num. ∀z:int. a₀ = z"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			stated := ParsePropTextAtDoor(tc.printed, scope)
			require.Empty(t, stated.Errors)
			reads := func(text string) bool {
				res := ParsePropTextAtDoor(text, scope)
				return len(res.Errors) == 0 && res.Prop.AlphaEquals(stated.Prop)
			}
			got := SurfaceForm(tc.printed, reads)
			require.Equal(t, tc.want, got)
			require.True(t, reads(got))
			require.Equal(t, got, SurfaceForm(got, reads), "the surface form is stable")
		})
	}
}

func TestSurfaceForm_ExpectedInteger(t *testing.T) {
	vars := map[string]core.HolType{"a": NumType, "b": NumType}
	for _, tc := range []struct{ printed, want string }{
		{"int_of_num(2)", "2"},
		{"int_of_num(a)", "a"},
		{"int_of_num(a - b)", "a - b"},
		{"int_of_num(a * b)", "a * b"},
		{"int_of_num(a) - int_of_num(b)", "&a - b"},
		{"int_of_num(a) * int_of_num(b)", "&a * b"},
	} {
		t.Run(tc.printed, func(t *testing.T) {
			stated := ParseTermText(tc.printed, vars, IntType)
			require.Empty(t, stated.Errors)
			reads := func(text string) bool {
				res := ParseTermText(text, vars, IntType)
				return len(res.Errors) == 0 && res.Term.AlphaEquals(stated.Term)
			}
			require.Equal(t, tc.want, SurfaceForm(tc.printed, reads))
		})
	}
}
