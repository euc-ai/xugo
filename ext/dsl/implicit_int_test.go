package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

func TestImplicitInt_ExpectedDomain(t *testing.T) {
	vars := map[string]core.HolType{
		"a": NumType, "k": NumType, "p": NumType,
		"f": core.MakeFun(NumType, NumType),
	}
	for _, tc := range []struct{ short, long string }{
		{"a", "int_of_num(a)"},
		{"2", "int_of_num(2)"},
		{"a * k", "int_of_num(a * k)"},
		{"a - k", "int_of_num(a - k)"},
		{"a ^ p", "int_of_num(a ^ p)"},
		{"-(a + k) ^ p", "-int_of_num((a + k) ^ p)"},
		{"(-(a + k)) ^ p", "(-int_of_num(a + k)) ^ p"},
		{"&a * k", "int_of_num(a) * int_of_num(k)"},
		{"&a * &k", "int_of_num(a) * int_of_num(k)"},
		{"f(a - k)", "int_of_num(f(a - k))"},
		{"nat_mod(a * k, p)", "int_of_num(nat_mod(a * k, p))"},
	} {
		t.Run(tc.short, func(t *testing.T) {
			got := ParseTermText(tc.short, vars, IntType)
			want := ParseTermText(tc.long, vars, IntType)
			require.Empty(t, got.Errors)
			require.Empty(t, want.Errors)
			require.True(t, got.Term.AlphaEquals(want.Term), "%s", ext.PrintTerm(got.Term))
		})
	}
	// Adopting an integer result preserves natural monus; embedding an
	// operand explicitly selects the distinct integer subtraction.
	monus := ParseTermText("int_of_num(a - k)", vars, IntType)
	sub := ParseTermText("a - k", vars, IntType)
	require.Empty(t, monus.Errors)
	require.Empty(t, sub.Errors)
	require.True(t, monus.Term.AlphaEquals(sub.Term))
	integerSub := ParseTermText("&a - k", vars, IntType)
	require.Empty(t, integerSub.Errors)
	require.False(t, monus.Term.AlphaEquals(integerSub.Term))
}

func TestImplicitInt_AnchoredPositions(t *testing.T) {
	for _, tc := range []struct{ short, long string }{
		{"a = z", "int_of_num(a) = z"},
		{"z ≠ a", "z ≠ int_of_num(a)"},
		{"a + z = z + a", "int_of_num(a) + z = z + int_of_num(a)"},
		{"a * k ≤ z", "int_of_num(a * k) ≤ z"},
		{"a - k = z", "int_of_num(a - k) = z"},
		{"z + (a - k) = z", "z + int_of_num(a - k) = z"},
		{"z ∣ a", "z ∣ int_of_num(a)"},
		{"f(a * k) = z", "f(int_of_num(a * k)) = z"},
		{"h(λn:num. n * k) = z", "h(λn:num. int_of_num(n * k)) = z"},
		{"nat_mod(a * k, p) ≡ a * k (mod &p)", "int_of_num(nat_mod(a * k, p)) ≡ int_of_num(a * k) (mod int_of_num(p))"},
		{"nat_mod(a * k, p) ≡ &a * k (mod &p)", "int_of_num(nat_mod(a * k, p)) ≡ int_of_num(a) * int_of_num(k) (mod int_of_num(p))"},
		{"a - k ≡ z (mod p)", "int_of_num(a - k) ≡ z (mod int_of_num(p))"},
		{"z ≡ a (mod p)", "z ≡ int_of_num(a) (mod int_of_num(p))"},
		{"a ≡ z (mod p)", "int_of_num(a) ≡ z (mod int_of_num(p))"},
		{"-a ≡ k (mod &p)", "-int_of_num(a) ≡ int_of_num(k) (mod int_of_num(p))"},
		{"a ≡ -k (mod z)", "int_of_num(a) ≡ -int_of_num(k) (mod z)"},
	} {
		t.Run(tc.short, func(t *testing.T) {
			prefix := "∀a k p:num. ∀z:int. ∀f:(int → int). ∀h:((num → int) → int). "
			got := ParsePropText(prefix + tc.short)
			want := ParsePropText(prefix + tc.long)
			require.Empty(t, got.Errors)
			require.Empty(t, want.Errors)
			require.True(t, got.Prop.AlphaEquals(want.Prop))
		})
	}
}

func TestImplicitInt_PreservesDomains(t *testing.T) {
	vars := map[string]core.HolType{"a": NumType, "k": NumType, "p": NumType, "z": IntType, "r": RealType}
	scope := &ParseScope{CoerceDomain: IntType, StrictResolution: true}
	for _, expr := range []string{"a", "a * k", "a - k"} {
		got := ParseTermTextInScope(expr, vars, scope, nil)
		require.Empty(t, got.Errors)
		require.True(t, got.Term.Type().Equals(NumType), expr)
	}
	nat := ParseTermTextInScope("a ≡ k (mod p)", vars, scope, core.TypeBool())
	require.Empty(t, nat.Errors)
	require.True(t, nat.Term.AlphaEquals(congNumTerm(core.Var("a", NumType), core.Var("k", NumType), core.Var("p", NumType))))
	for _, expr := range []string{"z + r", "a + r", "z ≡ r (mod p)", "suc(z)"} {
		got := ParseTermTextInScope(expr, vars, scope, nil)
		require.NotEmpty(t, got.Errors, expr)
	}
	require.NotEmpty(t, ParseTermText("z", vars, NumType).Errors)
	require.NotEmpty(t, ParseTermText("a", vars, RealType).Errors)
}

func TestImplicitInt_PolymorphicPinDoesNotForceEmbedding(t *testing.T) {
	meta := core.MakeConstMeta("zz_identity", core.MakeFun(core.TypeA(), core.TypeA()))
	scope := &ParseScope{Consts: map[string]core.ConstTerm{
		"zz_identity": core.MakeConstTerm(meta, core.MakeFun(IntType, IntType)),
	}, ConstMetas: map[string]core.ConstTermMeta{"zz_identity": meta}}
	vars := map[string]core.HolType{"a": NumType}
	got := ParseTermTextInScope("zz_identity(a)", vars, scope, NumType)
	require.Empty(t, got.Errors)
	want := core.Apply(core.MakeConstTerm(meta, core.MakeFun(NumType, NumType)), core.Var("a", NumType))
	require.True(t, got.Term.AlphaEquals(want))
	// An expected integer result embeds the application at its natural instance.
	got = ParseTermTextInScope("zz_identity(a)", vars, scope, IntType)
	require.Empty(t, got.Errors)
	require.True(t, got.Term.AlphaEquals(core.Apply(IntOfNumMeta.Term(), want)))
}

func TestImplicitInt_OverloadAmbiguity(t *testing.T) {
	metas := map[string]core.ConstTermMeta{
		"zz_int_nat": core.MakeConstMeta("zz_int_nat", core.MakeFun(IntType, NumType, IntType)),
		"zz_nat_int": core.MakeConstMeta("zz_nat_int", core.MakeFun(NumType, IntType, IntType)),
	}
	syntax := testSyntax{}
	for name, meta := range metas {
		syntax[name] = &ConstSyntax{Overload: &Overload{Word: "zz_mixed", Arity: 2, Type: meta.AbsType()}}
	}
	scope := &ParseScope{ConstResolver: func(name string) core.ConstTermMeta { return metas[name] }, Syntax: syntax}
	got := ParseTermTextInScope("zz_mixed(1, 2)", nil, scope, IntType)
	require.NotEmpty(t, got.Errors)
	require.Contains(t, got.Errors[0].Message, "alike")
}
