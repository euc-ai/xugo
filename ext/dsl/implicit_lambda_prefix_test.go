package dsl

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

type lambdaPrefixSyntax struct{ SyntaxTable }

func (s lambdaPrefixSyntax) ConstSyntax(name string) *ConstSyntax {
	switch name {
	case "zz_eval":
		return &ConstSyntax{Implicit: []string{"op", "e", "op", "e"}}
	case "real_add":
		return &ConstSyntax{Operator: &Operator{Symbol: "+", Args: []int{0, 1}}}
	case "real_mul":
		return &ConstSyntax{Operator: &Operator{Symbol: "*", Args: []int{0, 1}}}
	}
	return s.SyntaxTable.ConstSyntax(name)
}

func (s lambdaPrefixSyntax) OperatorConsts(symbol string, arity int) []string {
	if arity == 2 {
		switch symbol {
		case "+":
			return []string{"real_add"}
		case "*":
			return []string{"real_mul"}
		}
	}
	return s.SyntaxTable.OperatorConsts(symbol, arity)
}

func TestImplicitArgs_ExplicitLambdaOperationsBesideRecords(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err)
		return ty
	}
	scope.ConstMetas["zz_eval"] = core.MakeConstMeta("zz_eval", typ("(A → A → A) → A → (A → A → A) → A → (num → A) → A → A"))
	scope.ConstMetas["real_add"] = core.MakeConstMeta("real_add", typ("real → real → real"))
	scope.ConstMetas["real_mul"] = core.MakeConstMeta("real_mul", typ("real → real → real"))
	scope.Syntax = lambdaPrefixSyntax{scope.Syntax}

	const prefix = "∀S T:zz_ops(real). ∀P:(num → real). "
	want := ParsePropTextInScope(prefix+"zz_eval(λa:real. λb:real. real_add(a, b), &0, λa:real. λb:real. real_mul(a, b), &1, P, &1) = &0", scope)
	require.Empty(t, want.Errors)
	got := ParsePropTextInScope(prefix+"zz_eval(λa:real. λb:real. a + b, &0, λa:real. λb:real. a * b, &1, P, &1) = &0", scope)
	require.Empty(t, got.Errors)
	require.True(t, got.Prop.AlphaEquals(want.Prop))

	short := ParsePropTextInScope(prefix+"zz_eval(P, &1) = &0", scope)
	require.NotEmpty(t, short.Errors)
	require.Contains(t, short.Errors[0].Message, "more than one record")
	short = ParsePropTextInScope("∀S:zz_ops(real). ∀P:(num → real). zz_eval(λn:num. P(n), &1) = &0", scope)
	require.Empty(t, short.Errors)
}

// groundOperatorSyntax declares `+` and `^` at a fixed type no record
// reads, beside lambdaPrefixSyntax's constants.
type groundOperatorSyntax struct{ lambdaPrefixSyntax }

func (s groundOperatorSyntax) ConstSyntax(name string) *ConstSyntax {
	switch name {
	case "zz_or":
		return &ConstSyntax{Operator: &Operator{Symbol: "+", Args: []int{0, 1}}}
	case "zz_repeat":
		return &ConstSyntax{Operator: &Operator{Symbol: "^", Args: []int{0, 1}}}
	}
	return s.lambdaPrefixSyntax.ConstSyntax(name)
}

func (s groundOperatorSyntax) OperatorConsts(symbol string, arity int) []string {
	if arity == 2 {
		switch symbol {
		case "+":
			return []string{"zz_or"}
		case "^":
			return []string{"zz_repeat"}
		}
	}
	return s.lambdaPrefixSyntax.OperatorConsts(symbol, arity)
}

// An operand whose type the text does not fix leaves the built-in
// domain open: `&1 + &2` and `&2 ^ 3` build at real whatever else
// declares `+` and `^`, so the lambdas stay untyped, and the short
// reading, past zz_eval's spine, is the one contradicted.
func TestImplicitArgs_UnfixedOperandsLeaveTheBuiltInDomainOpen(t *testing.T) {
	scope := structFieldsTestScope(t)
	typ := func(text string) core.HolType {
		ty, err := ParseTypeText(text)
		require.NoError(t, err)
		return ty
	}
	scope.ConstMetas["zz_eval"] = core.MakeConstMeta("zz_eval", typ("(A → A → A) → A → (A → A → A) → A → (num → A) → A → A"))
	scope.ConstMetas["real_mul"] = core.MakeConstMeta("real_mul", typ("real → real → real"))
	scope.ConstMetas["zz_or"] = core.MakeConstMeta("zz_or", typ("bool → bool → bool"))
	scope.ConstMetas["zz_repeat"] = core.MakeConstMeta("zz_repeat", typ("bool → num → bool"))
	scope.Syntax = groundOperatorSyntax{lambdaPrefixSyntax{scope.Syntax}}

	for _, operation := range []string{"&1 + &2", "&2 ^ 3"} {
		got := ParsePropTextInScope("∀S:zz_ops(real). ∀P:(num → real). zz_eval(λa:real. λb:real. "+operation+", &0, λa:real. λb:real. real_mul(a, b), &1, P, &1) = &0", scope)
		require.Empty(t, got.Errors, operation)
	}
}
