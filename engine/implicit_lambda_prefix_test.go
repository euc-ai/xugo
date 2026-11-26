package engine

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

func TestImplicitArgs_ExplicitLambdaOperationsInFamily(t *testing.T) {
	_, s := boundSession(t, "real/real_formal_series")
	scope := s.StatementDoorScope()
	const prefix = "∀R S:ring_ops(real). ∀P:(num → real). "
	want := dsl.ParsePropTextInScope(prefix+"polynomial_eval(λa:real. λb:real. real_add(a, b), &0, λa:real. λb:real. real_mul(a, b), &1, P, &1) = &0", scope)
	require.Empty(t, want.Errors)
	parsed := dsl.ParsePropTextInScope(prefix+"polynomial_eval(λa:real. λb:real. a + b, &0, λa:real. λb:real. a * b, &1, P, &1) = &0", scope)
	require.Empty(t, parsed.Errors)
	require.True(t, parsed.Prop.AlphaEquals(want.Prop))
	short := dsl.ParsePropTextInScope(prefix+"polynomial_eval(P, &1) = &0", scope)
	require.NotEmpty(t, short.Errors)
	require.Contains(t, short.Errors[0].Message, "more than one record")
}

// Beside a ring record on another carrier, polynomial_eval reads its
// prefix from the record the polynomial and the point are on, and the
// served spelling drops that prefix; the same holds for records a goal
// declares, as a session's Skolems are.
func TestImplicitArgs_RecordPickedByTypeInFamily(t *testing.T) {
	_, s := boundSession(t, "real/real_formal_series")
	scope := s.StatementDoorScope()
	for _, tc := range []struct{ long, short string }{
		{"∀R:ring_ops(A). ∀S:ring_ops(B). comm_ring_on(R) ∧ comm_ring_on(S) ⇒ ∀P:(num → B). ∀y:B. polynomial_eval(S.add, S.zero, S.mul, S.one, P, y) = S.zero",
			"∀R:ring_ops(A). ∀S:ring_ops(B). comm_ring_on(R) ∧ comm_ring_on(S) ⇒ ∀P:(num → B). ∀y:B. polynomial_eval(P, y) = S.zero"},
		{"R:ring_ops(A), S:ring_ops(B), P:(num → A), x:A, comm_ring_on(R), comm_ring_on(S) ⊢ polynomial_eval(R.add, R.zero, R.mul, R.one, P, x) = R.zero",
			"R:ring_ops(A), S:ring_ops(B), P:(num → A), x:A, comm_ring_on(R), comm_ring_on(S) ⊢ polynomial_eval(P, x) = R.zero"},
	} {
		want := dsl.ParsePropTextInScope(tc.long, scope)
		require.Empty(t, want.Errors, tc.long)
		short := dsl.ParsePropTextInScope(tc.short, scope)
		require.Empty(t, short.Errors, tc.short)
		require.Equal(t, want.Prop.AlphaKey(), short.Prop.AlphaKey(), tc.short)
		served, err := dsl.ChapterSpelling(tc.long, scope.Syntax, scope.ImplicitBindings)
		require.NoError(t, err)
		require.NotContains(t, served, ".add", served)
		back := dsl.ParsePropTextInScope(served, scope)
		require.Empty(t, back.Errors, served)
		require.Equal(t, want.Prop.AlphaKey(), back.Prop.AlphaKey(), served)
	}
}

// x + -y has no local type (the prefix − gives none), so `c • (x + -y)`
// has none either: vec_scalar_mul declares `•` and would take it, but
// the build reads x − y at the module's elements and uses the module's
// smul. Typed as vec_scalar_mul's result, the second argument
// contradicted left_coset's explicit reading and its implicit mul was
// put in front of V.add.
func TestImplicitArgs_ScalarActionOnAnUntypedOperandInFamily(t *testing.T) {
	_, s := boundSession(t, "scheme/lattice_pair")
	scope := s.StatementDoorScope()
	parsed := dsl.ParsePropTextInScope("∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M':prod(set(B), set(B)). ∀c:A. ∀x y:B. "+
		"left_coset(V.add, c • (x + -y), set_mul(V.add, fst(M'), snd(M'))) = left_coset(V.add, c • x + -(c • y), set_mul(V.add, fst(M'), snd(M')))", scope)
	require.Empty(t, parsed.Errors)
}
