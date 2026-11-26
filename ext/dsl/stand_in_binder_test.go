package dsl

// A binder written without a type takes its type at its first use, and
// where that use is a polymorphic constant's argument the type is the
// constant's occurrence-local stand-in. A later use that reads the
// variable at another type cannot rewrite that one occurrence: the
// binder and every other occurrence keep the stand-in, so the rewritten
// occurrence would be another variable, free in the statement. The text
// is refused by name instead, on every path a later use is read by.

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestStandInBinder_NotRetyped(t *testing.T) {
	scope := resultLetterScope(t)
	const prefix = "∀s:(U → bool). ∀z:num. ∀q:U. ∀P:(U → bool). "
	for _, body := range []string{
		"zz_zero(z, x) = z ∧ zz_mem(x, s)",            // an argument of a constant
		"zz_zero(z, x) = z ∧ x = q",                   // an operand of =
		"zz_zero(z, x) = z ∧ zz_pair(x) = zz_pair(q)", // inside an operand
		"zz_zero(z, x) = z ∧ P(x)",                    // an argument of a variable
	} {
		res := ParsePropTextInScope(prefix+"∀x. "+body, scope)
		require.NotEmpty(t, res.Errors, "%s: the occurrence would be free beside its binder", body)
		require.Equal(t, CodeTypeMismatch, res.Errors[0].Code, body)
		require.Contains(t, res.Errors[0].Message, "x took the type", body)
		require.Contains(t, res.Errors[0].Message, "write its type at its binder", body)

		typed := ParsePropTextInScope(prefix+"∀x:U. "+body, scope)
		requireParses(t, typed)
		require.Empty(t, typed.Prop.Conclusion().Frees(nil), body)
	}
}
