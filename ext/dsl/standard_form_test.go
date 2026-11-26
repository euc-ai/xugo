// Tests for StandardStatement (standard_form.go).
package dsl

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestStandardStatement(t *testing.T) {
	cases := []struct {
		in   string
		want Statement
	}{
		// Curried: each antecedent one hypothesis.
		{"∀a b n:num. a < n ⇒ b < n ⇒ a = b",
			Statement{Binders: "∀a b n:num.", Hypotheses: []string{"a < n", "b < n"}, Conclusion: "a = b"}},
		// Interleaved: the inner binders move in front, in order.
		{"∀x:num. p(x) ⇒ ∀y:num. q(x, y) ∧ r(y) ⇒ x = y",
			Statement{Binders: "∀x y:num.", Hypotheses: []string{"p(x)", "q(x, y)", "r(y)"}, Conclusion: "x = y"}},
		// An inner ∀ after the one premise.
		{"∀T:set(set(A)). ∀f:(A → B). continuous_map(T, f) ⇒ ∀s:set(A). continuous_map(subtopology(T, s), f)",
			Statement{Binders: "∀T:set(set(A)). ∀f:(A → B). ∀s:set(A).", Hypotheses: []string{"continuous_map(T, f)"}, Conclusion: "continuous_map(subtopology(T, s), f)"}},
		// A hypothesis that is itself quantified stays one hypothesis;
		// the n it binds is not the conclusion's, which moves in front.
		{"∀P:(num → bool). P(0) ∧ (∀n:num. P(n) ⇒ P(suc(n))) ⇒ ∀n:num. P(n)",
			Statement{Binders: "∀P:(num → bool). ∀n:num.", Hypotheses: []string{"P(0)", "∀n:num. P(n) ⇒ P(suc(n))"}, Conclusion: "P(n)"}},
		// Already standard: unchanged.
		{"∀m n:num. m ≤ n ⇒ m < n ∨ m = n",
			Statement{Binders: "∀m n:num.", Hypotheses: []string{"m ≤ n"}, Conclusion: "m < n ∨ m = n"}},
		// A conclusion opening with ∃ stays the conclusion.
		{"∀n:num. 0 < n ⇒ ∃m:num. n = suc(m)",
			Statement{Binders: "∀n:num.", Hypotheses: []string{"0 < n"}, Conclusion: "∃m:num. n = suc(m)"}},
	}
	for _, c := range cases {
		got, err := StandardStatement(c.in)
		require.NoError(t, err, c.in)
		assert.Equal(t, c.want, got, c.in)
		text, err := got.Text()
		require.NoError(t, err)
		back, err := StandardStatement(text)
		require.NoError(t, err)
		assert.Equal(t, got, back, "the standard form is a fixpoint")
	}
}

func TestStandardStatementRefusals(t *testing.T) {
	_, err := StandardStatement("∀x:num. p(x) ⇒ ∀x:num. q(x)")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "rebinds")
	_, err = StandardStatement("∀x:num. p(y) ⇒ ∀y:num. q(x, y)")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "free")
	_, err = StandardStatement("p ⊢ q")
	require.Error(t, err)
}
