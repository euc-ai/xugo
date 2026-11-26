// Tests for Statement (statement.go): the assembly of the parts into
// one text, its parentheses, and SplitStatement as its inverse.
package dsl

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestStatementText(t *testing.T) {
	cases := []struct {
		s    Statement
		want string
	}{
		{Statement{Binders: "∀m n:num.", Hypotheses: []string{"m ≤ n"}, Conclusion: "m < n ∨ m = n"},
			"∀m n:num. m ≤ n ⇒ m < n ∨ m = n"},
		// A quantified or implied hypothesis is parenthesized; an ∧ in
		// a later hypothesis keeps its grouping.
		{Statement{Binders: "∀m n:num.", Hypotheses: []string{"m ≤ n", "∃d:num. n = m + d", "m = 0 ⇒ n = 0", "0 ≤ m ∧ 0 ≤ n"}, Conclusion: "m ≤ n"},
			"∀m n:num. m ≤ n ∧ (∃d:num. n = m + d) ∧ (m = 0 ⇒ n = 0) ∧ (0 ≤ m ∧ 0 ≤ n) ⇒ m ≤ n"},
		// No hypotheses, no binders.
		{Statement{Binders: "∀m n:num.", Conclusion: "m + n = n + m"}, "∀m n:num. m + n = n + m"},
		{Statement{Hypotheses: []string{"p"}, Conclusion: "q"}, "p ⇒ q"},
		// Binders in the author's spelling are regrouped canonically.
		{Statement{Binders: "∀m:num. ∀n:num.", Hypotheses: []string{"m ≤ n"}, Conclusion: "m ≤ n"},
			"∀m n:num. m ≤ n ⇒ m ≤ n"},
		// Abbreviations stay as spelled.
		{Statement{Binders: "∀x:num.", Hypotheses: []string{"«R» ≤ x"}, Conclusion: "«R» = x", Abbrev: Abbrev{{Name: "R", Text: "x + 1"}}},
			"∀x:num. «R» ≤ x ⇒ «R» = x"},
	}
	for _, c := range cases {
		got, err := c.s.Text()
		require.NoError(t, err, "%+v", c.s)
		assert.Equal(t, c.want, got)
	}
}

func TestStatementTextRefusals(t *testing.T) {
	_, err := Statement{Binders: "∃m:num.", Conclusion: "m = m"}.Text()
	require.Error(t, err)
	assert.Contains(t, err.Error(), "universal")
	_, err = Statement{Binders: "∀m:num. m = m", Conclusion: "m = m"}.Text()
	require.Error(t, err)
	_, err = Statement{Binders: "∀m:num."}.Text()
	require.Error(t, err)
	assert.Contains(t, err.Error(), "no Conclusion")
	_, err = Statement{Hypotheses: []string{"p ⊢ q"}, Conclusion: "q"}.Text()
	require.Error(t, err)
	assert.Contains(t, err.Error(), "no ⊢")
	_, err = Statement{Hypotheses: []string{"p ∧"}, Conclusion: "q"}.Text()
	require.Error(t, err)
	assert.Contains(t, err.Error(), "Hypotheses[0]")
}

func TestStatementBinderNames(t *testing.T) {
	names, err := Statement{Binders: "∀L:field_on(A). ∀k:set(A). ∀t e:A."}.BinderNames()
	require.NoError(t, err)
	assert.Equal(t, []string{"L", "k", "t", "e"}, names)
	names, err = Statement{}.BinderNames()
	require.NoError(t, err)
	assert.Nil(t, names)
}

func TestSplitStatement(t *testing.T) {
	s, ok := SplitStatement("∀m n:num. m ≤ n ∧ (∃d:num. n = m + d) ⇒ m < n ∨ m = n")
	require.True(t, ok)
	assert.Equal(t, Statement{Binders: "∀m n:num.", Hypotheses: []string{"m ≤ n", "∃d:num. n = m + d"}, Conclusion: "m < n ∨ m = n"}, s)

	// A parenthesized conjunction is one hypothesis; the ∧-spine is split.
	s, ok = SplitStatement("∀m:num. (a ∧ b) ∧ c ⇒ m = m")
	require.True(t, ok)
	assert.Equal(t, []string{"a ∧ b", "c"}, s.Hypotheses)
	s, ok = SplitStatement("∀m:num. a ∧ b ∧ c ⇒ m = m")
	require.True(t, ok)
	assert.Equal(t, []string{"a", "b", "c"}, s.Hypotheses)

	// No implication: the body is the conclusion. A curried chain keeps
	// its tail in the conclusion.
	s, ok = SplitStatement("∀m n:num. m + n = n + m")
	require.True(t, ok)
	assert.Equal(t, Statement{Binders: "∀m n:num.", Conclusion: "m + n = n + m"}, s)
	s, ok = SplitStatement("∀m:num. p ⇒ q ⇒ m = m")
	require.True(t, ok)
	assert.Empty(t, s.Hypotheses, "a curried statement lists no hypotheses")
	assert.Equal(t, "p ⇒ (q ⇒ m = m)", s.Conclusion, "the printer parenthesizes a chained ⇒")
	s, ok = SplitStatement("∀x:num. p(x) ⇒ ∀y:num. q(y) ⇒ x = y")
	require.True(t, ok)
	assert.Empty(t, s.Hypotheses, "an interleaved statement lists no hypotheses")
	assert.Equal(t, "∀x:num.", s.Binders)
	// A conclusion that quantifies without implying is still the consequent.
	s, ok = SplitStatement("∀x:num. p(x) ⇒ ∀y:num. q(y)")
	require.True(t, ok)
	assert.Equal(t, []string{"p(x)"}, s.Hypotheses)

	// A leading ∃ is not a binder prefix.
	s, ok = SplitStatement("∃m:num. m = m")
	require.True(t, ok)
	assert.Equal(t, "", s.Binders)
	assert.Equal(t, "∃m:num. m = m", s.Conclusion)

	_, ok = SplitStatement("p ⊢ q")
	assert.False(t, ok)
	_, ok = SplitStatement("p ∧")
	assert.False(t, ok)
}

// TestSplitStatementRoundTrip: the parts assemble to the text the
// formatter gives, for corpus-shaped statements.
func TestSplitStatementRoundTrip(t *testing.T) {
	inputs := []string{
		"∀m n:num. m ≤ n ∧ (∃d:num. n = m + d) ⇒ m < n ∨ m = n",
		"∀L:field_on(A). ∀k:set(A). ∀t e:A. ∀E:set(A). ∀N:(A → int). subfield(L, k) ∧ t ∈ L.carrier ∧ t ≠ L.zero ∧ e ∉ E ⇒ fst(«Q») = set_mul(L.add, fst(«S»), fst(«P»))",
		"∀s t:(A → bool). s ∪ t = t ∪ s",
		"∀P:(num → num). (∃B:num. ∀n:num. P(n) ≤ B) ⇔ ∃A B:num. ∀n:num. n * P(n) ≤ A * n + B",
		"∀x:num. (∀y:num. y ≤ x) ⇒ x = 0",
		"∀m:num. p ⇒ q ⇒ m = m",
		"∀m:num. (a ∧ b) ∧ c ⇒ m = m",
		"∀x:num. x = 0 ∨ (0 < x ∧ 0 ≤ x) ⇒ x = x",
	}
	for _, in := range inputs {
		canonical, err := FormatStmtText(in)
		require.NoError(t, err, in)
		s, ok := SplitStatement(in)
		require.True(t, ok, in)
		got, err := s.Text()
		require.NoError(t, err, "%s: %+v", in, s)
		assert.Equal(t, canonical, got, "%+v", s)
	}
}

// TestCanonicalParts: a text and its parts are one statement printed
// two ways — the parts of a text the author bracketed beyond the
// grammar's need assemble to its canonical spelling, a curried text has
// parts with no hypothesis, and a text that does not read has none.
func TestCanonicalParts(t *testing.T) {
	s, ok := CanonicalParts("∀n:num. ∀s:set(B). s ∈ c(n) ⇒ m(c, (λk:num. λx:B. x), n, s) = s")
	require.True(t, ok)
	assert.Equal(t, Statement{
		Binders:    "∀n:num. ∀s:set(B).",
		Hypotheses: []string{"s ∈ c(n)"},
		Conclusion: "m(c, λk:num. λx:B. x, n, s) = s",
	}, s)
	s, ok = CanonicalParts("∀m:num. p ⇒ q ⇒ m = m")
	require.True(t, ok)
	assert.Empty(t, s.Hypotheses)
	_, ok = CanonicalParts("p ∧")
	assert.False(t, ok)
	_, ok = CanonicalParts("x:num ⊢ x = x")
	assert.False(t, ok)
}

// TestAfterPrefix: a law's statement after its door's opening is the
// law's body — the components' binders and the predicate at them cut,
// a binder group split where the cut falls inside it — and a statement
// that does not open as the prefix does has no body there.
func TestAfterPrefix(t *testing.T) {
	split := func(text string) Statement {
		s, ok := SplitStatement(text)
		require.True(t, ok, text)
		return s
	}
	body, ok := split("∀X:(num → set(A)). ∀d s:(num → num → A → A). ∀f:A. quasi_category(X, d, s) ∧ f ∈ X(1) ⇒ simplicial_set(X, d, s)").
		AfterPrefix(split("∀X:(num → set(A)). ∀d s:(num → num → A → A). quasi_category(X, d, s) ⇒ ⊤"))
	require.True(t, ok)
	assert.Equal(t, Statement{Binders: "∀f:A.", Hypotheses: []string{"f ∈ X(1)"}, Conclusion: "simplicial_set(X, d, s)"}, body)

	body, ok = split("∀R:comm_ring(A). ∀c x:A. c * c = c ⇒ R.zero * x = R.zero").AfterPrefix(split("∀R:comm_ring(A). ⊤"))
	require.True(t, ok)
	assert.Equal(t, Statement{Binders: "∀c x:A.", Hypotheses: []string{"c * c = c"}, Conclusion: "R.zero * x = R.zero"}, body)

	body, ok = split("∀d s t:num. s = t").AfterPrefix(split("∀d s:num. ⊤"))
	require.True(t, ok)
	assert.Equal(t, Statement{Binders: "∀t:num.", Conclusion: "s = t"}, body, "the group is split at the cut")

	body, ok = split("∀d s:num. s = d").AfterPrefix(split("∀d s:num. ⊤"))
	require.True(t, ok)
	assert.Equal(t, Statement{Conclusion: "s = d"}, body, "a prefix that is every binder leaves none")

	for _, text := range []string{
		"∀Y:(num → set(A)). ∀d s:(num → num → A → A). quasi_category(Y, d, s) ⇒ simplicial_set(Y, d, s)",
		"∀X:(num → set(A)). ∀d s:(num → num → A → A). simplicial_set(X, d, s) ⇒ quasi_category(X, d, s)",
		"∀X:(num → set(A)). simplicial_set(X, d, s)",
	} {
		_, ok := split(text).AfterPrefix(split("∀X:(num → set(A)). ∀d s:(num → num → A → A). quasi_category(X, d, s) ⇒ ⊤"))
		assert.False(t, ok, text)
	}
}

func TestStandardParts(t *testing.T) {
	s, err := StandardParts("∀x y:num. x ≤ y ∧ y ≤ x ⇒ x = y")
	require.NoError(t, err)
	assert.Equal(t, Statement{Binders: "∀x y:num.", Hypotheses: []string{"x ≤ y", "y ≤ x"}, Conclusion: "x = y"}, s)
	s, err = StandardParts("∀x:num. x = x")
	require.NoError(t, err)
	assert.Equal(t, Statement{Binders: "∀x:num.", Conclusion: "x = x"}, s)
	_, err = StandardParts("∀x:num. p(x) ⇒ ∀y:num. q(y)")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "binds again")
	_, err = StandardParts("∀x:num. p(x) ⇒ q(x) ⇒ r(x)")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "a premise after its premises")
}
