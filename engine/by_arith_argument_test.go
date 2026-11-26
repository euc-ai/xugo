package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_ArgumentsDecideEqual: two applications of one head the
// layers do not read are equal where their arguments decide equal, the
// argument equations asked of the arith closer itself under the premises
// (omega argument_congruence.go) — a function's value, a predicate, a
// membership, a set-builder's bound, an index the premises fix.
func TestByArith_ArgumentsDecideEqual(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	none := []string{"strip_quant"}
	one := []string{"strip_quant", "strip_imp"}
	two := []string{"strip_quant", "strip_imp", "strip_imp"}
	three := []string{"strip_quant", "strip_imp", "strip_imp", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"an identity of the ring in a function's argument", "∀f:(num → A). ∀n:num. f(n + 1 + 1) = f(n + 2)", none, nil},
		{"a successor against a sum", "∀f:(num → A). ∀n:num. f(suc(n)) = f(n + 1)", none, nil},
		{"over ℝ", "∀g:(real → A). ∀x:real. g(x + &1 + &1) = g(x + &2)", none, nil},
		{"several arguments", "∀d:(num → num → A → A). ∀x:A. ∀n:num. d(n + 1 + 1, 0 + n, x) = d(n + 2, n, x)", none, nil},
		{"an application at a number carrier", "∀g:(num → num). ∀n:num. g(n + 1 + 1) = g(n + 2)", none, nil},
		{"an index the premises fix (simplicial_set.SpineEnds)",
			"∀f:(num → A). ∀n i q:num. i + 1 < n ∧ q = n - 1 - (i + 1) ⇒ f(n - 1 - i) = f(q + 1)", one, []int{0}},
		{"the same index in a face of four arguments",
			"∀d:(num → num → num → A → A). ∀x:A. ∀n i q:num. i + 1 < n ∧ q = n - 1 - (i + 1) ⇒ " +
				"d(n, n, n - 1 - i, x) = d(n, n, q + 1, x)", one, []int{0}},
		{"an equation with no variable side", "∀f:(num → A). ∀n i q:num. n - 1 - i = q + 1 ⇒ f(n - 1 - i) = f(q + 1)", one, []int{0}},
		{"a truncation the premise makes exact", "∀f:(num → A). ∀n m:num. m ≤ n ⇒ f(n - m + m) = f(n)", one, []int{0}},
		{"a chain of three comparisons", "∀f:(real → A). ∀x y z:real. x ≤ y ⇒ y ≤ z ⇒ z ≤ x ⇒ f(x) = f(y)", three, []int{0, 1, 2}},
		{"a predicate at a premise", "∀P:(num → bool). ∀n i:num. i < n ⇒ P(n - i - 1 + 1) ⇒ P(n - i)", two, []int{0, 1}},
		{"a predicate's negation at a premise",
			"∀P:(num → A → bool). ∀x:A. ∀n i q:num. i + 1 < n ⇒ q = n - 1 - (i + 1) ⇒ ¬P(q + 1, x) ⇒ ¬P(n - 1 - i, x)",
			three, []int{0, 1, 2}},
		{"a membership at a premise", "∀S:(num → set(A)). ∀x:A. ∀n i:num. i < n ⇒ x ∈ S(n - i - 1 + 1) ⇒ x ∈ S(n - i)", two, []int{0, 1}},
		{"an equation at a premise equation, its sides each a spelling apart",
			"∀f g:(num → A). ∀n m:num. f(n + 1) = g(m) ⇒ g(m + 0) = f(1 + n)", one, []int{0}},
		{"a set-builder's bound", "∀n:num. {i:num | i < n + 1} = {i:num | i < suc(n)}", none, nil},
		{"under card", "∀n i:num. i < n ⇒ card({j:num | j < n - i - 1 + 1}) = card({j:num | j < n - i})", one, []int{0}},
	})
}

// TestByArith_ArgumentsDecideEqualDeclines: statements that do not follow
// fail as a leaf the closer did not close, and so does a comparison of two
// atoms at a number carrier, which is the layers' formula and is not read
// by its arguments.
func TestByArith_ArgumentsDecideEqualDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	for _, row := range []struct {
		stmt   string
		strips int
		why    string
	}{
		{"∀f:(num → A). ∀n:num. f(n + 1) = f(n + 2)", 0, "false where f is one to one"},
		{"∀f:(num → A). ∀n i:num. f(n - 1 - i) = f((n - 1 - (i + 1)) + 1)", 0, "false at n = 0, where the monus truncates"},
		{"∀f:(num → A). ∀n m:num. f(n - m + m) = f(n)", 0, "false at n < m"},
		{"∀P:(num → bool). ∀n:num. P(n + 1) ⇒ P(n + 2)", 1, "false where P holds at one point"},
		{"∀f g:(num → A). ∀n:num. f(n + 2) = g(n + 2)", 0, "two heads"},
		{"∀g:(num → real). ∀n:num. g(n + 1 + 1) ≤ g(n + 2)", 0, "a comparison of atoms is the layers' formula"},
	} {
		strips := []string{"strip_quant"}
		var hyps []ByHypSpec
		for i := 0; i < row.strips; i++ {
			strips = append(strips, "strip_imp")
			hyps = append(hyps, ByHypSpec{HypIndex: idx(i)})
		}
		res := byArithOutcomeIn(t, e, constSyntax(), row.stmt, strips, hyps)
		require.False(t, res.Success, "%s closed: %s", row.stmt, row.why)
		require.NotEmpty(t, res.Diagnostics)
		require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
			"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
	}
}
