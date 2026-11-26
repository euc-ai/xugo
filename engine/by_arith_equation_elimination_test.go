package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_EliminatesEquations: `by {arith:true}` on goals whose
// contradiction is the rounding of a row an equation's substitution leaves,
// on the production bundles. The equation is a hypothesis in the first
// group and Division's identity, injected for the quotient or the remainder
// the goal names, in the second; the third is the same step over ℤ.
func TestByArith_EliminatesEquations(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"an even number above 0, the half named",
			"∀n q:num. n = 2 * q ∧ 0 < n ⇒ 2 ≤ n", strips, []int{0}},
		{"the half on the left",
			"∀n q:num. 2 * q = n ∧ 0 < n ⇒ 2 ≤ n", strips, []int{0}},
		{"an odd number above 1, the half named",
			"∀n q:num. n = 2 * q + 1 ∧ 1 < n ⇒ 3 ≤ n", strips, []int{0}},
		{"quotient and remainder as variables",
			"∀n q r:num. n = 2 * q + r ∧ r < 2 ∧ 0 < r ∧ 1 < n ⇒ 3 ≤ n", strips, []int{0}},
		{"no number is twice one and one more than twice another",
			"∀n q p:num. n = 2 * q ∧ n = 2 * p + 1 ⇒ 0 = 1", strips, []int{0}},
		{"an equation two inequalities state",
			"∀n q:num. 2 * q ≤ n ∧ n ≤ 2 * q ∧ 1 ≤ n ∧ n ≤ 1 ⇒ 0 = 1", strips, []int{0}},

		{"an odd number above 1 is at least 3",
			"∀n:num. nat_odd(n) ∧ 1 < n ⇒ 3 ≤ n", strips, []int{0}},
		{"an even number above 0 is at least 2",
			"∀n:num. nat_even(n) ∧ 0 < n ⇒ 2 ≤ n", strips, []int{0}},
		{"two odd numbers are two apart",
			"∀m n:num. nat_odd(m) ∧ nat_odd(n) ∧ m < n ⇒ m + 2 ≤ n", strips, []int{0}},
		{"a residue mod 3",
			"∀n:num. nat_mod(n, 3) = 2 ∧ 2 < n ⇒ 5 ≤ n", strips, []int{0}},
		{"the quotient of a number from 3 up",
			"∀n:num. 3 ≤ n ⇒ 1 ≤ nat_div(n, 2)", strips, []int{0}},
		{"the remainder of a shifted multiple",
			"∀n:num. nat_mod(4 * n + 3, 2) = 1", []string{"strip_quant"}, nil},

		{"over ℤ, the half named",
			"∀n q:int. n = &2 * q + &1 ∧ &1 < n ⇒ &3 ≤ n", strips, []int{0}},
		{"over ℤ, the remainder",
			"∀n:int. int_rem(n, &2) = &1 ∧ &1 < n ⇒ &3 ≤ n", strips, []int{0}},
		{"over ℤ, an equation two inequalities state",
			"∀n q:int. &2 * q ≤ n ∧ n ≤ &2 * q ∧ &1 ≤ n ∧ n ≤ &1 ⇒ q < q", strips, []int{0}},
	})
}

// TestByArith_EquationEliminationDeclines: the same facts on goals one past
// what they give fail as a leaf the closer did not close.
func TestByArith_EquationEliminationDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	for _, row := range []struct{ stmt, why string }{
		{"∀n:num. nat_odd(n) ∧ 1 < n ⇒ 4 ≤ n", "false at n = 3"},
		{"∀n:num. nat_even(n) ∧ 0 < n ⇒ 3 ≤ n", "false at n = 2"},
		{"∀n q:num. n = 2 * q ∧ 0 < n ⇒ 3 ≤ n", "false at n = 2"},
		{"∀n q:int. n = &2 * q + &1 ∧ n < &1 ⇒ n < n", "satisfied at n = −1"},
	} {
		res := byArithOutcome(t, e, row.stmt, []string{"strip_quant", "strip_imp"}, []ByHypSpec{{HypIndex: idx(0)}})
		require.False(t, res.Success, "%s closed, and it is %s", row.stmt, row.why)
		require.NotEmpty(t, res.Diagnostics)
		require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
			"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
	}
}
