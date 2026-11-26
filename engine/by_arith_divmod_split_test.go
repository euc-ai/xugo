package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_HypSplitReadsDivModBounds: `by {arith:true}` on facts about
// an odd number that need a hypothesis split and a bound of nat_mod(n, 2)
// together — the `≠` the parity bridge leaves (`nat_odd(n)` is read as
// `0 ≠ nat_mod(n, 2)`) is a case split, and `nat_mod(n, 2) ≤ n` is a fact
// the decider injects. End to end on the corpus and the production bundles.
func TestByArith_HypSplitReadsDivModBounds(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a nonzero remainder, the dividend not 0",
			"∀n:num. 0 ≠ nat_mod(n, 2) ⇒ n ≠ 0", strips, []int{0}},
		{"a nonzero remainder, the dividend at least 1",
			"∀n:num. 0 ≠ nat_mod(n, 2) ⇒ 1 ≤ n", strips, []int{0}},
		{"an odd number is at least 1",
			"∀n:num. nat_odd(n) ⇒ 1 ≤ n", strips, []int{0}},
		{"a nonzero remainder and n ≠ 1",
			"∀n:num. 0 ≠ nat_mod(n, 2) ∧ n ≠ 1 ⇒ 1 < n", strips, []int{0}},
		{"an odd number other than 1 exceeds 1",
			"∀n:num. nat_odd(n) ∧ n ≠ 1 ⇒ 1 < n", strips, []int{0}},
		{"a symbolic divisor",
			"∀n m:num. 0 ≠ nat_mod(n, m) ⇒ n ≠ 0", strips, []int{0}},
		{"a nonzero quotient",
			"∀n:num. 0 ≠ nat_div(n, 2) ⇒ n ≠ 0", strips, []int{0}},
	})
}

// TestByArith_HypSplitWithDivModBoundsDeclines: the same split and bounds
// on a goal that is false at n = 1 fail as a leaf the closer did not close.
func TestByArith_HypSplitWithDivModBoundsDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	res := byArithOutcome(t, byArithEngine(t), "∀n:num. nat_odd(n) ⇒ 2 ≤ n",
		[]string{"strip_quant", "strip_imp"}, []ByHypSpec{{HypIndex: idx(0)}})
	require.False(t, res.Success, "nat_odd(n) ⊢ 2 ≤ n closed, and it is false at n = 1")
	require.NotEmpty(t, res.Diagnostics)
	require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
		"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
}
