package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_CondOnACompoundCondition: a COND at ℕ, ℤ or ℝ is split
// whatever its condition is — a disjunction, a conjunction, a negation,
// an equation, a statement that is no comparison — by the condition's
// atoms, one at a time (omega compoundCondSplit), where a COND on one
// `<` or `≤` was the only one split.
func TestByArith_CondOnACompoundCondition(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	none := []string{"strip_quant"}
	one := []string{"strip_quant", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"a disjunction, either value in the bound", "∀v t m:num. v + COND(t < m - 1 ∨ t = m, 1, 0) ≤ v + 1", none, nil},
		{"a conjunction", "∀v t m:num. v + COND(t < m ∧ 0 < t, 1, 0) ≤ v + 1", none, nil},
		{"a disjunction the premise decides one way (kuhn.KuhnEarlierBelowExchanged)",
			"∀v t j m:num. j < m ⇒ v + COND(t < j, 1, 0) ≤ v + COND(t < m - 1 ∨ t = m, 1, 0)", one, []int{0}},
		{"an equation", "∀n x:num. COND(n = 0, x, x + 1) ≤ x + 1", none, nil},
		{"an equation whose branch reads it", "∀n x:num. COND(n = 0, x + n, x) = x", none, nil},
		{"a negation", "∀t m x:num. COND(¬(t < m), x, x + 1) ≤ x + 1", none, nil},
		{"an implication", "∀t m x:num. COND(t < m ⇒ m = 0, x, x + 1) ≤ x + 1", none, nil},
		{"over ℤ", "∀a b x:int. COND(a < b ∨ a = b, x, x + &1) ≤ x + &1", none, nil},
		{"over ℤ, each branch on its own facts", "∀a b:int. &0 ≤ COND(a < b ∨ a = b, b - a, a - b)", none, nil},
		{"over ℝ", "∀a b x:real. COND(a < b ∨ a = b, x, x + &1) ≤ x + &1", none, nil},
		{"over ℝ, each branch on its own facts", "∀a b:real. &0 ≤ COND(a < b ∨ a = b, b - a, a - b)", none, nil},
		{"over ℝ, a conjunction that is an equation", "∀a b:real. COND(a ≤ b ∧ b ≤ a, a - b, &0) = &0", none, nil},
		{"a condition that is no comparison", "∀P:bool. ∀x:real. COND(P, x, x + &1) ≤ x + &1", none, nil},
		{"a membership for the condition", "∀S:set(A). ∀p:A. ∀x:num. COND(p ∈ S, x, x + 1) ≤ x + 1", none, nil},
		{"under a product", "∀P Q:bool. ∀x:real. &0 ≤ x ⇒ x * COND(P ∨ Q, &1, &0) ≤ x", one, []int{0}},
		{"under a product on ℕ", "∀x a b:num. x * COND(a < b ∨ a = b, 1, 0) ≤ x", none, nil},
	})
}

// TestByArith_CondClosedWithoutTheSplit: two statements over a COND on a
// compound condition that close with the split by atoms and without it —
// an atom the premise states is read at its value, and two applications
// are compared by their arguments.
func TestByArith_CondClosedWithoutTheSplit(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	one := []string{"strip_quant", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"the first atom stated", "∀P:bool. ∀x:real. P ⇒ COND(P ∧ &0 ≤ x, x, -x) = x ∨ x < &0", one, []int{0}},
		{"inside an application", "∀f:(num → num). ∀a b:num. a ≤ b ⇒ f(COND(a < b ∨ a = b, a, b)) = f(a)", one, []int{0}},
	})
}

// TestByArith_CondOnACompoundConditionDeclines: a bound one value of the
// COND breaks fails as a leaf the arith closer did not close.
func TestByArith_CondOnACompoundConditionDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	for _, row := range []struct{ stmt, why string }{
		{"∀v t m:num. v + COND(t < m - 1 ∨ t = m, 1, 0) ≤ v", "false where the condition holds"},
		{"∀v t m:num. v + 1 ≤ v + COND(t < m ∧ 0 < t, 1, 0)", "false where the condition fails"},
		{"∀a b:real. &0 < COND(a < b ∨ a = b, b - a, a - b)", "false at a = b"},
		{"∀P:bool. ∀x:real. COND(P, x, x + &1) ≤ x", "false where P fails"},
	} {
		res := byArithOutcomeIn(t, e, constSyntax(), row.stmt, []string{"strip_quant"}, nil)
		require.False(t, res.Success, "%s closed: %s", row.stmt, row.why)
		require.NotEmpty(t, res.Diagnostics)
		require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
			"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
	}
}
