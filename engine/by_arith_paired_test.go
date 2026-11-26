package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_PairedComparisons: two premises that bound one difference
// from both sides are the equation of the sides, and a variable it defines
// is read at its definition wherever the leaf names it — under a product,
// inside an atom — as a stated `v = e` is (omega paired_equation.go). The
// pair is read in every spelling the linear layer reads a comparison in,
// and on ℕ and ℤ a strict comparison is its non-strict neighbour.
func TestByArith_PairedComparisons(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	one := []string{"strip_quant", "strip_imp"}
	two := []string{"strip_quant", "strip_imp", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"two variables, inside an atom, over ℝ",
			"∀x y:real. ∀f:(real → real). x ≤ y ⇒ y ≤ x ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"the pair as one conjunction",
			"∀x y:real. ∀f:(real → real). x ≤ y ∧ y ≤ x ⇒ f(x) = f(y)", one, []int{0}},
		{"written from the right",
			"∀x y:real. ∀f:(real → real). x ≥ y ⇒ y ≥ x ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"one of them a negated strict comparison",
			"∀x y:real. ∀f:(real → real). x ≤ y ⇒ ¬(x < y) ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"a value, under a product, over ℝ", "∀t A:real. t ≤ &0 ⇒ &0 ≤ t ⇒ t * A = &0", two, []int{0, 1}},
		{"a value, in a comparison of products", "∀t A:real. t ≤ &0 ⇒ &0 ≤ t ⇒ t * A ≤ &0", two, []int{0, 1}},
		{"a value, under a product, over ℤ", "∀t A:int. t ≤ &0 ⇒ &0 ≤ t ⇒ t * A = &0", two, []int{0, 1}},
		{"two variables, inside an atom, over ℤ",
			"∀x y:int. ∀f:(int → int). x ≤ y ⇒ y ≤ x ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"two variables, inside an atom, over ℕ",
			"∀x y:num. ∀f:(num → num). x ≤ y ⇒ y ≤ x ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"two variables, under a product, over ℕ", "∀x y A:num. x ≤ y ⇒ y ≤ x ⇒ x * A = y * A", two, []int{0, 1}},
		{"a variable against a sum",
			"∀x y:real. ∀f:(real → real). x ≤ y + &1 ⇒ y + &1 ≤ x ⇒ f(x) = f(y + &1)", two, []int{0, 1}},
		{"one of them written as a difference",
			"∀x y:real. ∀f:(real → real). x - y ≤ &0 ⇒ y ≤ x ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"a strict neighbour, over ℤ",
			"∀x y:int. ∀f:(int → int). x ≤ y ⇒ y < x + &1 ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"a strict neighbour, over ℕ",
			"∀x y:num. ∀f:(num → num). x ≤ y ⇒ y < x + 1 ⇒ f(x) = f(y)", two, []int{0, 1}},
		{"the pair a split's branch makes with a premise (the modulus's arm &0 ≤ x)",
			"∀x w:real. x ≤ &0 ⇒ |x| * w = -(x * w)", one, []int{0}},
		{"the pair a split's branch makes, over ℤ",
			"∀x w:int. x ≤ &0 ⇒ |x| * w = -(x * w)", one, []int{0}},
	})
}

// TestByArith_StrictFromAPair: the same pair from the other side of the
// turnstile. A strict goal `a < b` denies `b ≤ a`; beside a premise
// `a ≤ b` that is the equation `a = b`, and a premise the equation makes
// false proves the goal (omega denied_value.go).
func TestByArith_StrictFromAPair(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	two := []string{"strip_quant", "strip_imp", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"two points an atom tells apart, over ℝ",
			"∀x y:real. ∀f:(real → real). x ≤ y ⇒ ¬(f(x) = f(y)) ⇒ x < y", two, []int{0, 1}},
		{"the goal written from the right",
			"∀x y:real. ∀f:(real → real). x ≤ y ⇒ ¬(f(x) = f(y)) ⇒ y > x", two, []int{0, 1}},
		{"the goal a negated comparison",
			"∀x y:real. ∀f:(real → real). x ≤ y ⇒ ¬(f(x) = f(y)) ⇒ ¬(y ≤ x)", two, []int{0, 1}},
		{"over ℤ", "∀x y:int. ∀f:(int → int). x ≤ y ⇒ ¬(f(x) = f(y)) ⇒ x < y", two, []int{0, 1}},
		{"over ℕ", "∀x y:num. ∀f:(num → num). x ≤ y ⇒ ¬(f(x) = f(y)) ⇒ x < y", two, []int{0, 1}},
		{"a factor of a nonzero product is positive where it is not negative",
			"∀t A:real. &0 ≤ t ⇒ ¬(t * A = &0) ⇒ &0 < t", two, []int{0, 1}},
		{"a factor of a positive product", "∀t A:real. &0 ≤ t ⇒ &0 < t * A ⇒ &0 < t", two, []int{0, 1}},
		{"a factor of a nonzero product, over ℤ", "∀t A:int. &0 ≤ t ⇒ ¬(t * A = &0) ⇒ &0 < t", two, []int{0, 1}},
	})
}

// TestByArith_PairedComparisonsDecline: statements that do not follow fail
// as a leaf the closer did not close, and so do two that follow and that
// the pair's reading does not reach: an equation with no variable side
// defines nothing, stated or denied. (A chain of three comparisons is no
// pair either; its goal `f(x) = f(y)` closes by the arguments' equation,
// TestByArith_ArgumentsDecideEqual.)
func TestByArith_PairedComparisonsDecline(t *testing.T) {
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
		{"∀x y:real. ∀f:(real → real). x ≤ y ⇒ f(x) = f(y)", 1, "false at x < y"},
		{"∀x y:real. ∀f:(real → real). x ≤ y ⇒ y < x + &1 ⇒ f(x) = f(y)", 2, "false over ℝ at y = x + 1/2"},
		{"∀x y:real. ∀f:(real → real). x ≤ y ⇒ y ≤ x + &1 ⇒ f(x) = f(y)", 2, "false at y = x + 1"},
		{"∀x y:int. ∀f:(int → int). x ≤ y ⇒ y < x + &2 ⇒ f(x) = f(y)", 2, "false at y = x + 1"},
		{"∀t A:real. t ≤ &0 ⇒ &0 ≤ t + &1 ⇒ t * A = &0", 2, "false at t = -1"},
		{"∀x y:real. ∀f:(real → real). x ≤ y ⇒ ¬(f(x) = f(y)) ⇒ y < x", 2, "false at x < y"},
		{"∀x y:real. ∀f:(real → real). ¬(f(x) = f(y)) ⇒ x < y", 1, "false at y < x"},
		{"∀u A:int. u * &2 = &0 ⇒ u * A = &0", 1, "an equation with no variable side"},
		{"∀g u:int. ¬(g * u = &0) ⇒ ¬(u * &2 = &0)", 1, "the denial of an equation with no variable side"},
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
