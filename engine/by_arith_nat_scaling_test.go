package engine

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_NatScaling: a goal over ℕ that compares two products sharing
// factors follows from the comparison of what is left of them (omega
// nat_scaling.go), whatever the order and the grouping of the factors, and
// two products with no factor in common from their factors compared
// pairwise.
func TestByArith_NatScaling(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a left factor", "∀x y z:num. y ≤ z ⇒ x * y ≤ x * z", strips, []int{0}},
		{"a right factor", "∀x y z:num. y ≤ z ⇒ y * x ≤ z * x", strips, []int{0}},
		{"the factor on opposite sides", "∀x y z:num. y ≤ z ⇒ x * y ≤ z * x", strips, []int{0}},
		{"strictly, by a positive factor", "∀x y z:num. y < z ∧ 0 < x ⇒ x * y < x * z", strips, []int{0}},
		{"strictly, by a factor that is not zero", "∀x y z:num. y < z ∧ ¬(x = 0) ⇒ y * x < z * x", strips, []int{0}},
		{"a product against its factor", "∀x y:num. y ≤ 1 ⇒ x * y ≤ x", strips, []int{0}},
		{"a factor against its product", "∀x y:num. 0 < y ⇒ x ≤ y * x", strips, []int{0}},
		{"two products, factor by factor", "∀x y z w:num. y ≤ z ∧ x ≤ w ⇒ x * y ≤ w * z", strips, []int{0}},
		{"two products, the factors crossed", "∀x y z w:num. y ≤ z ∧ x ≤ w ⇒ x * y ≤ z * w", strips, []int{0}},
		{"a shared factor of three", "∀x a b c d:num. a ≤ b ∧ c ≤ d ⇒ x * a * c ≤ x * b * d", strips, []int{0}},
		{"beside a common summand", "∀x y z c:num. y ≤ z ⇒ x * y + c ≤ x * z + c", strips, []int{0}},
		{"summand by summand",
			"∀x y z u v:num. y ≤ z ∧ u ≤ v ⇒ x * y + x * u ≤ x * z + x * v", strips, []int{0}},
		{"a truncated difference times a factor", "∀a b w:num. b ≤ a ⇒ (a - b) * w ≤ a * w", strips, []int{0}},
		// A goal that is no comparison of two products: the hypotheses'
		// comparisons scaled by the cofactors the sequent spells.
		{"a premise's comparison scaled into a sum", "∀B S c q r:num. B ≤ S ∧ c ≤ q + B * r ⇒ c ≤ q + S * r", strips, []int{0}},
		{"a bound scaled by its cofactor", "∀d p i:num. 2 ≤ p ∧ d ≤ i ∧ 0 < d ⇒ suc(d) ≤ p * i", strips, []int{0}},
		{"a positive factor absorbs a cost",
			"∀B S c q r k:num. B ≤ S ∧ c ≤ k + q ∧ k ≤ q + B * r ∧ 0 < r ⇒ c ≤ q + q + (S + q) * r", strips, []int{0}},
		{"a strict bound, squared", "∀s g c:num. s < g ∧ c = s * s ∧ g * g ≤ c ⇒ ⊥", strips, []int{0}},
	})
}

// TestByArith_NatCancellation: a hypothesis over ℕ whose two sides share
// factors shown positive compares what is left of them — an equation, a
// `≤`, and a `<`, which needs no positivity and gives the factor's.
func TestByArith_NatCancellation(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"an equation, the factor positive", "∀x y z:num. 0 < x ∧ x * y = x * z ⇒ y = z", strips, []int{0}},
		{"an equation, the factor not zero", "∀x y z:num. ¬(x = 0) ∧ y * x = z * x ⇒ y = z", strips, []int{0}},
		{"an equation, the factor on opposite sides", "∀x y z:num. 0 < x ∧ x * y = z * x ⇒ y = z", strips, []int{0}},
		{"an equation, a successor for a factor", "∀x y z:num. (x + 1) * y = (x + 1) * z ⇒ y = z", strips, []int{0}},
		{"an equation, a power of a positive base",
			"∀p a b n:num. 0 < p ∧ p ^ n * a = p ^ n * b ⇒ a = b", strips, []int{0}},
		{"an equation, a power of two", "∀a b n:num. 2 ^ n * a = 2 ^ n * b ⇒ a = b", strips, []int{0}},
		{"an equation, two shared factors",
			"∀x y w z:num. 0 < x ∧ 0 < w ∧ x * y * w = x * z * w ⇒ y = z", strips, []int{0}},
		{"an equation against the factor itself", "∀x y:num. 0 < x ∧ x * y = x ⇒ y = 1", strips, []int{0}},
		{"an order", "∀x y z:num. 0 < x ∧ x * y ≤ x * z ⇒ y ≤ z", strips, []int{0}},
		{"an order written from the right", "∀x y z:num. 0 < x ∧ x * y ≥ x * z ⇒ z ≤ y", strips, []int{0}},
		{"an order against the factor itself", "∀x y:num. 0 < x ∧ x * y ≤ x ⇒ y ≤ 1", strips, []int{0}},
		{"a strict order, the factor unknown", "∀x y z:num. x * y < x * z ⇒ y < z", strips, []int{0}},
		{"a strict order shows its factor positive", "∀x y z:num. x * y < z * x ⇒ 0 < x", strips, []int{0}},
		{"the cancelled comparison feeds a sum", "∀x y z c:num. 0 < x ∧ x * y ≤ x * z ⇒ y + c ≤ z + c", strips, []int{0}},
		// The scaled comparison is one the premises prove and none states.
		{"two equations with a side in common",
			"∀p n k c:num. 2 ≤ p ∧ n * n = p * (k * k) ∧ n * n = p * (p * (c * c)) ⇒ k * k = p * (c * c)", strips, []int{0}},
		{"two orders through a common bound", "∀p a b X:num. 0 < p ∧ p * a ≤ X ∧ X ≤ p * b ⇒ a ≤ b", strips, []int{0}},
		{"a strict order through a common bound", "∀p a b X:num. p * a < X ∧ X ≤ b * p ⇒ a < b", strips, []int{0}},
		{"a bound of squares against a product",
			"∀p n x y:num. 2 ≤ p ∧ x * x + y * y + 1 = p * n ∧ (2 * x) * (2 * x) ≤ p * p ∧ (2 * y) * (2 * y) ≤ p * p ∧ 2 * 2 ≤ p * p ⇒ n < p",
			strips, []int{0}},
		{"a negated order", "∀x y:num. ¬(y < x * y) ∧ 0 < y ∧ 0 < x ⇒ x = 1", strips, []int{0}},
		{"a negated order, the factors' positivity from disequations",
			"∀x y:num. ¬(y < x * y) ∧ ¬(y = 0) ∧ ¬(x = x * y) ⇒ x = 1", strips, []int{0}},
	})
}

// TestByArith_NatPowerSign: on ℕ a power of a positive base is positive,
// and a power that is zero has a zero base and a positive exponent (omega
// nat_products.go).
func TestByArith_NatPowerSign(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a power of a positive base", "∀x n:num. 0 < x ⇒ 0 < x ^ n", strips, []int{0}},
		{"a power of a base that is not zero", "∀x n:num. ¬(x = 0) ⇒ 1 ≤ x ^ n", strips, []int{0}},
		{"not zero", "∀x n:num. 0 < x ⇒ ¬(x ^ n = 0)", strips, []int{0}},
		{"a power of a numeral", "∀n:num. 0 < 2 ^ n", []string{"strip_quant"}, nil},
		{"a zero power has a zero base", "∀x n:num. x ^ n = 0 ⇒ x = 0", strips, []int{0}},
		{"a zero power has a positive exponent", "∀x n:num. 0 = x ^ n ⇒ 0 < n", strips, []int{0}},
		{"a zero power of a positive base", "∀x n:num. x ^ n = 0 ∧ 0 < x ⇒ ⊥", strips, []int{0}},
	})
}

// TestByArith_NatScalingDeclines: statements over ℕ that do not follow.
func TestByArith_NatScalingDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	for _, row := range []struct{ stmt, why string }{
		{"∀x y z:num. x * y = x * z ⇒ y = z", "false at x = 0"},
		{"∀x y z:num. x * y ≤ x * z ⇒ y ≤ z", "false at x = 0"},
		{"∀x y z:num. y < z ⇒ x * y < x * z", "false at x = 0"},
		{"∀x y z:num. 0 < x ∧ x * y ≤ x * z ⇒ y < z", "false at y = z"},
		{"∀x y z:num. y ≤ z ⇒ x * z ≤ x * y", "false at x = 1, y < z"},
		{"∀x y z w:num. y ≤ z ⇒ x * y ≤ w * z", "false at w = 0"},
		{"∀B S c q r:num. S ≤ B ∧ c ≤ q + B * r ⇒ c ≤ q + S * r", "false at S = 0, B = c = r = 1, q = 0"},
		{"∀d p i:num. 1 ≤ p ∧ d ≤ i ∧ 0 < d ⇒ suc(d) ≤ p * i", "false at p = d = i = 1"},
		{"∀p a b X:num. p * a = X ∧ X = p * b ⇒ a = b", "false at p = 0"},
		{"∀p a b X:num. 0 < p ∧ p * a ≤ X ∧ X ≤ p * b ⇒ a < b", "false at a = b"},
		{"∀x n:num. 0 < x ^ n ⇒ 0 < x", "false at n = 0"},
		{"∀x n:num. x ^ n = 0 ⇒ n = 0", "false at x = 0, n = 1"},
	} {
		res := byArithOutcome(t, e, row.stmt, []string{"strip_quant", "strip_imp"}, []ByHypSpec{{HypIndex: idx(0)}})
		require.False(t, res.Success, "%s closed, and it is %s", row.stmt, row.why)
		require.NotEmpty(t, res.Diagnostics)
		require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
			"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
	}
}
