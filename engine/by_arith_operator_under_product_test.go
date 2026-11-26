package engine

import (
	"testing"
)

// TestByArith_OperatorUnderAProduct: a piecewise operator multiplied by
// another term. The operator's case split pins it to an arm, and the pinned
// term stands inside a monomial the linear prover reads as one unknown, so
// the branch is read at its pins and goes to the handlers that read a
// product (omega caseSplit, pin_reading.go). No lemma about the operator is
// handed in.
func TestByArith_OperatorUnderAProduct(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a capped factor is at most the other factor",
			"∀d w:real. &0 < w ⇒ real_min(d, &1) * w ≤ w", strips, []int{0}},
		{"a capped positive factor keeps the sign",
			"∀e w:real. &0 < e ∧ &0 < w ⇒ &0 < real_min(e, &1) * w", strips, []int{0}},
		{"a capped factor times a weight below one",
			"∀d w:real. &0 ≤ d ∧ &0 < w ∧ w ≤ &1 ⇒ real_min(d, &1) * w ≤ d", strips, []int{0}},
		{"a capped factor cancelled from a hypothesis",
			"∀a w ε:real. &0 < w ∧ ε ≤ &1 ∧ real_min(a, &1) * w < ε * w ⇒ a < ε", strips, []int{0}},
		{"a cap that does not bind",
			"∀d w:real. &0 < w ∧ d ≤ &1 ⇒ real_min(d, &1) * w = d * w", strips, []int{0}},
		{"a bare conditional under a product",
			"∀d w:real. &0 < w ⇒ COND(d ≤ &1, d, &1) * w ≤ w", strips, []int{0}},
		{"a floored factor is at least the other factor",
			"∀d w:real. &0 < w ⇒ w ≤ real_max(d, &1) * w", strips, []int{0}},
		{"an absolute value under a product",
			"∀x w:real. &0 < w ∧ x ≤ &1 ∧ -(&1) ≤ x ⇒ real_abs(x) * w ≤ w", strips, []int{0}},
		{"a sign under a product",
			"∀x w:real. &0 < w ⇒ real_sgn(x) * w ≤ w", strips, []int{0}},
		{"an absolute value squared",
			"∀x:real. real_abs(x) * real_abs(x) = x * x", []string{"strip_quant"}, nil},
		{"a capped factor, over ℤ",
			"∀d w:int. &0 < w ⇒ int_min(d, &1) * w ≤ w", strips, []int{0}},
		{"an absolute value under a product, over ℤ",
			"∀x w:int. &0 < w ∧ x ≤ &1 ∧ -(&1) ≤ x ⇒ int_abs(x) * w ≤ w", strips, []int{0}},
		{"a capped factor, over ℕ",
			"∀d w:num. nat_min(d, 1) * w ≤ w", []string{"strip_quant"}, nil},
	})
}

// TestByArith_AbsOfKnownSign: an absolute value whose argument has a
// known sign is that argument wherever it stands — a factor, a divisor,
// the base of a symbolic power — and the absolute value of a symbolic
// power of a positive base is the power.
func TestByArith_AbsOfKnownSign(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a factor", "∀r y:real. &0 < r ⇒ real_abs(r) * y = r * y", strips, []int{0}},
		{"a divisor", "∀x y:real. &0 < x ⇒ y / real_abs(x) = y / x", strips, []int{0}},
		{"the base of a symbolic power", "∀c:real. ∀R:num. &0 < c ⇒ real_abs(c) ^ R = c ^ R", strips, []int{0}},
		{"of a symbolic power", "∀c:real. ∀R:num. &0 < c ⇒ real_abs(c ^ R) = c ^ R", strips, []int{0}},
	})
}

// TestByArith_PinReadWhereNoProductReachesIt: the pin is an equation, and
// the reading substitutes it. The products pass reaches a pinned factor
// only through a sign fact about its cofactor and only among its first
// facts; the reading needs neither, and reaches the argument of an opaque
// atom, which no product does.
func TestByArith_PinReadWhereNoProductReachesIt(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a cofactor of unknown sign",
			"∀d w:real. d ≤ &1 ⇒ real_min(d, &1) * w = d * w", strips, []int{0}},
		{"a cofactor of unknown sign, over ℤ",
			"∀d w:int. d ≤ &1 ⇒ int_min(d, &1) * w = d * w", strips, []int{0}},
		{"a cofactor, over ℕ",
			"∀d w:num. d ≤ 1 ⇒ nat_min(d, 1) * w = d * w", strips, []int{0}},
		{"the argument of an opaque atom",
			"∀a b:real. ∀f:real→real. a ≤ b ⇒ f(real_min(a, b)) = f(a)", strips, []int{0}},
		{"thirteen facts ahead of the pin",
			"∀a b c e f g h i j k l m n d w:real. &0 < a ∧ &0 < b ∧ &0 < c ∧ &0 < e ∧ &0 < f ∧ &0 < g ∧ " +
				"&0 < h ∧ &0 < i ∧ &0 < j ∧ &0 < k ∧ &0 < l ∧ &0 < m ∧ &0 < n ∧ a * b ≤ c ∧ " +
				"&0 ≤ d ∧ &0 < w ∧ w ≤ &1 ⇒ real_min(d, &1) * w ≤ d", strips, []int{0}},
	})
}

// TestByArith_OperatorBesideAProduct: an operator that stands in no
// monomial, beside a product. Its split's guard and pin are linear facts
// the product's handlers need — the side condition of a monotone scaling,
// the factors of the products pass — so the branch goes to them as a
// hypothesis split's does.
func TestByArith_OperatorBesideAProduct(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a bound on an absolute value scales",
			"∀x c w:real. real_abs(x) ≤ c ∧ &0 ≤ w ⇒ x * w ≤ c * w", strips, []int{0}},
		{"two bounded terms multiplied",
			"∀x y c:real. real_abs(x) ≤ c ∧ real_abs(y) ≤ c ⇒ x * y ≤ c * c", strips, []int{0}},
		{"a hypothesis split above an operator's pin in a product",
			"∀s d w:real. (s = &1 ∨ s = &2) ∧ &0 < w ⇒ real_min(d, s) * w ≤ &2 * w", strips, []int{0}},
		{"a capped term, no product",
			"∀a ε:real. ε ≤ &1 ∧ real_min(a, &1) < ε ⇒ a < ε", strips, []int{0}},
		{"a product, no operator",
			"∀a w ε:real. &0 < w ∧ a * w < ε * w ⇒ a < ε", strips, []int{0}},
	})
}
