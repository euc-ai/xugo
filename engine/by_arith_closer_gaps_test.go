package engine

import (
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_SplitLeaf: a value known up to a finite disjunction reaches a
// product. The split's branch is not linear, and its leaf goes to the
// handlers that read the hypotheses — the products pass over ℤ and ℝ, the
// pin's substitution over ℕ (omega caseSplit).
func TestByArith_SplitLeaf(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a sign squared, over ℝ", "∀s:real. s = &1 ∨ s = -(&1) ⇒ s * s = &1", strips, []int{0}},
		{"a sign squared, over ℤ", "∀s:int. s = &1 ∨ s = -(&1) ⇒ s * s = &1", strips, []int{0}},
		{"one of two values squared, over ℕ", "∀s:num. s = 1 ∨ s = 2 ⇒ s * s ≤ 4", strips, []int{0}},
		{"a remainder from two values", "∀d:num. d = 0 ∨ d = 2 ⇒ 0 = nat_mod(d, 2)", strips, []int{0}},
	})
}

// TestByArith_StrictTimesNonStrict: the products pass pairs a strict fact
// with a non-strict one whatever the strict difference is written over, a
// monomial whose factors differ in strictness has its sign row, and an
// inverse standing alone takes its sign from its argument's.
func TestByArith_StrictTimesNonStrict(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a point of a segment",
			"∀t x y:real. &0 ≤ t ∧ t ≤ &1 ∧ x < y ⇒ x ≤ t * x + (&1 - t) * y", strips, []int{0}},
		{"a product below one",
			"∀a b:real. -(&1) < a ∧ a < &1 ∧ &0 ≤ b ∧ b ≤ &1 ⇒ a * b < &1", strips, []int{0}},
		{"a slack product",
			"∀t r A:real. t ≤ &1 ∧ A < r ⇒ &0 ≤ (&1 - t) * (r - A)", strips, []int{0}},
		{"a quotient's sign through an equation",
			"∀x p s:real. s = x / p ∧ &0 < p ∧ &0 ≤ x ⇒ &0 ≤ s", strips, []int{0}},
		{"a quotient's sign inside a sum",
			"∀M x:real. &0 ≤ M ∧ &0 < x ⇒ &1 ≤ (M + &1) / x + &1", strips, []int{0}},
	})
}

// TestByArith_BoundsThroughAnOperator: a bound stated through a square, an
// absolute value, a cast or a quotient by a sum reaches the product or the
// comparison it bounds.
func TestByArith_BoundsThroughAnOperator(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a comparison of squares", "∀x y:real. x ^ 2 ≤ y ^ 2 ∧ &0 ≤ y ⇒ x ≤ y", strips, []int{0}},
		{"the absolute value of a product below one",
			"∀a b:real. real_abs(a) < &1 ∧ &0 ≤ b ∧ b ≤ &1 ⇒ real_abs(a * b) < &1", strips, []int{0}},
		{"a factor of absolute value below one",
			"∀k x:real. real_abs(k) < &1 ∧ &0 ≤ x ⇒ k * x ≤ x", strips, []int{0}},
		{"a quotient by a sum",
			"∀ε a b:real. &0 < ε ∧ a < b ⇒ ε / (b - a + &1) * (b - a) < ε", strips, []int{0}},
		{"a quotient by a sum whose sign is stated",
			"∀ε a b:real. &0 < ε ∧ a < b ∧ &0 < b - a + &1 ⇒ ε / (b - a + &1) * (b - a) < ε", strips, []int{0}},
		{"a cast's sign in a product", "∀n:num. ∀x:real. &0 ≤ x ⇒ &0 ≤ &n * x", strips, []int{0}},
		{"a cast of a product in a product",
			"∀p:num. ∀x:real. &(2 * p) * x = &2 * &p * x", []string{"strip_quant"}, nil},
		{"a value read under an opaque atom",
			"∀h:real. h = pi / &2 ∧ real_cos(pi / &2) = &0 ⇒ real_cos(h) = &0", strips, []int{0}},
	})
}

// TestByArith_SeveralPairsAndInverseOfAProduct: every factor–inverse pair of
// a monomial cancels, each divisor on its own evidence, and the inverse of a
// product is the product of the inverses — a divisor a·b cancels factor by
// factor on the factors' evidence or on the product's, and its sign prices
// the quotient.
func TestByArith_SeveralPairsAndInverseOfAProduct(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"two pairs in one monomial",
			"∀a b x y:real. ¬(a = &0) ∧ ¬(b = &0) ⇒ x / a * (y / b) * (a * b) = x * y", strips, []int{0}},
		{"three pairs in one monomial",
			"∀a b c x:real. ¬(a = &0) ∧ ¬(b = &0) ∧ ¬(c = &0) ⇒ x / a / b / c * (a * b * c) = x", strips, []int{0}},
		{"the inverse of a product, written out",
			"∀a b x:real. ¬(a = &0) ∧ ¬(b = &0) ⇒ x * real_inv(a * b) * a * b = x", strips, []int{0}},
		{"a quotient by a product, one factor cancelled",
			"∀a b x:real. ¬(b = &0) ⇒ x / (a * b) * b = x / a", strips, []int{0}},
		{"a quotient by a product, the product nonzero the evidence",
			"∀a b x:real. ¬(a * b = &0) ⇒ x / (a * b) * a * b = x", strips, []int{0}},
		{"a quotient by a positive product keeps its numerator's sign",
			"∀a b x:real. &0 < a * b ∧ &0 ≤ x ⇒ &0 ≤ x / (a * b)", strips, []int{0}},
		{"a product of quotients is the quotient of the products",
			"∀a b x y:real. x / a * (y / b) = x * y / (a * b)", []string{"strip_quant"}, nil},
	})
}

// TestByArith_EquationUnderAProduct: a hypothesis `v = e` defines v, and
// the closer reads its target at the definition (omega eqHypSubst,
// variable_subst.go) — under a product and inside an atom, at every
// carrier, whatever the names of the variables. A value reaches a product
// of the goal and, through the rounds, a product of another hypothesis.
func TestByArith_EquationUnderAProduct(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"a zero factor, over ℕ", "∀t A:num. t = 0 ⇒ t * A = 0", strips, []int{0}},
		{"a zero factor, over ℤ", "∀t A:int. t = &0 ⇒ t * A = &0", strips, []int{0}},
		{"a zero factor, over ℝ", "∀t A:real. t = &0 ⇒ t * A = &0", strips, []int{0}},
		{"a zero factor, over ℂ",
			"∀t A:complex. t = complex_of_real(&0) ⇒ t * A = complex_of_real(&0)", strips, []int{0}},
		{"a zero factor inside a definition",
			"∀t A C x:real. t = &0 ∧ x = t * A + C ⇒ x = C", strips, []int{0}},
		{"a definition under a product, over ℕ", "∀a b c x:num. a = b + c ⇒ a * x = b * x + c * x", strips, []int{0}},
		{"a definition under a product, over ℤ", "∀a b c x:int. a = b + c ⇒ a * x = b * x + c * x", strips, []int{0}},
		{"a definition under a product, over ℝ", "∀a b c x:real. a = b + c ⇒ a * x = b * x + c * x", strips, []int{0}},
		{"a definition under a product, over ℂ",
			"∀a b c x:complex. a = b + c ⇒ a * x = b * x + c * x", strips, []int{0}},
		{"a definition written with the variable on the right",
			"∀a b c x:real. b + c = a ⇒ a * x = b * x + c * x", strips, []int{0}},
		{"a quotient of nonzero terms is nonzero",
			"∀f g q:real. f = g * real_inv(q) ∧ ¬(g = &0) ∧ ¬(q = &0) ⇒ ¬(f = &0)", strips, []int{0}},
		{"a unit product has no zero factor",
			"∀u v:real. u * v = &1 ∧ u = &0 ⇒ ⊥", strips, []int{0}},
		{"a value in another hypothesis' product",
			"∀t A y:real. t = &0 ∧ y ≤ t * A ⇒ y ≤ &0", strips, []int{0}},
		{"a hypothesis at the variable, the goal at the definition",
			"∀a b c:real. a = b + c ∧ real_abs(a) ≤ &3 ⇒ real_abs(b + c) ≤ &3", strips, []int{0}},
		{"a hypothesis at the definition, the goal at the variable",
			"∀a b c:real. a = b + c ∧ real_abs(b + c) ≤ &3 ⇒ real_abs(a) ≤ &3", strips, []int{0}},
		{"an atom decided as written beside its variable's definition",
			"∀a b c:real. a = b + c ∧ real_abs(a) ≤ &3 ⇒ real_abs(a) ≤ &3", strips, []int{0}},
		{"two definitions that name each other",
			"∀a b:real. a = b + &1 ∧ b = a + &1 ⇒ ⊥", strips, []int{0}},
	})
}

// TestByArith_ANamedTermIsDecidedAsWritten: a definition gives a decision
// two readings, and the closer tries the one the author wrote first. With
// `d` standing for a difference, `-2s ≤ d ≤ 2s` gives `d² ≤ 4s²` as one
// product of two premises; read at the definition the same goal is a
// polynomial in the difference's terms, which the products pass does not
// find. Each premise is a hypothesis of its own, as a proof's Have and
// Let leave them (elliptic_hasse_weil.RiemannHypothesisElliptic).
func TestByArith_ANamedTermIsDecidedAsWritten(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp", "strip_imp", "strip_imp", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"a named difference, squared",
			"∀d x N s:real. d = (real_exp(x) + &1) - N ⇒ -(&2 * s) ≤ d ⇒ d ≤ &2 * s ⇒ real_exp(x) = s ^ 2 ⇒ " +
				"d ^ 2 ≤ &4 * real_exp(x)",
			strips, []int{0, 1, 2, 3}},
	})
}

// TestByArith_ClosingKeepsEquations: the rounds of an arith close keep the
// value equations a redundant hypothesis holds (tactic.ArithTacticPassingOver).
// Each row is a step of the corpus whose close turns on an equation the
// rounds lost once the decider grew strong enough to prove it: an equation
// under an iff whose two sides are both true, dropped with the iff
// (euclidean.CoordinateNormBound), and one under a guard the context
// decides, left wrapped in a hypothesis decided ⊤
// (real_exp_log.ExpQuadraticBound).
func TestByArith_ClosingKeepsEquations(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"an equation under an iff, both sides true",
			"∀n:num. ∀b v:real. 0 < n ∧ &0 ≤ b ∧ v ^ 2 ≤ (&n * b) ^ 2 ∧ &0 ≤ v ∧ (real_abs(v) = v ⇔ &0 ≤ v) ∧ " +
				"(real_abs(&n * b) = &n * b ⇔ &0 ≤ &n * b) ∧ (real_abs(v) ≤ real_abs(&n * b) ⇔ v ^ 2 ≤ (&n * b) ^ 2) ⇒ v ≤ &n * b",
			strips, []int{0}},
		{"an equation under a guard the context decides",
			"∀h:real. (real_of_num(2) * (real_of_num(1) - real_of_num(1) / real_of_num(2)) = real_of_num(1) ⇒ " +
				"real_inv(real_of_num(1) - real_of_num(1) / real_of_num(2)) = real_of_num(2)) ⇒ " +
				"h ^ 2 / real_of_num(2) * real_inv(real_of_num(1) - real_of_num(1) / real_of_num(2)) = h ^ 2",
			strips, []int{0}},
	})
}

// TestByArith_AHypothesisIsReadByItsAtoms: in the rounds of an arith close
// a hypothesis the decider proves as a whole is read atom by atom before
// that verdict drops it (tactic readByAtoms). Each row hands the close an
// instance of a law the decider reads by itself, one side of which the
// context settles: the instance is then the other side, or its negation,
// which the leaf holds no other way.
func TestByArith_AHypothesisIsReadByItsAtoms(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	imps := func(n int) []string {
		return append([]string{"strip_quant"}, slices.Repeat([]string{"strip_imp"}, n)...)
	}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a quotient's bound from the floor law, its product side false (prime_distribution.MiddlePrimesDoNotDivide)",
			"∀n p:num. 2 ≤ p ⇒ 2 * n < 3 * p ⇒ " +
				"(p = 0 ∨ ((3 ≤ nat_div(2 * n, p)) ⇔ (p * 3 ≤ 2 * n))) ⇒ nat_div(2 * n, p) ≤ 2",
			imps(3), []int{0, 1, 2}},
		{"the floor of a double, from the same law (nat_div_mod.FloorDoubleBound)",
			"∀n d q r:num. ¬(d = 0) ⇒ n = q * d + r ⇒ r < d ⇒ " +
				"(d = 0 ∨ ((2 * q + 2 ≤ nat_div(2 * n, d)) ⇔ (d * (2 * q + 2) ≤ 2 * n))) ⇒ nat_div(2 * n, d) ≤ 2 * q + 1",
			imps(4), []int{0, 1, 2, 3}},
		{"a cancellation law whose scaled side the context proves (sylow.SylowCountIndex)",
			"∀G N n c:num. 0 < G ⇒ G = n * N ⇒ G = N * c ⇒ " +
				"((N * n = N * c) ⇔ (N = 0 ∨ n = c)) ⇒ n = c",
			imps(4), []int{0, 1, 2, 3}},
	})
}

// TestByArith_CloserGapsDecline: the same passes on statements that do not
// follow fail as a leaf the closer did not close.
func TestByArith_CloserGapsDecline(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	for _, row := range []struct{ stmt, why string }{
		{"∀s:real. s = &1 ∨ s = &2 ⇒ s * s = &1", "false at s = 2"},
		{"∀s:num. s = 1 ∨ s = 2 ⇒ s * s ≤ 3", "false at s = 2"},
		{"∀t x y:real. &0 ≤ t ∧ x < y ⇒ x ≤ t * x + (&1 - t) * y", "false at t = 2"},
		{"∀M x:real. &0 ≤ M ⇒ &1 ≤ (M + &1) / x + &1", "false at a negative x"},
		{"∀a b x y:real. ¬(a = &0) ⇒ x / a * (y / b) * (a * b) = x * y", "false at b = 0"},
		{"∀a b c x:real. a = b + c ⇒ a * x = b * x", "false at c = x = 1"},
		{"∀t A:real. t = &1 ⇒ t * A = &0", "false at A = 1"},
		{"∀u v:real. u * v = &0 ∧ u = &0 ⇒ ⊥", "true of u = 0"},
		{"∀a b x:real. a = a + b ⇒ a * x = &0", "false at b = 0, a = x = 1"},
	} {
		res := byArithOutcome(t, e, row.stmt, []string{"strip_quant", "strip_imp"}, []ByHypSpec{{HypIndex: idx(0)}})
		require.False(t, res.Success, "%s closed, and it is %s", row.stmt, row.why)
		require.NotEmpty(t, res.Diagnostics)
		require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
			"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
	}
}
