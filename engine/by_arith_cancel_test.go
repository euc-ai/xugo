package engine

import "testing"

// TestByArith_RealCancelPositiveFactor drives the hypothesis-side
// positive-factor cancellation (omega real_cancel.go) end-to-end on the REAL
// corpus with the production bundles installed — the test bundle's placeholder
// stand-in is absent here, so a leaf that did not bind its cancellation
// theorem would panic rather than fabricate.
//
// `p·a` and `p·b` are two distinct monomial unknowns to the ℝ linear layer, so
// the row `p·a ≤ p·b` says nothing about `a ≤ b` on its own: relating them means
// scaling a premise by the VARIABLE p, which no Farkas combination supplies.
func TestByArith_RealCancelPositiveFactor(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"cancel a positive left factor",
			"∀p a b:real. &0 < p ∧ p * a ≤ p * b ⇒ a ≤ b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"cancel a positive left factor, strictly",
			"∀p a b:real. &0 < p ∧ p * a < p * b ⇒ a < b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"cancel a positive right factor",
			"∀p a b:real. &0 < p ∧ a * p ≤ b * p ⇒ a ≤ b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"cancel a positive right factor, strictly",
			"∀p a b:real. &0 < p ∧ a * p < b * p ⇒ a < b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// The factor's positivity is derived from the hypotheses, and the
		// cancelled comparison is an ordinary linear row once available.
		{"the factor's sign derived, the cancelled row chained",
			"∀p a b c:real. &1 ≤ p ∧ p * a ≤ p * b ∧ b ≤ c ⇒ a ≤ c",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		// A compound factor's positivity descends to its own factors.
		{"a compound positive factor",
			"∀p q a b:real. &0 < p ∧ &0 < q ∧ (p * q) * a ≤ (p * q) * b ⇒ a ≤ b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
	})
}

// TestByArith_IntCancelPositiveFactor: the ℤ twin (omega int_cancel.go). ℤ
// states neither cancellation law, so the two bundle fields are the REAL pair
// lifted through IntOfRealThm at install time — a route that yields no
// placeholder, so a broken lift would panic here rather than fabricate.
func TestByArith_IntCancelPositiveFactor(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"cancel a positive left factor",
			"∀p a b:int. &0 < p ∧ p * a ≤ p * b ⇒ a ≤ b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"cancel a positive left factor, strictly",
			"∀p a b:int. &0 < p ∧ p * a < p * b ⇒ a < b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"cancel a positive right factor",
			"∀p a b:int. &0 < p ∧ a * p ≤ b * p ⇒ a ≤ b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"the factor's sign derived, the cancelled row chained",
			"∀p a b c:int. &1 ≤ p ∧ p * a ≤ p * b ∧ b ≤ c ⇒ a ≤ c",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
		{"a compound positive factor",
			"∀p q a b:int. &0 < p ∧ &0 < q ∧ (p * q) * a ≤ (p * q) * b ⇒ a ≤ b",
			[]string{"strip_quant", "strip_imp"}, []int{0}},
	})
}

// TestByArith_CancelFromAnEquation: an equation hypothesis whose two sides
// share a factor shown not zero gives the equation of what is left of them
// — over ℝ on any evidence that the factor is not zero (omega
// real_cancel.go), and at a field's structure ring, ℂ's and an abstract
// field's alike (structure_refute.go). The factor is read up to the order
// and the grouping of the products.
func TestByArith_CancelFromAnEquation(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	zero := "complex_of_real(&0)"
	field := "∀F:field_ops(A). field_on(F) ⇒ ∀x y z:A. x ∈ F.carrier ∧ y ∈ F.carrier ∧ z ∈ F.carrier ∧ "
	atField := []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"ℝ, a factor that is not zero", "∀x y z:real. ¬(x = &0) ∧ x * y = x * z ⇒ y = z", strips, []int{0}},
		{"ℝ, a right factor", "∀x y z:real. ¬(x = &0) ∧ y * x = z * x ⇒ y = z", strips, []int{0}},
		{"ℝ, the factor on opposite sides, the zero on the left",
			"∀x y z:real. ¬(&0 = x) ∧ x * y = z * x ⇒ y = z", strips, []int{0}},
		{"ℝ, a negative factor", "∀x y z:real. x < &0 ∧ x * y = x * z ⇒ y = z", strips, []int{0}},
		{"ℝ, a factor whose square is positive", "∀x y z:real. &0 < x * x ∧ x * y = x * z ⇒ y = z", strips, []int{0}},
		{"ℝ, a difference that is not zero",
			"∀x y z c:real. ¬(x = c) ∧ (x - c) * y = (x - c) * z ⇒ y = z", strips, []int{0}},
		{"ℝ, two shared factors",
			"∀x y z w:real. ¬(x = &0) ∧ ¬(w = &0) ∧ x * y * w = x * z * w ⇒ y = z", strips, []int{0}},
		{"ℝ, against the factor itself", "∀x y:real. ¬(x = &0) ∧ x * y = x ⇒ y = &1", strips, []int{0}},
		{"ℝ, the cancelled equation feeds a sum",
			"∀x y z:real. ¬(x = &0) ∧ x * y = x * z ⇒ y + &1 = z + &1", strips, []int{0}},
		{"ℂ, a factor that is not zero",
			"∀x y z:complex. ¬(x = " + zero + ") ∧ x * y = x * z ⇒ y = z", strips, []int{0}},
		{"ℂ, the factor on opposite sides",
			"∀x y z:complex. ¬(x = " + zero + ") ∧ x * y = z * x ⇒ y = z", strips, []int{0}},
		{"ℂ, a difference that is not zero",
			"∀x y z c:complex. ¬(x = c) ∧ (x - c) * y = (x - c) * z ⇒ y = z", strips, []int{0}},
		{"ℂ, two shared factors",
			"∀x y z w:complex. ¬(x = " + zero + ") ∧ ¬(w = " + zero + ") ∧ x * y * w = x * z * w ⇒ y = z", strips, []int{0}},
		{"ℂ, against the factor itself",
			"∀x y:complex. ¬(x = " + zero + ") ∧ x * y = x ⇒ y = complex_of_real(&1)", strips, []int{0}},
		{"a field, a factor that is not zero",
			field + "¬(x = F.zero) ∧ F.mul(x, y) = F.mul(x, z) ⇒ y = z", atField, []int{0, 1}},
		{"a field, a right factor",
			field + "¬(x = F.zero) ∧ F.mul(y, x) = F.mul(z, x) ⇒ y = z", atField, []int{0, 1}},
	})
}

// TestByArith_CancelFromAnEquationDeclines: no factor is cancelled without
// evidence that it is not zero, and none at a ring that is no field.
func TestByArith_CancelFromAnEquationDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	strips := []string{"strip_quant", "strip_imp"}
	atRing := []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}
	for _, row := range []struct {
		stmt   string
		strips []string
		hyps   []int
		why    string
	}{
		{"∀x y z:real. x * y = x * z ⇒ y = z", strips, []int{0}, "false at x = 0"},
		{"∀x y z w:real. ¬(x = &0) ∧ x * y * w = x * z * w ⇒ y = z", strips, []int{0}, "false at w = 0"},
		{"∀x y z:complex. x * y = x * z ⇒ y = z", strips, []int{0}, "false at x = 0"},
		{"∀R:ring_ops(A). comm_ring_on(R) ⇒ ∀x y z:A. x ∈ R.carrier ∧ y ∈ R.carrier ∧ z ∈ R.carrier ∧ " +
			"¬(x = R.zero) ∧ R.mul(x, y) = R.mul(x, z) ⇒ y = z", atRing, []int{0, 1}, "false at a zero divisor"},
	} {
		var hyps []ByHypSpec
		for _, i := range row.hyps {
			hyps = append(hyps, ByHypSpec{HypIndex: idx(i)})
		}
		res := byArithOutcomeIn(t, e, constSyntax(), row.stmt, row.strips, hyps)
		if res.Success {
			t.Errorf("%s closed, and it is %s", row.stmt, row.why)
		}
	}
}
