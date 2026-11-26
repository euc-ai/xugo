package engine

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_DeniedValue: a target that denies a variable a value is
// decided by the value read into the hypotheses, as a hypothesis `v = e` is
// read (omega denied_value.go) — a disequation at every carrier, and on ℕ
// the positivity of a variable in each of its spellings.
func TestByArith_DeniedValue(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	two := []string{"strip_quant", "strip_imp", "strip_imp"}
	three := []string{"strip_quant", "strip_imp", "strip_imp", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"a factor of a positive product, over ℕ", "∀g u:num. 0 < g * u ⇒ 0 < u", strips, []int{0}},
		{"the left factor", "∀g u:num. 0 < g * u ⇒ 0 < g", strips, []int{0}},
		{"positive written from the right", "∀g u:num. 0 < g * u ⇒ u > 0", strips, []int{0}},
		{"positive written as at least one", "∀g u:num. 1 ≤ g * u ⇒ 1 ≤ u", strips, []int{0}},
		{"positive from a product that is not zero", "∀g u:num. ¬(g * u = 0) ⇒ 0 < u", strips, []int{0}},
		{"not zero from a positive product", "∀g u:num. 0 < g * u ⇒ ¬(u = 0)", strips, []int{0}},
		{"not zero, the zero on the left", "∀g u:num. ¬(0 = g * u) ⇒ ¬(0 = u)", strips, []int{0}},
		{"a factor of one, over ℕ", "∀g u:num. g * u = 1 ⇒ ¬(u = 0)", strips, []int{0}},
		{"a factor of a nonzero product, over ℤ", "∀g u:int. ¬(g * u = &0) ⇒ ¬(u = &0)", strips, []int{0}},
		{"a factor of a positive product, over ℤ", "∀g u:int. &0 < g * u ⇒ ¬(u = &0)", strips, []int{0}},
		{"a factor of one, over ℤ", "∀g u:int. g * u = &1 ⇒ ¬(u = &0)", strips, []int{0}},
		{"a factor of one, over ℝ", "∀g u:real. g * u = &1 ⇒ ¬(u = &0)", strips, []int{0}},
		{"a factor of a positive product, over ℝ", "∀g u:real. &0 < g * u ⇒ ¬(&0 = u)", strips, []int{0}},
		{"a factor of one, over ℂ",
			"∀g u:complex. g * u = complex_of_real(&1) ⇒ ¬(u = complex_of_real(&0))", strips, []int{0}},
		{"a factor of a nonzero product, over ℂ",
			"∀g u:complex. ¬(g * u = complex_of_real(&0)) ⇒ ¬(u = complex_of_real(&0))", strips, []int{0}},
		{"two variables a strict product tells apart", "∀x y w:real. x * w < y * w ⇒ ¬(x = y)", strips, []int{0}},
		{"two points at different distances from one centre",
			"∀z w c:complex. ∀r:real. |z - c| = r ∧ |w - c| < r ⇒ ¬(z = w)", strips, []int{0}},
		{"a value read through a definition", "∀r g v:num. 0 < r ⇒ r = g * v ⇒ 0 < v", two, []int{0, 1}},
		{"a value read through a definition, as a disequation",
			"∀r g v:num. 0 < r ⇒ r = g * v ⇒ ¬(v = 0)", two, []int{0, 1}},
		{"beside an iff the context decides (nat_gcd.GcdFromCommonMultiples)",
			"∀r g v:num. 0 < r ⇒ r = g * v ⇒ ((0 = r) ⇔ (v = 0)) ⇒ 0 < v", three, []int{0, 1, 2}},
	})
}

// TestByArith_StructureRingRefutes: an equation a structure ring's context
// denies is decided ⊥ (omega structure_refute.go). A field denies
// `one = zero` whatever the context holds; ℂ's literals differ by ℝ's
// arithmetic; and at a field a product, an inverse and a quotient of terms
// that are not zero are not zero, a zero product giving its cofactor.
func TestByArith_StructureRingRefutes(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	zero, one, two := "complex_of_real(&0)", "complex_of_real(&1)", "complex_of_real(&2)"
	c := func(format string) string {
		return strings.NewReplacer("0c", zero, "1c", one, "2c", two).Replace(format)
	}
	strips := []string{"strip_quant", "strip_imp"}
	field := []string{"strip_quant", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"a unit product has no zero factor", c("∀z w:complex. z * w = 1c ∧ z = 0c ⇒ ⊥"), strips, []int{0}},
		{"zero is not one", c("0c = 1c ⇒ ⊥"), []string{"strip_imp"}, []int{0}},
		{"one is not zero, as a goal", c("¬(1c = 0c)"), []string{}, []int{}},
		{"zero is not one, as a goal", c("¬(0c = 1c)"), []string{}, []int{}},
		{"a literal is not zero", c("¬(2c = 0c)"), []string{}, []int{}},
		{"a variable with a literal value is not zero", c("∀z:complex. z = 2c ⇒ ¬(z = 0c)"), strips, []int{0}},
		{"an element is not its successor", c("∀z:complex. z + 1c = z ⇒ ⊥"), strips, []int{0}},
		{"two values of one variable", c("∀z:complex. z = 0c ∧ z = 1c ⇒ ⊥"), strips, []int{0}},
		{"the exponential is not zero (complex_exp.ExpNonzero)",
			c("∀z:complex. complex_exp(z) = 0c ∧ complex_exp(z) * complex_exp(complex_neg(z)) = 1c ⇒ ⊥"),
			strips, []int{0}},
		{"the inverse of a nonzero term", c("∀q:complex. ¬(q = 0c) ⇒ ¬(complex_inv(q) = 0c)"), strips, []int{0}},
		{"a quotient of nonzero terms, through a definition",
			c("∀f g q:complex. f = g * complex_inv(q) ∧ ¬(g = 0c) ∧ ¬(q = 0c) ⇒ ¬(f = 0c)"), strips, []int{0}},
		{"the cofactor of a zero product", c("∀g q:complex. g * q = 0c ∧ ¬(g = 0c) ⇒ q = 0c"), strips, []int{0}},
		{"the cofactor of a zero product, the right factor nonzero",
			c("∀g q:complex. 0c = g * q ∧ ¬(q = 0c) ⇒ g = 0c"), strips, []int{0}},
		{"a field's one is not its zero", "∀F:field_ops(A). field_on(F) ⇒ ¬(F.one = F.zero)", field, []int{0}},
		{"a field's zero is not its one", "∀F:field_ops(A). field_on(F) ⇒ ¬(F.zero = F.one)", field, []int{0}},
		{"a field's zero equal to its one",
			"∀F:field_ops(A). field_on(F) ⇒ F.zero = F.one ⇒ ⊥", []string{"strip_quant", "strip_imp", "strip_imp"}, []int{0, 1}},
		{"a unit product has no zero factor, at a field",
			"∀F:field_ops(A). field_on(F) ⇒ ∀x y:A. x ∈ F.carrier ∧ y ∈ F.carrier ∧ F.mul(x, y) = F.one ∧ x = F.zero ⇒ ⊥",
			[]string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"}, []int{0, 1}},
	})
}

// TestByArith_NatProducts: on ℕ a product is zero exactly where a factor
// is (omega nat_products.go) — a zero product splits into its factors, and
// a product of positive factors is positive in each spelling of positive.
func TestByArith_NatProducts(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a product of positive factors", "∀g q:num. 0 < g ∧ 0 < q ⇒ 0 < g * q", strips, []int{0}},
		{"three positive factors", "∀g q r:num. 0 < g ∧ 0 < q ∧ 0 < r ⇒ 0 < g * q * r", strips, []int{0}},
		{"factors at least one", "∀g q:num. 1 ≤ g ∧ 1 ≤ q ⇒ 1 ≤ g * q", strips, []int{0}},
		{"positive factors, the product not zero", "∀g q:num. 0 < g ∧ 0 < q ⇒ ¬(g * q = 0)", strips, []int{0}},
		{"the cofactor of a zero product", "∀g q:num. g * q = 0 ∧ ¬(g = 0) ⇒ q = 0", strips, []int{0}},
		{"the cofactor of a zero product, the zero on the left", "∀g q:num. 0 = g * q ∧ 0 < g ⇒ q = 0", strips, []int{0}},
		{"a square that is zero", "∀x:num. x * x = 0 ⇒ x = 0", strips, []int{0}},
		{"the square of a positive term", "∀x:num. 0 < x ⇒ 0 < x * x", strips, []int{0}},
		{"a positive product in a premise", "∀g q a c:num. 0 < g ∧ 0 < q ∧ g * q + a ≤ c ⇒ a < c", strips, []int{0}},
		{"a positive product is the successor of its predecessor",
			"∀a t:num. ¬(a = 0) ∧ ¬(t = 0) ⇒ suc(a * t - 1) = a * t", strips, []int{0}},
		{"the same beside the zero-product law at its factors (finite_field.FiniteConstantsFermat)",
			"∀a t:num. ¬(a = 0) ∧ ¬(t = 0) ∧ (a * t = 0 ⇔ a = 0 ∨ t = 0) ⇒ suc(a * t - 1) = a * t", strips, []int{0}},
		{"a positive product through a premise's definition", "∀g q c:num. 0 < g ∧ 0 < q ∧ c = g * q ⇒ 0 < c", strips, []int{0}},
	})
}

// TestByArith_ZeroOnEitherSide: a zero test closes whichever side of its
// equation the zero is written on (omega zero_sided.go), in the evidence
// and in what is asked, and whether what is asked stands as the conclusion
// or, negated, among the hypotheses.
func TestByArith_ZeroOnEitherSide(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	type carrier struct {
		name, typ, zero string
		shapes          []string // a term over g and q that is not zero where they are not
	}
	carriers := []carrier{
		{"ℕ", "num", "0", []string{"g * q"}},
		{"ℤ", "int", "&0", []string{"g * q", "-(g * q)", "-g"}},
		{"ℝ", "real", "&0", []string{"g * q", "g * real_inv(q)", "g / q", "real_inv(q)", "-(g * q)", "-q"}},
		{"ℂ", "complex", "complex_of_real(&0)", []string{"g * q", "g * complex_inv(q)", "g / q", "complex_inv(q)"}},
	}
	// eq spells `t = zero` with the zero on the right, or on the left.
	eq := func(t, zero string, zeroLeft bool) string {
		if zeroLeft {
			return zero + " = " + t
		}
		return t + " = " + zero
	}
	side := map[bool]string{false: "right", true: "left"}
	strips := []string{"strip_quant", "strip_imp"}
	var rows []byArithRow
	for _, c := range carriers {
		for _, shape := range c.shapes {
			for _, evidenceLeft := range []bool{false, true} {
				for _, askedLeft := range []bool{false, true} {
					evidence := fmt.Sprintf("¬(%s) ∧ ¬(%s)", eq("g", c.zero, evidenceLeft), eq("q", c.zero, evidenceLeft))
					asked := eq(shape, c.zero, askedLeft)
					name := fmt.Sprintf("%s over %s, evidence zero %s, asked zero %s", shape, c.name, side[evidenceLeft], side[askedLeft])
					rows = append(rows,
						byArithRow{name + ", as the conclusion",
							fmt.Sprintf("∀g q:%s. %s ⇒ ¬(%s)", c.typ, evidence, asked), strips, []int{0}},
						byArithRow{name + ", as a hypothesis",
							fmt.Sprintf("∀g q:%s. %s ∧ %s ⇒ ⊥", c.typ, evidence, asked), strips, []int{0}})
				}
			}
		}
	}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), rows)
}

// TestByArith_ZeroTestsDecline: the zero tests on statements that do not
// follow fail as a leaf the closer did not close.
func TestByArith_ZeroTestsDecline(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	for _, row := range []struct{ stmt, why string }{
		{"∀g u:num. 0 ≤ g * u ⇒ 0 < u", "false at u = 0"},
		{"∀g u:num. 0 < g + u ⇒ 0 < u", "false at g = 1, u = 0"},
		{"∀g u:int. g * u = &0 ⇒ ¬(u = &0)", "false at u = 0"},
		{"∀g u:real. &0 ≤ g * u ⇒ ¬(u = &0)", "false at u = 0"},
		{"∀g u:real. g * u = &1 ⇒ ¬(u = &1)", "false at g = u = 1"},
		{"∀g q:num. g * q = 0 ⇒ q = 0", "false at g = 0, q = 1"},
		{"∀g q:num. 0 < g ⇒ 0 < g * q", "false at q = 0"},
		{"∀z w:complex. complex_mul(z, w) = complex_of_real(&0) ⇒ z = complex_of_real(&0)", "false at w = 0, z = 1"},
		{"∀z:complex. complex_mul(z, z) = complex_of_real(&1) ⇒ ⊥", "true of z = 1"},
		{"∀g q:complex. ¬(g = complex_of_real(&0)) ⇒ ¬(complex_mul(g, q) = complex_of_real(&0))", "false at q = 0"},
		{"∀g q:real. ¬(g = &0) ⇒ ¬(&0 = g * real_inv(q))", "false at q = 0"},
	} {
		res := byArithOutcome(t, e, row.stmt, []string{"strip_quant", "strip_imp"}, []ByHypSpec{{HypIndex: idx(0)}})
		require.False(t, res.Success, "%s closed, and it is %s", row.stmt, row.why)
		require.NotEmpty(t, res.Diagnostics)
		require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
			"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
	}
	// A commutative ring that is no field may be the zero ring.
	ring := byArithOutcomeIn(t, e, constSyntax(), "∀R:ring_ops(A). comm_ring_on(R) ⇒ ¬(R.zero = R.one)",
		[]string{"strip_quant", "strip_imp"}, []ByHypSpec{{HypIndex: idx(0)}})
	require.False(t, ring.Success, "a commutative ring's zero and one were told apart")
}

// TestByArith_PowerZeroTest: a power is zero only where its base is, at
// every exponent — over ℝ (omega real_nonzero.go) and at a field's
// structure ring (structure_refute.go). The base's evidence is the
// power's, for a goal and for a divisor; and a hypothesis that a power is
// zero puts its base at zero.
func TestByArith_PowerZeroTest(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	c := func(format string) string {
		return strings.NewReplacer("0c", "complex_of_real(&0)", "pow(", "monoid_pow(complex_mul, complex_of_real(&1), ").Replace(format)
	}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"ℝ, a power of a base that is not zero", "∀r:real. ∀n:num. ¬(r = &0) ⇒ ¬(r ^ n = &0)", strips, []int{0}},
		{"ℝ, a divisor that is a power of a positive base",
			"∀M r:real. ∀n:num. &0 < r ⇒ M / r ^ n * r ^ n = M", strips, []int{0}},
		{"ℝ, a divisor that is a power of a negative base",
			"∀M r:real. ∀n:num. r < &0 ⇒ M / r ^ n * r ^ n = M", strips, []int{0}},
		{"ℝ, a divisor that is a power of a base that is not zero",
			"∀M r:real. ∀n:num. ¬(r = &0) ⇒ M / r ^ n * r ^ n = M", strips, []int{0}},
		{"ℝ, a power of a difference that is not zero",
			"∀M r c:real. ∀n:num. ¬(r = c) ⇒ M / (r - c) ^ n * (r - c) ^ n = M", strips, []int{0}},
		{"ℝ, a base times its power",
			"∀M r:real. ∀n:num. &0 < r ⇒ M / (r * r ^ n) * (r * r ^ n) = M", strips, []int{0}},
		{"ℝ, a zero power has a zero base", "∀r:real. ∀n:num. r ^ n = &0 ⇒ r = &0", strips, []int{0}},
		{"ℝ, the zero on the left", "∀r:real. ∀n:num. &0 = r ^ n ⇒ r = &0", strips, []int{0}},
		{"ℝ, a zero power of a base that is not zero", "∀r:real. ∀n:num. r ^ n = &0 ∧ ¬(r = &0) ⇒ ⊥", strips, []int{0}},
		{"ℂ, a power of a base that is not zero", c("∀z:complex. ∀n:num. ¬(z = 0c) ⇒ ¬(pow(z, n) = 0c)"), strips, []int{0}},
		{"ℂ, a divisor that is a power",
			c("∀z M:complex. ∀n:num. ¬(z = 0c) ⇒ M / pow(z, n) * pow(z, n) = M"), strips, []int{0}},
		{"ℂ, a power of a point off the centre, from a punctured disc",
			c("∀z c M:complex. ∀n:num. &0 < |z - c| ⇒ M / pow(z - c, n) * pow(z - c, n) = M"), strips, []int{0}},
		{"ℂ, a zero power has a zero base", c("∀z:complex. ∀n:num. pow(z, n) = 0c ⇒ z = 0c"), strips, []int{0}},
	})
}

// TestByArith_PowerZeroTestDeclines: a power that is not zero says nothing
// of its base, the exponent being free to be zero; and a power with no
// evidence for its base is no divisor.
func TestByArith_PowerZeroTestDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	strips := []string{"strip_quant", "strip_imp"}
	for _, row := range []struct{ stmt, why string }{
		{"∀r:real. ∀n:num. ¬(r ^ n = &0) ⇒ ¬(r = &0)", "false at r = 0, n = 0"},
		{"∀r:real. ∀n:num. r ^ n = &1 ⇒ r = &1", "false at n = 0"},
		{"∀M r s:real. ∀n:num. ¬(s = &0) ⇒ M / r ^ n * r ^ n = M", "false at r = 0, n = 1"},
		{"∀z:complex. ∀n:num. ¬(monoid_pow(complex_mul, complex_of_real(&1), z, n) = complex_of_real(&0)) ⇒ ¬(z = complex_of_real(&0))",
			"false at z = 0, n = 0"},
	} {
		res := byArithOutcomeIn(t, e, constSyntax(), row.stmt, strips, []ByHypSpec{{HypIndex: idx(0)}})
		require.False(t, res.Success, "%s closed, and it is %s", row.stmt, row.why)
	}
}
