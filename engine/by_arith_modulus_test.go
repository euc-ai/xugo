package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestByArith_ModulusLaws: the session `by {arith:true}` reads ℂ's
// modulus by its laws (omega modulus.go) — a modulus of a product, a
// quotient, an inverse, a power, a negative, a conjugate, an embedded
// real or the imaginary unit is rewritten toward the leaves, in the goal
// and in a hypothesis alike, so each law closes bare and a hypothesis
// spelled one way meets a goal spelled the other. Real corpus, the
// production install.
func TestByArith_ModulusLaws(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strip := []string{"strip_quant", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"a product", "∀z w:complex. |z * w| = |z| * |w|", []string{"strip_quant"}, nil},
		{"a quotient", "∀z w:complex. |z / w| = |z| / |w|", []string{"strip_quant"}, nil},
		{"an inverse", "∀z:complex. |complex_inv(z)| = real_inv(|z|)", []string{"strip_quant"}, nil},
		{"a power", "∀z:complex. ∀n:num. |monoid_pow(complex_mul, complex_of_real(&1), z, n)| = real_pow(|z|, n)", []string{"strip_quant"}, nil},
		{"a negative", "∀z:complex. |-z| = |z|", []string{"strip_quant"}, nil},
		{"a conjugate", "∀z:complex. |conj(z)| = |z|", []string{"strip_quant"}, nil},
		{"an embedded real", "∀x:real. |complex_of_real(x)| = |x|", []string{"strip_quant"}, nil},
		{"the imaginary unit", "|complex_i| = &1", nil, nil},
		{"the laws nested",
			"∀z w:complex. ∀r:real. |complex_of_real(r) * (z * conj(w))| = |r| * (|z| * |w|)",
			[]string{"strip_quant"}, nil},
		{"a product in a hypothesis, its factors in the goal",
			"∀z w:complex. ∀B:real. |z * w| ≤ B ⇒ |z| * |w| ≤ B", strip, []int{0}},
		{"the factors in a hypothesis, the product in the goal",
			"∀z w:complex. ∀B:real. |z| * |w| ≤ B ⇒ |z * w| ≤ B", strip, []int{0}},
		{"a power bound carried to the summand",
			"∀a z:complex. ∀n:num. ∀B:real. |a * monoid_pow(complex_mul, complex_of_real(&1), z, n)| ≤ B ⇒ |a| * real_pow(|z|, n) ≤ B", strip, []int{0}},
		{"an embedded real of known sign", "∀r:real. &0 ≤ r ⇒ |complex_of_real(r)| = r", strip, []int{0}},
		{"a real factor whose absolute value is resident",
			"∀z:complex. ∀r:real. real_abs(r) = r ⇒ |complex_of_real(r) * z| = r * |z|", strip, []int{0}}})
}

// TestByArith_ModulusSign: `&0 ≤ |z|` stands beside every decision's
// hypotheses for the moduli the sequent spells (omega modulusProver), so
// the sign is no premise: bare, as a factor's sign under a product, and
// as the side condition of a scaling.
func TestByArith_ModulusSign(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strip := []string{"strip_quant", "strip_imp"}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		{"the sign", "∀z:complex. &0 ≤ |z|", []string{"strip_quant"}, nil},
		{"the sign of a difference's modulus", "∀z w:complex. &0 ≤ |z - w|", []string{"strip_quant"}, nil},
		{"a product of moduli", "∀z w:complex. &0 ≤ |z| * |w|", []string{"strip_quant"}, nil},
		{"the modulus of a product", "∀z w:complex. &0 ≤ |z * w|", []string{"strip_quant"}, nil},
		{"a bound below a modulus", "∀z:complex. ∀r:real. r < &0 ⇒ r < |z|", strip, []int{0}},
		{"a scaling by a modulus",
			"∀z:complex. ∀a b:real. a ≤ b ⇒ |z| * a ≤ |z| * b", strip, []int{0}},
		{"a product bounded by its factors' bounds",
			"∀z w:complex. |z| ≤ &1 ∧ |w| ≤ &1 ⇒ |z * w| ≤ &1", strip, []int{0}},
		{"a modulus that is not positive is zero",
			"∀z:complex. |z| ≤ &0 ⇒ |z| = &0", strip, []int{0}},
	})
}

// TestByArith_ModulusZeroTest: a term and its modulus vanish together
// (omega modulus_zero.go). What ℂ's ring shows of a modulus's argument is
// a fact about the modulus, and what ℝ's rows show of a modulus is a fact
// about its argument — each way round, for a real target and for a ℂ
// one, in a hypothesis and in the goal.
func TestByArith_ModulusZeroTest(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strip := []string{"strip_quant", "strip_imp"}
	bare := []string{"strip_quant"}
	c := func(format string) string {
		return strings.NewReplacer("0c", "complex_of_real(&0)").Replace(format)
	}
	runByArithRowsIn(t, byArithEngine(t), constSyntax(), []byArithRow{
		// A real target from the ring's evidence.
		{"positive where the argument is not zero", c("∀z:complex. ¬(z = 0c) ⇒ &0 < |z|"), strip, []int{0}},
		{"not zero where the argument is not", c("∀z:complex. ¬(z = 0c) ⇒ ¬(|z| = &0)"), strip, []int{0}},
		{"positive where two points differ", "∀z w:complex. ¬(z = w) ⇒ &0 < |z - w|", strip, []int{0}},
		{"zero where the argument is", c("∀z:complex. z = 0c ⇒ |z| = &0"), strip, []int{0}},
		{"zero where two points agree", "∀z w:complex. z = w ⇒ |z - w| = &0", strip, []int{0}},
		{"zero at a ring zero", "∀c:complex. |c - c| = &0", bare, nil},
		{"a disc holds its centre", "∀c:complex. ∀r:real. &0 < r ⇒ |c - c| < r", strip, []int{0}},
		{"a product of terms that are not zero",
			c("∀z w:complex. ¬(z = 0c) ∧ ¬(w = 0c) ⇒ &0 < |z * w|"), strip, []int{0}},
		{"under an inverse", c("∀z:complex. ¬(z = 0c) ⇒ &0 < &1 / |z|"), strip, []int{0}},
		{"under a power", c("∀z:complex. ∀n:num. ¬(z = 0c) ⇒ &0 < |z| ^ n"), strip, []int{0}},
		// A ℂ target from ℝ's rows.
		{"not zero where the modulus is positive", c("∀z:complex. &0 < |z| ⇒ ¬(z = 0c)"), strip, []int{0}},
		{"not zero where the modulus is not", c("∀z:complex. ¬(|z| = &0) ⇒ ¬(z = 0c)"), strip, []int{0}},
		{"two points differ at a positive distance", "∀z w:complex. &0 < |z - w| ⇒ ¬(z = w)", strip, []int{0}},
		{"a point of a punctured disc is off the centre",
			"∀z c:complex. ∀δ:real. &0 < |z - c| ∧ |z - c| < δ ⇒ ¬(z = c)", strip, []int{0}},
		{"a modulus above a distance is positive", c("∀u v:complex. |u - v| < |u| ⇒ ¬(u = 0c)"), strip, []int{0}},
		{"zero where the modulus is", c("∀z:complex. |z| = &0 ⇒ z = 0c"), strip, []int{0}},
		{"zero where the modulus is not positive", c("∀z:complex. |z| ≤ &0 ⇒ z = 0c"), strip, []int{0}},
		{"two points agree at distance zero", "∀z w:complex. |z - w| ≤ &0 ⇒ z = w", strip, []int{0}},
		{"a divisor has its evidence from a punctured disc",
			"∀z c f:complex. &0 < |z - c| ⇒ f / (z - c) * (z - c) = f", strip, []int{0}},
	})
}

// TestByArith_ModulusZeroTestDeclines: statements about a modulus and its
// argument that do not follow.
func TestByArith_ModulusZeroTestDeclines(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	idx := func(i int) *int { return &i }
	e := byArithEngine(t)
	strip := []string{"strip_quant", "strip_imp"}
	for _, row := range []struct {
		stmt   string
		strips []string
		hyps   []ByHypSpec
		why    string
	}{
		{"∀z:complex. &0 ≤ |z| ⇒ ¬(z = complex_of_real(&0))", strip, []ByHypSpec{{HypIndex: idx(0)}}, "false at z = 0"},
		{"∀z w:complex. ¬(z = w) ⇒ &0 < |z|", strip, []ByHypSpec{{HypIndex: idx(0)}}, "false at z = 0, w = 1"},
		{"∀z:complex. |z| ≤ &1 ⇒ z = complex_of_real(&0)", strip, []ByHypSpec{{HypIndex: idx(0)}}, "false at z = 1"},
		{"∀z w:complex. &0 < |z| ⇒ ¬(z = w)", strip, []ByHypSpec{{HypIndex: idx(0)}}, "false at z = w = 1"},
		{"∀z:complex. &0 < |z|", []string{"strip_quant"}, nil, "false at z = 0"},
		{"∀z:complex. |z| = &0", []string{"strip_quant"}, nil, "false at z = 1"},
	} {
		res := byArithOutcomeIn(t, e, constSyntax(), row.stmt, row.strips, row.hyps)
		require.False(t, res.Success, "%s closed, and it is %s", row.stmt, row.why)
	}
}

// TestByArith_ModulusBoundary: what the reading leaves to a cited law. A
// sum or a difference under a modulus is one unknown as spelled, so the
// swap and the triangle inequality do not close bare.
func TestByArith_ModulusBoundary(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	for _, stmt := range []string{
		"∀z w:complex. |z - w| = |w - z|",
		"∀z w:complex. |z + w| ≤ |z| + |w|",
	} {
		t.Run(stmt, func(t *testing.T) {
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
				Syntax: constSyntax(),
			})
			require.Empty(t, parsed.Errors, "add-goal %q", stmt)
			s.mu.Lock()
			gid := s.AddGoal(parsed.Prop)
			s.mu.Unlock()
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "strip_quant"}})
			require.NoError(t, err)
			require.Len(t, res.Produced, 1)
			res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: res.Produced[0].GoalID,
				Tactic: TacticReq{Type: "by", Arith: true}})
			require.True(t, err != nil || res.Effect != "close", "%s closed bare", stmt)
		})
	}
}
