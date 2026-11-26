package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestByArith_WideNumerals drives `by {arith:true}` on numerals and products
// past a machine word, end to end on the REAL corpus with the production
// bundles installed: the rounding cuts and the numeral evaluators run on
// their bound theorems, so a step the model and the proof side disagree on
// is refused by the kernel here and nowhere hidden behind a stand-in.
//
// 2⁶¹ = 2305843009213693952 and 20! = 2432902008176640000 are below 2⁶³;
// the products below land under 2⁶³, between 2⁶³ and 2⁶⁴, and past 2⁶⁴.
func TestByArith_WideNumerals(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"4·2⁶¹ = 2⁶³",
			"∀x:num. x = 2305843009213693952 ⇒ 4 * x = 9223372036854775808", strips, []int{0}},
		{"4·(2⁶¹ − 1), under 2⁶³",
			"∀x:num. x = 2305843009213693951 ⇒ 4 * x = 9223372036854775804", strips, []int{0}},
		{"8·2⁶¹ = 2⁶⁴",
			"∀x:num. x = 2305843009213693952 ⇒ 8 * x = 18446744073709551616", strips, []int{0}},
		{"2·20!",
			"∀x:num. x = 2432902008176640000 ⇒ 2 * x = 4865804016353280000", strips, []int{0}},
		{"3·20!",
			"∀x:num. x = 2432902008176640000 ⇒ 3 * x = 7298706024529920000", strips, []int{0}},
		{"4·20!, past 2⁶³",
			"∀x:num. x = 2432902008176640000 ⇒ 4 * x = 9731608032706560000", strips, []int{0}},
		{"5·20!",
			"∀x:num. x = 2432902008176640000 ⇒ 5 * x = 12164510040883200000", strips, []int{0}},
		{"7·20!",
			"∀x:num. x = 2432902008176640000 ⇒ 7 * x = 17030314057236480000", strips, []int{0}},
		{"8·20!, past 2⁶⁴",
			"∀x:num. x = 2432902008176640000 ⇒ 8 * x = 19463216065413120000", strips, []int{0}},
		{"16·20!",
			"∀x:num. x = 2432902008176640000 ⇒ 16 * x = 38926432130826240000", strips, []int{0}},
		{"21·20!",
			"∀x:num. x = 2432902008176640000 ⇒ 21 * x = 51090942171709440000", strips, []int{0}},
		{"a strict bound across 2⁶⁴",
			"∀x:num. x = 2432902008176640000 ⇒ 7 * x < 8 * x", strips, []int{0}},
		{"a bound between literals either side of 2⁶⁴",
			"∀x:num. 18446744073709551616 ≤ x ⇒ 18446744073709551615 < x", strips, []int{0}},
		{"a rounding cut with a divisor past 2⁶³",
			"∀x:num. 9223372036854775808 * x ≤ 18446744073709551621 ⇒ x ≤ 2", strips, []int{0}},
		{"over ℝ",
			"∀x:real. x = &2432902008176640000 ⇒ &21 * x = &51090942171709440000", strips, []int{0}},
		{"over ℤ",
			"∀x:int. x = &2432902008176640000 ⇒ &21 * x = &51090942171709440000", strips, []int{0}},
		// 25!/20! = 21·22·23·24·25, on literals past 2⁶⁴.
		{"a quotient of wide literals",
			"∀x:num. x = nat_div(15511210043330985984000000, 2432902008176640000) ⇒ x = 6375600", strips, []int{0}},
		{"a remainder of wide literals",
			"∀x:num. x = nat_mod(15511210043330985984000007, 2432902008176640000) ⇒ x = 7", strips, []int{0}},
	})
}

// byArithOutcome states stmt, applies the strips given and then
// `by {arith:true}` over the premises given, and returns that last step's
// result — closed or not.
func byArithOutcome(t *testing.T, e *Engine, stmt string, strips []string, hyps []ByHypSpec) *StepResult {
	t.Helper()
	return byArithOutcomeIn(t, e, nil, stmt, strips, hyps)
}

// byArithOutcomeIn is byArithOutcome with the statement read under the
// constant syntax given, as runByArithRowsIn reads its rows.
func byArithOutcomeIn(t *testing.T, e *Engine, syntax dsl.SyntaxTable, stmt string, strips []string, hyps []ByHypSpec) *StepResult {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		Syntax: syntax,
	})
	require.Empty(t, parsed.Errors, "add-goal %q", stmt)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range strips {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, "strip %s", typ)
		require.Len(t, res.Produced, 1, "strip %s", typ)
		gid = res.Produced[0].GoalID
	}
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
		Tactic: TacticReq{Type: "by", Arith: true, ByHyps: hyps}})
	require.NoError(t, err)
	return res
}

// TestByArith_WideNumeralsFalseGoal: a false goal over the same numerals
// fails as a goal the closer did not close. A model that hands the kernel a
// step it refuses would surface here as the kernel's own panic text.
func TestByArith_WideNumeralsFalseGoal(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	idx := func(i int) *int { return &i }
	strips := []string{"strip_quant", "strip_imp"}
	for name, stmt := range map[string]string{
		"b = 21·20! is not 1":   "∀a b:num. a = 2432902008176640000 ∧ b = 21 * a ⇒ b = 1",
		"4·20! off by one":      "∀x:num. x = 2432902008176640000 ⇒ 4 * x = 9731608032706560001",
		"8·20! off by one":      "∀x:num. x = 2432902008176640000 ⇒ 8 * x = 19463216065413120001",
		"8·2⁶¹ is not 0":        "∀x:num. x = 2305843009213693952 ⇒ 8 * x = 0",
		"a bound the wrong way": "∀x:num. 18446744073709551616 ≤ x ⇒ x < 18446744073709551616",
	} {
		t.Run(name, func(t *testing.T) {
			res := byArithOutcome(t, e, stmt, strips, []ByHypSpec{{HypIndex: idx(0)}})
			require.False(t, res.Success, "%s closed", name)
			require.NotEmpty(t, res.Diagnostics)
			for _, d := range res.Diagnostics {
				require.NotContains(t, d.Message, "Should not happen", "the kernel refused a step the closer built")
			}
			require.True(t, strings.Contains(res.Diagnostics[0].Message, "Arith"),
				"the failure is not the arith closer's own: %s", res.Diagnostics[0].Message)
		})
	}
}

// TestByArith_FactorialChapterShape: the shape a chapter meets — a resident
// value of factorial(20) and the recursion law read at the instances that
// lead from it. The law is the newer hypothesis, so it is hyp 0.
func TestByArith_FactorialChapterShape(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	idx := func(i int) *int { return &i }
	const residents = "factorial(20) = 2432902008176640000 ⇒ (∀n. factorial(n + 1) = (n + 1) * factorial(n)) ⇒ "
	strips := []string{"strip_imp", "strip_imp"}
	premises := func(instances ...string) []ByHypSpec {
		hyps := []ByHypSpec{{HypIndex: idx(1)}}
		for _, n := range instances {
			hyps = append(hyps, ByHypSpec{HypIndex: idx(0), Terms: []string{n}})
		}
		return hyps
	}
	closes := []struct {
		name, goal string
		instances  []string
	}{
		{"factorial(21) as a product", "factorial(21) = 21 * factorial(20)", []string{"20"}},
		{"factorial(21) as a numeral", "factorial(21) = 51090942171709440000", []string{"20"}},
		{"factorial(25) as a numeral", "factorial(25) = 15511210043330985984000000", []string{"20", "21", "22", "23", "24"}},
	}
	for _, c := range closes {
		t.Run(c.name, func(t *testing.T) {
			res := byArithOutcome(t, e, residents+c.goal, strips, premises(c.instances...))
			require.True(t, res.Success, "%v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
	t.Run("factorial(21) off by one", func(t *testing.T) {
		res := byArithOutcome(t, e, residents+"factorial(21) = 51090942171709440001", strips, premises("20"))
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		for _, d := range res.Diagnostics {
			require.NotContains(t, d.Message, "Should not happen", "the kernel refused a step the closer built")
		}
	})
}
