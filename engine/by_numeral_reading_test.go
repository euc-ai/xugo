package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// plainByRow is a statement, the strips that expose its leaf, the
// hypotheses a plain `by` lists, and whether that `by` closes the leaf.
type plainByRow struct {
	name, stmt string
	strips     []string
	hyps       []int
	closes     bool
}

// runPlainByRows adds each row's statement, strips it, and applies the
// session `by` — the refuter's, no arith — over the listed hypotheses.
func runPlainByRows(t *testing.T, e *Engine, rows []plainByRow) {
	t.Helper()
	ctx := context.Background()
	idx := func(i int) *int { return &i }
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope(r.stmt, &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
			})
			require.Empty(t, parsed.Errors, "add-goal %q", r.stmt)
			s.mu.Lock()
			gid := s.AddGoal(parsed.Prop)
			s.mu.Unlock()
			for _, typ := range r.strips {
				res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
				require.NoError(t, err, "strip %s", typ)
				require.Len(t, res.Produced, 1, "strip %s", typ)
				gid = res.Produced[0].GoalID
			}
			var hyps []ByHypSpec
			for _, i := range r.hyps {
				hyps = append(hyps, ByHypSpec{HypIndex: idx(i)})
			}
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
				Tactic: TacticReq{Type: "by", ByHyps: hyps}})
			if r.closes {
				require.NoError(t, err)
				require.Equal(t, "close", res.Effect, "%s did not close", r.name)
				return
			}
			closed := err == nil && res != nil && res.Effect == "close"
			require.False(t, closed, "%s is no reading of numerals: a plain by must not close it", r.name)
		})
	}
}

// TestBy_ReadsNumerals: the plain `by` reads a statement at its numerals
// where the apply rung compares statements, under the corpus's bundles —
// a guard that is a comparison of numerals asks for no supplier, a goal
// that is one is closed, a hypothesis that is a false one closes the
// leaf, and a statement one numeral term from a resident one is that
// one. What names a variable, and what the reading leaves to the
// arithmetic closer, it does not close.
func TestBy_ReadsNumerals(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	one := []string{"strip_quant", "strip_imp"}
	two := []string{"strip_quant", "strip_imp", "strip_imp"}
	runPlainByRows(t, byArithEngine(t), []plainByRow{
		{"a guard that is a comparison of naturals", "∀Q:bool. (0 < 2 ⇒ Q) ⇒ Q", one, []int{0}, true},
		{"a goal that is a disequation of naturals", "∀Q:bool. Q ⇒ 4 ≠ 0", one, []int{0}, true},
		{"a hypothesis that is a false comparison", "∀Q:bool. 2 < 0 ⇒ Q", one, []int{0}, true},
		{"a sum of naturals read at its value", "∀P:num→bool. P(0 + 1) ⇒ P(1)", one, []int{0}, true},
		{"a truncated difference read at zero", "∀P:num→bool. P(0) ⇒ P(1 - 3)", one, []int{0}, true},
		{"a successor of a numeral", "∀P:num→bool. P(2) ⇒ P(suc(1))", one, []int{0}, true},
		{"a law read at a numeral dimension",
			"∀X:num→(num→bool). ∀d:num→num. ∀x:num. x ∈ X(3) ⇒ (x ∈ X(2 + 1) ∧ 1 ≤ 2 + 1 ⇒ d(x) ∈ X(2)) ⇒ d(x) ∈ X(2)",
			two, []int{0, 1}, true},
		{"a guard that is a comparison of reals", "∀R:real→bool. ∀x:real. R(x) ⇒ (real_of_num(0) ≤ real_of_num(1) ∧ R(x) ⇒ R(x + x)) ⇒ R(x + x)",
			two, []int{0, 1}, true},
		{"a comparison with a quotient and a negation", "∀R:real→bool. ∀x:real. (-real_of_num(1) ≤ real_of_num(1) / real_of_num(2) ⇒ R(x)) ⇒ R(x)",
			one, []int{0}, true},
		{"an equation of real numeral terms", "∀R:real→bool. ∀x:real. (real_of_num(1) - real_of_num(1) / real_of_num(2) = real_of_num(1) / real_of_num(2) ⇒ R(x)) ⇒ R(x)",
			one, []int{0}, true},
		{"a product of real literals read at its value", "∀R:real→bool. R(&2 * &3) ⇒ R(&6)", one, []int{0}, true},
		{"a product of integer literals read at its value", "∀Z:int→bool. Z(&2 * &3) ⇒ Z(&6)", one, []int{0}, true},

		{"a bound a law gives", "∀Q:bool. ∀n:num. (0 ≤ n ⇒ Q) ⇒ Q", one, []int{0}, false},
		{"a reflexive bound", "∀Q:bool. ∀u:real. (u ≤ u ⇒ Q) ⇒ Q", one, []int{0}, false},
		{"a sum with a variable", "∀P:num→bool. ∀n:num. P(n + 1 + 1) ⇒ P(n + 2)", one, []int{0}, false},
		{"a factorial", "∀P:num→bool. P(factorial(3)) ⇒ P(6)", one, []int{0}, false},
		{"a power", "∀P:num→bool. P(2 ^ 3) ⇒ P(8)", one, []int{0}, false},
	})
}
