package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestBy_ChoiceFunctionOfAHypothesis: a goal `∃R. ∀x̄. P[R(x̄)]` beside the
// hypothesis `∀x̄. ∃J. P` it is the choice function of. The Skolem stage
// gives the hypothesis the goal's own form, and the close is that
// identity — no search, no key — where a refutation reads the goal
// negated and has to find R by higher-order unification: at once for the
// bare statement, not within the budget once R is read twice or its
// values are sets.
func TestBy_ChoiceFunctionOfAHypothesis(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	zero := 0
	for _, row := range []struct{ name, stmt string }{
		{"two arguments",
			"∀P:(num → num → num → bool). (∀I n:num. ∃J:num. P(I, n, J)) ⇒ ∃R:(num → num → num). ∀I n:num. P(I, n, R(I, n))"},
		{"read twice, under a guard",
			"∀G:(num → num → bool). ∀P:(num → num → num → bool). (∀I n:num. G(I, n) ⇒ ∃J:num. P(I, n, J) ∧ G(J, n)) ⇒ " +
				"∃R:(num → num → num). ∀I n:num. G(I, n) ⇒ P(I, n, R(I, n)) ∧ G(R(I, n), n)"},
		{"read twice, the conjuncts in the other order",
			"∀G:(num → num → bool). ∀P:(num → num → num → bool). (∀I n:num. G(I, n) ⇒ ∃J:num. P(I, n, J) ∧ G(J, n)) ⇒ " +
				"∃R:(num → num → num). ∀I n:num. G(I, n) ⇒ G(R(I, n), n) ∧ P(I, n, R(I, n))"},
		{"set-valued",
			"∀G:(set(A) → num → bool). ∀P:(set(A) → num → set(A) → bool). (∀I:set(A). ∀n:num. G(I, n) ⇒ ∃J:set(A). P(I, n, J)) ⇒ " +
				"∃R:(set(A) → num → set(A)). ∀I:set(A). ∀n:num. G(I, n) ⇒ P(I, n, R(I, n))"},
		{"the bound names differ",
			"∀P:(num → num → num → bool). (∀a b:num. ∃c:num. P(a, b, c)) ⇒ ∃next:(num → num → num). ∀I n:num. P(I, n, next(I, n))"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, row.stmt, "strip_quant", "strip_imp")
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid, Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}}},
			})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			var said []string
			for _, d := range res.Diagnostics {
				said = append(said, d.Message)
			}
			text := strings.Join(said, "\n")
			require.Contains(t, text, "choice function of a hypothesis (no key)")
			require.Contains(t, text, "Records nothing")
		})
	}
}
