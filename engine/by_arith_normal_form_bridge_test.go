package engine

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_NormalFormBridgeIsNoRule: the arithmetic normal form of a
// term is not always its smaller spelling — a cast of a power, `&2 ^ n`,
// is read as `&(2 ^ n)` — and the closer leaves the equation between the
// two spellings beside the leaf it rewrote. Read as a congruence rule
// that equation points back at the spelling the closer just left, so the
// next round's rewrite of the leaf returns to the leaf: no step, and the
// closer goes on to close or to name the leaf it stopped on.
func TestByArith_NormalFormBridgeIsNoRule(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	zero := 0
	by := func(t *testing.T, stmt string) *StepResult {
		t.Helper()
		sid, gid := bareArithLeaf(t, e, stmt, "strip_quant", "strip_imp")
		res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: &zero}}},
		})
		require.NoError(t, err)
		return res
	}
	const stopped = "the closer Arith did not close the leaf"
	// The power under an atom arithmetic does not read, so the closer
	// stops: in the conclusion, then in a hypothesis.
	for _, row := range []struct{ name, stmt string }{
		{"the conclusion's power", "∀n:num. log(&2) ≤ log(&3) ⇒ log(&2 ^ n) ≤ log(&3)"},
		{"a hypothesis's power", "∀n:num. log(&2 ^ n) ≤ log(&3) ⇒ log(&2) ≤ log(&3)"},
	} {
		t.Run(row.name, func(t *testing.T) {
			res := by(t, row.stmt)
			require.False(t, res.Success)
			require.Len(t, res.Diagnostics, 1)
			require.Contains(t, res.Diagnostics[0].Message, stopped)
		})
	}
	// The power as a factor of the products a linear goal is stated over:
	// the round trip is the conclusion's, and past it the goal closes.
	t.Run("a factor of the conclusion's product", func(t *testing.T) {
		res := by(t, "∀m N:num. ∀a b:real. &m ≤ a * &2 ^ N ∧ &1 < &2 ^ N * (b - a) ⇒ &(m + 1) < b * &2 ^ N")
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Equal(t, "close", res.Effect)
	})
}
