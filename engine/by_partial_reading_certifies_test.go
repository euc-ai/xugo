package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestBy_PartialReadingCertifiesAsItsTelescope: a law read at a resident
// hypothesis and grounded at fewer witnesses than the reading has
// binders is installed as the reading's telescope at the tuple —
// smooth_curve.DegreeOneClosedPointsRational reads `∀k A₀ A₁ A₀₁ t P.
// curve ⇒ …` at `field_on(L₀)`, and at five witnesses its curve
// hypothesis, which names none of P, stands ahead of `∀P`. The claim
// that install leaves is the telescope of the derived reading, and the
// reading certifies it. Every length of the tuple closes the leaf, one
// direction of the law's equivalence.
func TestBy_PartialReadingCertifiesAsItsTelescope(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	leaf := func(t *testing.T) (*Engine, *Session) {
		e, s := boundSession(t, "scheme/smooth_curve")
		const statement = "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). " +
			"smooth_finite_curve(L, k, t, A₀, A₁, A₀₁) ∧ " +
			"curve_closed_point(field_ring(L), A₀, A₁, A₀₁, P) ∧ curve_closed_degree(field_ring(L), k, A₀, A₁, P) = 1 ⇒ " +
			"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, P)"
		parsed := dsl.ParsePropTextInScope(statement, s.StatementDoorScope())
		require.Empty(t, parsed.Errors, "add-goal %q", statement)
		s.mu.Lock()
		s.AddGoal(parsed.Prop)
		s.mu.Unlock()
		for _, strip := range []string{"intro", "strip_imp", "strip_quant", "strip_imp"} {
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: strip})
		}
		return e, s
	}
	by := func(t *testing.T, e *Engine, s *Session, table map[string]string) *StepResult {
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: soleGoal(t, e, s.ID).ID, Tactic: TacticReq{
			Type:   "by",
			ByHyps: everyHyp(soleGoal(t, e, s.ID)),
			WithLemmas: []LemmaWithSpec{{
				Key:            "smooth_curve.DegreeOneClosedPointsRational",
				ReadAt:         &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "field_on(")},
				TermSpecialize: table,
			}},
		}})
		require.NoError(t, err)
		return res
	}
	binders := []string{"k", "A₀", "A₁", "A₀₁", "t", "P"}
	witnesses := []string{"k₀", "A₀", "A₁", "A₀₁", "t₀", "P₀"}
	for n := range len(binders) + 1 {
		table := map[string]string{}
		for i := range n {
			table[binders[i]] = witnesses[i]
		}
		t.Run("through "+strings.Join(binders[:n], " "), func(t *testing.T) {
			e, s := leaf(t)
			res := by(t, e, s, table)
			require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}

	// The tuple that stops at t, the last binder the curve hypothesis
	// names: the member it emits spells the reading at those witnesses.
	e, s := leaf(t)
	res := by(t, e, s, map[string]string{"k": "k₀", "A₀": "A₀", "A₁": "A₁", "A₀₁": "A₀₁", "t": "t₀"})
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_ZzPartialReading"})
	require.NoError(t, err)
	assert.Contains(t, strings.Join(strings.Fields(out.Go), " "), "At(DegreeOneClosedPointsRational.Read(L), k, A0, A1, A01, t)")
	replayEmittedInFamily(t, "scheme/smooth_curve", "ZzPartialReading", out)
}
