package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestBy_ClosersReadRecordProjections: a claim spelled with a ring record's
// own carrier, `polynomial_algebra_ring(R, S).carrier`, meets a fact spelled
// at the carrier the record equations compute, `polynomial_algebra(R, S)` —
// the form a cited instance arrives in. The inclusion is no identity the
// apply rung takes, so the close is the set driver's, on the leaf the
// conditioning stage read (proof conditionOpts.readRecords); the refuter is
// handed the same leaf.
func TestBy_ClosersReadRecordProjections(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	zero := 0
	const member = "∀R:ring_ops(A). ∀S:set(num). ∀P:((num → num) → A). P ∈ polynomial_algebra(R, S) ⇒ "
	for _, row := range []struct {
		name, stmt string
		settac     bool
	}{
		{"an inclusion in the record's carrier, by the set driver", member + "{P} ⊆ polynomial_algebra_ring(R, S).carrier", true},
		{"the same inclusion at the computed carrier", member + "{P} ⊆ polynomial_algebra(R, S)", true},
		{"a membership beside another fact, by the refuter",
			"∀R:ring_ops(A). ∀S:set(num). ∀P:((num → num) → A). ∀Q:bool. " +
				"(P ∈ polynomial_algebra(R, S) ∨ Q) ∧ ¬Q ⇒ P ∈ polynomial_algebra_ring(R, S).carrier", false},
	} {
		t.Run(row.name, func(t *testing.T) {
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope(row.stmt, &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
				Syntax: constSyntax(),
			})
			require.Empty(t, parsed.Errors, "add-goal %q", row.stmt)
			s.mu.Lock()
			gid := s.AddGoal(parsed.Prop)
			s.mu.Unlock()
			for _, typ := range []string{"strip_quant", "strip_imp"} {
				res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
				require.NoError(t, err, "strip %s", typ)
				require.Len(t, res.Produced, 1, "strip %s", typ)
				gid = res.Produced[0].GoalID
			}
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
				Tactic: TacticReq{Type: "by", Settac: row.settac, ByHyps: []ByHypSpec{{HypIndex: &zero}}}})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
}
