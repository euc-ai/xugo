package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestBy_AReadingTakesItsLawsBinderName: a law read at an instance is
// addressed by the binder names its statement gives, whatever the
// kernel renamed apart. quotient_group.QuotientGroupOn binds N; read at
// a group whose record spells a session `let N := …`, the kernel holds
// that binder as Kʹ, and a term_specialize table takes either name.
func TestBy_AReadingTakesItsLawsBinderName(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	sole := func(core.Prop) bool { return true }
	by := func(t *testing.T, table map[string]string) (*StepResult, error) {
		e, s := boundSession(t, "algebra/group/quotient_group")
		statement := "∀G:group_ops(A). ∀H K:set(A). group_on(restrict_group(G, H ∩ K)) ⇒ " +
			"normal_subgroup(restrict_group(G, H ∩ K), H) ⇒ group_on(quotient_group(restrict_group(G, H ∩ K), H))"
		parsed := dsl.ParsePropTextInScope(statement, s.StatementDoorScope())
		require.Empty(t, parsed.Errors, "add-goal %q", statement)
		s.mu.Lock()
		s.AddGoal(parsed.Prop)
		s.mu.Unlock()
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		// The let folds H₀ ∩ K₀ to N in the group fact the law is read at.
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "let", Name: "N", Const: "H₀ ∩ K₀"})
		return e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: soleGoal(t, e, s.ID).ID, Tactic: TacticReq{
			Type: "by",
			WithLemmas: []LemmaWithSpec{{
				Key:            "quotient_group.QuotientGroupOn",
				ReadAt:         &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "group_on(")},
				TermSpecialize: table,
			}},
			ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, sole, "normal_subgroup(")}},
		}})
	}
	for _, name := range []string{"N", "Kʹ"} {
		t.Run("named "+name, func(t *testing.T) {
			res, err := by(t, map[string]string{name: "H₀"})
			require.NoError(t, err)
			require.True(t, res.Success, "the by did not close: %v", res.Diagnostics)
			require.Equal(t, "close", res.Effect)
		})
	}
	refused := func(t *testing.T, table map[string]string) string {
		res, err := by(t, table)
		require.NoError(t, err)
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		return res.Diagnostics[0].Message
	}
	t.Run("both names", func(t *testing.T) {
		require.Contains(t, refused(t, map[string]string{"N": "H₀", "Kʹ": "H₀"}),
			`"N" and "Kʹ" name one binder — the law states it N and this reading holds it as Kʹ`)
	})
	t.Run("a name the law does not state", func(t *testing.T) {
		require.Contains(t, refused(t, map[string]string{"M": "H₀"}), "available: [N (held here as Kʹ)]")
	})
}
