package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestFiniteImage_TermSpecialize_CrossTypeVarBinding is the
// iterated-product shape for resolveTermSpecializeWitnesses's
// σ-accumulator under a type-variable name collision: loading the
// finite_set.FiniteImage entry with
// `term_specialize={s: t(a), f: λj:B.,(a, j)}` against a goal where
// `a:A, t:A→(B→bool)` are free vars must bind lemma-α := goal-B
// (from t(a):B→bool) and lemma-β := prod(goal-A, goal-B) (from the
// pair-λ's codomain), producing an installed hyp whose finite
// polymorphic-head arg = prod(A,B) — NOT a spurious type-unification
// failure and NOT a collapsed ∀f:(var:B → var:B).
//
// The goal is DSL-synthesized because the natural statement for this
// pattern (identity-pair-set finite) has `a` bound inside an inner ∀x
// hyp and requires strip work to bring it into scope. What the test
// EXERCISES is the registry LEMMA + the term_specialize dispatch path.
//
// The in-memory unit twin (no registry entry needed) is
// TestApply_LemmaTermSpecialize_GoalLemmaTypeVarNameCollision.
func TestFiniteImage_TermSpecialize_CrossTypeVarBinding(t *testing.T) {

	const lemmaKey = "prop_db7b9fb5a43038a" // finite_set.FiniteImage

	// Verify the entry's form still has distinct type vars — if the
	// stated form changes, the test needs re-derivation.
	lemProp := finiteImageLemma(t)
	require.Contains(t, ext.PrintTermWithPolyBinders(lemProp.Conclusion()),
		"∀f:(var:A → var:B)",
		"the finite_set.FiniteImage entry must have f at A→B (distinct vars)")

	// DSL-synthesized goal that brings `a:A, t:A→(B→bool)` into the
	// free-var scope so `t(a)` and `λj:B.,(a, j)` parse in the
	// witness-resolution step. We use `T` (top) as the conclusion —
	// we're not proving anything; we're verifying that the specialize
	// dispatch installs the FiniteImage hyp with the right types.
	parseRes := dsl.ParsePropText(
		"a:A, t:A→(B→bool), a = a ⊢ T ∧ t = t")
	require.Empty(t, parseRes.Errors, "goal parse must succeed: %v", parseRes.Errors)
	goalProp := parseRes.Prop

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sess, _ := e.getSession(info.ID)
	sess.AddGoal(goalProp)
	sess.rebuildGoalIndex()

	var goalID string
	for id, ge := range sess.goalIndex {
		if ge.sectionID == 0 {
			goalID = id
			break
		}
	}
	require.NotEmpty(t, goalID)

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{
			Type:     "lemma",
			LemmaKey: lemmaKey,
			TermSpecialize: map[string]string{
				"s": "t(a)",
				"f": "λj:B. ,(a, j)",
			},
		},
	})
	require.NoError(t, err)
	require.True(t, res.Success,
		"term_specialize must succeed on finite_set.FiniteImage cross-type-var binding "+
			"(the σ-threading bug erroneously fails with 'cannot unify (var:B → var:B) "+
			"with (var:B → prod(var:A,var:B))'); diagnostics=%v",
		res.Diagnostics)
	require.NotNil(t, res.State)
	require.NotEmpty(t, res.State.Goals)

	// The installed hyp — post `term_specialize` — must have the
	// lemma-side type var β=B bound to prod(A,B). Read that off the
	// finite polymorphic-head arg: `finite⟨A:prod(var:A,var:B)⟩(...)`.
	var installed string
	for _, h := range res.State.Goals[0].Hypotheses {
		p := ext.PrintTermWithPolyBinders(h)
		if strings.Contains(p, "image") {
			installed = p
			break
		}
	}
	require.NotEmpty(t, installed,
		"must find the installed finite_set.FiniteImage hyp; got hyps:\n%s",
		dumpHyps(res.State.Goals[0].Hypotheses))
	t.Logf("installed hyp: %s", installed)

	assert.Contains(t, installed, "prod(var:A,var:B)",
		"installed finite hyp must carry β := prod(A,B) — the cross-var propagation "+
			"from the second witness's codomain")
}
