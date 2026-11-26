package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// byPremiseIsGoalSession opens a session on cardinal.CountableEmpty's
// own statement, `countable(∅)`, under the given ambient hypotheses.
func byPremiseIsGoalSession(t *testing.T, ambient ...core.Term) (e *Engine, sessionID, goalID string) {
	t.Helper()
	entry, ok := registry.ByName("cardinal.CountableEmpty")
	require.True(t, ok, "cardinal.CountableEmpty is not registered")
	goalProp := prop.MakeProp(entry.Statement().Prop.Conclusion(), ambient...)

	e = newEngine(testEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(goalProp)
	s.rebuildGoalIndex()
	for id, ge := range s.goalIndex {
		if ge.sectionID == 0 {
			goalID = id
			break
		}
	}
	require.NotEmpty(t, goalID)
	return e, info.ID, goalID
}

// TestByTactic_PremiseIsTheLeafStatement — a `by` whose one premise is
// the entry the leaf states. The leaf's context is not named, so the
// composite clears it and is left with the entry's statement: that is
// the premise's claim, certified by the entry, and the leaf closes —
// Lean's `exact`, the session twin of a chapter's `By(X)` on such a
// leaf. An install has nothing to add there: its claim child would be
// the cleared leaf again.
func TestByTactic_PremiseIsTheLeafStatement(t *testing.T) {
	e, sid, gid := byPremiseIsGoalSession(t, ext.Var("p", core.TypeBool()).Core())

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "by",
			WithLemmas: []LemmaWithSpec{{Key: "cardinal.CountableEmpty"}},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("by diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success)
	assert.Equal(t, 0, out.State.NumOpen)
}

// With no context to clear, the By's goal is the premise's statement
// and the composite has nothing to do: the refusal names the cite.
func TestByTactic_PremiseIsTheWholeGoal_NamesLemma(t *testing.T) {
	e, sid, gid := byPremiseIsGoalSession(t)

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "by",
			WithLemmas: []LemmaWithSpec{{Key: "cardinal.CountableEmpty"}},
		},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	var text []string
	for _, d := range out.Diagnostics {
		text = append(text, d.Message)
	}
	assert.Contains(t, strings.Join(text, "\n"), "the `lemma` tactic at that key")
}

// byWholeGoalSession opens a session of the corpus engine on a closed
// statement, unstripped, and returns the goal's id.
func byWholeGoalSession(t *testing.T, e *Engine, statement string) (sessionID, goalID string) {
	t.Helper()
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	return info.ID, byWholeGoalAdd(t, e, info.ID, statement)
}

// byWholeGoalAdd adds a closed statement to the session as a new
// section and returns its goal's id.
func byWholeGoalAdd(t *testing.T, e *Engine, sessionID, statement string) string {
	t.Helper()
	s, err := e.getSession(sessionID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(statement, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		Syntax: constSyntax(),
	})
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.AddGoal(parsed.Prop)
}

// TestByTactic_PremiseStatesTheWholeGoalAtATypeInstance — the By's goal
// is the premise's statement at another type instance, and the premise
// installs in a clause form that spells it otherwise (an equation of
// sets read pointwise). The stated form is then no head of the apply
// rung: installed, its claim would be the By's own goal, the goal its
// own obligation. The rung passes it over and the closer proves the goal
// from the clause form, whose claim the premise's source certifies — a
// registered entry by its key, a proved sibling section by its text.
func TestByTactic_PremiseStatesTheWholeGoalAtATypeInstance(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	const atNum = "∀a b:set(num). a ⊆ b ∧ b ⊆ a ⇒ a = b"
	closes := func(t *testing.T, e *Engine, sid, gid string, premise LemmaWithSpec) {
		t.Helper()
		out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{premise}},
		})
		require.NoError(t, err)
		require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
		assert.Equal(t, 0, out.State.NumOpen)
	}
	t.Run("a registered entry", func(t *testing.T) {
		e := byArithEngine(t)
		sid, gid := byWholeGoalSession(t, e, atNum)
		closes(t, e, sid, gid, LemmaWithSpec{Key: "set_order.SubsetAntisym"})
	})
	t.Run("a proved sibling section", func(t *testing.T) {
		const polymorphic = "∀s t:set(A). s ⊆ t ∧ t ⊆ s ⇒ s = t"
		e := byArithEngine(t)
		sid, gid := byWholeGoalSession(t, e, polymorphic)
		out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by", Settac: true}})
		require.NoError(t, err)
		require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
		closes(t, e, sid, byWholeGoalAdd(t, e, sid, atNum), LemmaWithSpec{Text: polymorphic})
	})
}
