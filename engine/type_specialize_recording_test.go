package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// cardClauses is the polymorphic member the simp_with instance tests
// fire: cardinality.CardClauses, `card(∅) = 0 ∧ (∀x s. finite(s) ⇒ …)` —
// a conjunction over the set element type whose left clause is ground
// at every instance.
func cardClauses(t *testing.T) *registry.ProofEntry {
	t.Helper()
	entry, ok := registry.ByName("cardinality.CardClauses")
	require.True(t, ok, "cardinality.CardClauses is not registered: the fixture names what the corpus no longer has")
	return entry
}

// TestSimpWith_TypeSpecializedRule_StoreDecompositionResolves is the
// regression test for the silent-bad-recording defect first seen on a
// polymorphic list rule:
//
//	simp_with with an explicit per-entry type_specialize on a polymorphic
//	rule succeeded in-session, but the specialized rule child was closed
//	by a _KnownThmStep whose payload is the PER-SESSION type instance — a
//	statement whose normalized AlphaKey names nothing. The session looked
//	complete; the recording then failed to resolve the dep.
//
// The correct recording channel for a type-instance rule child is
// _TypeInstStep against the POLYMORPHIC source (the same channel
// `lemma`'s claim child uses via runAutoMatchTypeInstance) — which is what
// the post-step pass produces when it is handed the pre-specialization
// source prop instead of the specialized instance.
//
// The test drives the full pipeline: simp_with {key: CardClauses,
// type_specialize: {A: num}} on a goal the specialized rule fires on →
// close residuals → emit. It asserts the emit resolves and declares the
// member as a dep.
func TestSimpWith_TypeSpecializedRule_StoreDecompositionResolves(t *testing.T) {
	member := cardClauses(t)
	e := newEngine(serveLikeEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	lenProp := member.Statement().Prop

	// Specialize EVERY type var of the member to num (it has one: the
	// set element type). Resolve the name dynamically so the test does
	// not hard-code the statement's type-var spelling.
	tvNames := collectLemmaTypeVarNames(lenProp)
	require.NotEmpty(t, tvNames, "CardClauses must be polymorphic")
	spec := map[string]string{}
	for name := range tvNames {
		spec[name] = "num"
	}
	specialized, _, err := buildSpecializedLemma(lenProp, spec, groundTestGoal())
	require.NoError(t, err)
	require.False(t, ext.PropHasTypeVars(specialized))

	// Goal: the empty-set clause instance `⊢ card⟨num⟩(∅⟨num⟩) = 0`,
	// extracted from the specialized member itself (strip the ∀s, take the
	// left conjunct) so the terms are engine-canonical by construction.
	body := specialized.Conclusion()
	for {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			break
		}
		body = abs.Body()
	}
	nilClause, _, isAnd := ext.MatchesAND(body)
	require.True(t, isAnd, "CardClauses must be a conjunction, got %s", ext.PrintTerm(body))
	goal := prop.MakeProp(nilClause)

	gid := s.AddGoal(goal)
	s.rebuildGoalIndex()

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "simp_with",
			WithLemmas: []LemmaWithSpec{{
				Key:            member.Key,
				TypeSpecialize: spec,
			}},
		},
	})
	require.NoError(t, err)
	require.True(t, out.Success,
		"simp_with with the type-specialized CardClauses rule must fire on card(∅) = 0; diagnostics: %+v",
		out.Diagnostics)

	// Close any surviving children (the rewritten residual `0 = 0`; the
	// specialized rule child should have been auto-closed by the post-step
	// type-instance pass).
	for range 8 {
		stateRes, gerr := e.InspectState(ctx, info.ID)
		require.NoError(t, gerr)
		if stateRes.NumOpen == 0 {
			break
		}
		closed := false
		for _, og := range stateRes.Goals {
			for _, tac := range []string{"simplify", "auto"} {
				aout, aerr := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
					GoalID: og.ID,
					Tactic: TacticReq{Type: tac},
				})
				if aerr == nil && aout.Success {
					closed = true
					break
				}
			}
			if closed {
				break
			}
		}
		if !closed {
			for _, og := range stateRes.Goals {
				t.Logf("still open: %s = %s", og.ID, prop.PrintProp(og.Statement))
			}
		}
		require.True(t, closed, "every child must close by simplify/auto")
	}
	stateRes, gerr := e.InspectState(ctx, info.ID)
	require.NoError(t, gerr)
	require.Equal(t, 0, stateRes.NumOpen, "proof tree must be fully closed before emit")

	// THE regression assertion: the emit must resolve every recorded
	// step's dep — the specialized instance recorded as a TypeInst
	// against the polymorphic member, not a KnownThm payload naming
	// nothing.
	deps := emittedDepNames(t, e, info.ID, 0)
	assert.Contains(t, deps, member.Name,
		"the member must be a dep of the emitted member; deps=%v", deps)
}
