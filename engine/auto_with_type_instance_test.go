package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Registry-backed regressions for the auto_with install divergence
// (`auto_with` skipping the type-instance auto-match on
// `type_specialize` entries): plain `lemma` and
// `simp_with` close a polymorphic entry's claim subgoal through BOTH
// auto-match channels (generic α-key + type-instance-with-source-key),
// while auto_with ran only the generic pass — so any entry installed at
// a type instance (explicit type_specialize σ, or LemmaPreserve's
// internal adaptation) left its claim leaf open and failed the whole
// close-or-fail apply. Met at an iterated product and at the
// finiteness of a cartesian product (the product and subset laws
// loaded at an instance).
//
// Both tests drive the exact agent surface (ApplyStep, Type:"auto_with")
// against the registry's finite_set.FiniteImage entry —
// the statement of the KI's repro. The session goal is the sighting
// shape: an instance-typed GROUND consequence of the entry (its
// ∀-stripped disjunction at free s/f), so that
//
//   - the RESIDUAL (installed instance-hyp ⊢ ground disjunction) closes
//     via the ordinary first-order close pass — no type reasoning; and
//   - the CLAIM (⊢ the entry at the goal's type instance) α-differs from
//     the entry's statement and can ONLY close through the type-instance
//     channel. Left open it reaches close-or-fail and the whole apply
//     rolls back.
func autoWithTypeInstanceFixture(
	t *testing.T, goalText string,
) (e *Engine, sessionID, goalID string) {
	t.Helper()

	lemProp := finiteImageLemma(t)
	// Pin the entry precondition: the statement must still be polymorphic
	// with distinct A/B (else the instance goals below stop being proper
	// type instances and the tests need re-derivation).
	require.Contains(t, ext.PrintTermWithPolyBinders(lemProp.Conclusion()),
		"∀f:(var:A → var:B)",
		"the finite_set.FiniteImage entry must have f at A→B (distinct vars)")

	// Parse the ground goal in the entry's const scope so finite / image
	// resolve as registered constants (plain dsl.ParsePropText would read
	// them as free vars).
	goalProp, err := parsePropTextInGoalScope(goalText, lemProp, nil)
	require.NoError(t, err)

	e = newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
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

const autoWithFiniteImageKey = "prop_db7b9fb5a43038a" // finite_set.FiniteImage: ∀s:(A→bool).∀f:(A→B). finite(image(f,s)) ∨ ¬finite(s)

// finiteImageLemma is finite_set.FiniteImage
// in the normalized form the fixtures state
// their ground instances against: ∀s f. finite(image(f, s)) ∨ ¬finite(s).
func finiteImageLemma(t *testing.T) core.Prop {
	t.Helper()
	entry, ok := registry.ByKey(autoWithFiniteImageKey)
	require.True(t, ok, "no entry carries finite_set.FiniteImage's key %s", autoWithFiniteImageKey)
	normalized, _ := prop.Normalize(entry.Statement().Prop)
	return normalized
}

// TestAutoWith_TypeSpecializedEntry_ClaimClosesViaTypeInstance is the
// KI's primary shape: a with_lemmas entry carrying an explicit
// type_specialize σ, at DISTINCT instances (A:=num, B:=num→bool — the
// funspace-cardinality flavor of the sightings). The install's claim
// subgoal is the σ-instance of the polymorphic entry — invisible to the
// generic α-key pass, closeable only by
// applyAutoMatchTypeInstanceOnRoots with the entry's key as
// source. Without that channel it fails close-or-fail with the claim
// leaf open.
func TestAutoWith_TypeSpecializedEntry_ClaimClosesViaTypeInstance(t *testing.T) {
	e, sid, gid := autoWithTypeInstanceFixture(t,
		"s:(num → bool), f:(num → (num → bool)) ⊢ finite(image(f, s)) ∨ ¬finite(s)")

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type: "auto_with",
			WithLemmas: []LemmaWithSpec{{
				Key:            autoWithFiniteImageKey,
				TypeSpecialize: map[string]string{"A": "num", "B": "(num → bool)"},
			}},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("auto_with diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success,
		"auto_with with a type_specialize'd entry must close: the claim "+
			"subgoal is a type instance of the entry and needs the type-instance "+
			"auto-match channel")
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestAutoWith_PlainKeyEntry_AdaptedClaimClosesViaTypeInstance is the
// finite-product / finite-subset shape: a plain-key polymorphic entry
// on an instance-typed goal.
// The goal sits at the SAME instance on both finite anchors (A=B=num)
// so ApplyLemmaPreserve's internal type adaptation fires unambiguously
// (no bareConstAnchorAmbiguous abstain) and pins the entry to the goal's
// instance — the claim subgoal again α-differs from the entry's statement.
func TestAutoWith_PlainKeyEntry_AdaptedClaimClosesViaTypeInstance(t *testing.T) {
	e, sid, gid := autoWithTypeInstanceFixture(t,
		"s:(num → bool), f:(num → num) ⊢ finite(image(f, s)) ∨ ¬finite(s)")

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:       "auto_with",
			WithLemmas: []LemmaWithSpec{{Key: autoWithFiniteImageKey}},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("auto_with diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success,
		"auto_with with a plain-key polymorphic entry on an instance-typed goal "+
			"must close: the internally-adapted claim subgoal needs the "+
			"type-instance auto-match channel")
	assert.Equal(t, 0, out.State.NumOpen)
}
