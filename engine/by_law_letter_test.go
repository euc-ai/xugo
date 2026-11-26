package engine

import (
	"context"
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestBy_ALawAtAnInstanceHoldingItsOwnLetterName: associativity of `∘`
// cited at (num → A) — an instance holding the goal's letter A, which
// the law's statement spells too — closes as it does at (num → E). It
// reached a kernel assertion: the law's install was adapted to a mixed
// instance (the law's A read as the goal's), whose claim was the By's
// own goal.
func TestBy_ALawAtAnInstanceHoldingItsOwnLetterName(t *testing.T) {
	for _, letter := range []string{"A", "E"} {
		e, s := boundSession(t, "sets/functions")
		addTextGoal(t, s, "∀f g h:((num → "+letter+") → (num → "+letter+")). f ∘ (g ∘ h) = (f ∘ g) ∘ h")
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID,
			Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "functions.ComposeAssoc"}}}})
		require.NoError(t, err)
		require.True(t, res.Success, "letter %s: %v", letter, res.Diagnostics)
		require.True(t, s.sections[0].root.Proved(), "letter %s", letter)
	}
}

// TestBy_ABareLawInNormalFormAtAnInstanceHoldingItsOwnLetter: the
// union law cited at sets of (prod(B, C) → A) — the law's A read at a
// type holding A — closes in an unbound session by the apply rung, as
// it does at (prod(B, C) → D). The law is its own clause form; the
// install and the rung's head enumeration each reach the instance with
// the law's letters renamed apart.
func TestBy_ABareLawInNormalFormAtAnInstanceHoldingItsOwnLetter(t *testing.T) {
	for _, letter := range []string{"D", "A"} {
		e := newEngine(statedSessionEnv())
		info, err := e.CreateSession(context.Background())
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		addTextGoal(t, s, "∀s t w:set(prod(B, C) → "+letter+"). s ⊆ w ⇒ t ⊆ w ⇒ s ∪ t ⊆ w")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(1)},
			WithLemmas: []LemmaWithSpec{{Key: "set_order.UnionSubset"}}})
		require.Contains(t, fmt.Sprint(res.Diagnostics), "apply/conditioning", "letter %s: the apply rung closes it", letter)
		require.True(t, s.sections[0].root.Proved(), "letter %s", letter)
	}
}
