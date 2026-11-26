package engine

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// TestClaimDoor_APolymorphicGoalConstantIsNoPin: a polymorphic constant
// the goal mentions is not pinned at the goal's instance for the texts
// the session reads under it (goalConstScope). With `F ≠ ∅` resident —
// ∅ at set(set(A)) — a claim's bare ∅ takes its instance from its
// partner, as Go's claim parse reads it: `∃x:set(A). x = ∅` holds ∅ at
// set(A), and one claim may hold ∅ at two instances. A letter no term
// of the claim fixes is refused by name, not read at the instance the
// goal happens to hold.
func TestClaimDoor_APolymorphicGoalConstantIsNoPin(t *testing.T) {
	parsed := dsl.ParsePropTextInScope("F:set(set(A)), s:set(A), t:set(B), F ≠ ∅ ⊢ s = s ∧ t = t",
		&dsl.ParseScope{ConstResolver: registryConstResolver, FreshenMetaLetters: true, Syntax: constSyntax()})
	require.Empty(t, parsed.Errors)
	goal := parsed.Prop

	setOfA := core.MakeFun(core.MakeVarType("A"), core.TypeBool())
	claim, err := parseClaimTextInGoalScope("∃x:set(A). x = ∅", goal, nil)
	require.NoError(t, err, "the resident ∅ at set(set(A)) must not pin the claim's ∅")
	found := false
	for sub := range ext.SubTerms(claim.Conclusion()) {
		if c, ok := sub.AsConst(); ok && c.Name() == "empty_set" {
			require.True(t, sub.Type().Equals(setOfA), "the claim's ∅ is at %s", ext.FormatType(sub.Type()))
			found = true
		}
	}
	require.True(t, found, "the claim holds ∅")

	for _, text := range []string{"s = ∅ ∨ t = ∅", "F = ∅ ∨ ∅ ∈ F"} {
		_, err := parseClaimTextInGoalScope(text, goal, nil)
		require.NoError(t, err, text)
	}

	_, err = parseClaimTextInGoalScope("∅ = ∅", goal, nil)
	require.ErrorContains(t, err, "unpinned", "no term of the claim fixes ∅'s letter")
}
