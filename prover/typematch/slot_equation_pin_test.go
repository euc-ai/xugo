package typematch

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/stretchr/testify/require"
)

func parseForPins(t *testing.T, text string) core.Prop {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{})
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop
}

// A rule anchored by polymorphic built-ins alone — set extensionality,
// `∀s t:(A → bool). s = t ⇔ ∀x. x ∈ s ⇔ x ∈ t` — at a goal that spells
// its equation at a SECOND element type. The rule's one real constant,
// `∈`, occurs nowhere in the goal (it appears only after extensionality
// has fired), so before the slot-equation pin the enumeration offered
// no instance at all and the rule fired nothing, silently. The equation
// between the rule's own binders is at `A → bool`, a compound type: its
// type is the author's declaration, it cannot unify with bool, and it
// is what a reader pins the instance from.
func TestEnumerateLemmaTypeAdaptations_SlotEquationAtCompoundTypePins(t *testing.T) {
	extension := parseForPins(t, "∀s t:(A → bool). s = t ⇔ ∀x:A. x ∈ s ⇔ x ∈ t")
	// set_of_list⟨B⟩(list_map(f, l)) = image(f, set_of_list⟨A⟩(l)), with
	// variable heads standing in for the chapter's constants: the goal
	// holds sets at A and at B and no `∈`.
	goal := parseForPins(t, "f:(A → B), l:L, sl:(L → (A → bool)), slB:(M → (B → bool)), map:((A → B) → L → M), image:((A → B) → (A → bool) → (B → bool)) ⊢ slB(map(f, l)) = image(f, sl(l))")

	out := EnumerateLemmaTypeAdaptations(extension, goal)
	require.Len(t, out, 1, "the equation's own type is the one instance the goal offers")
	binders, _ := ematch.StripGuardedForalls(out[0].Conclusion())
	require.Len(t, binders, 2)
	fType := goalVarType(t, goal, "f")
	wantSet := core.MakeFun(fType.(core.CompositeType).SubType(1), core.TypeBool())
	require.True(t, binders[0].Type().Equals(wantSet), "s must be at B → bool, got %s", ext.FormatType(binders[0].Type()))

	// The primary sweep is unchanged: it keeps the informative-var drop,
	// so TryAdaptLemmaTypes still adapts nothing here. Session
	// simp_with reads the enumeration, which is where the rule is
	// expanded to the goal's instances.
	require.Nil(t, TryAdaptLemmaTypes(extension, goal))
}

// The pin is read only off an equation at a COMPOUND type. A slot
// equation at a bare type variable matches every `⇔` in the goal (= at
// bool), which is the coincidence the weak-anchor drop exists for, so
// it stays weak: with an informative anchor owning A, no pin comes off
// `x = y` — neither from a `⇔` nor from an equation at num.
func TestEnumerateLemmaTypeAdaptations_SlotEquationAtBareTypeVarStaysWeak(t *testing.T) {
	law := parseForPins(t, "∀x y:A. ∀p:bool. x = y ⇔ COND(p, x, y) = y")
	require.Empty(t, EnumerateLemmaTypeAdaptations(law, parseForPins(t, "p:bool, q:bool ⊢ p ⇔ q")),
		"a bare-variable slot equation must not pin A := bool off a ⇔")
	require.Empty(t, EnumerateLemmaTypeAdaptations(law, parseForPins(t, "n:num, m:num ⊢ n = m")),
		"nor A := num off an equation, while COND owns A and finds nothing")
}
