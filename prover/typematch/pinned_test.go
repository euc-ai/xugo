package typematch

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/stretchr/testify/require"
)

// The coin toss a law with two carrier letters presents, in miniature:
// the goal holds `=` at two function types, so the anchor for the
// lemma's `h = h` can pair B → C either way, and the goal alone cannot
// say which. The type of the term pinned to h can: it fixes B and C,
// and the sweep completes A from the remaining anchor.
func TestEnumerateLemmaTypeAdaptationsPinned_DecidesTheCoinToss(t *testing.T) {
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{})
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop
	}
	// A structure law's shape: the pinned binder sits UNDER the guard,
	// where a leading-∀ walk never finds it.
	// COND⟨A⟩ is the one constant-headed anchor for A — a bare `s = z`
	// between variables is uninformative to the sweep by design.
	lemma := parse("∀op:(B → B → B). (∀b:B. op(b, b) = b) ⇒ ∀h:(B → C). ∀s z:A. ∀p:bool. COND(p, s, z) = s ⇒ h = h")
	goal := parse("k:((num → X) → X), m:(X → num), t:num, w:num, q:bool ⊢ COND(q, t, w) = t ⇒ m = m ⇒ k = k")

	// The goal's own X, read off k so the pointer is the goal's.
	kType := goalVarType(t, goal, "k")
	pinned := map[string]core.HolType{"h": kType}

	// Read from the anchors alone, the pairing is undecided: the plain
	// enumeration does not settle on k's type for h.
	unpinned := EnumerateLemmaTypeAdaptations(lemma, goal)
	decided := false
	if len(unpinned) == 1 {
		bs, _ := ematch.StripGuardedForalls(unpinned[0].Conclusion())
		decided = bs[1].Type().Equals(kType)
	}
	require.False(t, decided, "the goal alone must not already decide the pairing, or the pin proves nothing")

	out := EnumerateLemmaTypeAdaptationsPinned(lemma, goal, pinned)
	require.Len(t, out, 1, "the pin selects one instance")
	binders, _ := ematch.StripGuardedForalls(out[0].Conclusion())
	require.Len(t, binders, 5)
	require.Equal(t, "h", string(binders[1].Name()))
	require.True(t, binders[1].Type().Equals(kType), "h must read k's type, got %s", ext.FormatType(binders[1].Type()))
	require.True(t, binders[2].Type().Equals(ext.NumType), "s must be at A := num, got %s", ext.FormatType(binders[2].Type()))

	// An inconsistent pin (h at m's type, whose C would be num while
	// the anchors say otherwise) or a name the lemma does not bind
	// yields nothing rather than a guess.
	require.Empty(t, EnumerateLemmaTypeAdaptationsPinned(lemma, goal, map[string]core.HolType{"nobody": kType}))
	require.Nil(t, EnumerateLemmaTypeAdaptationsPinned(lemma, goal, nil))
}

func goalVarType(t *testing.T, goal core.Prop, name string) core.HolType {
	t.Helper()
	for _, v := range goal.Conclusion().Frees(nil) {
		if string(v.Name()) == name {
			return v.Type()
		}
	}
	t.Fatalf("goal has no free %s", name)
	return nil
}
