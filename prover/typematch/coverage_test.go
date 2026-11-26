package typematch

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/stretchr/testify/require"
)

// A law is read at the instance the goal holds all of its constants at.
// The goal holds ⊆ and ∅ at sets of sets alone and a membership both
// there and at the element type; the law's membership anchor is its
// largest, and the sweep commits the first membership it meets. The
// answer is the same whichever of the law's disjuncts comes first,
// whichever order the goal spells its memberships in, and whether or not
// the goal's letter is the law's.
func TestTryAdaptLemmaTypes_ReadsTheInstanceTheGoalHoldsItsConstantsAt(t *testing.T) {
	lemmas := []string{
		"∀x:A. ∀s:(A → bool). ¬(x ∈ s) ∨ ¬(s ⊆ ∅)",
		"∀x:A. ∀s:(A → bool). ¬(s ⊆ ∅) ∨ ¬(x ∈ s)",
	}
	goals := []string{
		"F:((%[1]s → bool) → bool), y:%[1]s, t:(%[1]s → bool) ⊢ (y ∈ t ∧ t ∈ F) ∧ ¬(F ⊆ ∅)",
		"F:((%[1]s → bool) → bool), y:%[1]s, t:(%[1]s → bool) ⊢ ¬(F ⊆ ∅) ∧ (t ∈ F ∧ y ∈ t)",
	}
	for _, lemmaText := range lemmas {
		lemma := parseCoverage(t, lemmaText)
		for _, goalText := range goals {
			for _, letter := range []string{"A", "B"} {
				goal := parseCoverage(t, fmt.Sprintf(goalText, letter))
				want := goalVarType(t, goal, "F")
				adapted := TryAdaptLemmaTypes(lemma, goal)
				require.NotNil(t, adapted, "%s at %s: no adaptation", lemmaText, prop.PrintProp(goal))
				binders, _ := ematch.StripGuardedForalls(adapted.Conclusion())
				require.Len(t, binders, 2)
				require.True(t, binders[1].Type().Equals(want),
					"%s at %s: s is read at %s, the goal holds ⊆ at %s",
					lemmaText, prop.PrintProp(goal), ext.FormatType(binders[1].Type()), ext.FormatType(want))
			}
		}
	}
}

// Where the law's constants disagree about the instance — the goal
// holds its membership at the element type alone, its ⊆ and ∅ at sets of
// sets alone — every instance misses one, and the commit stands.
func TestTryAdaptLemmaTypes_NoInstanceThatMissesAConstantIsTaken(t *testing.T) {
	lemma := parseCoverage(t, "∀x:A. ∀s:(A → bool). ¬(x ∈ s) ∨ ¬(s ⊆ ∅)")
	goal := parseCoverage(t, "F:((B → bool) → bool), y:B, t:(B → bool) ⊢ y ∈ t ∧ ¬(F ⊆ ∅)")
	committed := sweepCommit(lemma, goal)
	require.NotNil(t, committed)
	require.True(t, committed.AlphaEquals(TryAdaptLemmaTypes(lemma, goal)))

	// What the install misses, and the instance that reads it, are there
	// for a caller to report.
	install, offered := InstanceReadings(lemma, goal, committed)
	require.Equal(t, []core.TermName{"set_member"}, install.Reads)
	require.Equal(t, []core.TermName{"empty_set", "subset"}, install.Misses)
	require.Len(t, offered, 1)
	require.Equal(t, []core.TermName{"empty_set", "subset"}, offered[0].Reads)
	require.Equal(t, []core.TermName{"set_member"}, offered[0].Misses)
	binders, _ := ematch.StripGuardedForalls(offered[0].Instance.Conclusion())
	require.True(t, binders[1].Type().Equals(goalVarType(t, goal, "F")))
}

// Where the sweep's commit misses nothing the goal holds, it stands: a
// goal holding the law's constants at two instances keeps the first.
func TestTryAdaptLemmaTypes_ACommitMissingNothingStands(t *testing.T) {
	lemma := parseCoverage(t, "∀x:A. ∀s:(A → bool). ¬(x ∈ s) ∨ ¬(s ⊆ ∅)")
	goal := parseCoverage(t, "F:((B → bool) → bool), G:(B → bool), u:(B → bool), y:B ⊢ (y ∈ G ∧ ¬(G ⊆ ∅)) ∧ (u ∈ F ∧ ¬(F ⊆ ∅))")
	law := collectLawConstants(lemma)
	committed := sweepCommit(lemma, goal)
	require.NotNil(t, committed)
	reading, judged := law.reading(collectGoalConstants(goal, law.consts), committed)
	require.True(t, judged)
	require.Empty(t, reading.Misses)
	require.True(t, committed.AlphaEquals(TryAdaptLemmaTypes(lemma, goal)))
	install, offered := InstanceReadings(lemma, goal, committed)
	require.Empty(t, install.Misses)
	require.Empty(t, offered)
}

// A lemma whose every type letter its context spells — a hypothesis, a
// free variable — has one instance: it stands as it is, whatever the
// goal holds its constants at.
func TestTryAdaptLemmaTypes_ALetterTheContextSpellsIsNotMoved(t *testing.T) {
	fact := parseCoverage(t, "G:((A → bool) → bool), u:(A → bool) ⊢ u ∈ G ⇒ ¬(G ⊆ ∅)")
	goal := parseCoverage(t, "F:(((A → bool) → bool) → bool), H:((A → bool) → bool), y:A, t:(A → bool) ⊢ (y ∈ t ∧ H ∈ F) ∧ ¬(F ⊆ ∅)")
	require.Empty(t, collectLawConstants(fact).consts)
	committed := sweepCommit(fact, goal)
	chosen := TryAdaptLemmaTypes(fact, goal)
	require.True(t, (committed == nil && chosen == nil) || (committed != nil && chosen != nil && committed.AlphaEquals(chosen)))
}

func parseCoverage(t *testing.T, text string) core.Prop {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{FreshenMetaLetters: true})
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	return res.Prop
}
