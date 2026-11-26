package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// byFailureAt is the failure of a plain By over the resident hypotheses
// of the leaf text states, its leading antecedents assumed.
func byFailureAt(t *testing.T, text string, antecedents int) string {
	t.Helper()
	res := dsl.ParsePropTextInScope(text, lawScope())
	require.Empty(t, res.Errors, "%v", res.Errors)
	sec := NewScript(makeStepTestEnv()).Section(res.Prop)
	for range antecedents {
		sec.Do(StripImp())
	}
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	leaf := leaves[0].Goal
	return failureOf(residentByStep(makeStepTestEnv(), t.Context(), leaf), leaf)
}

// A plain By reads a guard at its numerals and does no other arithmetic
// on it: an instance whose guard names a variable, and which the context
// does not hold as written, keeps it, and the close fails at the
// refuter, which reads no arithmetic. Where the arithmetic closer
// decides that guard under the leaf — a reflexive bound, a consequence
// of a resident bound — the failure says so beside the guard, with the
// ways on: the guard stated as a Have by ByArith, or the step closed by
// ByArith. A guard arithmetic does not decide is named as before, with
// no such advice; a guard that is a comparison of numerals is no longer
// a guard the close could not discharge (TestBy_ReadsNumeralsOnTheRung).
func TestBy_AGuardArithmeticDecidesIsNamed(t *testing.T) {
	const advice = "arithmetic decides this guard"
	for _, row := range []struct{ name, text string }{
		{"a reflexive bound", "(n + 1 ≤ n + 1 ⇒ Q) ⇒ Q"},
		{"a consequence of a resident bound", "n + 1 < 3 ⇒ (n < 3 ⇒ Q) ⇒ Q"},
	} {
		antecedents := 1
		if row.name == "a consequence of a resident bound" {
			antecedents = 2
		}
		failure := byFailureAt(t, row.text, antecedents)
		require.Contains(t, failure, "still guarded", "%s: the By must fail on the guard: %s", row.name, failure)
		require.Contains(t, failure, advice, "%s: the failure does not say arithmetic decides the guard: %s", row.name, failure)
		require.Contains(t, failure, "ByArith", row.name)
	}
	// Controls: a guard that is no arithmetic, and one arithmetic does
	// not decide from this leaf.
	for _, text := range []string{"(P(n) ⇒ Q) ⇒ Q", "(n < 3 ⇒ Q) ⇒ Q"} {
		failure := byFailureAt(t, text, 1)
		require.Contains(t, failure, "still guarded", "the By must fail on the guard: %s", failure)
		require.NotContains(t, failure, advice, "%s: arithmetic does not decide this guard", text)
	}
	// A comparison of numerals is read ⊤: where a close fails for another
	// reason, its guard is not among those the context does not supply.
	require.NotContains(t, byFailureAt(t, "(0 < 2 ⇒ Q) ⇒ S", 1), "still guarded")
}

// A law cited at its witnesses whose instance's guard the context does
// not hold installs in its clause form, for the closer. Where the
// arithmetic closer decides that guard — a reflexive bound, which the
// numeral reading does not read — the premise's line of a failure says
// so as the still-guarded line does.
func TestBy_AClauseFormGuardArithmeticDecidesIsNamed(t *testing.T) {
	const advice = "arithmetic decides this guard"
	hyps := []string{"zz_gs_finite(t)"}
	goal := "zz_gs_finite(zz_gs_insert(a, t))"
	failure := func(law string) string {
		out := runGuardSupply(t, hyps, goal, residentAt(0), lawAt(law, "a", "t"))
		require.False(t, out.live, "fixture: the refuter reads no arithmetic and the By must fail")
		return out.liveFailure
	}
	reflexive := failure("∀b:num. ∀u:(num → bool). b ≤ b ∧ zz_gs_finite(u) ⇒ zz_gs_finite(zz_gs_insert(b, u))")
	require.Contains(t, reflexive, "installed in its clause form", "fixture: the law must fall to its clause form: %s", reflexive)
	require.Contains(t, reflexive, advice, "the failure does not say arithmetic decides the guard a ≤ a: %s", reflexive)
	opaque := failure("∀b:num. ∀u:(num → bool). b ∈ u ∧ zz_gs_finite(u) ⇒ zz_gs_finite(zz_gs_insert(b, u))")
	require.Contains(t, opaque, "installed in its clause form", "fixture: the law must fall to its clause form: %s", opaque)
	require.NotContains(t, opaque, advice, "arithmetic does not decide the guard a ∈ t")
}
