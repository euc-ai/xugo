package engine

import (
	"context"
	"regexp"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

// bareLawInstanceOutcome states stmt in a session bound to the
// cardinality family, strips it to its one implication, applies the
// setup steps given, and returns what `by` over the first hypothesis and
// cardinality.CardClauses — at the type instance given, or bare — did.
func bareLawInstanceOutcome(t *testing.T, stmt string, setup []TacticReq, inst map[string]string) *StepResult {
	t.Helper()
	e, s := boundSession(t, "sets/cardinality")
	addTextGoal(t, s, stmt)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	for _, step := range setup {
		applyOnSoleGoal(t, e, s.ID, step)
	}
	res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: soleGoal(t, e, s.ID).ID, Tactic: TacticReq{
		Type:       "by",
		ByHyps:     []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{{Key: "cardinality.CardClauses", TypeSpecialize: inst}},
	}})
	require.NoError(t, err)
	return res
}

// nonemptyOfCount states, over the type letter given, that a family
// {S | pred} of sets with a nonzero count is not empty: its card and its
// ∅ stand at sets of sets of that letter.
func nonemptyOfCount(letter, pred string) string {
	const stmt = "∀C:set(set(L)). ∀f:(L → L). ∀x:L. ¬(card({S:set(L) | P}) = 0) ⇒ ¬({S:set(L) | P} = ∅)"
	return strings.NewReplacer("L", letter, "P", pred).Replace(stmt)
}

// TestBy_BareLawReadsItsInstanceOffTheLeaf: a polymorphic law cited bare
// is installed at the instance the leaf holds all of its constants at —
// cardinality.CardClauses where card and ∅ stand, at sets of sets —
// whatever the leaf spells beside them: a membership at the element
// type, which the law's insert clause spells too, before or after the
// membership at sets, or none; and whether the statement's letter is
// the law's own or another.
func TestBy_BareLawReadsItsInstanceOffTheLeaf(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	for _, letter := range []string{"A", "B"} {
		for _, pred := range []string{
			"S ∈ C ∧ f(x) ∈ S",
			"f(x) ∈ S ∧ S ∈ C",
			"S ∈ C",
			"S ∈ C ∧ image(f, S) = S",
		} {
			t.Run(letter+": "+pred, func(t *testing.T) {
				res := bareLawInstanceOutcome(t, nonemptyOfCount(letter, pred), nil, nil)
				require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
			})
		}
	}
	// The same leaf closes at the instance pinned, and with the family
	// named by a Let: the law's instance is what the bare cite lacked.
	t.Run("pinned", func(t *testing.T) {
		res := bareLawInstanceOutcome(t, nonemptyOfCount("A", "S ∈ C ∧ f(x) ∈ S"), nil, map[string]string{"A": "set(A)"})
		require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	})
	t.Run("named by a Let", func(t *testing.T) {
		res := bareLawInstanceOutcome(t, nonemptyOfCount("A", "S ∈ C ∧ f(x) ∈ S"),
			[]TacticReq{{Type: "let", Name: "F", Const: "{S:set(A) | S ∈ C₀ ∧ f₀(x₀) ∈ S}"}}, nil)
		require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	})
}

// TestBy_FailureNamesTheInstanceABareLawIsInstalledAt: where the law's
// constants disagree about the instance — the leaf holds a membership at
// the element type alone, card and ∅ at sets of sets alone — no instance
// reads them all and the install is the sweep's. The failed By names the
// premise, the instance installed, the constants the leaf holds
// elsewhere and the instance the leaf offers that reads them; that
// instance, pinned as the failure spells it, closes the leaf.
func TestBy_FailureNamesTheInstanceABareLawIsInstalledAt(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	offered := regexp.MustCompile(`(?m)^\s+A := (.+?): reads card, empty_set`)
	for _, letter := range []string{"A", "B"} {
		t.Run(letter, func(t *testing.T) {
			stmt := nonemptyOfCount(letter, "f(x) ∈ S")
			res := bareLawInstanceOutcome(t, stmt, nil, nil)
			require.False(t, res.Success)
			require.NotEmpty(t, res.Diagnostics)
			msg := res.Diagnostics[0].Message
			require.Contains(t, msg, "premise cardinality.CardClauses is a polymorphic law installed at ONE type instance", "%s", msg)
			require.Contains(t, msg, "the leaf holds its card, empty_set at no type that instance gives them", "%s", msg)
			found := offered.FindStringSubmatch(msg)
			require.NotNil(t, found, "the failure names no instance reading card and ∅:\n%s", msg)
			pinned := bareLawInstanceOutcome(t, stmt, nil, map[string]string{"A": found[1]})
			require.True(t, pinned.Success, "pinned at %s; diagnostics: %v", found[1], pinned.Diagnostics)
		})
	}
	// A By that fails with its law installed where the leaf holds every
	// constant of it carries no such note.
	t.Run("an install that misses nothing", func(t *testing.T) {
		e, s := boundSession(t, "sets/cardinality")
		addTextGoal(t, s, "∀s:set(A). ∀x:A. finite(s) ⇒ card(insert(x, s)) = card(s)")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: soleGoal(t, e, s.ID).ID, Tactic: TacticReq{
			Type:       "by",
			ByHyps:     []ByHypSpec{hyp(0)},
			WithLemmas: []LemmaWithSpec{{Key: "cardinality.CardClauses"}},
		}})
		require.NoError(t, err)
		require.False(t, res.Success)
		require.NotContains(t, res.Diagnostics[0].Message, "installed at ONE type instance")
	})
}
