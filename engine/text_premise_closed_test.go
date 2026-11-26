package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// A text read at a focus whose strip-minted variables are live
// (`T₀ X₀ res₀`, spelled `T X res` by their surface names) is read closed
// where it is closed — a bundle-headed `∀X:presheaf(A, B). …` binds X's
// components itself, so its `T` is the bundle's, never the focus's —
// and a short bundle spelling of a resident instance, `comm_monoid_on(M₀)`,
// is that instance's components, with a second instance resident beside
// it as with one.

// addStatement reads a statement at the session's statement door — the
// bound family's bundles and vocabulary — and adds it as a goal.
func addStatement(t *testing.T, s *Session, text string) {
	t.Helper()
	parsed := dsl.ParsePropTextInScope(text, s.StatementDoorScope())
	require.Empty(t, parsed.Errors, "add-goal %q", text)
	s.mu.Lock()
	s.AddGoal(parsed.Prop)
	s.mu.Unlock()
}

// soleGoal is the session's one open goal.
func soleGoal(t *testing.T, e *Engine, sid string) GoalView {
	t.Helper()
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1, "one open goal; open: %v", goalIDs(state))
	return state.Goals[0]
}

// everyHyp names every resident hypothesis of the goal as a `by` premise.
func everyHyp(g GoalView) []ByHypSpec {
	out := make([]ByHypSpec, len(g.Hypotheses))
	for i := range out {
		out[i] = hyp(i)
	}
	return out
}

// stripToLeaf opens a bundle-headed statement down to its leaf: the
// components and the bundle, the structure fact, the set, the
// antecedent — stopping where a strip's own simplification closed the
// section.
func stripToLeaf(t *testing.T, e *Engine, sid string) {
	t.Helper()
	for _, typ := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		state, err := e.InspectState(context.Background(), sid)
		require.NoError(t, err)
		if len(state.Goals) == 0 {
			return
		}
		res := applyOnSoleGoal(t, e, sid, TacticReq{Type: typ})
		require.True(t, res.Success, "%s: %v", typ, res.Diagnostics)
	}
}

// TestBy_ClosedTextPremiseReadsItsOwnBundleAtALiveFocus is the #1429
// shape: a proved sibling section, stated over a presheaf bundle, is
// passed as a text premise at a leaf where the presheaf's strip-minted
// components are live under their surface names. The text binds every
// name it uses, so it reads as the sibling's statement and certifies.
func TestBy_ClosedTextPremiseReadsItsOwnBundleAtALiveFocus(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "topology/presheaf")
	sibling := "∀X:presheaf(A, B). ∀S:set(set(A)). ∀U:set(A). S ⊆ T ∧ U ∈ S ⇒ U ∈ T"
	addStatement(t, s, sibling)
	stripToLeaf(t, e, s.ID)
	if !s.sections[0].root.Proved() {
		res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: everyHyp(soleGoal(t, e, s.ID))})
		require.True(t, res.Success, "the sibling closes: %v", res.Diagnostics)
	}
	require.True(t, s.sections[0].root.Proved())

	addStatement(t, s, "∀X:presheaf(A, B). ∀S R:set(set(A)). ∀U:set(A). S ⊆ T ∧ U ∈ S ∧ U ∈ R ⇒ U ∈ T ∩ R")
	stripToLeaf(t, e, s.ID)
	leaf := soleGoal(t, e, s.ID)
	t.Logf("leaf:\n%s", describeGoal(leaf))
	require.Contains(t, surfaceNamesView(leaf.Statement), "T", "the focus spells T₀ as T")

	parsed, err := parsePropTextInGoalScope(sibling, leaf.Statement, s.familyScope())
	require.NoError(t, err)
	require.True(t, parsed.AlphaEquals(s.sections[0].root.Goal),
		"the text reads as the sibling's statement\n  read:    %s\n  sibling: %s", ext.PrintTerm(parsed.Conclusion()), ext.PrintTerm(s.sections[0].root.Goal.Conclusion()))
	preview, err := e.ParsePropInGoalScope(s.ID, leaf.ID, sibling)
	require.NoError(t, err)
	require.Empty(t, preview.Errors)
	require.True(t, preview.Prop.AlphaEquals(parsed), "the parse-prop preview reads the text as the door does")

	res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: everyHyp(leaf),
		WithLemmas: []LemmaWithSpec{{Text: sibling}}})
	require.True(t, res.Success, "the text premise certifies on the sibling: %v", res.Diagnostics)
	require.Equal(t, "close", res.Effect)
}

// TestAssert_ShortBundleSpellingReadsTheResidentInstance is the #1425
// shape: with one comm_monoid_on resident, `comm_monoid_on(M₀)` is the
// resident instance's components, the carrier M₀ and the operation and
// identity minted under it, and an assert spelling it certifies.
func TestAssert_ShortBundleSpellingReadsTheResidentInstance(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "algebra/group/comm_monoid")
	addStatement(t, s, "∀M:comm_monoid_on(A). ∀N:set(A). N ⊆ M ⇒ M ⊆ N")
	stripToLeaf(t, e, s.ID)
	leaf := soleGoal(t, e, s.ID)
	t.Logf("leaf:\n%s", describeGoal(leaf))
	resident := -1
	for i, h := range leaf.Hypotheses {
		if strings.HasPrefix(ext.PrintTerm(h), "comm_monoid_on(") {
			resident = i
		}
	}
	require.NotEqual(t, -1, resident)

	parsed, err := parseClaimTextInGoalScope("comm_monoid_on(M₀)", leaf.Statement, s.familyScope())
	require.NoError(t, err)
	require.True(t, parsed.Conclusion().AlphaEquals(leaf.Hypotheses[resident]),
		"the short spelling is the resident fact\n  read:     %s\n  resident: %s", ext.PrintTerm(parsed.Conclusion()), ext.PrintTerm(leaf.Hypotheses[resident]))

	res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "comm_monoid_on(M₀) ∧ N₀ ⊆ M₀"})
	require.True(t, res.Success, "assert: %v", res.Diagnostics)
}

// TestAssert_ShortBundleSpellingReadsEachInstance: with two monoids
// resident, each short spelling lays out its own bundle — the first's
// components minted bare, the second's under its name.
func TestAssert_ShortBundleSpellingReadsEachInstance(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "algebra/group/comm_monoid")
	addStatement(t, s, "∀M:comm_monoid_on(A). ∀K:comm_monoid_on(A). ∀N:set(A). N ⊆ M ∧ N ⊆ K ⇒ M ⊆ N")
	for _, typ := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: typ})
		require.True(t, res.Success, "%s: %v", typ, res.Diagnostics)
	}
	leaf := soleGoal(t, e, s.ID)
	t.Logf("leaf:\n%s", describeGoal(leaf))

	first, err := parseClaimTextInGoalScope("comm_monoid_on(M₀)", leaf.Statement, s.familyScope())
	require.NoError(t, err, "the first monoid's short spelling is its own components")
	require.Contains(t, ext.PrintTerm(first.Conclusion()), "comm_monoid_on(M₀, op₀, e₀)")

	second, err := parseClaimTextInGoalScope("comm_monoid_on(K₀)", leaf.Statement, s.familyScope())
	require.NoError(t, err, "the second monoid's short spelling is its own components")
	require.Contains(t, ext.PrintTerm(second.Conclusion()), "comm_monoid_on(K₀, K_op₀, K_e₀)")
}
