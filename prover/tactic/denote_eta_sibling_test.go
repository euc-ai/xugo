package tactic

// A denote of a λ rewrites each hypothesis that spells an instance of
// its body into the name applied at the instance's argument, and the
// rewrite matches up to η: `R(u, λq. g(0, q))` is read as the body at
// `g(0)`. The reconstruct carries such a hypothesis back through a βη
// bridge, and that bridge must return the image to the hypothesis it
// came from. These tests hold the case where a goal holds two
// hypotheses that are η-variants of each other: the image of the
// second is βη-equal to the first as well, and the first is a
// hypothesis of the goal, not an image — bridged away, it would leave
// the image behind, a reconstruction that is not IsStronger than the
// goal, which makeSubGoalsAt asserts.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/require"
)

// etaSiblingTerms parses, over one set of typed free names, the λ the
// rows denote and the two hypotheses they draw from:
//
//	λE. ∀u. R(u, E) ⇒ K(u)
//	fin(g(0)) ⇒ ∀u. R(u, g(0)) ⇒ K(u)                         (the η-reduced instance)
//	fin(λq. g(0, q)) ⇒ ∀u. R(u, λq. g(0, q)) ⇒ K(u)            (its η-expansion)
//
// the pair the grounding stage leaves when it grounds a wide law at a
// set and at its η-expansion, both of which the leaf spells.
func etaSiblingTerms(t *testing.T) (lam, reduced, expanded core.Term) {
	t.Helper()
	text := "∀fin:((A → bool) → bool). ∀g:(num → A → bool). ∀R:((A → bool) → (A → bool) → bool). ∀K:((A → bool) → bool). " +
		"((λE:(A → bool). ∀u:(A → bool). R(u, E) ⇒ K(u)) = (λE:(A → bool). ∀u:(A → bool). R(u, E) ⇒ K(u))) ∧ " +
		"(fin(g(0)) ⇒ ∀u:(A → bool). R(u, g(0)) ⇒ K(u)) ∧ " +
		"(fin(λq:A. g(0, q)) ⇒ ∀u:(A → bool). R(u, λq:A. g(0, q)) ⇒ K(u))"
	body := dsl.MustParseProp(text).Conclusion()
	for abs := ext.MatchesFORALL(body); !abs.IsZero(); abs = ext.MatchesFORALL(body) {
		body = abs.Body()
	}
	parts := ext.DecomposesBinaryOp(MatchesAND)(body)
	require.Len(t, parts, 3)
	lam, _, ok := MatchesEQ(parts[0])
	require.True(t, ok)
	return lam, parts[1], parts[2]
}

// The denote over a goal holding both η-variants fires, and its
// reconstruction of the child is a reconstruction of the goal. The
// goal with the η-expanded hypothesis alone is the control: its image
// has one hypothesis to return to.
func TestDenoteTerm_EtaVariantHypothesesReconstructToTheGoal(t *testing.T) {
	lam, reduced, expanded := etaSiblingTerms(t)
	for name, hyps := range map[string][]core.Term{
		"both η-variants resident":     {reduced, expanded},
		"the η-expanded one (control)": {expanded},
	} {
		t.Run(name, func(t *testing.T) {
			goal := prop.MakeProp(F, hyps...)
			var sg *SubGoals
			require.NotPanics(t, func() { sg = DenoteTermTactic(lam, "α")(goal) },
				"the denote's reconstruction must be IsStronger than the goal")
			require.NotNil(t, sg)
			require.True(t, prop.IsStronger(sg.Reconstruct(sg.ChildGoal(0)), goal))
		})
	}
}

// LetTermTactic carries its hypotheses back through the same bridge.
func TestLetTerm_EtaVariantHypothesesReconstructToTheGoal(t *testing.T) {
	lam, reduced, expanded := etaSiblingTerms(t)
	for name, hyps := range map[string][]core.Term{
		"both η-variants resident":     {reduced, expanded},
		"the η-expanded one (control)": {expanded},
	} {
		t.Run(name, func(t *testing.T) {
			goal := prop.MakeProp(F, hyps...)
			var sg *SubGoals
			require.NotPanics(t, func() { sg = LetTermTactic(lam, "α")(goal) },
				"the definition's reconstruction must be IsStronger than the goal")
			require.NotNil(t, sg)
			require.True(t, prop.IsStronger(sg.Reconstruct(sg.ChildGoal(0)), goal))
		})
	}
}
