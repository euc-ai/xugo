package engine

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A law's proof can specialize a premise at a member abbreviation
// even when the printed headline does not spell that abbreviation.
func TestEmitSection_ALawDeclaresItsProofAbbreviations(t *testing.T) {
	e, s := boundSession(t, "algebra/module/free_module")
	const text = "∀R:comm_ring_on(A). ∀J:set(B). ∀P:(module_ops(A, B → A) → bool). (∀T:module_ops(A, B → A). P(T)) ⇒ P(«proofModule»)"
	table, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "proofModule", Text: "free_module_record(R, J)"}})
	require.NoError(t, err)
	scope := s.StatementDoorScope()
	scope.Abbreviations = table
	scope.AbbreviationBinders = map[string]bool{}
	for _, name := range dsl.LeadingBinderNames(text) {
		scope.AbbreviationBinders[name] = true
	}
	parsed := dsl.ParsePropTextAtDoor(text, scope)
	require.Empty(t, parsed.Errors)
	_, err = s.AddGoalWith(parsed.Prop, table)
	require.NoError(t, err)
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{
		Type:   "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, sole, "∀"), Terms: []string{"«proofModule»"}}},
	})
	out := emitSoleResult(t, e, s, "Build_ZzLawOwnAbbreviation")
	assert.Contains(t, out.Go, ".Law(Statement{")
	assert.Contains(t, out.Go, `Abbrev: Abbrev{`)
	assert.Contains(t, out.Go, `{Name: "proofModule", Text: "free_module_record(R, J)"}`)
	assert.NotContains(t, out.Go, "family.Theorem(")
	replayEmittedInFamily(t, "algebra/module/free_module", "ZzLawOwnAbbreviation", out)
}
