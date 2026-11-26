package engine

// How emit-section writes a Have whose claim has a premise: in parts,
// the Statement literal the claim verbs read (prover/proof/derive.go,
// claimParts), where the one string would not fit on the claim's line
// (xugofmt.LineWidth), and as the one string where it fits; a claim
// without a premise stays the one string.

import (
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

// emitHaveWithAPremise is the member a staircase of two asserts under
// the premises renders as, the statement's binders named p and f: the
// first `p ⇒ f(0) + 0 = 0`, the second `f(0) = 0`.
func emitHaveWithAPremise(t *testing.T, p, f, funcName string) string {
	t.Helper()
	e, s := boundSession(t, "nat_num/nat_arith")
	addTextGoal(t, s, fmt.Sprintf("∀%s:bool. ∀%s:(num → num). (%s ⇒ %s(0) = 0) ∧ %s ⇒ %s(0) + 0 = 0", p, f, p, f, p, f))
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: fmt.Sprintf("%s₀ ⇒ %s₀(0) + 0 = 0", p, f)})
	isClaim := func(g core.Prop) bool { _, _, imp := ext.MatchesIMPLY(g.Conclusion()); return imp }
	applyTo(t, e, s, isClaim, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddZero"}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: fmt.Sprintf("%s₀(0) = 0", f)})
	applyTo(t, e, s, func(g core.Prop) bool { return !strings.Contains(ext.PrintTerm(g.Conclusion()), "+") },
		TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(1)}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddZero"}}})
	src := emitSole(t, e, s, funcName)
	writeProbeMember(t, "nat_num/nat_arith", funcName, src)
	return src
}

// TestEmitSection_HaveWithAPremisePastTheLineIsWrittenInParts: under
// names long enough that the first claim's one string runs past the
// line, it renders as `a.Have(label, Statement{Hypotheses: …,
// Conclusion: …}, …)`, the hypothesis and the conclusion each a literal
// of its own, and the second as the one string; the one string of the
// first appears at no claim position.
func TestEmitSection_HaveWithAPremisePastTheLineIsWrittenInParts(t *testing.T) {
	const p, f = "thePremiseUnderWhichTheFunctionVanishesAtZero", "functionWhoseValueAtZeroVanishesIdentically"
	src := emitHaveWithAPremise(t, p, f, "Build_ZzHaveWithALongPremise")
	for _, want := range []string{
		"\t\t\ta.Have(\n\t\t\t\t\"" + p + " ⇒ \"+\n\t\t\t\t\t\"" + f + "(0) + 0 = 0\",\n\t\t\t\tStatement{\n",
		"\t\t\t\t\tHypotheses: []string{\n\t\t\t\t\t\t\"" + p + "\",\n\t\t\t\t\t},\n",
		"\t\t\t\t\tConclusion: \"" + f + "(0) + 0 = 0\",\n\t\t\t\t},\n\t\t\t\tBy(h, AddZero),\n\t\t\t)\n",
		":= a.Have(\n\t\t\t\t\"" + f + "(0) = 0\",\n\t\t\t\t\"" + f + "(0) = 0\",\n",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	assert.Equal(t, 0, strings.Count(src, `"`+p+` ⇒ `+f+`(0) + 0 = 0",`), "the one string of a claim past the line is written nowhere: its label is laid out over two lines and its claim is in parts\n--- source: ---\n%s", src)
	assert.Equal(t, 2, strings.Count(src, "Statement{"), "the headline and the first claim are in parts, the second claim is not\n--- source: ---\n%s", src)
}

// TestEmitSection_HaveWithAPremiseThatFitsIsTheOneString: under short
// names the first claim's one string fits on its line, and it renders
// as the one string, its label beside it; only the headline is in
// parts.
func TestEmitSection_HaveWithAPremiseThatFitsIsTheOneString(t *testing.T) {
	src := emitHaveWithAPremise(t, "P", "f", "Build_ZzHaveWithAPremise")
	assert.Contains(t, src, "\t\t\ta.Have(\n\t\t\t\t\"P ⇒ f(0) + 0 = 0\",\n\t\t\t\t\"P ⇒ f(0) + 0 = 0\",\n\t\t\t\tBy(h, AddZero)",
		"--- source: ---\n%s", src)
	assert.Equal(t, 1, strings.Count(src, "Statement{"), "the headline alone is in parts\n--- source: ---\n%s", src)
}
