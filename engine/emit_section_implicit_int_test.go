package engine

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
)

// The same integer term appears in the headline and as a grounded
// premise's witness. Its shortened forms must compile and replay as
// emitted, including the distinct natural and integer subtractions.
func TestEmitSection_ImplicitIntegerTerms(t *testing.T) {
	for i, tc := range []struct{ binders, term, witness string }{
		{"", "int_of_num(2)", "2"},
		{"∀a:num. ", "int_of_num(a)", "a"},
		{"∀a b:num. ", "int_of_num(a - b)", "a - b"},
		{"∀a b:num. ", "int_of_num(a * b)", "a * b"},
		{"∀a b:num. ", "int_of_num(a) - int_of_num(b)", "&a - b"},
		{"∀a b:num. ", "int_of_num(a) * int_of_num(b)", "&a * b"},
	} {
		t.Run(tc.term, func(t *testing.T) {
			e, s := boundSession(t, "int_num/int_embed")
			addDoorGoal(t, s, tc.binders+"∀P:(int → bool). (∀z:int. P(z)) ⇒ P("+tc.term+")")
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
			premise := hyp(0)
			premise.Terms = []string{tc.term}
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{premise}})
			pkg := fmt.Sprintf("implicitint%d", i)
			src := emitInto(t, e, s, pkg, "ImplicitInteger")
			assert.Contains(t, src, `.TermAs[Int]("`+tc.witness+`")`, "%s", src)
			assert.NotContains(t, src, "int_of_num(", "%s", src)
			replayEmitted(t, pkg, "ImplicitInteger", src)
		})
	}
}

func TestEmitSection_ImplicitIntegerClaim(t *testing.T) {
	e, s := boundSession(t, "int_num/int_embed")
	addDoorGoal(t, s, "∀n:num. ∀P:(int → bool). ∀Q:bool. (∀z:int. P(z)) ⇒ (P(int_of_num(n)) ⇒ Q) ⇒ Q")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "P(int_of_num(n))"})
	premise := hyp(0)
	premise.Terms = []string{"int_of_num(n)"}
	applyOnGoalProving(t, e, s, "P₀(int_of_num(n₀))", TacticReq{Type: "by", ByHyps: []ByHypSpec{premise}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(2)}})
	const pkg = "implicitintclaim"
	src := emitInto(t, e, s, pkg, "ImplicitIntegerClaim")
	assert.Contains(t, src, `ctx.MakePropText("P₀(n₀)")`, "%s", src)
	assert.Contains(t, src, `.TermAs[Int]("n")`, "%s", src)
	replayEmitted(t, pkg, "ImplicitIntegerClaim", src)
}
