package engine

import (
	"testing"

	"github.com/stretchr/testify/require"
)

// A denote lambda binds names also fixed by the section boundary. Its
// emitted term must keep those binders local to the lambda and compile
// and replay without undeclared or unused Go variables.
func TestEmitSection_DenotedLambdaShadowsSectionBinders(t *testing.T) {
	e, s := boundSession(t, "nat_num/nat_order")
	addDoorGoal(t, s, "∀a b:num. ∀P:((num → num → num) → bool). P(λa:num. λb:num. a + b) ⇒ P(λa:num. λb:num. b + a) ∧ a + b = b + a")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{
		Type:       "by",
		ByHyps:     []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddSym"}},
		ByShape:    &ByShapeReq{DenotedAs: &ByDenoteAsReq{Name: "sum", Term: "λa:num. λb:num. a + b"}},
	})
	out := emitSoleResult(t, e, s, "Build_ZzDenotedLambda")
	require.Contains(t, out.Go, `DenotedAs("sum", arg.TermAs[Op[Nat]]("λa:num. λb:num. a + b"))`, "--- source: ---\n%s", out.Go)
	replayEmittedInFamily(t, "nat_num/nat_order", "ZzDenotedLambda", out)
}
