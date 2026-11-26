package engine

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestEmitSection_PartialByPremiseAtFunctionInstance(t *testing.T) {
	e, s := boundSession(t, "algebra/group/comm_monoid")
	addStatement(t, s, "∀op:((num → real) → (num → real) → num → real). ∀e:(num → real). comm_monoid(op, e) ⇒ ∀x y:(num → real). ∀n:num. monoid_pow(op, e, op(x, y), n) = op(monoid_pow(op, e, x, n), monoid_pow(op, e, y, n))")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	zero := 0
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}}, WithLemmas: []LemmaWithSpec{{
		Key: "comm_monoid.MulPow", TermSpecialize: map[string]string{"op": "op₀", "e": "e₀"},
	}}})
	require.True(t, s.sections[0].root.Proved())
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, Family: "algebra/group/comm_monoid", FuncName: "Build_FunctionMulPow"})
	require.NoError(t, err)
	require.NotContains(t, out.Go, "TODO: unresolved lemma")
	require.Contains(t, out.DepNames, "comm_monoid.MulPow")
	replayEmittedInFamily(t, "algebra/group/comm_monoid", "FunctionMulPow", out)
}
