package engine

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestEmitSection_TwoBranchFacts keeps both outer facts after a later
// Have rewrites them in its claim branches: the branches bind copies
// of both facts, and the final close reads the outer handles.
func TestEmitSection_TwoBranchFacts(t *testing.T) {
	e, s := boundSession(t, "algebra/module/function_module")
	addTextGoal(t, s, "∀zero:A. ∀c:set(A). ∀S:set(D). ∀f g:(D → A). f ∈ finite_supp(zero, c, S) ∧ g ∈ finite_supp(zero, c, S) ∧ zero ∈ c ⇒ finite(fun_support(zero, f)) ∧ finite(fun_support(zero, g)) ∧ f ∈ finite_supp(zero, c, S) ∧ g ∈ finite_supp(zero, c, S)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	member := "f₀ ∈ finite_supp(zero₀, c₀, S₀)"
	other := "g₀ ∈ finite_supp(zero₀, c₀, S₀)"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: member})
	applyTo(t, e, s, concluding(member), TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, concluding(member), "((f₀")}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: other})
	applyTo(t, e, s, concluding(other), TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, concluding(other), "((f₀")}}})
	claimText := "finite(fun_support(zero₀, f₀)) ∧ finite(fun_support(zero₀, g₀))"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: claimText})
	applyTo(t, e, s, concluding("finite(fun_support(zero₀, f₀)) ∧ finite(fun_support(zero₀, g₀))"), TacticReq{Type: "split_conj"})
	for _, v := range []string{"f₀", "g₀"} {
		claim := concluding("finite(fun_support(zero₀, " + v + "))")
		at := v + " ∈ finite_supp(zero₀, c₀, S₀)"
		applyTo(t, e, s, claim, TacticReq{Type: "simp_with", HypIndex: hypAt(t, e, s, claim, at),
			WithLemmas: []LemmaWithSpec{{Key: "function_module.FiniteSuppDef"}, {Key: "function_module.FiniteSupportDef"}}})
		rewritten := func(g core.Prop) bool {
			return claim(g) && g.AnyHyp(func(h core.Term) bool { return strings.Contains(ext.PrintTerm(h), "finite(fun_support(") })
		}
		applyTo(t, e, s, rewritten, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, rewritten, v+" ∈ {f")}}})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{
		{HypIndex: hypAt(t, e, s, sole, member)}, {HypIndex: hypAt(t, e, s, sole, other)},
		{HypIndex: hypAt(t, e, s, sole, "finite(fun_support(zero₀, f₀")}}})
	src := emitInto(t, e, s, "zztwobranchfacts", "ZzTwoBranchFacts")
	assert.Equal(t, 2, strings.Count(src, ".Hyp("), "the claim's branch binds both facts:\n%s", src)
	replayEmitted(t, "zztwobranchfacts", "ZzTwoBranchFacts", src)
}

// TestEmitSection_VecZeroAtNestedType grounds the definition at a
// set-valued zero. Normalizing its type instance adds extensional
// binders, so no entry states the install; the premise's recorded entry
// names the definition, grounded at zero before the index.
func TestEmitSection_VecZeroAtNestedType(t *testing.T) {
	e, s := boundSession(t, "vector/vec_space")
	addTextGoal(t, s, "∀zero:set(A). ∀p:(num → set(A)). (∀i:num. p(i) = zero) ⇒ p = vec_zero(zero)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{{Key: "vec_space.VecZeroDef", TermSpecialize: map[string]string{"zero": "zero₀"}}}})
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, Family: "vector/vec_space", FuncName: "Build_ZzNestedVecZero"})
	require.NoError(t, err)
	require.NotContains(t, out.Go, "TODO: unresolved lemma")
	require.Contains(t, out.Go, "At(VecZeroDef.Inst[Set[A]](), zero)", "the definition is read at the nested type, grounded at zero")
	replayEmittedInFamily(t, "vector/vec_space", "ZzNestedVecZero", out)
}
