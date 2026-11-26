package refuter

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
)

// etaShortDenoteGoal is the shape of a set_tac residual after the
// normalizer's η: two α-equivalent comprehensions `{v | s v ∧ f v = y}`,
// one from the goal and one from a premise, denote apart (α₀, α₁) and
// occur BARE in argument position — S(G(α₀), g), not S(G(λv.α₀ v), g).
// Under the hypotheses the fibre is empty, so the refuter derives
// ∀v.¬α₀(v) and ∀v.¬α₁(v); closing then needs those unit clauses to
// reach the bare symbols (α₀ ↦ λv.⊥, α₁ ↦ λv.⊥), after which the two
// sides coincide up to α.
func etaShortDenoteGoal(sameBinder bool) Prop {
	x := Var("x", TypeA)
	v := Var("v", TypeA)
	w := Var("w", TypeA)
	if sameBinder {
		w = v
	}
	y := Var("y", TypeB)
	z := Var("z", TypeInd)
	p := Var("p", MakeFun(TypeA, TypeBool))
	s := Var("s", MakeFun(TypeA, TypeBool))
	t := Var("t", MakeFun(TypeB, TypeBool))
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeInd))
	G := Var("G", core.MakeFun(core.MakeFun(TypeA, TypeBool), core.MakeFun(TypeA, TypeBool)))
	S := Var("S", core.MakeFun(core.MakeFun(TypeA, TypeBool), core.MakeFun(TypeA, TypeInd), TypeInd))
	fibreV := G.Apply(v.To(s.Apply(v).And(f.Apply(v).Eq(y))))
	fibreW := G.Apply(w.To(s.Apply(w).And(f.Apply(w).Eq(y))))
	hyps := []Term{
		t.Apply(y),
		Not(Exists(x)(s.Apply(x).And(y.Eq(f.Apply(x))))),
		ForAll(p, v)(G.Apply(p).Apply(v).Eq(p.Apply(v))),
		Exists(x)(z.Eq(S.Apply(fibreV, g)).Or(
			Not(g.Apply(x).Eq(z)).And(s.Apply(x).And(f.Apply(x).Eq(y))))),
	}
	return TestProp(S.Apply(fibreW, g).Eq(z), hyps...)
}

// The η-short denote shape refutes, and quickly: a unit clause
// ∀v.¬α(v) rewrites the bare symbol α (EqRewrite matches the pattern
// λv.α(v) at its η-contraction) and Simplifies accepts the
// symbol-to-constant substitution although it grows the term.
func TestRefuteEtaShortDenoteSymbols(t *testing.T) {
	for _, same := range []bool{false, true} {
		var cache utils.Map[core.TermKey, Prop]
		ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
		p := CreateRefuter(t.Context(), etaShortDenoteGoal(same), &cache)
		p.Prove(ctx)
		cancel()
		assert.True(t, p.Refuted(), "sameBinder=%v", same)
	}
}
