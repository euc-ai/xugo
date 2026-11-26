package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// A handle names its hypothesis as it stands at the leaf, and a rewrite
// of it in one branch is that branch's alone.

// Conjuncts splits the hypothesis as the Let respelled it, not the text
// the handle was bound to: the parts spell the Let's name, and the
// ambient equation the parts' closes clear is never needed.
func TestConjuncts_ReadsTheHypothesisAsItStandsAfterALet(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀f:num → num. ∀a:num. ∀P Q R:num → bool. P(f(a)) ∧ Q(f(a)) ⇒ (∀z. P(z) ⇒ R(z)) ⇒ R(f(a))",
			func(a *Argument, f *ext.Expr[natFun], x *ext.Expr[ext.Nat], P, Q, R *ext.Expr[natSet], all Fact) {
				a.Let("w", a.Term("f(a)").Core())
				parts := a.Conjuncts(all, "P at w", "Q at w", "P gives R")
				for i, want := range []string{"P₀(w)", "Q₀(w)"} {
					got, _ := parts[i].BoundContent()
					require.Equal(t, want, ext.PrintTerm(got), "conjunct %d", i+1)
				}
				a.Show("R at w", By(parts[0], parts[2]))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Simplified on one captured fact in each of two sibling branches: the
// first branch's rewrite is bound at its own residual leaf, and the
// second branch still resolves the fact from the bind above the split.
func TestHypHandle_SimplifiedInSiblingBranches(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀f g:num → num. ∀P:num → bool. ∀u:num. P(f(u)) ⇒ (∀y. f(y) = g(y)) ⇒ P(g(u))",
			func(a *Argument, f, g *ext.Expr[natFun], P *ext.Expr[natSet], u *ext.Expr[ext.Nat], holds, same Fact) {
				a.Cases(a.Term("f(u) = g(u)"))
				a.When("f and g agree at u", func(a *Argument, _ Fact) {
					at := a.Simplified(holds, Fwd(same))
					a.Show("the simplified fact", By(at))
				})
				a.Otherwise("they differ at u", func(a *Argument, _ Fact) {
					at := a.Simplified(holds, Fwd(same))
					a.Show("the simplified fact", By(at))
				})
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// An Unfold's tidy splits a resident conjunction into its conjuncts;
// a handle on the conjunction used after it is refused naming the
// handle, the Unfold, and the conjuncts now resident on their own.
func TestHypHandle_UnfoldSplitsTheConjunctionItNames(t *testing.T) {
	ctx := wrappedTestScript()
	requirePanicContains(t, "HypHandle \"assumption\".By: its hypothesis was consumed by step \"DefExpand: zz_wrapped\" and has no single successor past it — "+
		"the step split it into its conjuncts, P₀(x₀) and Q₀(x₀) and R₀(y₀), each resident on its own "+
		"(cite them as ResidentHyp, or take them before the step with a.Conjuncts), so the handle cannot be used past that step",
		func() {
			ctx.Theorem("∀P Q R:num → bool. ∀x y:num. P(x) ∧ Q(x) ⇒ R(y) ⇒ "+wrappedTestConst+"(R, x)",
				func(a *Argument, P, Q, R *ext.Expr[natSet], x, y *ext.Expr[ext.Nat], all Fact) {
					a.Do(Unfold(wrappedTestDefinition))
					a.Show("by the conjunction", By(all))
				})
		})
}
