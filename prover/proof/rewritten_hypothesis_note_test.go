package proof

import (
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// A refusal that says the context does not hold a fact names the step
// that rewrote the hypothesis which held it, where there is one: an
// earlier Simp at the hypothesis, an Unfold whose tidy reached it
// (#1455, DualityMapKillsLattice and InvertibleFinite).

// Simp at a hypothesis rewrote `u ∈ s` to `u ∈ t` in place; the guard of
// a fact in hand grounded afterwards is refused, and the refusal names
// the step and what the hypothesis became.
func TestRewrittenHypothesis_FactInHandGuardNamesTheSimp(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	requirePanicContains(t, "u₀ ∈ s₀ stood in the context until step", func() {
		ctx.Theorem("∀s t:(num → bool). ∀f g:num → num. ∀P:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ g(x) = f(x)) ⇒ u ∈ s ⇒ (∀y. y ∈ s ⇔ y ∈ t) ⇒ P(f(u)) ⇒ P(g(u))",
			func(a *Argument, s, tt *ext.Expr[natSet], f, g *ext.Expr[natFun], P *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, uIn, same, holds Fact) {
				a.Do(uIn.Simp(Fwd(same)))
				a.Do(agree.At(u).Rw())
			})
	})
}

// The same, as a By premise: the premise's clause-form note names the
// step that rewrote the hypothesis holding its guard.
func TestRewrittenHypothesis_ByPremiseGuardNamesTheSimp(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	requirePanicContains(t, "u₀ ∈ s₀ stood in the context until step", func() {
		ctx.Theorem("∀s t:(num → bool). ∀f g:num → num. ∀P:num → bool. ∀u:num. "+
			"(∀x. x ∈ s ⇒ g(x) = f(x)) ⇒ u ∈ s ⇒ (∀y. y ∈ s ⇔ y ∈ t) ⇒ P(f(u)) ⇒ P(g(u))",
			func(a *Argument, s, tt *ext.Expr[natSet], f, g *ext.Expr[natFun], P *ext.Expr[natSet], u *ext.Expr[ext.Nat],
				agree, uIn, same, holds Fact) {
				a.Do(uIn.Simp(Fwd(same)))
				a.Have("the equation at u", "g(u) = f(u)", By(agree.At(u)))
			})
	})
}

// A rewrite that finds nothing left to rewrite names the side that
// occurs nowhere and the step past which it stopped occurring: here the
// handle's own earlier Rw substituted `f(a)` everywhere, and the second
// Rw has nothing to do.
func TestRewrittenHypothesis_HandleRwNamesTheStepThatSubstituted(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	requirePanicContains(t, "its left side f₀(a₀) occurs nowhere else in the goal, so there is nothing to rewrite\n"+
		"  f₀(a₀) last stood in the goal before step \"Rw on hyp 1\", which rewrote it away", func() {
		ctx.Theorem("∀f:num → num. ∀a b:num. ∀P Q:num → bool. f(a) = b ⇒ Q(b) ⇒ P(f(a))",
			func(a *Argument, f *ext.Expr[natFun], x, b *ext.Expr[ext.Nat], P, Q *ext.Expr[natSet], eq, holds Fact) {
				a.Do(eq.Rw())
				a.Do(eq.Rw())
			})
	})
}

// wrappedTestConst is a definitional constant `zz_wrapped(P, x) = P(x)`,
// for an Unfold beside a resident equation.
const wrappedTestConst = "zz_wrapped"

var wrappedTestDef = sync.OnceValue(func() core.ConstTerm {
	numType := ext.NumType
	P := Var("P", core.MakeFun(numType, core.TypeBool()))
	x := Var("x", numType)
	return core.NewConstDef(P.To(x.To(P.Apply(x))).Core(), wrappedTestConst)
})

// wrappedTestDefinition is the fixture constant as Unfold takes it.
var wrappedTestDefinition = mintedDefinition(wrappedTestDef)

func wrappedTestScript() *Script {
	env := makeStepTestEnv()
	c := wrappedTestDef()
	env.ProofService.LoadOrStoreConstMeta(c.Meta())
	ctx := NewScript(env)
	ctx.Const(wrappedTestConst, c.Meta().AbsType())
	return ctx
}

// The tidy after an Unfold rewrites by no resident equation: with
// `f(a) = b` resident, the Unfold of zz_wrapped leaves the opened goal
// `P(f(a))` as it stands, and the author's `eq.Rw()` is what substitutes.
func TestUnfoldTidy_LeavesAResidentEquationToTheAuthor(t *testing.T) {
	ctx := wrappedTestScript()
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀f:num → num. ∀a b:num. ∀P:num → bool. f(a) = b ⇒ P(b) ⇒ "+wrappedTestConst+"(P, f(a))",
			func(a *Argument, f *ext.Expr[natFun], x, b *ext.Expr[ext.Nat], P *ext.Expr[natSet], eq, holds Fact) {
				a.Do(Unfold(wrappedTestDefinition))
				require.Equal(t, "P₀(f₀(a₀))", ext.PrintTerm(a.cur.Goal.Conclusion()), "the opened goal stands unrewritten")
				a.Do(eq.Rw())
				a.Show("the rewritten goal is the fact", By(holds))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}
