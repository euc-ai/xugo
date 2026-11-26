package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The contract a Simp rule is served under: a dep named by NAME reaches
// the driver in its STATED form, so a direction marker reads against
// the statement as written, and a function-valued equation is not
// η-expanded on the way — it rewrites the function where it occurs as
// an argument.

// simpStatedEnv: k : ind → ind, c : ind, Q : ind → bool, and the
// function-valued pair g, h : ind → ind under P : (ind → ind) → bool.
type simpStatedEnv struct {
	ctx     *Script
	k, g, h *ext.TermWrapper
	c       *ext.TermWrapper
	Q, P    *ext.TermWrapper
	a       *ext.TermWrapper
}

func makeSimpStatedEnv() *simpStatedEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	fnTy := MakeFun(TypeInd, TypeInd)
	predTy := MakeFun(TypeInd, TypeBool)
	fnPredTy := MakeFun(fnTy, TypeBool)
	for _, c := range []struct {
		name string
		ty   core.HolType
	}{
		{"simpK", fnTy}, {"simpG", fnTy}, {"simpH", fnTy},
		{"simpC", TypeInd}, {"simpQ", predTy}, {"simpP", fnPredTy},
	} {
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(c.name, c.ty))
	}
	return &simpStatedEnv{
		ctx: ctx,
		k:   ctx.Const("simpK", fnTy),
		g:   ctx.Const("simpG", fnTy),
		h:   ctx.Const("simpH", fnTy),
		c:   ctx.Const("simpC", TypeInd),
		Q:   ctx.Const("simpQ", predTy),
		P:   ctx.Const("simpP", fnPredTy),
		a:   ext.WrapTerm(Var("a", TypeInd)),
	}
}

// residualOf runs Simp on a fresh section over `goal` and returns the
// one leaf it leaves — the rewritten residual, every rule obligation
// discharged.
func residualOf(t *testing.T, ctx *Script, goal core.Term, rule SimpRule) core.Term {
	t.Helper()
	sec := ctx.Section(prop.MakeProp(goal))
	sec.Do(Simp(rule))
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1, "Simp leaves exactly the residual; the rule obligation closes from the dep's certificate")
	return leaves[0].Goal.Conclusion()
}

// A dep stated `∀x. k(x) = c` would normalize with the bare constant on
// the LEFT (`c = k(x)`); Fwd still fires it as written, k(a) ↦ c.
func TestSimp_RuleFiresInItsStatedDirection(t *testing.T) {
	e := makeSimpStatedEnv()
	x := Var("x", TypeInd)
	rule := ext.ForAll(x)(e.k.Apply(x).Eq(e.c))
	serveThm(e.ctx, "zz_simp_k", core.TestThm(rule.Core()))

	got := residualOf(t, e.ctx, e.Q.Apply(e.k.Apply(e.a)).Core(), Fwd(depName("zz_simp_k")))
	require.True(t, got.AlphaEquals(e.Q.Apply(e.c).Core()),
		"Fwd reads the statement as written, k(a) ↦ c; got %s", ext.PrintTerm(got))
}

// A dep stated `g = h` at a function type reaches the driver as that
// equation, not as its pointwise expansion `∀ẋ. g(ẋ) = h(ẋ)`, so it
// rewrites g where g stands unapplied as an argument.
func TestSimp_FunctionValuedRuleRewritesAnUnappliedOccurrence(t *testing.T) {
	e := makeSimpStatedEnv()
	serveThm(e.ctx, "zz_simp_fun_eq", core.TestThm(e.g.Eq(e.h).Core()))

	got := residualOf(t, e.ctx, e.P.Apply(e.g).Core(), Fwd(depName("zz_simp_fun_eq")))
	require.True(t, got.AlphaEquals(e.P.Apply(e.h).Core()),
		"the unapplied g under P is rewritten to h; got %s", ext.PrintTerm(got))

	// Flipped is the statement's reverse, h ↦ g, read against the same
	// stated form.
	got = residualOf(t, e.ctx, e.P.Apply(e.h).Core(), Rev(depName("zz_simp_fun_eq")))
	require.True(t, got.AlphaEquals(e.P.Apply(e.g).Core()),
		"Flipped rewrites the unapplied h back to g; got %s", ext.PrintTerm(got))
}

// A rule carries no witnesses: `Simp(Fwd(At(dep, w)))` is refused, and
// the refusal names spellings that exist — the cite verbs' own repair,
// `verb(dep, w…)`, is not one a simp verb has.
func TestSimp_RefusesAGroundedRuleNamingWhatToWrite(t *testing.T) {
	e := makeSimpStatedEnv()
	x := Var("x", TypeInd)
	rule := ext.ForAll(x)(e.k.Apply(x).Eq(e.c))
	serveThm(e.ctx, "zz_simp_grounded", core.TestThm(rule.Core()))

	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.k.Apply(e.a)).Core()))
	defer func() {
		r := recover()
		require.NotNil(t, r, "a grounded rule must be refused")
		msg, _ := r.(string)
		require.Contains(t, msg, "Fwd(dep)")
		require.Contains(t, msg, "Fwd(dep.Inst[T]())")
		require.Contains(t, msg, "h.Rw()")
		require.NotContains(t, msg, "Simp(dep, w…)", "a spelling Simp does not have")
	}()
	sec.Do(Simp(Fwd(At(depName("zz_simp_grounded"), e.a))))
}

// A Show that rewrites its conclusion and then closes by contradiction:
// the By denotes a term, so its leaf is refuted from the hypotheses and
// the negated conclusion, the refutation reads no negated conclusion,
// and the residual's theorem concludes ⊥ where the residual states
// Q(simpC). Simp takes that theorem back to the goal as it takes one
// that concludes the rewritten conclusion.
func TestSimp_AResidualClosedByContradictionClosesTheGoal(t *testing.T) {
	e := makeSimpStatedEnv()
	x := ext.Var("x", TypeInd)
	rule := core.TestThm(ext.ForAll(x)(e.k.Apply(x).Eq(e.c)).Core())

	closed := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("∀P:num → bool. ∀g:num → num. ∀b:num. (∀y. ¬P(y)) ⇒ P(g(g(b))) ⇒ simpQ(simpK(simpC))",
			func(a *Argument, P *ext.Expr[natSet], g *ext.Expr[natFun], b *ext.Expr[ext.Nat], never, holds Fact) {
				a.Show("P holds at g(g(b)), and nowhere",
					Simp(Fwd(MakeFact(rule))), By(DenotedAs("d", a.Term("g(g(b))")), never, holds))
			})
	})
	require.True(t, closed != nil && closed.Proved(), "the residual closed by contradiction")

	control := provesInHand(t, func() *GoalStackNode {
		return e.ctx.Theorem("simpQ(simpC) ⇒ simpQ(simpK(simpC))", func(a *Argument, held Fact) {
			a.Show("Q holds at the constant", Simp(Fwd(MakeFact(rule))), By(held))
		})
	})
	require.True(t, control != nil && control.Proved(), "the residual closed at its conclusion")
}
