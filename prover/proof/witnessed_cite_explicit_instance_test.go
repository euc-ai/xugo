package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// witnessedCiteEnv serves two laws about a two-letter predicate: a
// stability law `∀ψ. closed(ψ) ⇒ ∃N. ∀x:A. ∀y:B. stab(ψ, N, x, y)` and
// the bound it yields, `(∀x:A. ∀y:B. stab(ψ, N, x, y)) ⇒ all(ψ, N)`.
func witnessedCiteEnv() *Script {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	num := ext.HolTypeOf[ext.Nat]()
	tyB := core.MakeVarType("B")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("handClosed", MakeFun(num, TypeBool)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("handStab",
		MakeFun(num, MakeFun(num, MakeFun(core.TypeA(), MakeFun(tyB, TypeBool))))))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("handAll", MakeFun(num, MakeFun(num, TypeBool))))
	serveThm(ctx, "zz_hand_stab", core.TestThm(ctx.MakePropText(
		"∀ψ:num. handClosed(ψ) ⇒ ∃N:num. ∀x:A. ∀y:B. handStab(ψ, N, x, y)").Conclusion()))
	serveThm(ctx, "zz_hand_all", core.TestThm(ctx.MakePropText(
		"∀ψ:num. ∀N:num. (∀x:A. ∀y:B. handStab(ψ, N, x, y)) ⇒ handAll(ψ, N)").Conclusion()))
	return ctx
}

// A witnessed cite of an EXPLICIT type instance installs the instance
// the author wrote. The fact verbs and the Cite verb hand a witnessed
// cite to citeSpecializeRef, which types any other polymorphic form by
// its tuple and the goal (witnessTypedForm); an explicit instance is
// exempt, as a By premise's is (pr.exact). The goal here holds the
// law's constant at prod(A, B) alone, so the goal-anchored adaptation
// would carry the identity instance at A, B off to prod(A, B): the
// lefschetz chapter's QuantifierFreeStability.At[A, B](ψ) at a goal
// whose host field is at prod(A, B).
func TestWitnessedCite_ExplicitInstanceInstallsAsWritten(t *testing.T) {
	const goal = "∀ψ:num. ∀u:prod(A, B). ∀v:prod(A, B). handClosed(ψ) ∧ handStab(ψ, 0, u, v) ⇒ ∃N:num. handAll(ψ, N)"
	stabAt := func(a, b TypeBinding) Fact { return Inst(depName("zz_hand_stab"), a, b) }
	allAt := func(a, b TypeBinding) Fact { return Inst(depName("zz_hand_all"), a, b) }
	t.Run("a fact in hand", func(t *testing.T) {
		ctx := witnessedCiteEnv()
		sec := provesInHand(t, func() *GoalStackNode {
			return ctx.Theorem(goal, func(a *Argument, ψ, u, v Term, closed Fact) {
				N, stable := a.UnpackAs[ext.Nat](GroupPremises(closed,
					stabAt(TypeBinder.BindA[ext.A](), TypeBinder.BindB[ext.B]()).At(ψ)), "N")
				a.Take(N)
				a.Show("the bound", By(stable, allAt(TypeBinder.BindA[ext.A](), TypeBinder.BindB[ext.B]()).At(ψ, N)))
			})
		})
		require.True(t, sec != nil && sec.Proved())
	})
	t.Run("the Cite verb", func(t *testing.T) {
		ctx := witnessedCiteEnv()
		sec := provesInHand(t, func() *GoalStackNode {
			return ctx.Theorem(goal, func(a *Argument, ψ, u, v Term, closed Fact) {
				a.Do(Cite(stabAt(TypeBinder.BindA[ext.A](), TypeBinder.BindB[ext.B]()), ψ))
				N, stable := a.UnpackAs[ext.Nat](a.Hyp(a.Term("∃N:num. ∀x:A. ∀y:B. handStab(ψ, N, x, y)")), "N")
				a.Take(N)
				a.Show("the bound", By(stable, allAt(TypeBinder.BindA[ext.A](), TypeBinder.BindB[ext.B]()).At(ψ, N)))
			})
		})
		require.True(t, sec != nil && sec.Proved())
	})
	t.Run("an instance at other letters, where the goal is at them", func(t *testing.T) {
		ctx := witnessedCiteEnv()
		sec := provesInHand(t, func() *GoalStackNode {
			return ctx.Theorem("∀ψ:num. ∀x:C. ∀y:D. handClosed(ψ) ⇒ ∃N:num. handStab(ψ, N, x, y)",
				func(a *Argument, ψ, x, y Term, closed Fact) {
					N, stable := a.UnpackAs[ext.Nat](GroupPremises(closed,
						stabAt(TypeBinder.BindA[ext.C](), TypeBinder.BindB[ext.D]()).At(ψ)), "N")
					a.Take(N)
					a.Show("the bound", By(stable))
				})
		})
		require.True(t, sec != nil && sec.Proved())
	})
}

// A witnessed cite the goal types keeps its theorem: the adaptation is
// of the served certificate, not of its bare statement, so the instance
// it registers is known (registerKnownThm). A bare cite of the two-letter
// law at a theorem over C and D takes the instance at C, D from the goal.
func TestWitnessedCite_GoalTypedInstanceIsATheorem(t *testing.T) {
	ctx := witnessedCiteEnv()
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀ψ:num. ∀x:C. ∀y:D. handClosed(ψ) ⇒ ∃N:num. handStab(ψ, N, x, y)",
			func(a *Argument, ψ, x, y Term, closed Fact) {
				N, stable := a.UnpackAs[ext.Nat](GroupPremises(closed, At(depName("zz_hand_stab"), ψ)), "N")
				a.Take(N)
				a.Show("the bound", By(stable))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}
