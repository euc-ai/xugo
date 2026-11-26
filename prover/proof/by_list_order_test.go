// by_list_order_test.go — a failing By reads the order of its premise
// list (listOrderNote): a premise is installed into the leaf as the
// premises listed before it have built it, and a failure names the
// premise that, listed last, changes what the installs leave.
package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// byListOrderFailure runs spec on goal under a strict env with an empty
// store — a close is one the installs or the keyless rungs make, and a
// leaf that reaches the refuter fails — and returns the failure's text,
// empty where the By closed.
func byListOrderFailure(t *testing.T, goal Prop, spec BySpec) (failure string) {
	t.Helper()
	env := groundTestEnv(t)
	newGroundByStore().wire(env, true)
	env.RequireCNFCacheHit = true
	defer func() {
		if r := recover(); r != nil {
			failure = fmt.Sprint(r)
		}
	}()
	require.True(t, ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec))
	return ""
}

// The composite's law, bare, and the instance stating Q of the
// composite: Q(λw. T(S(w))) closes at the law's install where the
// instance is listed first, and where the law is listed first the
// failure says so.
//
//	law:      ∀f g x. f(g(x)) = comp(f, g)(x)
//	instance: ∀f g. Q(comp(f, g))   at (T, S)
//	⊢ Q(λw. T(S(w)))
//
// The law is handed in its clause form with the point bound last, the
// order functions.ComposeApply's clause has: the chain's rewrite reaches
// under the goal's binder from that order.
func TestByListOrder_ABareLawAheadOfTheInstanceItsRewriteMeets(t *testing.T) {
	ind := TypeInd
	fn := MakeFun(ind, ind)
	f := ext.Var("f", fn)
	g := ext.Var("g", fn)
	x := ext.Var("x", ind)
	w := ext.Var("w", ind)
	T := ext.Var("T", fn)
	S := ext.Var("S", fn)
	comp := ext.TestConst("zz_order_comp", MakeFun(fn, MakeFun(fn, fn)))
	Q := ext.TestConst("zz_order_q", MakeFun(fn, TypeBool))

	law := prop.MakeProp(ext.ForAll(f, g, x)(f.Apply(g.Apply(x)).Eq(comp.Apply(f, g).Apply(x))).Core())
	composite := ext.ForAll(f, g)(Q.Apply(comp.Apply(f, g)))
	goal := prop.MakeProp(Q.Apply(w.To(T.Apply(S.Apply(w)))).Core())

	bare := ByPremiseSpec{Install: law, Clause: law, Describe: "the composite's law"}
	instance := ByPremiseSpec{
		Install:   prop.MakeProp(composite.Core()),
		Witnesses: []Term{T.Core(), S.Core()},
		Describe:  "Q of the composite",
	}

	require.Empty(t, byListOrderFailure(t, goal, BySpec{Premises: []ByPremiseSpec{instance, bare}}),
		"the law listed after the instance closes the goal at its install")

	failure := byListOrderFailure(t, goal, BySpec{Premises: []ByPremiseSpec{bare, instance}})
	require.NotEmpty(t, failure, "the law listed first is installed as a clause, and the leaf goes to the refuter")
	assert.Contains(t, failure, "the order of the premise list (checked): premise the composite's law, a bare law, "+
		"closes this goal at its install when it is listed last")
	assert.Contains(t, failure, "Move it to the end of the list.")
}

// A witnessed premise listed ahead of the law that supplies its guard
// takes its clause form, and the failure of the close says that listed
// last it takes its stated form; listed after the law it says nothing of
// the order.
//
//	guarded:  ∀x. G(x) ⇒ K(x)   at (a)
//	supplier: ∀x. G(x)
//	⊢ R
func TestByListOrder_AnInstanceAheadOfTheFactThatSuppliesItsGuard(t *testing.T) {
	ind := TypeInd
	x := ext.Var("x", ind)
	a := ext.Var("a", ind)
	G := ext.TestConst("zz_order_g", MakeFun(ind, TypeBool))
	K := ext.TestConst("zz_order_k", MakeFun(ind, TypeBool))
	R := ext.TestConst("zz_order_r", MakeFun(ind, TypeBool))

	guarded := ByPremiseSpec{
		Install:   prop.MakeProp(ext.ForAll(x)(G.Apply(x).Imply(K.Apply(x))).Core()),
		Witnesses: []Term{a.Core()},
		Describe:  "the guarded law",
	}
	supplier := ByPremiseSpec{Install: prop.MakeProp(ext.ForAll(x)(G.Apply(x)).Core()), Describe: "the guard's law"}
	goal := prop.MakeProp(R.Apply(a).Core())

	failure := byListOrderFailure(t, goal, BySpec{Premises: []ByPremiseSpec{guarded, supplier}})
	require.NotEmpty(t, failure, "nothing listed states R")
	assert.Contains(t, failure, "the order of the premise list (checked): premise the guarded law took its clause form")
	assert.Contains(t, failure, "list it after the fact that supplies its guard")

	failure = byListOrderFailure(t, goal, BySpec{Premises: []ByPremiseSpec{supplier, guarded}})
	require.NotEmpty(t, failure, "nothing listed states R")
	assert.NotContains(t, failure, "the order of the premise list", "the guard is supplied where the premise is listed")
}
