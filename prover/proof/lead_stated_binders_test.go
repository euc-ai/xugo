package proof

// lead_stated_binders_test.go — a PARTIAL tuple is read in the stated
// order on a clause install too (leadStatedBinders, witness_order.go).
// The lanes: the stated binders are moved to the front of the clause's
// ∀-block when the canonical labeling put others first; nothing moves
// when they already lead; a stated name the block does not bind keeps
// the positional reading. End to end: a By citing a transitivity law at
// its first two stated binders grounds THOSE binders, where the clause
// form's prefix starts with others.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// leadFixture: a relation R over ind and the stated transitivity law
// ∀m n p. R(m, n) ∧ R(n, p) ⇒ R(m, p), with the three binders.
func leadFixture() (R, m, n, p *ext.TermWrapper, body *ext.TermWrapper) {
	R = ext.Var("R", core.MakeFun(TypeInd, core.MakeFun(TypeInd, core.TypeBool())))
	m, n, p = ext.Var("m", TypeInd), ext.Var("n", TypeInd), ext.Var("p", TypeInd)
	body = transBody(R, m, n, p)
	return
}

func transBody(R, m, n, p *ext.TermWrapper) *ext.TermWrapper {
	return R.Apply(m, n).And(R.Apply(n, p)).Imply(R.Apply(m, p))
}

func TestLeadStatedBinders_MovesStatedBindersToFront(t *testing.T) {
	_, m, n, p, body := leadFixture()
	ref := core.TestThm(ext.ForAll(m)(ext.ForAll(n)(ext.ForAll(p)(body))))
	// The clause's canonical labeling put n and p in front of m.
	install := core.TestThm(ext.ForAll(n)(ext.ForAll(p)(ext.ForAll(m)(body))))

	led := leadStatedBinders(install, ref, 2)
	require.NotNil(t, led, "m is behind the block's first two slots, so it must move")
	names, _ := forallPrefixNames(led.AsProp().Conclusion())
	assert.Equal(t, []string{"m", "n", "p"}, names, "the stated binders lead, in stated order; the rest follow")
	assert.True(t, led.Proved(), "the re-generalized form is derived from the install, so it stays proved")

	// The tuple then maps by name onto the stated binders.
	a, b := ext.Var("a", TypeInd), ext.Var("b", TypeInd)
	out := reorderWitnessesToInstall(ref, led.AsProp().Conclusion(), []Term{a, b})
	if assert.Len(t, out, 2) {
		assert.True(t, any(a) == any(out[0]), "a grounds m")
		assert.True(t, any(b) == any(out[1]), "b grounds n")
	}
}

// A binder hoisted in front of the stated ones — the pointwise ẋ of a
// set inequality — is moved behind them: stated ∀s t b, block ∀ẋ b s t.
func TestLeadStatedBinders_HoistedBinderMovesBehind(t *testing.T) {
	_, m, n, p, body := leadFixture()
	x := ext.Var("ẋ", TypeInd)
	ref := core.TestThm(ext.ForAll(m)(ext.ForAll(n)(ext.ForAll(p)(body))))
	install := core.TestThm(ext.ForAll(x)(ext.ForAll(p)(ext.ForAll(m)(ext.ForAll(n)(body)))))

	led := leadStatedBinders(install, ref, 3)
	require.NotNil(t, led)
	names, _ := forallPrefixNames(led.AsProp().Conclusion())
	assert.Equal(t, []string{"m", "n", "p", "ẋ"}, names)
}

func TestLeadStatedBinders_NothingToMove(t *testing.T) {
	_, m, n, p, body := leadFixture()
	ref := core.TestThm(ext.ForAll(m)(ext.ForAll(n)(ext.ForAll(p)(body))))

	// The stated binders already lead (in either order): the name map
	// handles it, nothing is rebuilt.
	leads := core.TestThm(ext.ForAll(n)(ext.ForAll(m)(ext.ForAll(p)(body))))
	assert.Nil(t, leadStatedBinders(leads, ref, 2))

	// A stated name the block does not bind (Normalize renamed it):
	// the positional reading stands.
	R, _, _, _, _ := leadFixture()
	q := ext.Var("q", TypeInd)
	foreign := core.TestThm(ext.ForAll(n)(ext.ForAll(p)(ext.ForAll(q)(transBody(R, q, n, p)))))
	assert.Nil(t, leadStatedBinders(foreign, ref, 2))

	assert.Nil(t, leadStatedBinders(leads, ref, 0), "an empty tuple grounds nothing")
}

// End to end through the By executor, the session `by`'s path: the law
// cited at (a, b) — its stated m and n — with R(a, b) and R(b, c)
// resident closes R(a, c). Read positionally against a clause prefix
// that starts with n, the same tuple would ground n and p instead.
func TestApplyByStep_PartialTupleOnClauseReadsStatedOrder(t *testing.T) {
	env := makeStepTestEnv()
	R, m, n, p, body := leadFixture()
	law := core.TestThm(ext.ForAll(m)(ext.ForAll(n)(ext.ForAll(p)(body))))

	norm, _ := Normalize(law)
	require.NotNil(t, norm)
	prefix, _ := forallPrefixNames(norm.Conclusion())
	if !assert.NotEqual(t, []string{"m", "n"}, prefix[:2],
		"fixture must normalize with a stated binder behind the first two slots, else it tests nothing") {
		return
	}

	a, b, c := ext.Var("a", TypeInd), ext.Var("b", TypeInd), ext.Var("c", TypeInd)
	goal := prop.MakeProp(R.Apply(a, c).Core(), R.Apply(a, b).Core(), R.Apply(b, c).Core())
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(goal.Hyp(0)), Resident: true, Describe: "R(a, b)"},
		{Install: prop.MakeProp(goal.Hyp(1)), Resident: true, Describe: "R(b, c)"},
		{Install: law, Witnesses: []Term{a, b}, Describe: "transitivity at (a, b)"},
	}}
	nd := CreateGoalStack(goal)
	require.True(t, ApplyByStep(nd, env, t.Context(), spec), "the tuple grounds the stated m and n")
	for _, leaf := range nd.UnsolvedLeaves() {
		// Only the premise's claim obligation may remain — the residual closed.
		nl, _ := Normalize(leaf.Goal)
		assert.True(t, nl != nil && nl.AlphaEquals(norm),
			"an open leaf other than the law's own claim: %s", prop.PrintProp(leaf.Goal))
	}
}
