package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// cardFixture is a closed card whose body, under its own guard, opens
// with a guarded ∀ of its own, and a leaf that wants the card's
// instance at its leading binders as the antecedent of another law —
// the shape of a chain-complex assembly law fed a card's square:
//
//	card:  ∀g P Q x. P(x) ⇒ ∀y. Q(y) ⇒ zk(y) = g(x, y)
//	leaf:  P(a),  (∀y. Q(y) ⇒ zk(y) = g(a, y)) ⇒ S  ⊢  S
//
// The goal pins nothing of the card's y, so no tuple completion reads
// it off the goal: the cite stands at its own four binders.
func cardFixture() (card, goal Prop, tuple []Term) {
	ind2 := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	pred := core.MakeFun(TypeInd, core.TypeBool())
	g := ext.Var("g", ind2)
	P, Q := ext.Var("P", pred), ext.Var("Q", pred)
	x, y := ext.Var("x", TypeInd), ext.Var("y", TypeInd)
	a := ext.Var("a", TypeInd)
	S := ext.Var("S", core.TypeBool())
	zk := ext.WrapTerm(zkConst)

	body := func(x *ext.TermWrapper) *ext.TermWrapper {
		return ext.ForAll(y)(Q.Apply(y).Imply(zk.Apply(y).Eq(g.Apply(x, y))))
	}
	card = core.TestThm(ext.ForAll(g)(ext.ForAll(P)(ext.ForAll(Q)(ext.ForAll(x)(P.Apply(x).Imply(body(x)))))).Core())
	goal = prop.MakeProp(S.Core(), P.Apply(a).Core(), body(a).Imply(S).Core())
	return card, goal, []Term{g.Core(), P.Core(), Q.Core(), a.Core()}
}

// A tuple is counted against the card's own leading binders: (g, P, Q,
// a) grounds the whole prefix of `∀g P Q x. P(x) ⇒ ∀y. …` and leaves
// the guarded ∀y of its body, so with P(a) resident it takes the stated
// form. Counted against the guarded binders it reached into the body
// for, it was a partial tuple and installed in clause form.
func TestStatedGuardsSupplied_TupleOfTheLeadingBinders(t *testing.T) {
	card, goal, tuple := cardFixture()
	require.True(t, statedGuardsSupplied(goal, card, tuple, rungOpts{}),
		"a tuple naming the card's leading binders, its guard resident, takes the stated form")
	require.Nil(t, unsuppliedStatedGuard(goal, card, tuple, rungOpts{}))

	bare := prop.MakeProp(goal.Conclusion(), goal.Hyp(1))
	require.False(t, statedGuardsSupplied(bare, card, tuple, rungOpts{}), "the guard P(a) is not resident")
	missing := unsuppliedStatedGuard(bare, card, tuple, rungOpts{})
	require.NotNil(t, missing)
	require.Equal(t, "P(a)", ext.PrintTerm(missing))

	require.False(t, statedGuardsSupplied(goal, card, tuple[:3], rungOpts{}), "a tuple short of the leading binders stays partial")
}

// End to end through the By executor: the card cited at its leading
// binders installs as the instance `∀y. Q(y) ⇒ zk(y) = g(a, y)`, its
// guard discharged from the context, which is the other law's
// antecedent as written, and the leaf closes on the apply rung — under
// strict replay from an EMPTY store, so no key is read.
func TestApplyByStep_LeadingBinderTupleInstallsStated(t *testing.T) {
	card, goal, tuple := cardFixture()
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(goal.Hyp(0)), Resident: true, Describe: "P(a)"},
		{Install: prop.MakeProp(goal.Hyp(1)), Resident: true, Describe: "the law fed the instance"},
		{Install: card, Witnesses: tuple, Describe: "the card at (g, P, Q, a)"},
	}}
	strict := groundTestEnv(t)
	newGroundByStore().wire(strict, true)
	strict.RequireCNFCacheHit = true
	nd := CreateGoalStack(goal)
	require.True(t, ApplyByStep(nd, strict, t.Context(), spec),
		"strict replay from an empty store: the stated instance closes the leaf keyless")
	for _, leaf := range nd.UnsolvedLeaves() {
		require.True(t, leaf.Goal.NumHyps() == 0 && leaf.Goal.Conclusion().AlphaEquals(card.Conclusion()),
			"an open leaf other than the card's own claim: %s", prop.PrintProp(leaf.Goal))
	}
}
