// step_by_conj_test.go — the conditioning stage splits a conjunctive goal
// (step_condition.go, the goal strip) and the By executor closes the
// conjuncts in turn:
//
//  1. each conjunct takes its own route — one the context holds costs
//     nothing, one the rung applies costs nothing, one that wants a
//     search records ITS certificate, and the whole replays strictly
//     from that store;
//  2. a bare attempt does not split: a store that holds the certificate
//     of the goal whole, recorded before the stage split, still closes
//     it on the ladder's first rung;
//  3. every conjunct is conditioned before it is closed — a conjunct
//     that follows one the rung closed is stripped and offered to the
//     rung in a round of its own, never handed to the closer as the
//     split left it.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// conjGoalFixture is a goal of three conjuncts over one context:
//
//	P(a),  ∀x. P(x) ⇒ Q(x),  q((a ⊕ b) ⊕ c),  ⊕ associative, ⊕ commutative
//	  ⊢  P(a) ∧ Q(a) ∧ q(c ⊕ (b ⊕ a))
//
// P(a) is in the context, Q(a) is one apply away, and the third is its
// hypothesis up to a regrouping only a search over the two laws finds.
func conjGoalFixture() (goal Prop, spec BySpec) {
	opTy := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	pred := core.MakeFun(TypeInd, core.TypeBool())
	P, Q, q := ext.Var("P", pred), ext.Var("Q", pred), ext.Var("q", pred)
	plus := ext.Var("plus", opTy)
	a, b, c := ext.Var("a", TypeInd), ext.Var("b", TypeInd), ext.Var("c", TypeInd)
	x, m, n, k := ext.Var("x", TypeInd), ext.Var("m", TypeInd), ext.Var("n", TypeInd), ext.Var("k", TypeInd)
	lhs := plus.Apply(plus.Apply(a, b), c)
	rhs := plus.Apply(c, plus.Apply(b, a))
	hyps := []*ext.TermWrapper{
		P.Apply(a),
		ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x))),
		q.Apply(lhs),
		ext.ForAll(m)(ext.ForAll(n)(ext.ForAll(k)(plus.Apply(plus.Apply(m, n), k).Eq(plus.Apply(m, plus.Apply(n, k)))))),
		ext.ForAll(m)(ext.ForAll(n)(plus.Apply(m, n).Eq(plus.Apply(n, m)))),
	}
	terms := make([]core.Term, len(hyps))
	for i, h := range hyps {
		terms[i] = h.Core()
	}
	goal = prop.MakeProp(P.Apply(a).And(Q.Apply(a)).And(q.Apply(rhs)), terms...)
	for i := range goal.NumHyps() {
		spec.Premises = append(spec.Premises, ByPremiseSpec{Install: prop.MakeProp(goal.Hyp(i)), Resident: true, Describe: "premise"})
	}
	return goal, spec
}

func TestByConj_EachConjunctTakesItsOwnRoute(t *testing.T) {
	goal, spec := conjGoalFixture()
	st := newGroundByStore()

	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close")
	require.True(t, n.Proved())
	assert.Len(t, st.Proofs(), 1, "one conjunct wanted a search; the held one and the applied one recorded nothing")

	strict := groundTestEnv(t)
	st.wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), spec), "strict replay closes from what the live run recorded")
	require.True(t, n2.Proved())
}

func TestByConj_ABareCertificateOfTheWholeGoalStillCloses(t *testing.T) {
	goal, spec := conjGoalFixture()

	// The certificate of the goal WHOLE, as a recording made before the
	// stage split would hold it: the bare closer, run once.
	st := newGroundByStore()
	recorder := groundTestEnv(t)
	st.wire(recorder, true)
	whole := CreateGoalStack(goal)
	require.True(t, whole.runStep(_CNFRefute{env: recorder, ctx: t.Context()}), "the bare closer refutes the goal whole")
	require.Len(t, st.Proofs(), 1)

	strict := groundTestEnv(t)
	st.wire(strict, true)
	strict.RequireCNFCacheHit = true
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, strict, t.Context(), spec), "the ladder's first rung reads the goal unsplit")
	require.True(t, n.Proved())
}

// conjLawFixture is a goal whose second conjunct is a law, which the
// rung closes only once the strips have opened it:
//
//	P(a),  ∀x. P(x) ⇒ Q(x)  ⊢  P(a) ∧ (∀y. P(y) ∧ P(a) ⇒ Q(y))
func conjLawFixture() (goal Prop, spec BySpec) {
	pred := core.MakeFun(TypeInd, core.TypeBool())
	P, Q := ext.Var("P", pred), ext.Var("Q", pred)
	a, x, y := ext.Var("a", TypeInd), ext.Var("x", TypeInd), ext.Var("y", TypeInd)
	held := P.Apply(a)
	law := ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x)))
	opened := ext.ForAll(y)(P.Apply(y).And(P.Apply(a)).Imply(Q.Apply(y)))
	goal = prop.MakeProp(P.Apply(a).And(opened), held, law)
	for i := range goal.NumHyps() {
		spec.Premises = append(spec.Premises, ByPremiseSpec{Install: prop.MakeProp(goal.Hyp(i)), Resident: true, Describe: "premise"})
	}
	return goal, spec
}

func TestByConj_EveryConjunctIsConditioned(t *testing.T) {
	goal, spec := conjLawFixture()
	st := newGroundByStore()

	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close")
	require.True(t, n.Proved())
	assert.Empty(t, st.Proofs(), "the first conjunct is held and the second, opened, is one apply away: no search")
	assert.Empty(t, st.Plans())

	strict := groundTestEnv(t)
	newGroundByStore().wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), spec), "strict replay closes from an EMPTY store")
	require.True(t, n2.Proved())
}
