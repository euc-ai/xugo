// set_tac_rung_test.go — the set driver's terminal runs the apply rung
// on its unfolded residual, before the refuter.
//
// A law that concludes a membership in a comprehension — the ∀ half of
// a radius fact, `∀y. |y − c| < δ ⇒ y ∈ {x | x ∈ space ∧ P(x)}` — does
// not apply to the goal `P(a)` on the conditioning stage: the rung
// there reads the folded spelling. The driver unfolds the membership
// in the hypotheses as in the goal, and on that residual the same rung
// closes the goal with no key. These tests pin, under strictEnv (any
// refuter reach panics on the empty cache):
//
//  1. the membership driver closes such a residual on the rung;
//  2. the goal takes one apply and its antecedent one more, as on the
//     stage — a chain of two closes, a chain of three is the refuter's;
//  3. the BySets composite inherits it end to end, on the conjunctive
//     goal a Take leaves (the radius's positivity and its ∀ half).
//
// The sets are the mini set theory's (def-carrying set_member and
// set_comprehension, the driver's anchors); the predicates are
// variables.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// setRungTheory is the mini set theory with the comprehension marker,
// at the ground element type, plus the predicate and point variables
// the fixtures share.
type setRungTheory struct {
	fullMiniSetTheory
	in, setComprehension *ext.TermWrapper
	P, Q, R, S, v        *ext.TermWrapper
	f                    *ext.TermWrapper
	a, x, y, z, w        *ext.TermWrapper
}

func makeSetRungTheory() setRungTheory {
	m := makeFullMiniSetTheory()
	pred := core.MakeFun(m.elemT, core.TypeBool())
	return setRungTheory{
		fullMiniSetTheory: m,
		in:                m.at(m.in, m.elemT),
		setComprehension:  m.at(m.setComprehension, m.elemT),
		P:                 ext.Var("P", pred), Q: ext.Var("Q", pred), R: ext.Var("R", pred),
		S: ext.Var("S", pred), v: ext.Var("v", pred),
		f: ext.Var("f", core.MakeFun(m.elemT, m.elemT)),
		a: ext.Var("a", m.elemT), x: ext.Var("x", m.elemT), y: ext.Var("y", m.elemT),
		z: ext.Var("z", m.elemT), w: ext.Var("w", m.elemT),
	}
}

// member is `e ∈ {x | body(x)}`: set_member(e, set_comprehension(λx. body)).
func (m setRungTheory) member(e *ext.TermWrapper, body *ext.TermWrapper) *ext.TermWrapper {
	return m.in.Apply(e, m.setComprehension.Apply(m.x.To(body)))
}

func TestSetTacMembership_ResidualClosesOnTheRung(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := strictEnv()
	m := makeSetRungTheory()

	// The law concludes a membership in a comprehension; the goal is
	// one conjunct of what that membership unfolds to:
	//
	//	∀y. P(y) ⇒ y ∈ {x | Q(x) ∧ R(x)},  P(a)  ⊢  R(a)
	law := ext.ForAll(m.y)(m.P.Apply(m.y).Imply(m.member(m.y, m.Q.Apply(m.x).And(m.R.Apply(m.x)))))
	n := CreateGoalStack(prop.MakeProp(m.R.Apply(m.a).Core(), law.Core(), m.P.Apply(m.a).Core()))
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"the membership driver closes the unfolded residual on the rung, without the refuter")
	require.True(t, n.Proved())

	// The same goal opened one level: a ∀ the strips fix, an antecedent
	// they assume, and a conjunction closed conjunct by conjunct:
	//
	//	∀y. P(y) ⇒ y ∈ {x | Q(x) ∧ R(x)}  ⊢  ∀z. P(z) ⇒ z ∈ {x | R(x) ∧ P(x)}
	goal := ext.ForAll(m.z)(m.P.Apply(m.z).Imply(m.member(m.z, m.R.Apply(m.x).And(m.P.Apply(m.x)))))
	n = CreateGoalStack(prop.MakeProp(goal.Core(), law.Core()))
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"a ∀ goal into a comprehension closes conjunct by conjunct")
	require.True(t, n.Proved())
}

func TestSetTacMembership_RungReadsOneApplyIntoTheAntecedent(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := strictEnv()
	m := makeSetRungTheory()

	// The backward direction of ContinuousMapIffPointwise: the goal's
	// membership by the first law, whose antecedent is the second
	// law's consequent, whose own antecedent is held:
	//
	//	∀w. S(w) ⇒ w ∈ v,  ∀z. P(z) ⇒ S(f(z))  ⊢  ∀z. P(z) ⇒ z ∈ {x | P(x) ∧ f(x) ∈ v}
	inV := func(e *ext.TermWrapper) *ext.TermWrapper { return m.in.Apply(e, m.v) }
	first := ext.ForAll(m.w)(m.S.Apply(m.w).Imply(inV(m.w)))
	second := ext.ForAll(m.z)(m.P.Apply(m.z).Imply(m.S.Apply(m.f.Apply(m.z))))
	goal := ext.ForAll(m.z)(m.P.Apply(m.z).Imply(m.member(m.z, m.P.Apply(m.x).And(inV(m.f.Apply(m.x))))))
	n := CreateGoalStack(prop.MakeProp(goal.Core(), first.Core(), second.Core()))
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"one apply for the goal and one into its antecedent close the chain of two")
	require.True(t, n.Proved())

	// A chain of three that DESCENDS — each antecedent left to close a
	// smaller term than its goal — is structural and spends no depth:
	// the rung closes it too.
	//
	//	∀w. S(w) ⇒ w ∈ v,  ∀z. Q(z) ⇒ S(f(z)),  ∀z. P(z) ⇒ Q(z)  ⊢  the same goal
	secondQ := ext.ForAll(m.z)(m.Q.Apply(m.z).Imply(m.S.Apply(m.f.Apply(m.z))))
	third := ext.ForAll(m.z)(m.P.Apply(m.z).Imply(m.Q.Apply(m.z)))
	n = CreateGoalStack(prop.MakeProp(goal.Core(), first.Core(), secondQ.Core(), third.Core()))
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"a descending chain of three closes on the rung")
	require.True(t, n.Proved())

	// A chain of three that does not descend is the refuter's: each
	// law's antecedent is as large as its conclusion (`S(f(w))` against
	// `w ∈ v`, `Q(f(f(z)))` against `S(f(f(z)))`), so every apply spends
	// depth, and the membership driver's two are spent before the
	// innermost. Under strictEnv the reach is the cache MISS panic.
	//
	//	∀w. S(f(w)) ⇒ w ∈ v,  ∀z. Q(f(f(z))) ⇒ S(f(f(z))),  ∀z. P(z) ⇒ Q(f(f(z)))  ⊢  the same goal
	ffz := m.f.Apply(m.f.Apply(m.z))
	firstLevel := ext.ForAll(m.w)(m.S.Apply(m.f.Apply(m.w)).Imply(inV(m.w)))
	secondLevel := ext.ForAll(m.z)(m.Q.Apply(ffz).Imply(m.S.Apply(ffz)))
	thirdLevel := ext.ForAll(m.z)(m.P.Apply(m.z).Imply(m.Q.Apply(ffz)))
	n = CreateGoalStack(prop.MakeProp(goal.Core(), firstLevel.Core(), secondLevel.Core(), thirdLevel.Core()))
	require.Panics(t, func() {
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil)
	}, "a chain of three that does not descend reaches the refuter")
}

func TestApplyByStep_SettacCloser_RadiusFactClosesTheTakenGoal(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := strictEnv()
	m := makeSetRungTheory()

	// After Take(δ): the goal is the radius's positivity and its ∀ half
	// read into the comprehension the preimage is; the premise is the
	// radius fact as obtained:
	//
	//	S(a) ∧ ∀y. R(y) ⇒ y ∈ {x | Q(x) ∧ f(x) ∈ v}  ⊢  S(a) ∧ ∀z. R(z) ⇒ f(z) ∈ v
	inV := func(e *ext.TermWrapper) *ext.TermWrapper { return m.in.Apply(e, m.v) }
	radius := m.S.Apply(m.a).And(ext.ForAll(m.y)(m.R.Apply(m.y).Imply(
		m.member(m.y, m.Q.Apply(m.x).And(inV(m.f.Apply(m.x)))))))
	taken := m.S.Apply(m.a).And(ext.ForAll(m.z)(m.R.Apply(m.z).Imply(inV(m.f.Apply(m.z)))))
	n := CreateGoalStack(prop.MakeProp(taken.Core(), radius.Core()))
	spec := BySpec{
		Premises: []ByPremiseSpec{{
			Install:  prop.MakeProp(radius.Core()),
			Resident: true,
			Describe: "the radius",
		}},
		Settac: true,
	}
	require.True(t, ApplyByStep(n, env, t.Context(), spec),
		"BySets(radius) closes the taken goal: the positivity on the stage's rung, the ∀ half on the driver's")
	require.True(t, n.Proved())
}
