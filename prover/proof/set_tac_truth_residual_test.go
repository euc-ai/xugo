// set_tac_truth_residual_test.go — the membership driver's residual
// carries no propositional constant of the driver's own making.
//
// Background (real_topology.ClosedIntervalClosed and RealHausdorff):
// unfolding `x ∈ 𝕌` yields ⊤ and `x ∈ ∅` yields ⊥, so a complement in
// the whole type left `⊤ ∧ ¬P(ẋ)` and a disjointness left
// `(A(ẋ) ∧ B(ẋ)) ⇔ ⊥`. Neither is α-equal to the resident pointwise
// fact of the same content, so the terminal's assumption pre-check
// missed and the refuter was paid a key for a refute with no content.
// No author-level shaping reaches these constants: they are born inside
// the driver, after every shaping has run.
//
// These tests pin that the driver simplifies the boolean constants it
// introduces (their clauses ride beside
// the membership rules), so both residuals close by ASSUMPTION — under
// strictEnv any refuter reach panics on the empty cache.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// truthSetTheory extends fullMiniSetTheory with the three constants
// whose membership formulas carry ⊤ or ⊥ or sit beside them: the whole
// type, the empty set and the difference.
type truthSetTheory struct {
	fullMiniSetTheory
	universe, empty, difference core.ConstTerm
}

func makeTruthSetTheory() truthSetTheory {
	m := makeFullMiniSetTheory()
	genSetT := core.MakeFun(core.TypeA(), core.TypeBool())
	inG := ext.WrapTerm(m.in)

	// universe := λx. ⊤ ;  empty_set := λx. ⊥
	x := ext.Var("x", core.TypeA())
	universeC := core.NewConstDef(x.To(ext.T).Core(), "universe")
	emptyC := core.NewConstDef(x.To(ext.F).Core(), "empty_set")

	// set_difference := λs.λt.λy. set_member(y, s) ∧ ¬set_member(y, t)
	s := ext.Var("s", genSetT)
	t2 := ext.Var("t", genSetT)
	y := ext.Var("y", core.TypeA())
	differenceC := core.NewConstDef(
		s.To(t2.To(y.To(inG.Apply(y, s).And(ext.Not(inG.Apply(y, t2)))))).Core(),
		"set_difference")

	return truthSetTheory{fullMiniSetTheory: m,
		universe: universeC, empty: emptyC, difference: differenceC}
}

// disjointGoal is RealHausdorff's last leaf:
//
//	∀z. ¬(p(z) ∧ q(z))  ⊢  p ∩ q = ∅
//
// whose membership residual read `∀ẋ. (p(ẋ) ∧ q(ẋ)) ⇔ ⊥`.
func (m truthSetTheory) disjointGoal() Prop {
	p := ext.Var("p", m.setT)
	q := ext.Var("q", m.setT)
	z := ext.Var("z", m.elemT)

	hyp := ext.ForAll(z)(ext.Not(p.Apply(z).And(q.Apply(z))))
	concl := m.at(m.inter, m.elemT).Apply(p, q).Eq(m.at(m.empty, m.elemT))
	return prop.MakeProp(concl.Core(), hyp.Core())
}

// complementGoal is ClosedIntervalClosed's first leaf:
//
//	∀z. ¬s(z) ⇔ r(z)  ⊢  𝕌 ∖ s = r
//
// whose membership residual read `∀ẋ. (⊤ ∧ ¬s(ẋ)) ⇔ r(ẋ)`.
func (m truthSetTheory) complementGoal() Prop {
	s := ext.Var("s", m.setT)
	r := ext.Var("r", m.setT)
	z := ext.Var("z", m.elemT)

	hyp := ext.ForAll(z)(ext.Not(s.Apply(z)).Eq(r.Apply(z)))
	concl := m.at(m.difference, m.elemT).Apply(m.at(m.universe, m.elemT), s).Eq(r)
	return prop.MakeProp(concl.Core(), hyp.Core())
}

func TestSetTacMembership_EmptySetResidual_ClosesWithoutRefuter(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeTruthSetTheory()

	n := CreateGoalStack(m.disjointGoal())
	require.True(t,
		ApplySetTacMode(n, strictEnv(), t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"a disjointness whose pointwise reading is resident must close without the refuter")
	assert.True(t, n.Proved())
}

func TestSetTacMembership_UniverseResidual_ClosesWithoutRefuter(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeTruthSetTheory()

	n := CreateGoalStack(m.complementGoal())
	require.True(t,
		ApplySetTacMode(n, strictEnv(), t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"a complement in the whole type whose pointwise reading is resident must close without the refuter")
	assert.True(t, n.Proved())
}

// TestApplyByStep_SettacCloser_TruthResidual is the BySets(premise)
// spelling of the same two leaves, end to end.
func TestApplyByStep_SettacCloser_TruthResidual(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeTruthSetTheory()

	for name, goal := range map[string]Prop{
		"disjoint":   m.disjointGoal(),
		"complement": m.complementGoal(),
	} {
		n := CreateGoalStack(goal)
		spec := BySpec{
			Premises: []ByPremiseSpec{{
				Install:  prop.MakeProp(goal.Hyp(0)),
				Resident: true,
				Describe: "the pointwise fact",
			}},
			Settac: true,
		}
		require.True(t, ApplyByStep(n, strictEnv(), t.Context(), spec), name)
		assert.True(t, n.Proved(), name)
	}
}
