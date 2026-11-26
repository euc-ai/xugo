// set_tac_fixpoint_test.go — the membership driver expands to its
// fixpoint whatever the goal's size.
//
// Background (topology/continuous ClosedPreimage): the leaf
// `preimage_on(⋃T, f, c) ⊆ ⋃T` is small, and its expansion — the
// preimage, the comprehension, comprehension_spec, the membership in ⋃T —
// takes more passes than the leaf has nodes. A pass budget of the goal's
// size stopped the driver with comprehension_spec still in the residual,
// and BySets failed on a leaf the same set spelled as a comprehension
// closed.
//
// The test pins that the residual of nested compact constants carries
// no vocabulary constant: the driver ran to its fixpoint. The mini
// theory's comprehension is shallower than the corpus's, so the leaf
// nests the preimage to make the expansion outgrow the goal.

package proof

import (
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

var declarePreimageOnce sync.Once

func TestSetTacMembership_CompactConstantExpandsToFixpoint(t *testing.T) {
	m := makeFullMiniSetTheory()
	genSetT := core.MakeFun(core.TypeA(), core.TypeBool())
	inG := ext.WrapTerm(m.in)

	// subset := λs.λt. ∀y. set_member(y, s) ⇒ set_member(y, t)
	s := ext.Var("s", genSetT)
	t2 := ext.Var("t", genSetT)
	y := ext.Var("y", core.TypeA())
	subsetC := core.NewConstDef(
		s.To(t2.To(ext.ForAll(y)(inG.Apply(y, s).Imply(inG.Apply(y, t2))))).Core(), "subset")

	// preimage_on := λs.λf.λt. set_comprehension(λx. ∃z.
	//   comprehension_spec(x, set_member(z, s) ∧ set_member(f(z), t), z))
	f := ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA()))
	x := ext.Var("x", core.TypeA())
	z := ext.Var("z", core.TypeA())
	spec := ext.WrapTerm(m.comprehensionSpec).Apply(x, inG.Apply(z, s).And(inG.Apply(f.Apply(z), t2)), z)
	preimageC := core.NewConstDef(
		s.To(f.To(t2.To(ext.WrapTerm(m.setComprehension).Apply(x.To(ext.Exists(z)(spec)))))).Core(), "preimage_on")
	// The set driver's vocabulary holds preimage_on as the corpus's
	// does: its definition declares that its membership is read.
	declarePreimageOnce.Do(func() { tactic.DeclareMembershipRead(preimageC) })

	// preimage_on(preimage_on(preimage_on(⋃T, f, c), f, c), f, c) ⊆ ⋃T
	// at the ground element type, its variables free as at a stripped
	// leaf: each nesting adds a few nodes to the goal and a whole
	// unfolding chain to the expansion.
	T := ext.Var("T", m.famT)
	fT := ext.Var("f", core.MakeFun(m.elemT, m.elemT))
	c := ext.Var("c", m.setT)
	unionsT := m.at(m.unions, m.elemT).Apply(T)
	pulled := unionsT
	for range 3 {
		pulled = m.at(preimageC, m.elemT).Apply(pulled, fT, c)
	}
	concl := m.at(subsetC, m.elemT).Apply(pulled, unionsT)
	goal := prop.MakeProp(concl.Core())

	sub := tactic.MembershipSetTacExpand(t.Context(), goal, DefaultSetTacConsts())
	require.NotNil(t, sub, "the driver rewrites the leaf")
	for i := 0; i < sub.Size(); i++ {
		residual := sub.ChildGoal(i)
		for _, name := range DefaultSetTacConsts() {
			require.False(t, prop.ContainsConstName(residual, name),
				"residual %d still spells %s — the driver stopped short of its fixpoint: %v", i, name, residual)
		}
	}
}
