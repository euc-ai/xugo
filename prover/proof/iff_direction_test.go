package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// The named ⇔ splits — SplitIff with Forward / Backward, SplitHypIff
// with BothHold / NeitherHolds — commit two children in the order the
// halves assume, and DECLINE where the tactic constructor merges the
// two into one because one subsumes the other: a one-child split has
// no half to give a name to.

// TestSplitIff_DeclinesWhereTheHalvesMerge: L ⊢ L ⇔ ⊥. The ⇒ half,
// L ⊢ ⊥, subsumes the ⇐ half, ⊥, L ⊢ L, so the constructor hands back
// one child; the step does not apply and the section is untouched.
func TestSplitIff_DeclinesWhereTheHalvesMerge(t *testing.T) {
	e := makeGivenTestEnv()
	l := e.P.Apply(e.x)
	sec := e.ctx.Section(MakeProp(l.Eq(F), l))
	require.False(t, ApplySplitIff(sec))
	require.Empty(t, sec.children)
	require.False(t, sec.Proved())
}

// TestSplitIff_TwoHalvesInOrder: ⊢ p ⇔ q and ⊢ ¬p ⇔ ¬q each split into
// the ⇐ half first — q ⊢ p — and the ⇒ half second.
func TestSplitIff_TwoHalvesInOrder(t *testing.T) {
	e := makeGivenTestEnv()
	p, q := e.P.Apply(e.x), e.Q.Apply(e.x)
	for _, sides := range []struct {
		name string
		l, r Term
	}{
		{"plain", p.Core(), q.Core()},
		{"negated", Not(p).Core(), Not(q).Core()},
	} {
		t.Run(sides.name, func(t *testing.T) {
			sec := e.ctx.Section(MakeProp(ext.WrapTerm(sides.l).Eq(sides.r)))
			require.True(t, ApplySplitIff(sec))
			require.Len(t, sec.children, 2)
			back, fwd := sec.children[0].Goal, sec.children[1].Goal
			require.True(t, back.Conclusion().AlphaEquals(sides.l) && back.HasHyp(sides.r), "child 0 is not the ⇐ half: %s", back)
			require.True(t, fwd.Conclusion().AlphaEquals(sides.r) && fwd.HasHyp(sides.l), "child 1 is not the ⇒ half: %s", fwd)
		})
	}
}

// TestSplitHypIff_DeclinesWhereTheBranchesMerge: p ⇔ q, p, q ⊢ R. The
// both-branch, p, q ⊢ R, subsumes the neither-branch, ¬p, ¬q, p, q ⊢ R,
// so the constructor hands back one child; the step declines in both
// its forms — and so for ¬p ⇔ ¬q, ¬p, ¬q ⊢ R, whose denials the tactic
// contracts.
func TestSplitHypIff_DeclinesWhereTheBranchesMerge(t *testing.T) {
	e := makeGivenTestEnv()
	p, q := e.P.Apply(e.x), e.Q.Apply(e.x)
	r := Var("R", MakeFun(TypeA, TypeBool)).Apply(e.x)
	for _, sides := range []struct {
		name string
		l, r Term
	}{
		{"plain", p.Core(), q.Core()},
		{"negated", Not(p).Core(), Not(q).Core()},
	} {
		iff := ext.WrapTerm(sides.l).Eq(sides.r)
		goal := MakeProp(r, iff, sides.l, sides.r)
		for _, indexed := range []bool{false, true} {
			name := sides.name + "/first"
			if indexed {
				name = sides.name + "/at"
			}
			t.Run(name, func(t *testing.T) {
				sec := e.ctx.Section(goal)
				if indexed {
					require.False(t, ApplySplitHypIffAt(sec, hypIndexOf(t, goal, iff.Core())))
				} else {
					require.False(t, ApplySplitHypIff(sec))
				}
				require.Empty(t, sec.children)
				require.False(t, sec.Proved())
			})
		}
	}
}

// TestSplitHypIff_TwoBranchesInOrder: p ⇔ q, p ⊢ R and ¬p ⇔ ¬q, ¬p ⊢ R
// each split into the both-branch first and the neither-branch second,
// the denial of a ¬-headed side its contraction.
func TestSplitHypIff_TwoBranchesInOrder(t *testing.T) {
	e := makeGivenTestEnv()
	p, q := e.P.Apply(e.x), e.Q.Apply(e.x)
	r := Var("R", MakeFun(TypeA, TypeBool)).Apply(e.x)
	for _, sides := range []struct {
		name string
		l, r Term
	}{
		{"plain", p.Core(), q.Core()},
		{"negated", Not(p).Core(), Not(q).Core()},
	} {
		t.Run(sides.name, func(t *testing.T) {
			iff := ext.WrapTerm(sides.l).Eq(sides.r)
			sec := e.ctx.Section(MakeProp(r, iff, sides.l))
			require.True(t, ApplySplitHypIff(sec))
			require.Len(t, sec.children, 2)
			both, neither := sec.children[0].Goal, sec.children[1].Goal
			require.True(t, both.HasHyp(sides.l) && both.HasHyp(sides.r), "child 0 is not the both-branch: %s", both)
			require.True(t, neither.HasHyp(denied(sides.l)) && neither.HasHyp(denied(sides.r)), "child 1 is not the neither-branch: %s", neither)
		})
	}
}

// TestSplitHypIff_PassesOverAMergingHypothesis: with p ⇔ q, p, q
// resident and S ⇔ U beside them, the form without an index passes
// over the ⇔-hypothesis whose branches merge and splits the next, as it
// passes over one whose sides are α-equal.
func TestSplitHypIff_PassesOverAMergingHypothesis(t *testing.T) {
	e := makeGivenTestEnv()
	p, q := e.P.Apply(e.x), e.Q.Apply(e.x)
	s := Var("S", MakeFun(TypeA, TypeBool)).Apply(e.x)
	u := Var("U", MakeFun(TypeA, TypeBool)).Apply(e.x)
	r := Var("R", MakeFun(TypeA, TypeBool)).Apply(e.x)
	merging, standing := p.Eq(q), s.Eq(u)
	goal := MakeProp(r, merging, p, q, standing)
	require.Less(t, hypIndexOf(t, goal, merging.Core()), hypIndexOf(t, goal, standing.Core()),
		"fixture defeated: the merging hypothesis has to come first")
	sec := e.ctx.Section(goal)
	require.True(t, ApplySplitHypIff(sec))
	require.Len(t, sec.children, 2)
	both, neither := sec.children[0].Goal, sec.children[1].Goal
	require.True(t, both.HasHyp(s.Core()) && both.HasHyp(u.Core()), "child 0 is not S ⇔ U's both-branch: %s", both)
	require.True(t, neither.HasHyp(Not(s).Core()) && neither.HasHyp(Not(u).Core()), "child 1 is not S ⇔ U's neither-branch: %s", neither)
}
