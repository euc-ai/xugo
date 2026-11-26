package tactic

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// The one-atom reading: a term that is itself a membership in a
// set-builder reads as its condition at the point, the three-part form
// as the ∃ over its binders; a membership the condition tests is left as
// written, and a term that is no membership at its top is not read.
func TestMembershipAtomReading_TopLevelOnly(t *testing.T) {
	scope := readingScope(true)
	parse := func(text string) core.Term { return readingTerm(t, scope, text) }
	for _, c := range []struct{ term, read string }{
		{"a ∈ {p:num | P(p) ∧ K(p) ∧ p ≤ n}", "P(a) ∧ K(a) ∧ a ≤ n"},
		{"a ∈ {p:num | p ∈ {q:num | K(q)} ∧ P(p)}", "a ∈ {q:num | K(q)} ∧ P(a)"},
		{"a ∈ {b + p:num | p:num | P(p)}", "∃p:num. P(p) ∧ a = b + p"},
	} {
		got, ok := MembershipAtomReading(parse(c.term))
		require.True(t, ok, "%s is read", c.term)
		require.True(t, got.AlphaEquals(parse(c.read)), "%s reads as %s, want %s", c.term, ext.PrintTerm(got), c.read)
	}
	for _, text := range []string{
		"P(a) ∧ a ∈ {p:num | K(p)}",
		"¬(a ∈ {p:num | K(p)})",
		"a ∈ S",
	} {
		scope.Vars["S"] = core.MakeFun(ext.NumType, core.TypeBool())
		_, ok := MembershipAtomReading(parse(text))
		require.False(t, ok, "%s is not read", text)
	}
	_, ok := MembershipAtomReading(readingTerm(t, readingScope(false), "a ∈ {p:num | P(p)}"))
	require.False(t, ok, "a surface constant without a definition is not read")
}

// The index-targeted hypothesis splits read a membership in a
// set-builder through its predicate where the hypothesis is not the
// shape as written: the ∨ of `a ∈ {p | P(p) ∨ K(p)}` splits into two
// branches, the ∃ of `a ∈ {p | ∃q. R(p, q)}` and of the three-part form
// is Skolemized, a ⇔ and a ⇒ split as theirs do. Each branch holds the
// read piece in the membership's place, its provenance tracked, and the
// parent's proof is rebuilt from the branches'. The pick-first forms do
// not read it: the hypothesis they would take is named.
func TestHypothesisSplitAt_ReadsAMembership(t *testing.T) {
	scope := readingScope(true)
	parse := func(text string) core.Term { return readingTerm(t, scope, text) }
	concl := parse("P(n)")
	scope.Vars["p₀"], scope.Vars["q₀"] = ext.NumType, ext.NumType
	// The branches taken as their own proofs: the parent's is rebuilt
	// from them.
	closeAll := func(sg *SubGoals) Prop {
		t.Helper()
		branches := make([]Prop, sg.Size())
		for k := range sg.Size() {
			branches[k] = sg.ChildGoal(k)
		}
		return sg.Reconstruct(branches...)
	}
	for _, c := range []struct {
		name     string
		hyp      string
		split    func(Prop, int) *SubGoals
		branches []string
	}{
		{"split_disj", "a ∈ {p:num | P(p) ∨ K(p)}", HypDisjTacticAt, []string{"P(a)", "K(a)"}},
		{"strip_quant", "a ∈ {p:num | ∃q:num. R(p, q)}", StripQuantAtTactic, []string{"R(a, q₀)"}},
		{"strip_quant, three-part", "a ∈ {b + p:num | p:num | P(p)}", StripQuantAtTactic, []string{"P(p₀) ∧ a = b + p₀"}},
		{"split_hyp_iff", "a ∈ {p:num | P(p) ⇔ K(p)}", HypIffTacticAt, []string{"P(a)", "¬P(a)"}},
		{"split_hyp_imply", "a ∈ {p:num | P(p) ⇒ K(p)}", HypImplyTacticAt, []string{"¬P(a)", "K(a)"}},
	} {
		t.Run(c.name, func(t *testing.T) {
			member := parse(c.hyp)
			goal := MakeProp(concl, member, parse("b ≤ n"))
			idx := hypIndexOf(goal, member)
			sg := c.split(goal, idx)
			require.NotNil(t, sg, "%s reads the membership", c.name)
			require.Equal(t, len(c.branches), sg.Size())
			for k, want := range c.branches {
				child := sg.ChildGoal(k)
				require.True(t, child.AnyHyp(parse(want).AlphaEquals), "branch %d holds %s", k, want)
				require.False(t, child.AnyHyp(member.AlphaEquals), "branch %d no longer holds the membership", k)
				succ := sg.HypSuccessors(k)
				require.NotNil(t, succ, "branch %d's provenance is tracked", k)
				require.NotEqual(t, NoSuccessor, succ[hypIndexOf(goal, parse("b ≤ n"))], "the untouched hypothesis is tracked")
			}
			proved := closeAll(sg)
			require.True(t, proved.Conclusion().AlphaEquals(concl))
			for h := range proved.HypIter() {
				require.True(t, goal.AnyHyp(h.AlphaEquals), "a hypothesis of the proof is the goal's: %s", ext.PrintTerm(h))
			}
		})
	}

	t.Run("a hypothesis already the shape is split as written", func(t *testing.T) {
		disj := parse("a ∈ {p:num | K(p)} ∨ P(a)")
		goal := MakeProp(concl, disj)
		sg := HypDisjTacticAt(goal, 0)
		require.NotNil(t, sg)
		require.True(t, sg.ChildGoal(0).AnyHyp(parse("a ∈ {p:num | K(p)}").AlphaEquals), "the disjunct is not read")
	})
	t.Run("a reading that is not the shape declines", func(t *testing.T) {
		goal := MakeProp(concl, parse("a ∈ {p:num | P(p) ∧ K(p)}"))
		require.Nil(t, HypDisjTacticAt(goal, 0))
		require.Nil(t, StripQuantAtTactic(goal, 0))
		require.Nil(t, HypIffTacticAt(goal, 0))
		require.Nil(t, HypImplyTacticAt(goal, 0))
	})
	t.Run("the pick-first forms do not read it", func(t *testing.T) {
		require.Nil(t, HypDisjTactic(MakeProp(concl, parse("a ∈ {p:num | P(p) ∨ K(p)}"))))
		require.Nil(t, StripQuantTactic(MakeProp(concl, parse("a ∈ {p:num | ∃q:num. R(p, q)}"))))
	})
}
