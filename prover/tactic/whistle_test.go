package tactic

import (
	"fmt"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A breadth cut is read at the goal the case analysis was entered with.
// The goal at the cut is the leaf that reached the count: every
// equivalence already split into its literals, none of them left to
// read.
func TestBreadthCutIsReadAtTheGoalItWasEnteredWith(t *testing.T) {
	withOpenLeafBackstop(t, 16)
	events, _ := recordWhistleFires(t)

	goal := iffHypGoal(5)
	require.Nil(t, mergeTactics(HypIffTactic)(goal))
	require.Len(t, *events, 1)
	ev := (*events)[0]

	require.NotNil(t, ev.Entry)
	assert.True(t, ev.Entry.AlphaEquals(goal))
	assert.NotContains(t, prop.PrintProp(ev.Goal), "⇔", "the leaf at the cut has every equivalence split")
	assert.Equal(t, prop.PrintProp(goal), WhistleCutStatement(ev))

	described := DescribeWhistleCut(ev)
	assert.Contains(t, described, "a case analysis reached 16 open leaves")
	_, statement, found := strings.Cut(described, "the goal it was entered with:")
	require.True(t, found, described)
	for i := range 5 {
		assert.Contains(t, statement, fmt.Sprintf("P%d(x) ⇔ Q%d(x)", i, i))
	}
	assert.False(t, strings.HasPrefix(described, "in "), "no step was watching")

	ev.Step = "By(hyp 0; hyp 1) at library/proofs/a/b.go:12"
	assert.True(t, strings.HasPrefix(DescribeWhistleCut(ev), "in By(hyp 0; hyp 1) at library/proofs/a/b.go:12: a case analysis"))
}

// A branch cut as divergent is read at the goal it had reached, which
// has grown by construction: its statement is cut at the bound, on a
// rune.
func TestDepthCutStatementIsBounded(t *testing.T) {
	x := Var("x", TypeA)
	conclusion := Var("P0", core.MakeFun(TypeA, TypeBool)).Apply(x)
	for i := 1; i < 800; i++ {
		conclusion = conclusion.And(Var(TermName(fmt.Sprintf("P%d", i)), core.MakeFun(TypeA, TypeBool)).Apply(x))
	}
	grown := MakeProp(conclusion.Core())
	require.Greater(t, utf8.RuneCountInString(prop.PrintProp(grown)), whistleStatementRunes)

	described := DescribeWhistleCut(skeleton.WhistleEvent{Driver: "mergeTactics", Depth: 129, Budget: 128, Goal: grown, Entry: grown})
	assert.Contains(t, described, "a simplification branch was cut at depth 129")
	assert.Contains(t, described, "more characters)")
	assert.True(t, utf8.ValidString(described))
	assert.Less(t, utf8.RuneCountInString(described), whistleStatementRunes+400)
}

// A listing has one entry for each distinct cut, counted when it was
// reported more than once, and spells out the first few.
func TestListWhistleCuts(t *testing.T) {
	assert.Equal(t, "\n  1. (2 times) a\n  2. b", ListWhistleCuts([]string{"a", "b", "a"}))

	var many []string
	for i := range whistleCutsListed + 3 {
		many = append(many, fmt.Sprintf("cut %d", i))
	}
	listed := ListWhistleCuts(many)
	assert.Contains(t, listed, fmt.Sprintf("\n  %d. cut %d", whistleCutsListed, whistleCutsListed-1))
	assert.NotContains(t, listed, fmt.Sprintf("cut %d", whistleCutsListed))
	assert.True(t, strings.HasSuffix(listed, "\n  and 3 more cut(s) elsewhere, not listed"))
}
