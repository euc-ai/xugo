package tactic

// Contract tests for the EXPLICIT denote (DenoteTermTactic and friends)
// and for the recording sink the search form now fills.
//
// The defect these exist to hold shut: the size-threshold form is a
// RECIPE ("name whatever subterm the heuristic picks above n"), so a
// recorded step re-derived its own choice at replay and upstream drift
// could silently swap the named term — surfacing far downstream as a CNF
// cache miss. The explicit form is a RECORD, and every way it can be
// wrong must fail AT THE STEP.

import (
	"math/big"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// denoteRowGoal builds `⊥`-form goal whose single hypothesis repeats the
// sum (x + y) on both sides of a product:
//
//	(x + y) * (x + y) ≠ 0 ⊢ ⊥
//
// The repeated `x + y` is the term every row below names.
func denoteRowGoal() (goal Prop, sum *ext.TermWrapper) {
	num := ext.NumType
	x, y := ext.Var("x", num), ext.Var("y", num)
	add := ext.WrapTerm(dsl.NatPlusMeta.Term())
	mul := ext.WrapTerm(dsl.NatStarMeta.Term())
	zero := ext.WrapTerm(ext.MakeNumeral(big.NewInt(0)))

	sum = add.Apply(x, y)
	goal = prop.MakeProp(F, ext.Not(mul.Apply(sum, sum).Eq(zero)))
	return goal, sum
}

// The explicit form names the GIVEN term under the GIVEN variable: the
// hypothesis comes back rewritten and the defining equation joins it.
func TestDenoteTermTacticNamesTheGivenTerm(t *testing.T) {
	goal, sum := denoteRowGoal()

	sg := DenoteTermTactic(sum, "s")(goal)
	require.NotNil(t, sg, "explicit denote must fire")
	require.Equal(t, 1, sg.Size())

	child := sg.ChildGoal(0)
	s := core.Var("s", sum.Type())
	hyps := slices.Collect(child.HypIter())
	assert.True(t, slices.ContainsFunc(hyps, ext.Eq(s, sum).AlphaEquals),
		"the defining equation s = x + y must be a hypothesis: %v", hyps)
	for _, h := range hyps {
		assert.False(t, ext.IsSub(sum, h) && !ext.Eq(s, sum).AlphaEquals(h),
			"x + y must be gone from %s outside the defining equation", ext.PrintTerm(h))
	}
}

// A term the goal does not contain is the failure mode the explicit form
// exists to catch, and it must fail HERE — not silently, and not
// downstream.
func TestDenoteTermTacticPanicsOnAbsentTerm(t *testing.T) {
	goal, _ := denoteRowGoal()
	absent := ext.WrapTerm(dsl.NatStarMeta.Term()).
		Apply(ext.Var("u", ext.NumType), ext.Var("v", ext.NumType))

	assert.Panics(t, func() { DenoteTermTactic(absent, "q")(goal) },
		"naming a term the goal does not contain must panic at the step")
}

// The OPTIONAL flavor is the By-shaping's: a leaf without the term
// declines instead of panicking (a Broadcast fan legitimately meets
// such leaves), and the By checks separately that the shaping landed
// somewhere.
func TestDenoteTermTacticOptionalDeclinesOnAbsentTerm(t *testing.T) {
	goal, _ := denoteRowGoal()
	absent := ext.WrapTerm(dsl.NatStarMeta.Term()).
		Apply(ext.Var("u", ext.NumType), ext.Var("v", ext.NumType))

	assert.Nil(t, DenoteTermTacticOptional(absent, "q")(goal),
		"the shaping flavor declines rather than panics")
}

// The name is part of the record, so a collision is never silently
// renamed away — renaming it would move the goal keys the explicit form
// exists to pin.
func TestDenoteTermTacticPanicsOnNameCollision(t *testing.T) {
	goal, sum := denoteRowGoal()

	assert.Panics(t, func() { DenoteTermTactic(sum, "x")(goal) },
		"x is already free in the goal — the denote must refuse the name")
}

// The SEARCH form is unchanged in behaviour but now reports what it
// chose, which is what the ministep records instead of the threshold.
func TestDenoteTacticRecordingSurfacesTheSelection(t *testing.T) {
	goal, sum := denoteRowGoal()

	var sel DenoteSelection
	sg := DenoteTacticRecording(2, &sel)(goal)
	require.NotNil(t, sg, "the heuristic must fire on the repeated sum")
	require.NotNil(t, sel.Term, "a firing must report its selection")
	assert.True(t, sel.Term.AlphaEquals(sum),
		"selected %s, expected %s", ext.PrintTerm(sel.Term), ext.PrintTerm(sum))
	assert.NotEmpty(t, sel.Name, "a firing must report the name it minted")

	// The recorded pair replays to the SAME subgoal — that equivalence is
	// what lets a search firing be persisted as an explicit step.
	replay := DenoteTermTactic(sel.Term, sel.Name)(goal)
	require.NotNil(t, replay)
	require.Equal(t, sg.Size(), replay.Size())
	assert.True(t, sg.ChildGoal(0).AlphaEquals(replay.ChildGoal(0)),
		"explicit replay of the recorded choice must reproduce the subgoal")
}

// A term already denoted by some variable declines in BOTH modes — the
// abbreviation is there, adding a second name for it is not progress.
func TestDenoteDeclinesWhenAlreadyDenoted(t *testing.T) {
	goal, sum := denoteRowGoal()
	d := core.Var("d", sum.Type())
	withEq := prop.MakeProp(F, append(goal.Hyps(), ext.Eq(d, sum))...)

	assert.Nil(t, DenoteTermTactic(sum, "s")(withEq),
		"the term already has a name; the step declines")
}
