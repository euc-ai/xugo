package proof

// Wire contract of the denote ministep: what a firing WRITES DOWN.
//
// The point of the explicit form is that the record is a decision, not a
// recipe. A search firing therefore comes back from apply already
// resolved (applyRecording), and the proto carries the term it chose
// plus the name it minted. The proto3 zero of the new `term` field is
// what every pb recorded before this change decodes as, and it must
// still mean "re-run the heuristic" — that is the whole backward
// compatibility argument, so it is asserted here rather than only
// observed through the suite.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// denoteStepGoal is `¬P(f(x, y), f(x, y)) ⊢ ⊥` — one repeated subterm,
// which the heuristic names and the explicit form can be pointed at.
// Deliberately built from VARIABLES only, so the serialization rows below
// need no const-metadata service to read the pool back.
func denoteStepGoal() (Prop, *ext.TermWrapper) {
	num := ext.NumType
	x, y := ext.Var("x", num), ext.Var("y", num)
	f := ext.Var("f", core.MakeFun(num, core.MakeFun(num, num)))
	p := ext.Var("P", core.MakeFun(num, core.MakeFun(num, core.TypeBool())))

	sum := f.Apply(x, y)
	return prop.MakeProp(ext.F, ext.Not(p.Apply(sum, sum))), sum
}

func denoteProtoOf(t *testing.T, step _AutoDenote) (*AutoDenoteProto, *ext.PoolReader) {
	t.Helper()
	b := ext.NewPoolBuilder()
	wire, ok := step.proto(b).(*StepProto_Denote)
	require.True(t, ok, "denote must serialize as StepProto_Denote")
	return wire.Denote, ext.NewPoolReader(b.Pool(), nil)
}

// A SEARCH firing records the choice it made, not the threshold it made
// it at — and the size threshold stays populated alongside.
func TestAutoDenoteSearchRecordsItsChoice(t *testing.T) {
	goal, sum := denoteStepGoal()

	recorded, subGoals := _AutoDenote{sizeThreshold: 2}.applyRecording(goal, nil)
	require.NotNil(t, subGoals, "the heuristic must fire on the repeated sum")

	step, ok := recorded.(_AutoDenote)
	require.True(t, ok)
	require.NotNil(t, step.term, "the committed step must carry the chosen term")
	assert.True(t, step.term.AlphaEquals(sum),
		"recorded %s, expected %s", ext.PrintTerm(step.term), ext.PrintTerm(sum))
	assert.NotEmpty(t, step.name, "the committed step must carry the minted name")

	p, r := denoteProtoOf(t, step)
	assert.Equal(t, int32(2), p.GetSizeThreshold(), "the threshold rides along")
	require.NotZero(t, p.GetTerm(), "the chosen term must reach the wire")
	assert.Equal(t, step.name, p.GetName())
	assert.True(t, r.Term(p.GetTerm()).AlphaEquals(sum), "the pool term is the chosen one")
}

// An EXPLICIT step is recorded verbatim, and the caller-side `optional`
// tolerance (a By shaping's, see ByShape) is NOT part of the record: the
// step that applied did contain the term, so replay gets the strict
// contract.
func TestAutoDenoteExplicitStepRecordsWithoutOptional(t *testing.T) {
	goal, sum := denoteStepGoal()

	recorded, subGoals := _AutoDenote{term: sum, name: "s", optional: true}.applyRecording(goal, nil)
	require.NotNil(t, subGoals)
	step := recorded.(_AutoDenote)
	assert.False(t, step.optional, "the caller's tolerance is not part of the record")
	assert.Equal(t, "s", step.name)

	p, _ := denoteProtoOf(t, step)
	assert.Equal(t, "s", p.GetName())
	assert.NotZero(t, p.GetTerm())
}
