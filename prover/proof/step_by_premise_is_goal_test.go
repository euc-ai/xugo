// step_by_premise_is_goal_test.go — a named premise that IS the leaf's
// statement, its claim not yet proved: the session's case, where a
// premise is a registry statement certified after the composite by the
// entry it names (a chapter's premise carries its certificate and
// closes the leaf outright).

package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// premiseIsGoalFixture is a closed atomic statement over two
// uninterpreted constants — what an entry states and Normalize leaves
// as written — and an ambient hypothesis beside it.
func premiseIsGoalFixture() (stated core.Term, ambient core.Term) {
	predT := core.MakeFun(TypeInd, core.TypeBool())
	holds := ext.Const(core.MakeConstMeta("zz_holds", predT), predT)
	point := ext.Const(core.MakeConstMeta("zz_point", TypeInd), TypeInd)
	h := ext.Var("h", core.TypeBool())
	return holds.Apply(point).Core(), h.Core()
}

// The leaf has ambient hypotheses the premise list does not name: By
// clears them, and what is left is the premise's statement. That leaf
// is the premise's claim obligation — the composite's one child, for
// the caller to certify — and nothing is refuted.
func TestApplyByStep_UnprovedPremiseIsTheClearedLeaf(t *testing.T) {
	defer goleak.VerifyNone(t)
	stated, ambient := premiseIsGoalFixture()

	n := CreateGoalStack(prop.MakeProp(stated, ambient))
	spec := BySpec{Premises: []ByPremiseSpec{{
		Install:  prop.MakeProp(stated),
		Describe: "fixture.Stated",
	}}}
	require.True(t, ApplyByStep(n, strictEnv(), t.Context(), spec),
		"the premise is the goal: the By closes on the premise's claim, with no refuter reach")
	open := n.UnsolvedLeaves()
	require.Len(t, open, 1, "one obligation: the premise's claim")
	assert.True(t, open[0].Goal.AlphaEquals(prop.MakeProp(stated)),
		"the obligation is the premise's statement, got %s", prop.PrintProp(open[0].Goal))
}

// The goal is the premise's statement with nothing to clear: a
// composite cannot hand its own goal back as its obligation, and the
// refusal names the move that closes the leaf.
func TestApplyByStep_UnprovedPremiseIsTheWholeGoal_NamesTheCite(t *testing.T) {
	defer goleak.VerifyNone(t)
	stated, _ := premiseIsGoalFixture()

	n := CreateGoalStack(prop.MakeProp(stated))
	spec := BySpec{Premises: []ByPremiseSpec{{
		Install:  prop.MakeProp(stated),
		Describe: "fixture.Stated",
	}}}
	var refusal string
	func() {
		defer func() { refusal = fmt.Sprint(recover()) }()
		ApplyByStep(n, strictEnv(), t.Context(), spec)
	}()
	assert.Contains(t, refusal, "Cite(fixture.Stated)", "the Go move")
	assert.Contains(t, refusal, "`lemma`", "the session move")
	assert.False(t, n.Proved())
}
