// cnf_miss_basic_check_test.go — a strict CNF-cache MISS reached through
// a bare CnfRefute() (a Calc leg, a kit's terminal, the set driver's own
// refute) says whether the goal closes under Basic(), as a MISS reached
// through By does: the question "does this leaf want the refuter at
// all" has one answer whichever verb reached it.

package proof

import (
	"context"
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func bareRefuteMiss(goal Prop) (text string) {
	defer func() {
		if r := recover(); r != nil {
			text = fmt.Sprint(r)
		}
	}()
	CreateGoalStack(goal).runStep(_CNFRefute{env: strictEnv(), ctx: context.Background()})
	return ""
}

func TestCnfRefute_StrictMissSaysWhetherBasicCloses(t *testing.T) {
	// ∀i. b(i) ⇒ q(i) ⊢ ∀x. b(x) ⇒ q(x): the clause maker does not
	// refute it outright (the Skolemized goal meets the hypothesis only
	// by unification), and Basic() closes it by assumption up to α.
	avoidable := alphaHypGoal(t)
	require.True(t, auditBasicCloses(t.Context(), avoidable), "fixture: Basic() closes it")
	miss := bareRefuteMiss(avoidable)
	require.Contains(t, miss, "CNF cache MISS", "fixture: the goal must reach resolution: %s", miss)
	assert.Contains(t, miss, "Checked: this goal closes under Basic()")

	// f(a) = g(b), g(b) = h(c), h(c) = k(d) ⊢ f(a) = k(d): a chain Basic()
	// does not close — its links are of one size, so no rewrite shrinks
	// its target, and none makes the conclusion a hypothesis.
	ind := TypeInd
	fun := core.MakeFun(ind, ind)
	f, g, h, k := ext.Var("f", fun), ext.Var("g", fun), ext.Var("h", fun), ext.Var("k", fun)
	a, b, c, d := ext.Var("a", ind), ext.Var("b", ind), ext.Var("c", ind), ext.Var("d", ind)
	wanted := prop.MakeProp(f.Apply(a).Eq(k.Apply(d)).Core(),
		f.Apply(a).Eq(g.Apply(b)).Core(), g.Apply(b).Eq(h.Apply(c)).Core(), h.Apply(c).Eq(k.Apply(d)).Core())
	require.False(t, auditBasicCloses(t.Context(), wanted), "fixture: Basic() does not close it")
	miss = bareRefuteMiss(wanted)
	require.Contains(t, miss, "CNF cache MISS")
	assert.Contains(t, miss, "Checked: this goal does NOT close under Basic()")

	// A cache-only PROBE — the By ladder's first rung — is asked nothing:
	// its miss is recovered and read by no one.
	probe := ""
	func() {
		defer func() { probe = fmt.Sprint(recover()) }()
		CreateGoalStack(avoidable).runStep(_CNFRefute{env: makeStepTestEnv(), ctx: withCNFCacheOnlyProbe(t.Context())})
	}()
	require.Contains(t, probe, "CNF cache MISS")
	assert.NotContains(t, probe, "Checked:")
}
