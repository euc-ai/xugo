// apply_close_every_equation_test.go — the apply rung's miss on a head
// whose conclusion equates two of its own binders.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A spelled-out injectivity `∀u v. f(u) = f(v) ⇒ u = v` has the
// conclusion `u = v`, which matches EVERY equation goal: the rung's
// miss on it ("matches the goal …, but its antecedent … is not in the
// context") is true at any equation and says nothing about the step.
// The miss says so; on a head whose conclusion reads the goal it does
// not.
func TestApplyClose_MissOnAConclusionThatMatchesEveryEquationSaysSo(t *testing.T) {
	ind := TypeInd
	f := ext.Var("f", core.MakeFun(ind, ind))
	g := ext.Var("g", core.MakeFun(ind, ind))
	u, v := ext.Var("u", ind), ext.Var("v", ind)
	a, b := ext.Var("a", ind), ext.Var("b", ind)

	miss := func(goal, head core.Term) string {
		root := CreateGoalStack(prop.MakeProp(goal, head))
		var claims []*GoalStackNode
		closed, diag := applyClose(root, &claims, nil, rungOpts{depth: antecedentApplies})
		require.False(t, closed, "the antecedent is not in the context")
		return diag
	}

	injective := ext.ForAll(u)(ext.ForAll(v)(f.Apply(u).Eq(f.Apply(v)).Imply(u.Eq(v)))).Core()
	diag := miss(a.Eq(b).Core(), injective)
	require.Contains(t, diag, "is not in the context", "the rung's miss: %s", diag)
	assert.Contains(t, diag, "matches every equation")

	// g(u) = g(v) reads the goal's two sides: an ordinary miss.
	congruent := ext.ForAll(u)(ext.ForAll(v)(f.Apply(u).Eq(f.Apply(v)).Imply(g.Apply(u).Eq(g.Apply(v))))).Core()
	diag = miss(g.Apply(a).Eq(g.Apply(b)).Core(), congruent)
	require.Contains(t, diag, "is not in the context", "the rung's miss: %s", diag)
	assert.NotContains(t, diag, "matches every equation")
}
