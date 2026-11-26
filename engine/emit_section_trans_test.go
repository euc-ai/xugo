package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// Trans prints its middle term as a Go expression. A lambda binder
// shadowed by a lifted section parameter still needs its own local
// declaration under the name the signature allocator assigns it, built
// by `Var`: a binder of a Go term registers no name in the script's
// scope, where it would be the `x` the closure's parameter aliases.
func TestEmitSection_TransLambdaShadowsSectionBinder(t *testing.T) {
	e, s := boundSession(t, "nat_num/nat_order")
	addDoorGoal(t, s, "∀x y z:num. ∀f:(num → num). (λn:num. (f(n) + y) + z) = (λn:num. z + (y + f(n))) ∧ x + y = y + x")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj"})
	applyOnGoalWhere(t, e, s, holds("λ"), TacticReq{Type: "trans", Const: "λx:num. (f(x) + z) + y"})
	for {
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		if state.Complete {
			break
		}
		g := state.Goals[0]
		concl := g.Statement.Conclusion()
		tactic := TacticReq{Type: "by", Arith: true}
		if !ext.MatchesFORALL(concl).IsZero() {
			tactic = TacticReq{Type: "strip_quant"}
		} else if strings.Contains(ext.PrintTerm(concl), "λ") {
			tactic = TacticReq{Type: "funext"}
		}
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: tactic})
		require.NoError(t, err)
		require.True(t, res.Success, "%s: %v", tactic.Type, res.Diagnostics)
	}
	out := emitSoleResult(t, e, s, "Build_ZzTransLambda")
	require.Contains(t, out.Go, "Trans(")
	require.Regexp(t, `(?m)^\s*x_\d+ := Var\("x", NumType\)$`, out.Go, "the shadowed lambda binder must be declared")
	require.NotContains(t, out.Go, `ctx.Var("x"`, "the lambda binder registers no name")
	replayEmittedInFamily(t, "nat_num/nat_order", "ZzTransLambda", out)
}
