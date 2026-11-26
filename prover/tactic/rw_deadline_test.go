package tactic

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
)

// TestRwHypTacticUntil_ARuleThatFeedsItselfIsCutOffAtItsDeadline: an rw
// whose passes do not end in the time it has is cut off between two
// passes, by a utils.Cut, and returns no subgoals a caller could read as
// a rewrite that ran to its end or as a rule that does not apply.
//
// The rule is f(m) = g((λn. f(n))(m)): its right side holds its left
// side once the redex is reduced, which the guard against a
// self-expanding rule, reading the two sides as written, does not see.
// Each pass rewrites f(m), the pass's cleanup reduces the redex, and
// f(m) stands in the target again. The passes run to their budget, the
// goal's size, which a second hypothesis of a thousand nodes puts in the
// thousands; a pass costs more as the target grows, and the run takes
// minutes.
func TestRwHypTacticUntil_ARuleThatFeedsItselfIsCutOffAtItsDeadline(t *testing.T) {
	m := Var("m", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	n := core.Var(core.TermName("n"), TypeA)
	redex := core.Apply(ext.Abs(n, f.Apply(ext.WrapTerm(n)).Core()), m.Core())
	eq := f.Apply(m).Eq(g.Apply(ext.WrapTerm(redex))).Core()
	wide := m.Core()
	for range 1000 {
		wide = g.Apply(ext.WrapTerm(wide)).Core()
	}
	goal := testProp(Q.Apply(f.Apply(m).Core()).Core(), eq, P.Apply(ext.WrapTerm(wide)).Core())

	const budget = 300 * time.Millisecond
	// One pass is milliseconds at the deadline; the slack is for a loaded
	// machine. An rw that polled nothing would fail on this timer.
	const slack = 10 * time.Second
	ctx, cancel := context.WithTimeout(t.Context(), budget)
	defer cancel()
	type outcome struct {
		recovered any
		subGoals  *SubGoals
	}
	done := make(chan outcome, 1)
	start := time.Now()
	go func() {
		var out outcome
		defer func() {
			out.recovered = recover()
			done <- out
		}()
		out.subGoals = RwHypTacticUntil(ctx, rwEqHypIndex(t, goal, eq), false)(goal)
	}()
	var out outcome
	select {
	case out = <-done:
	case <-time.After(budget + slack):
		t.Fatalf("the rw is still running %v after its %v deadline", budget+slack, budget)
	}
	cut, isCut := utils.AsCut(out.recovered)
	require.True(t, isCut, "the rw ends by a cut, not by returning %v or panicking with %v", out.subGoals, out.recovered)
	require.Contains(t, cut.Where, "inside rw")
	require.ErrorIs(t, cut.Cause, context.DeadlineExceeded)
	require.GreaterOrEqual(t, time.Since(start), budget, "the rw ran to its deadline")
}
