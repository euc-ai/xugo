package engine

// A session `by` whose close fired the divergence whistle says so.
//
// The cut is a function of the goal (prover/tactic openLeafBackstop), so
// the live close meets it as a replay does and goes on to close; only
// the replay is held whistle-free, by the recorder. A close that fired
// it is one whose Go transcription the recorder refuses, and the
// response is where the author can still choose another spelling.

import (
	"context"
	"encoding/json"
	"fmt"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// equivalencesGoal is `(P0(x) ∨ … ) ⇒ (Q0(x) ∨ …)` under k hypotheses
// Pᵢ(x) ⇔ Qᵢ(x) over distinct predicate variables: k case splits no rule
// decides, 2^k open leaves under Basic's case analysis. Nine reach the
// breadth backstop.
func equivalencesGoal(k int) core.Prop {
	pred := core.MakeFun(core.TypeA(), core.TypeBool())
	x := ext.Var("x", core.TypeA())
	var hyps []core.Term
	var ps, qs *ext.TermWrapper
	for i := range k {
		p := ext.Var(core.TermName(fmt.Sprintf("P%d", i)), pred).Apply(x)
		q := ext.Var(core.TermName(fmt.Sprintf("Q%d", i)), pred).Apply(x)
		hyps = append(hyps, ext.Apply(core.IFF(), p.Core(), q.Core()))
		if i == 0 {
			ps, qs = p, q
			continue
		}
		ps, qs = ps.Or(p), qs.Or(q)
	}
	return prop.MakeProp(ps.Imply(qs).Core(), hyps...)
}

// byOverEveryHyp is `by` naming every hypothesis of goal, with Basic()
// between the installs and the close.
func byOverEveryHyp(goal core.Prop) TacticReq {
	req := TacticReq{Type: "by", ByShape: &ByShapeReq{Normalized: true}}
	for i := range goal.NumHyps() {
		req.ByHyps = append(req.ByHyps, ByHypSpec{HypIndex: &i})
	}
	return req
}

func sessionWithPropGoal(t *testing.T, goal core.Prop) (*Engine, *Session, string) {
	t.Helper()
	e := newEngine(testEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(goal)
	s.rebuildGoalIndex()
	return e, s, info.ID
}

func whistleDiagnostics(out *StepResult) []Diagnostic {
	var found []Diagnostic
	for _, d := range out.Diagnostics {
		if d.Type == DiagByWhistle {
			found = append(found, d)
		}
	}
	return found
}

func TestBy_ReportsTheWhistleItsCloseFired(t *testing.T) {
	goal := equivalencesGoal(9)
	e, s, sid := sessionWithPropGoal(t, goal)
	leafID := ematchOpenLeafID(t, s)

	probed, err := e.Probe(context.Background(), sid, &ProbeRequest{GoalID: leafID, Tactic: byOverEveryHyp(goal)})
	require.NoError(t, err)
	require.Equal(t, ProbeSuccess, probed.Outcome, "the probe closes: %s", probed.Diagnostic)
	require.Contains(t, probed.Whistle, "P0(x) ⇔ Q0(x)", "the probe states the goal whose case analysis was refused")
	require.Contains(t, probed.Whistle, "the recorder refuses", "the probe says what the cut costs")
	wire, err := json.Marshal(probed)
	require.NoError(t, err)
	require.Contains(t, string(wire), `"by_whistle":`, "on the wire beside by_closer and records")

	// The apply runs beside another session of the same engine, as in the
	// serve: that session probes a close that meets no backstop for as
	// long as this one's close runs, and must never be told of a cut.
	quietGoal := equivalencesGoal(3)
	quiet, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	quietSession, _ := e.getSession(quiet.ID)
	quietSession.AddGoal(quietGoal)
	quietLeaf := ematchOpenLeafID(t, quietSession)
	applied := make(chan struct{})
	var quietProbes []*ProbeResult
	var quietErr error
	var beside sync.WaitGroup
	beside.Go(func() {
		for {
			probed, err := e.Probe(context.Background(), quiet.ID, &ProbeRequest{GoalID: quietLeaf, Tactic: byOverEveryHyp(quietGoal)})
			select {
			case <-applied:
				// This probe may have run after the apply: it shows nothing.
				return
			default:
			}
			if err != nil {
				quietErr = err
				return
			}
			quietProbes = append(quietProbes, probed)
		}
	})

	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: leafID, Tactic: byOverEveryHyp(goal)})
	close(applied)
	beside.Wait()
	require.NoError(t, err)
	require.True(t, out.Success, "the close stands: %+v", out.Diagnostics)
	found := whistleDiagnostics(out)
	require.Len(t, found, 1, "one diagnostic for the close, whatever the number of cuts: %+v", out.Diagnostics)
	require.Contains(t, found[0].Message, "P0(x) ⇔ Q0(x)", "the diagnostic states the goal whose case analysis was refused")
	require.Contains(t, found[0].Message, "the recorder refuses", "the diagnostic says what the cut costs")

	require.NoError(t, quietErr)
	require.NotEmpty(t, quietProbes, "no probe of the quiet session finished while the apply ran: the test showed nothing")
	for _, probed := range quietProbes {
		require.Equal(t, ProbeSuccess, probed.Outcome, "%s", probed.Diagnostic)
		require.Empty(t, probed.Whistle, "a cut in another session's close is not this close's")
	}
	t.Logf("%d probe(s) of the quiet session finished while the close that was cut ran", len(quietProbes))
}

// A close that met no backstop says nothing: three equivalences fan into
// eight leaves.
func TestBy_NoWhistleNoDiagnostic(t *testing.T) {
	goal := equivalencesGoal(3)
	e, s, sid := sessionWithPropGoal(t, goal)
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: ematchOpenLeafID(t, s), Tactic: byOverEveryHyp(goal)})
	require.NoError(t, err)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	require.Empty(t, whistleDiagnostics(out))
}
