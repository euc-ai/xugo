package engine

import (
	"errors"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestBy_ApplyReportsRecords: a session `by` that closes carries a
// by_records diagnostic saying what the recorder would write for the
// close. The CurriedFunInImage leaf closes on the apply rung, keyless,
// so the diagnostic is "Records nothing".
func TestBy_ApplyReportsRecords(t *testing.T) {
	e, sid, _, gid := simpAdaptationSession(t, "", "f:num→B→C, n:num, u:B, S:set(B), u ∈ S ⊢ f(n)(u) ∈ image(f(n), S)")
	idx := 0
	out, err := e.ApplyStep(t.Context(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "by", ByHyps: []ByHypSpec{{HypIndex: &idx}}, WithLemmas: []LemmaWithSpec{{Key: "set_image.FunInImage"}},
	}})
	require.NoError(t, err)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	require.Zero(t, out.State.NumOpen)

	var records, closer string
	for _, d := range out.Diagnostics {
		switch d.Type {
		case DiagByRecords:
			records = d.Message
		case DiagByCloser:
			closer = d.Message
		}
	}
	require.NotEmpty(t, records, "a successful `by` must carry a by_records diagnostic; diags: %+v", out.Diagnostics)
	assert.Contains(t, records, "Records nothing", "the apply-rung close is keyless")
	require.NotEmpty(t, closer, "a successful `by` names its closer; diags: %+v", out.Diagnostics)
	assert.NotContains(t, closer, "cnf", "the curried application closes on the apply rung, before any refutation")
}

// TestProbe_ByNamesCloserAndRecords: a `by` probe that closes reports the
// closer and the recorder rows on the probe response, so comparing
// spellings' key cost no longer needs an apply and a restore each.
func TestProbe_ByNamesCloserAndRecords(t *testing.T) {
	e, sid, _, gid := simpAdaptationSession(t, "", "f:num→B→C, n:num, u:B, S:set(B), u ∈ S ⊢ f(n)(u) ∈ image(f(n), S)")
	idx := 0
	res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, Tactic: TacticReq{
		Type: "by", ByHyps: []ByHypSpec{{HypIndex: &idx}}, WithLemmas: []LemmaWithSpec{{Key: "set_image.FunInImage"}},
	}})
	require.NoError(t, err)
	require.Equal(t, ProbeSuccess, res.Outcome)
	require.Equal(t, "close", res.Effect)
	require.NotEmpty(t, res.ByCloser, "a `by` probe that closes must name the closer")
	assert.Contains(t, res.ByCloser, "apply/conditioning")
	assert.Contains(t, res.Records, "Records nothing", "the apply-rung close is keyless; records: %q", res.Records)
}

// TestFormatByRecords: the by_records text for the key, plan and keyless
// cases.
func TestFormatByRecords(t *testing.T) {
	assert.Equal(t,
		"Records nothing: the recorder writes no CNF key and no conditioning plan for this close.",
		formatByRecords(nil, nil))
	assert.Equal(t,
		"Records 1 key (prop_a).",
		formatByRecords([]core.PropKey{"prop_a"}, nil))
	assert.Equal(t,
		"Records 2 keys (prop_a, prop_b), 1 plan (prop_c).",
		formatByRecords([]core.PropKey{"prop_a", "prop_b"}, []core.PropKey{"prop_c"}))
}

// TestByProbeTimeoutDiagnostic: a `by` probe's timeout text names both
// the probe budget and the session refuter budget an apply would use.
func TestByProbeTimeoutDiagnostic(t *testing.T) {
	msg := byProbeTimeoutDiagnostic("by", 200, 2*time.Second, errors.New("cut off"))
	assert.Contains(t, msg, "200ms probe budget")
	assert.Contains(t, msg, "apply runs the CNF refuter under the session budget (2s)")
}
