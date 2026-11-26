package proof

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/tactic"
)

// TestStructuralTactic_ProtoRoundTrip is the regression test for the
// "_TacticStep does not support proto serialization" panic: each
// structural sub-tactic must emit a proto without panicking, and the
// proto must survive a Marshal/Unmarshal round-trip on its own oneof arm.
func TestStructuralTactic_ProtoRoundTrip(t *testing.T) {
	cases := []struct {
		name string
		step _Step
		arm  func(*StepProto) bool
	}{
		{"Rewrite", _Rewrite{}, func(p *StepProto) bool { return p.GetRewrite() != nil }},
		{"SplitConj", _SplitConj{}, func(p *StepProto) bool { return p.GetSplitConj() != nil }},
		{"SplitDisj", _SplitDisj{}, func(p *StepProto) bool { return p.GetSplitDisj() != nil }},
		{"StripImp", _StripImp{}, func(p *StepProto) bool { return p.GetStripImp() != nil }},
		{"StripQuant", _StripQuant{}, func(p *StepProto) bool { return p.GetStripQuant() != nil }},
		{"StripQuant1", _StripQuant1{}, func(p *StepProto) bool { return p.GetStripQuant1() != nil }},
		{"OpenTelescope", _OpenTelescope{items: []tactic.TelescopeItem{{Binder: 0}, {Binder: -1, Pieces: []tactic.PieceRef{{Block: 0, Index: 1}}}}}, func(p *StepProto) bool {
			o := p.GetOpenTelescope()
			return o != nil && len(o.GetItems()) == 2 && o.GetItems()[1].GetBinder() == -1 && o.GetItems()[1].GetPieces()[0].GetIndex() == 1
		}},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			pb := ext.NewPoolBuilder()
			var p isStepProto_Step
			require.NotPanics(t, func() { p = tc.step.proto(pb) })
			require.NotNil(t, p)

			bytes, err := proto.Marshal(&StepProto{Step: p})
			require.NoError(t, err)
			var decoded StepProto
			require.NoError(t, proto.Unmarshal(bytes, &decoded))
			assert.True(t, tc.arm(&decoded), "round-trip should preserve the step's oneof arm")
		})
	}
}

// TestHypIndexPayload_RoundTrip pins the wire contract for the optional
// hyp_index of _SplitDisj / _SplitHypIff / _SplitHypImply / _StripQuant:
// a Marshal/Unmarshal round-trip preserves an explicit index and
// preserves "unset" (nil) — emit renders the two differently.
func TestHypIndexPayload_RoundTrip(t *testing.T) {
	idx := 15
	for _, tc := range []struct {
		name     string
		explicit _Step
		unset    _Step
		get      func(*StepProto) *HypIndexProto
	}{
		{"SplitDisj", _SplitDisj{hypIndex: &idx}, _SplitDisj{}, (*StepProto).GetSplitDisj},
		{"SplitHypIff", _SplitHypIff{hypIndex: &idx}, _SplitHypIff{}, (*StepProto).GetSplitHypIff},
		{"SplitHypImply", _SplitHypImply{hypIndex: &idx}, _SplitHypImply{}, (*StepProto).GetSplitHypImply},
		{"StripQuant", _StripQuant{hypIndex: &idx}, _StripQuant{}, (*StepProto).GetStripQuant},
	} {
		roundTrip := func(t *testing.T, step _Step) *HypIndexProto {
			pb := ext.NewPoolBuilder()
			raw, err := proto.Marshal(&StepProto{Step: step.proto(pb)})
			require.NoError(t, err)
			var decoded StepProto
			require.NoError(t, proto.Unmarshal(raw, &decoded))
			payload := tc.get(&decoded)
			require.NotNil(t, payload)
			return payload
		}
		t.Run(tc.name+"/explicit", func(t *testing.T) {
			payload := roundTrip(t, tc.explicit)
			require.NotNil(t, payload.HypIndex, "explicit hyp_index must survive round-trip")
			assert.Equal(t, int32(15), *payload.HypIndex)
		})
		t.Run(tc.name+"/unset", func(t *testing.T) {
			assert.Nil(t, roundTrip(t, tc.unset).HypIndex, "unset hyp_index must stay unset")
		})
	}
}
