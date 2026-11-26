package proof

import (
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/encoding/protowire"
	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A known-theorem close that carries no reading serializes as a record
// made before KnownThmProto.reading existed — the stronger goal alone —
// and such a record decodes to no reading, so a persisted section
// record re-marshals byte for byte. A close that carries a reading (the
// session's `lemma {key, read_at}`) round-trips it.
func TestKnownThmProto_ReadingIsAbsentUnlessRecorded(t *testing.T) {
	P := core.Var("P", TypeBool)
	goal := prop.MakeProp(P)
	b := ext.NewPoolBuilder()

	plain := _KnownThmStep{strongerGoal: goal}.proto(b).(*StepProto_KnownThm).KnownThm
	got, err := proto.Marshal(plain)
	require.NoError(t, err)
	strongerBytes, err := proto.Marshal(plain.GetStrongerGoal())
	require.NoError(t, err)
	legacy := protowire.AppendBytes(protowire.AppendTag(nil, 1, protowire.BytesType), strongerBytes)
	require.Equal(t, legacy, got, "no reading, no field 3: the pre-reading encoding")
	var decoded KnownThmProto
	require.NoError(t, proto.Unmarshal(legacy, &decoded))
	require.Nil(t, decoded.GetReading())
	again, err := proto.Marshal(&decoded)
	require.NoError(t, err)
	require.Equal(t, legacy, again)

	read := _KnownThmStep{strongerGoal: goal, reading: &ReadingRecord{Law: goal, Under: P}}.proto(b).(*StepProto_KnownThm).KnownThm
	withReading, err := proto.Marshal(read)
	require.NoError(t, err)
	var back KnownThmProto
	require.NoError(t, proto.Unmarshal(withReading, &back))
	require.NotNil(t, back.GetReading().GetLaw())
	require.NotNil(t, back.GetReading().GetUnder())
}
