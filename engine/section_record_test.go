package engine

import (
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"
)

// sectionRecord serializes a proved section as the lineage records it
// and the emit reads it: the section's DetailedProofProto, round-tripped
// through the wire.
func sectionRecord(t *testing.T, sec *sectionState) *proof.DetailedProofProto {
	t.Helper()
	detailed := sec.root.DetailedProofProto()
	require.NotNil(t, detailed, "section root is not proved")
	bytes, err := proto.Marshal(detailed)
	require.NoError(t, err)
	require.NotEmpty(t, bytes)
	var decoded proof.DetailedProofProto
	require.NoError(t, proto.Unmarshal(bytes, &decoded))
	return &decoded
}

// emittedDepNames renders a proved section through EmitSection under
// the family profile and returns the registered names the emitted member
// declares as its deps — the merged flow's dep oracle (what the landed
// member's replay preloads). Every recorded cite must resolve to a
// registered entry for the emit to succeed.
func emittedDepNames(t *testing.T, e *Engine, sessionID string, section int) []string {
	t.Helper()
	emit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: sessionID, Section: section, FuncName: "Build_Record", Family: "zz_record", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted member:\n%s", emit.Go)
	return emit.DepNames
}
