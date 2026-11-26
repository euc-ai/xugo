package engine

import (
	"encoding/json"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"
)

// replayEmittedInFamily lands an emitted member in its family through a build
// overlay — the member file beside the family's, and the family's CNF
// blob with the member recorded as the recorder would land it
// (mergeCNFBlob), the tree itself untouched — and replays the member
// through the gates harness in a subprocess, the compile and the
// replay the landing's own. The harness links the corpus, so the
// replay runs only under XUGO_EMIT_REPLAY=1; the rendering assertions
// a test makes before it run always.
func replayEmittedInFamily(t *testing.T, family, name string, out *EmitSectionResult) {
	t.Helper()
	t.Logf("--- emitted member: ---\n%s", out.Go)
	if os.Getenv("XUGO_EMIT_REPLAY") == "" {
		t.Skip("set XUGO_EMIT_REPLAY=1 to land the emitted member through a build overlay and replay it with the gates harness")
	}
	fam, ok := registry.FamilyByName(family)
	require.True(t, ok, "family %s", family)
	dir := fam.Dir
	if dir == "" {
		dir = fam.Name
	}
	root := moduleRoot(t)
	familyDir := filepath.Join(root, "library", "proofs", filepath.FromSlash(dir))
	scratch := t.TempDir()
	memberFile := filepath.Join(scratch, "zz_emit_"+name+".go")
	require.NoError(t, os.WriteFile(memberFile, []byte(out.Go), 0o644))
	replace := map[string]string{filepath.Join(familyDir, "zz_emit_"+name+".go"): memberFile}
	entryName := path.Base(fam.Name) + "." + name
	blobName := path.Base(fam.Name) + ".cnf.pb"
	base, err := os.ReadFile(filepath.Join(familyDir, blobName))
	require.NoError(t, err, "the family's recorded blob")
	merged := mergeCNFBlob(t, base, entryName, out)
	blobFile := filepath.Join(scratch, blobName)
	require.NoError(t, os.WriteFile(blobFile, merged, 0o644))
	replace[filepath.Join(familyDir, blobName)] = blobFile
	overlay, err := json.Marshal(map[string]any{"Replace": replace})
	require.NoError(t, err)
	overlayFile := filepath.Join(scratch, "overlay.json")
	require.NoError(t, os.WriteFile(overlayFile, overlay, 0o644))

	cmd := exec.Command("go", "test", "-overlay", overlayFile, "-count=1", "-v", "-run", "TestReplayAll", "./library/integrity/gates/")
	cmd.Dir = root
	cmd.Env = append(os.Environ(), "XUGO_REPLAY_ONE="+entryName)
	got, err := cmd.CombinedOutput()
	require.NoError(t, err, "the emitted member %s does not land and replay:\n%s\n--- member: ---\n%s", entryName, got, out.Go)
	require.Contains(t, string(got), "replaying entry "+entryName, "the harness replayed the member:\n%s", got)
	require.Contains(t, string(got), "--- PASS: TestReplayAll", "the harness replayed the member:\n%s", got)
	t.Logf("%s landed through an overlay and replayed", entryName)
}

// mergeCNFBlob is the family's blob with the member recorded as the
// recorder would land it: the emit's certificates and plans added,
// the emit's winning at a shared key, and the member's record — the
// entries it reads (EmitSectionResult.DepNames, what the harness
// serves it) and the capabilities it uses.
func mergeCNFBlob(t *testing.T, base []byte, entryName string, out *EmitSectionResult) []byte {
	t.Helper()
	var b, o proof.CNFCache
	require.NoError(t, proto.Unmarshal(base, &b))
	if len(out.CNFCache) > 0 {
		require.NoError(t, proto.Unmarshal(out.CNFCache, &o))
	}
	for k, p := range o.Entries {
		if b.Entries == nil {
			b.Entries = map[string]*refuter.CNFRefuteProofProto{}
		}
		b.Entries[k] = p
	}
	for k, p := range o.Plans {
		if b.Plans == nil {
			b.Plans = map[string]*proof.ByConditionPlanProto{}
		}
		b.Plans[k] = p
	}
	if b.MemberDeps == nil {
		b.MemberDeps = map[string]*proof.EntryList{}
	}
	b.MemberDeps[entryName] = &proof.EntryList{Names: append([]string(nil), out.DepNames...)}
	if b.MemberUnfolds == nil {
		b.MemberUnfolds = map[string]*proof.EntryList{}
	}
	b.MemberUnfolds[entryName] = &proof.EntryList{Names: append([]string(nil), out.UnfoldNames...)}
	if b.MemberCapabilities == nil {
		b.MemberCapabilities = map[string]*proof.CapabilityList{}
	}
	b.MemberCapabilities[entryName] = &proof.CapabilityList{Names: append([]string(nil), out.Capabilities...)}
	b.RecordedMembers = append(b.RecordedMembers, entryName)
	sort.Strings(b.RecordedMembers)
	merged, err := proto.MarshalOptions{Deterministic: true}.Marshal(&b)
	require.NoError(t, err)
	return merged
}

// moduleRoot is the directory of the module's go.mod.
func moduleRoot(t *testing.T) string {
	t.Helper()
	got, err := exec.Command("go", "env", "GOMOD").Output()
	require.NoError(t, err)
	return filepath.Dir(strings.TrimSpace(string(got)))
}
