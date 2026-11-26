// recorded_deps_test.go — the dependency record a proved member's
// replay is served and the record of the definitions it opens, and the
// drift gates on them (checkRecordedDeps, checkRecordedUnfolds,
// replay_test.go).

package gates

import (
	"slices"
	"strings"
	"testing"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestRecordedDeps_DriftFailsBothWays: a member verified against its
// family blob replays green, and the same blob with the member's
// record altered fails — once with an entry the build reads taken off
// the record (the read is refused, and named), once with an entry the
// build does not read put on it (the record no longer matches what the
// build read). Without the first a record could silently lose an edge
// the build stands on; without the second a stale edge would stay in
// the graph every reader of DepEntries sees.
func TestRecordedDeps_DriftFailsBothWays(t *testing.T) {
	member, ok := registry.ByName("list.AppendAssoc")
	if !ok {
		t.Skip("datatypes/list is not in this build")
	}
	unread, ok := registry.ByName("peano.Recursion")
	if !ok {
		t.Skip("nat_num/peano is not in this build")
	}
	blob := member.Family().CNF
	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		t.Fatal(err)
	}
	record := cache.GetMemberDeps()[member.Name].GetNames()
	if len(record) == 0 {
		t.Fatalf("%s has no recorded deps to take one off — record the family", member.Name)
	}
	if slices.Contains(record, unread.Name) {
		t.Fatalf("%s reads %s; the control needs an entry it does not read", member.Name, unread.Name)
	}
	with := func(names []string) []byte {
		c := proto.Clone(&cache).(*proof.CNFCache)
		c.MemberDeps[member.Name] = &proof.EntryList{Names: names}
		out, err := proto.MarshalOptions{Deterministic: true}.Marshal(c)
		if err != nil {
			t.Fatal(err)
		}
		return out
	}

	setup := prepareRecorder(t)
	if err := verifyRecordedMember(t, member, blob, setup); err != nil {
		t.Fatalf("%s against its own record: %v", member.Name, err)
	}
	dropped := record[0]
	err := verifyRecordedMember(t, member, with(record[1:]), setup)
	if err == nil || !strings.Contains(err.Error(), "which its recorded deps do not list") || !strings.Contains(err.Error(), dropped) {
		t.Fatalf("%s with %s taken off its record: want the read named as refused, got %v", member.Name, dropped, err)
	}
	added := append(slices.Clone(record), unread.Name)
	slices.Sort(added)
	err = verifyRecordedMember(t, member, with(added), setup)
	if err == nil || !strings.Contains(err.Error(), "dependencies drifted") {
		t.Fatalf("%s with %s put on its record: want a drift, got %v", member.Name, unread.Name, err)
	}
}

// TestRecordedUnfolds_DriftFailsBothWays: a member whose proof opens
// definitions replays green against its family blob, stands on those
// definitions in the graph and is not served them, and the same blob
// with the member's unfold row altered fails — with a definition the
// build opens taken off the row, with one it does not open put on it,
// and with the row gone. Without the first an edge the proof stands on
// would be missing from the graph; without the second a stale edge
// would stay in it.
func TestRecordedUnfolds_DriftFailsBothWays(t *testing.T) {
	member, ok := registry.ByName("int_construction.GreaterEqIffLessEq")
	if !ok {
		t.Skip("int_num/int_construction is not in this build")
	}
	unopened, ok := registry.ByName("set_basic.SubsetDef")
	if !ok {
		t.Skip("sets/set_basic is not in this build")
	}
	blob := member.Family().CNF
	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		t.Fatal(err)
	}
	record := cache.GetMemberUnfolds()[member.Name].GetNames()
	if len(record) == 0 {
		t.Fatalf("%s has no recorded unfolds to take one off — record the family", member.Name)
	}
	if slices.Contains(record, unopened.Name) {
		t.Fatalf("%s opens %s; the control needs a definition it does not open", member.Name, unopened.Name)
	}

	// The record is the member's edges: in the graph, served to no build.
	names := func(entries []*registry.ProofEntry) []string {
		out := make([]string, len(entries))
		for i, e := range entries {
			out[i] = e.Name
		}
		return out
	}
	graph, served := names(member.DepEntries()), names(member.ServedDeps())
	for _, definition := range record {
		if !slices.Contains(graph, definition) {
			t.Errorf("%s opens %s, and its DepEntries do not hold it: %v", member.Name, definition, graph)
		}
		if slices.Contains(served, definition) && !slices.Contains(cache.GetMemberDeps()[member.Name].GetNames(), definition) {
			t.Errorf("%s is served %s, which it only opens: %v", member.Name, definition, served)
		}
	}

	with := func(row *proof.EntryList) []byte {
		c := proto.Clone(&cache).(*proof.CNFCache)
		if row == nil {
			delete(c.MemberUnfolds, member.Name)
		} else {
			c.MemberUnfolds[member.Name] = row
		}
		out, err := proto.MarshalOptions{Deterministic: true}.Marshal(c)
		if err != nil {
			t.Fatal(err)
		}
		return out
	}

	setup := prepareRecorder(t)
	if err := verifyRecordedMember(t, member, blob, setup); err != nil {
		t.Fatalf("%s against its own record: %v", member.Name, err)
	}
	err := verifyRecordedMember(t, member, with(&proof.EntryList{Names: record[1:]}), setup)
	if err == nil || !strings.Contains(err.Error(), "unfolds drifted") {
		t.Fatalf("%s with %s taken off its unfold row: want a drift, got %v", member.Name, record[0], err)
	}
	added := append(slices.Clone(record), unopened.Name)
	slices.Sort(added)
	err = verifyRecordedMember(t, member, with(&proof.EntryList{Names: added}), setup)
	if err == nil || !strings.Contains(err.Error(), "unfolds drifted") {
		t.Fatalf("%s with %s put on its unfold row: want a drift, got %v", member.Name, unopened.Name, err)
	}
	err = verifyRecordedMember(t, member, with(nil), setup)
	if err == nil || !strings.Contains(err.Error(), "records no unfolds") {
		t.Fatalf("%s with no unfold row: want the missing record named, got %v", member.Name, err)
	}
}

// TestVerifyRecordedMember_MakesTheReplaysChecks: the recorder's
// verification refuses what a replay of the member refuses — an entry
// with no Key, a Key that is not its statement's, and a capability row
// the build does not match — so a recording that passes stands in for
// the member's replay. The member's own blob passes first.
func TestVerifyRecordedMember_MakesTheReplaysChecks(t *testing.T) {
	member, ok := registry.ByName("list.AppendAssoc")
	if !ok {
		t.Skip("datatypes/list is not in this build")
	}
	blob := member.Family().CNF
	setup := prepareRecorder(t)
	if err := verifyRecordedMember(t, member, blob, setup); err != nil {
		t.Fatalf("%s against its own blob: %v", member.Name, err)
	}

	for _, tc := range []struct {
		key, why string
	}{
		{registry.UnmintedKeyPrefix + member.Name, "has no Key"},
		{"prop_0000000000000000", "is not the statement's own normalized key"},
	} {
		wrong := *member
		wrong.Key = tc.key
		err := verifyRecordedMember(t, &wrong, blob, setup)
		if err == nil || !strings.Contains(err.Error(), tc.why) {
			t.Errorf("Key %s: got %v, want an error saying %q", tc.key, err, tc.why)
		}
	}

	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		t.Fatal(err)
	}
	if names := cache.GetMemberCapabilities()[member.Name].GetNames(); slices.Contains(names, "arith:nat") {
		t.Fatalf("%s uses arith:nat; the control needs a capability it does not use", member.Name)
	}
	cache.MemberCapabilities[member.Name] = &proof.CapabilityList{Names: []string{"arith:nat"}}
	drifted, err := proto.MarshalOptions{Deterministic: true}.Marshal(&cache)
	if err != nil {
		t.Fatal(err)
	}
	if err := verifyRecordedMember(t, member, drifted, setup); err == nil || !strings.Contains(err.Error(), "capability use drifted") {
		t.Errorf("a capability row the build does not match: got %v, want a drift", err)
	}
}
