package main

import (
	"bytes"
	"maps"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/cnfblob"
	pproof "github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// cert is a certificate row told apart from others by its pool's one
// string: two certs are the same row exactly when their marks agree.
func cert(mark string) *refuter.CNFRefuteProofProto {
	return &refuter.CNFRefuteProofProto{Pool: &ext.PoolProto{Strings: []string{mark}}}
}

func plan(conditioned string) *pproof.ByConditionPlanProto {
	return &pproof.ByConditionPlanProto{ConditionedGoalKey: conditioned}
}

func deps(names ...string) *pproof.EntryList { return &pproof.EntryList{Names: names} }

func capabilities(names ...string) *pproof.CapabilityList {
	return &pproof.CapabilityList{Names: names}
}

func marshal(t *testing.T, c *pproof.CNFCache) []byte {
	t.Helper()
	b, err := proto.MarshalOptions{Deterministic: true}.Marshal(c)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

func decode(t *testing.T, b []byte) *pproof.CNFCache {
	t.Helper()
	var c pproof.CNFCache
	if err := proto.Unmarshal(b, &c); err != nil {
		t.Fatal(err)
	}
	return &c
}

// TestMergeCaches_GoalKeyedTablesUnion: certificates, plans and exact
// keys are the
// union of the two trees, ours standing where both hold a key with
// different rows — and a row ours dropped stays dropped only when
// theirs dropped it too: a row theirs holds unchanged from base is
// kept, since a member of theirs may have read it.
func TestMergeCaches_GoalKeyedTablesUnion(t *testing.T) {
	base := &pproof.CNFCache{
		Entries: map[string]*refuter.CNFRefuteProofProto{"k_shared": cert("b"), "k_gone": cert("g")},
	}
	ours := &pproof.CNFCache{
		Entries:   map[string]*refuter.CNFRefuteProofProto{"k_shared": cert("b"), "k_both": cert("ours"), "k_ours": cert("o")},
		Plans:     map[string]*pproof.ByConditionPlanProto{"p_both": plan("k_both")},
		ExactKeys: map[string]string{"x_both": "k_both", "x_ours": "k_ours"},
	}
	theirs := &pproof.CNFCache{
		Entries: map[string]*refuter.CNFRefuteProofProto{
			"k_shared": cert("b"), "k_gone": cert("g"), "k_both": cert("theirs"), "k_theirs": cert("t"),
		},
		Plans:     map[string]*pproof.ByConditionPlanProto{"p_both": plan("k_other"), "p_theirs": plan("k_theirs")},
		ExactKeys: map[string]string{"x_both": "k_theirs", "x_theirs": "k_theirs"},
	}
	out := mergeCaches(base, ours, theirs)
	got := decode(t, out.merged)
	if want := map[string]string{"x_both": "k_both", "x_ours": "k_ours", "x_theirs": "k_theirs"}; !maps.Equal(got.ExactKeys, want) {
		t.Errorf("exact keys %v, want the union with ours standing %v", got.ExactKeys, want)
	}
	wantKeys := []string{"k_both", "k_gone", "k_ours", "k_shared", "k_theirs"}
	if keys := slices.Sorted(maps.Keys(got.Entries)); !slices.Equal(keys, wantKeys) {
		t.Errorf("entries %v, want %v", keys, wantKeys)
	}
	if !proto.Equal(got.Entries["k_both"], cert("ours")) {
		t.Errorf("k_both: theirs's row replaced ours's")
	}
	if !proto.Equal(got.Plans["p_both"], plan("k_both")) || !proto.Equal(got.Plans["p_theirs"], plan("k_theirs")) {
		t.Errorf("plans %v", got.Plans)
	}
	if out.keysAdded != 2 || out.keysCollided != 1 || out.plansAdded != 1 || out.plansCollided != 1 {
		t.Errorf("counts: keys +%d/%d collided, plans +%d/%d collided; want +2/1, +1/1",
			out.keysAdded, out.keysCollided, out.plansAdded, out.plansCollided)
	}
}

// TestMergeCaches_MemberRowsThreeWay: a member's row stands from the
// tree that changed it — recorded, added or deleted — and a member
// changed identically in both is no conflict.
func TestMergeCaches_MemberRowsThreeWay(t *testing.T) {
	base := &pproof.CNFCache{
		MemberDeps: map[string]*pproof.EntryList{
			"f.TheirsRecorded": deps("x"), "f.OursRecorded": deps("x"), "f.Untouched": deps("x"),
			"f.OursDeleted": deps("x"), "f.TheirsDeleted": deps("x"), "f.BothSame": deps("x"),
		},
		MemberCapabilities: map[string]*pproof.CapabilityList{"f.TheirsRecorded": capabilities()},
		RecordedMembers:    []string{"f.BothSame", "f.OursDeleted", "f.OursRecorded", "f.TheirsDeleted", "f.TheirsRecorded", "f.Untouched"},
	}
	ours := &pproof.CNFCache{
		MemberDeps: map[string]*pproof.EntryList{
			"f.TheirsRecorded": deps("x"), "f.OursRecorded": deps("y"), "f.Untouched": deps("x"),
			"f.TheirsDeleted": deps("x"), "f.BothSame": deps("z"), "f.OursAdded": deps("x"),
		},
		MemberCapabilities: map[string]*pproof.CapabilityList{"f.TheirsRecorded": capabilities()},
		RecordedMembers:    []string{"f.BothSame", "f.OursAdded", "f.OursRecorded", "f.TheirsDeleted", "f.TheirsRecorded", "f.Untouched"},
	}
	theirs := &pproof.CNFCache{
		MemberDeps: map[string]*pproof.EntryList{
			"f.TheirsRecorded": deps("y"), "f.OursRecorded": deps("x"), "f.Untouched": deps("x"),
			"f.OursDeleted": deps("x"), "f.BothSame": deps("z"), "f.TheirsAdded": deps("x"),
		},
		MemberCapabilities: map[string]*pproof.CapabilityList{
			"f.TheirsRecorded": capabilities("arith:nat"), "f.TheirsAdded": capabilities(),
		},
		MemberRows:      map[string]*pproof.RowList{"f.TheirsRecorded": rows("k_t"), "f.TheirsAdded": rows()},
		RecordedMembers: []string{"f.BothSame", "f.OursDeleted", "f.OursRecorded", "f.TheirsAdded", "f.TheirsRecorded", "f.Untouched"},
	}
	out := mergeCaches(base, ours, theirs)
	if len(out.recordedInBoth) > 0 {
		t.Fatalf("recorded in both: %v", out.recordedInBoth)
	}
	got := decode(t, out.merged)
	want := map[string][]string{
		"f.TheirsRecorded": {"y"}, "f.OursRecorded": {"y"}, "f.Untouched": {"x"},
		"f.BothSame": {"z"}, "f.OursAdded": {"x"}, "f.TheirsAdded": {"x"},
	}
	if len(got.MemberDeps) != len(want) {
		t.Errorf("member_deps %v, want the members %v", slices.Sorted(maps.Keys(got.MemberDeps)), slices.Sorted(maps.Keys(want)))
	}
	for member, names := range want {
		if row, ok := got.MemberDeps[member]; !ok || !slices.Equal(row.GetNames(), names) {
			t.Errorf("member_deps[%s] = %v, want %v", member, row.GetNames(), names)
		}
	}
	if got := got.MemberCapabilities["f.TheirsRecorded"].GetNames(); !slices.Equal(got, []string{"arith:nat"}) {
		t.Errorf("member_capabilities[f.TheirsRecorded] = %v, want theirs's", got)
	}
	if _, ok := got.MemberCapabilities["f.TheirsAdded"]; !ok {
		t.Errorf("member_capabilities lost f.TheirsAdded's empty row (measured, uses nothing)")
	}
	wantRecorded := []string{"f.BothSame", "f.OursAdded", "f.OursRecorded", "f.TheirsAdded", "f.TheirsRecorded", "f.Untouched"}
	if row := got.MemberRows["f.TheirsRecorded"]; !slices.Equal(row.GetCertificates(), []string{"k_t"}) {
		t.Errorf("member_rows[f.TheirsRecorded] = %v, want theirs's row", row)
	}
	if _, ok := got.MemberRows["f.TheirsAdded"]; !ok {
		t.Errorf("member_rows has no row for f.TheirsAdded, which theirs recorded")
	}
	if !slices.Equal(got.RecordedMembers, wantRecorded) {
		t.Errorf("recorded_members %v, want %v", got.RecordedMembers, wantRecorded)
	}
	wantFromTheirs := []string{"f.TheirsAdded", "f.TheirsDeleted", "f.TheirsRecorded"}
	if !slices.Equal(out.members, wantFromTheirs) {
		t.Errorf("members from theirs %v, want %v", out.members, wantFromTheirs)
	}
}

// TestMergeCaches_MemberChangedInBothKeepsOurs: a member whose row
// changed in both trees to different rows keeps ours's rows and is
// named once, whichever tables moved.
func TestMergeCaches_MemberChangedInBothKeepsOurs(t *testing.T) {
	base := &pproof.CNFCache{MemberDeps: map[string]*pproof.EntryList{"f.A": deps("x")}}
	ours := &pproof.CNFCache{
		MemberDeps:         map[string]*pproof.EntryList{"f.A": deps("y")},
		MemberCapabilities: map[string]*pproof.CapabilityList{"f.New": capabilities("arith:nat")},
	}
	theirs := &pproof.CNFCache{
		MemberDeps:         map[string]*pproof.EntryList{"f.A": deps("z")},
		MemberCapabilities: map[string]*pproof.CapabilityList{"f.New": capabilities()},
	}
	out := mergeCaches(base, ours, theirs)
	if want := []string{"f.A", "f.New"}; !slices.Equal(out.recordedInBoth, want) {
		t.Errorf("recorded in both %v, want %v", out.recordedInBoth, want)
	}
	got := decode(t, out.merged)
	if row := got.MemberDeps["f.A"].GetNames(); !slices.Equal(row, []string{"y"}) {
		t.Errorf("member_deps[f.A] = %v, want ours's [y]", row)
	}
	if row := got.MemberCapabilities["f.New"].GetNames(); !slices.Equal(row, []string{"arith:nat"}) {
		t.Errorf("member_capabilities[f.New] = %v, want ours's [arith:nat]", row)
	}
	if !strings.Contains(out.describe(), "recorded in both trees, ours kept, the replay is the judge: f.A, f.New") {
		t.Errorf("report: %s", out.describe())
	}
}

// TestMergeFile_Decisions: the file-level cases — nothing to bring, a
// new family copied, a family gone here and changed there (the one
// stop), and a merge that brings nothing leaving ours's bytes.
func TestMergeFile_Decisions(t *testing.T) {
	a := marshal(t, &pproof.CNFCache{Entries: map[string]*refuter.CNFRefuteProofProto{"k": cert("a")}, RecordedMembers: []string{"f.A"}})
	b := marshal(t, &pproof.CNFCache{Entries: map[string]*refuter.CNFRefuteProofProto{"k": cert("a"), "k2": cert("b")}, RecordedMembers: []string{"f.A"}})
	cases := []struct {
		name  string
		sides _Sides
		write bool
		copy  bool
		stop  bool
	}{
		{"theirs equals ours", _Sides{base: a, inBase: true, ours: b, inOurs: true, theirs: b}, false, false, false},
		{"theirs equals base", _Sides{base: a, inBase: true, ours: b, inOurs: true, theirs: a}, false, false, false},
		{"new family", _Sides{theirs: b}, true, true, false},
		{"gone here, changed there", _Sides{base: a, inBase: true, theirs: b}, false, false, true},
		{"theirs brings a key", _Sides{base: a, inBase: true, ours: a, inOurs: true, theirs: b}, true, false, false},
		{"theirs holds only what ours holds", _Sides{base: nil, inBase: true, ours: b, inOurs: true, theirs: a}, false, false, false},
		{"empty scaffold blob, first member there", _Sides{base: nil, inBase: true, ours: nil, inOurs: true, theirs: b}, true, false, false},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			out, err := mergeFile(c.sides)
			if err != nil {
				t.Fatal(err)
			}
			if out.write != c.write || out.copied != c.copy || (out.stop != "") != c.stop {
				t.Fatalf("write=%v copied=%v stop=%q; want write=%v copied=%v stop=%v",
					out.write, out.copied, out.stop, c.write, c.copy, c.stop)
			}
			if c.write && !c.copy && !bytes.Equal(out.merged, b) {
				t.Errorf("merged bytes differ from the recorder's marshal of the same cache")
			}
		})
	}
}

// rows is a member's row record naming the given certificates.
func rows(certificates ...string) *pproof.RowList {
	return &pproof.RowList{Certificates: certificates}
}

// TestLockBlob_HeldUntilReleased: the lock the merge takes on this
// tree's blob keeps another writer of its directory waiting until the
// merge releases it.
func TestLockBlob_HeldUntilReleased(t *testing.T) {
	dir := t.TempDir()
	release := lockBlob(filepath.Join(dir, "fam.cnf.pb"))
	waiting := make(chan struct{})
	acquired := make(chan error, 1)
	go func() {
		second, err := cnfblob.Lock(dir, func() { close(waiting) })
		if err == nil {
			second()
		}
		acquired <- err
	}()
	select {
	case <-waiting:
	case err := <-acquired:
		t.Fatalf("another writer took the directory the merge holds (err=%v)", err)
	case <-time.After(10 * time.Second):
		t.Fatal("the other writer neither waited nor returned")
	}
	release()
	select {
	case err := <-acquired:
		if err != nil {
			t.Fatalf("the other writer after the release: %v", err)
		}
	case <-time.After(10 * time.Second):
		t.Fatal("the other writer is still waiting after the release")
	}
}

// TestLockBlob_NoDirectoryTakesNoLock: a blob whose directory this
// tree does not have (a family deleted here) is read with no lock, so
// the merge reaches its decision on it.
func TestLockBlob_NoDirectoryTakesNoLock(t *testing.T) {
	release := lockBlob(filepath.Join(t.TempDir(), "absent", "fam.cnf.pb"))
	release()
}

// TestMergeCaches_UnfoldRowsThreeWay: a member's unfold row merges as
// its dependency row does — the tree that recorded it stands, and a row
// both trees changed to different rows is reported.
func TestMergeCaches_UnfoldRowsThreeWay(t *testing.T) {
	base := &pproof.CNFCache{MemberUnfolds: map[string]*pproof.EntryList{
		"f.TheirsRecorded": deps("d"), "f.OursRecorded": deps("d"), "f.Both": deps("d"),
	}}
	ours := &pproof.CNFCache{MemberUnfolds: map[string]*pproof.EntryList{
		"f.TheirsRecorded": deps("d"), "f.OursRecorded": deps("d", "e"), "f.Both": deps("e"),
	}}
	theirs := &pproof.CNFCache{MemberUnfolds: map[string]*pproof.EntryList{
		"f.TheirsRecorded": deps(), "f.OursRecorded": deps("d"), "f.Both": deps("g"), "f.TheirsAdded": deps("d"),
	}}
	out := mergeCaches(base, ours, theirs)
	if !slices.Equal(out.recordedInBoth, []string{"f.Both"}) {
		t.Errorf("recorded in both: %v, want f.Both", out.recordedInBoth)
	}
	got := decode(t, out.merged)
	want := map[string][]string{
		"f.TheirsRecorded": {}, "f.OursRecorded": {"d", "e"}, "f.Both": {"e"}, "f.TheirsAdded": {"d"},
	}
	if len(got.MemberUnfolds) != len(want) {
		t.Errorf("member_unfolds %v, want the members %v", slices.Sorted(maps.Keys(got.MemberUnfolds)), slices.Sorted(maps.Keys(want)))
	}
	for member, names := range want {
		if row, ok := got.MemberUnfolds[member]; !ok || !slices.Equal(row.GetNames(), names) {
			t.Errorf("member_unfolds[%s] = %v, want %v", member, row.GetNames(), names)
		}
	}
}
