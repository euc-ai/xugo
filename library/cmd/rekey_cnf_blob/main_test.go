package main

import (
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
	"time"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/cnfblob"
	"github.com/euc-ai/xugo/library/registry"
	pproof "github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// blobWithRecords is a family blob whose member records name fam.Old:
// as a member (its dependency row, capability row, row record and
// measured mark) and as a dep of fam.A — every place a rename of
// fam.Old must reach — beside one certificate the rename must not
// touch.
func blobWithRecords() *pproof.CNFCache {
	return &pproof.CNFCache{
		Entries: map[string]*refuter.CNFRefuteProofProto{"prop_cert": {}},
		MemberDeps: map[string]*pproof.EntryList{
			"fam.A":   {Names: []string{"fam.Old", "other.X"}},
			"fam.Old": {Names: []string{"other.X"}},
			"fam.C":   {Names: []string{"fam.Old", "fam.Z"}},
		},
		MemberCapabilities: map[string]*pproof.CapabilityList{
			"fam.Old": {Names: []string{"arith:nat"}},
		},
		MemberRows:      map[string]*pproof.RowList{"fam.Old": {Certificates: []string{"prop_cert"}}},
		RecordedMembers: []string{"fam.A", "fam.C", "fam.Old"},
	}
}

// TestRenameEntries_ReachesEveryRecord: a rename moves the dependency
// row, the names in other rows (re-sorted), the capability row, the
// row record and the measured mark, and leaves the certificates as
// they were.
func TestRenameEntries_ReachesEveryRecord(t *testing.T) {
	c := blobWithRecords()
	cert := proto.Clone(c.Entries["prop_cert"])
	moved, err := renameEntries(c, map[string]string{"fam.Old": "fam.B"})
	if err != nil {
		t.Fatal(err)
	}
	if moved != 6 {
		t.Errorf("moved %d names, want 6 (one row, two deps, the capability row, the row record, the measured mark)", moved)
	}
	want := map[string][]string{
		"fam.A": {"fam.B", "other.X"},
		"fam.B": {"other.X"},
		"fam.C": {"fam.B", "fam.Z"},
	}
	if len(c.MemberDeps) != len(want) {
		t.Fatalf("member_deps rows: %v", c.MemberDeps)
	}
	for member, names := range want {
		if got := c.MemberDeps[member].GetNames(); !slices.Equal(got, names) {
			t.Errorf("member_deps[%s] = %v, want %v", member, got, names)
		}
	}
	if _, ok := c.MemberCapabilities["fam.B"]; !ok || len(c.MemberCapabilities) != 1 {
		t.Errorf("member_capabilities = %v, want the row under fam.B", c.MemberCapabilities)
	}
	if row, ok := c.MemberRows["fam.B"]; !ok || len(c.MemberRows) != 1 || !slices.Equal(row.GetCertificates(), []string{"prop_cert"}) {
		t.Errorf("member_rows = %v, want fam.Old's row under fam.B", c.MemberRows)
	}
	if !slices.Equal(c.RecordedMembers, []string{"fam.A", "fam.B", "fam.C"}) {
		t.Errorf("recorded_members = %v", c.RecordedMembers)
	}
	if !proto.Equal(c.Entries["prop_cert"], cert) || len(c.Entries) != 1 {
		t.Errorf("a rename touched a certificate: %v", c.Entries)
	}
}

// TestRenameEntries_RefusesAMerge: a rename onto a name a record
// already carries would make two rows one, or put one name twice in a
// row — a merge, which the tool refuses rather than resolving.
func TestRenameEntries_RefusesAMerge(t *testing.T) {
	for _, tc := range []struct {
		onto, why string
	}{
		{"fam.A", "two rows would be fam.A"},
		{"fam.Z", "fam.Z would appear twice"},
	} {
		_, err := renameEntries(blobWithRecords(), map[string]string{"fam.Old": tc.onto})
		if err == nil || !strings.Contains(err.Error(), tc.why) {
			t.Errorf("fam.Old=%s: got %v, want an error saying %q", tc.onto, err, tc.why)
		}
	}
}

// TestRenameEntries_UntouchedBlobMovesNothing: a blob that records no
// renamed name reports nothing moved, so the tool leaves its bytes alone.
func TestRenameEntries_UntouchedBlobMovesNothing(t *testing.T) {
	moved, err := renameEntries(blobWithRecords(), map[string]string{"elsewhere.Old": "elsewhere.New"})
	if err != nil || moved != 0 {
		t.Fatalf("moved %d, err %v; want nothing", moved, err)
	}
}

// TestDropEntries_ReachesEveryRecord: dropping a deleted entry takes
// out its dependency row, its name in the other rows, its capability
// row, its row record and its measured mark, and leaves the
// certificates as they were.
func TestDropEntries_ReachesEveryRecord(t *testing.T) {
	c := blobWithRecords()
	cert := proto.Clone(c.Entries["prop_cert"])
	dropped := dropEntries(c, map[string]bool{"fam.Old": true})
	if dropped != 6 {
		t.Errorf("dropped %d names, want 6 (one row, two deps, the capability row, the row record, the measured mark)", dropped)
	}
	want := map[string][]string{
		"fam.A": {"other.X"},
		"fam.C": {"fam.Z"},
	}
	if len(c.MemberDeps) != len(want) {
		t.Fatalf("member_deps rows: %v", c.MemberDeps)
	}
	for member, names := range want {
		if got := c.MemberDeps[member].GetNames(); !slices.Equal(got, names) {
			t.Errorf("member_deps[%s] = %v, want %v", member, got, names)
		}
	}
	if len(c.MemberCapabilities) != 0 {
		t.Errorf("member_capabilities = %v, want no row", c.MemberCapabilities)
	}
	if len(c.MemberRows) != 0 {
		t.Errorf("member_rows = %v, want no row", c.MemberRows)
	}
	if !slices.Equal(c.RecordedMembers, []string{"fam.A", "fam.C"}) {
		t.Errorf("recorded_members = %v", c.RecordedMembers)
	}
	if !proto.Equal(c.Entries["prop_cert"], cert) || len(c.Entries) != 1 {
		t.Errorf("a drop touched a certificate: %v", c.Entries)
	}
}

// TestDropEntries_LeavesACiterThatReadNothingElse: a citer whose only
// recorded read was the deleted entry keeps an empty row — measured,
// reads nothing — rather than losing its measurement.
func TestDropEntries_LeavesACiterThatReadNothingElse(t *testing.T) {
	c := &pproof.CNFCache{
		MemberDeps: map[string]*pproof.EntryList{
			"fam.A": {Names: []string{"fam.Old"}},
		},
		RecordedMembers: []string{"fam.A"},
	}
	if dropped := dropEntries(c, map[string]bool{"fam.Old": true}); dropped != 1 {
		t.Fatalf("dropped %d, want 1", dropped)
	}
	row, ok := c.MemberDeps["fam.A"]
	if !ok || len(row.GetNames()) != 0 {
		t.Errorf("member_deps[fam.A] = %v (present %v), want an empty row", row.GetNames(), ok)
	}
	if !slices.Equal(c.RecordedMembers, []string{"fam.A"}) {
		t.Errorf("recorded_members = %v", c.RecordedMembers)
	}
}

// TestDropEntries_UntouchedBlobDropsNothing: a blob that records no
// dropped name reports nothing dropped, so the tool leaves its bytes
// alone.
func TestDropEntries_UntouchedBlobDropsNothing(t *testing.T) {
	c := blobWithRecords()
	before := proto.Clone(c).(*pproof.CNFCache)
	if dropped := dropEntries(c, map[string]bool{"elsewhere.Old": true}); dropped != 0 {
		t.Fatalf("dropped %d, want nothing", dropped)
	}
	if !proto.Equal(c, before) {
		t.Errorf("a drop of a name the blob does not record changed it")
	}
}

// TestFollowRekeys: a row names a moved certificate by its new key
// (re-sorted), loses a dropped one — its member is named — and keeps
// its plans; a row the re-keying does not touch stays as it is.
func TestFollowRekeys(t *testing.T) {
	c := &pproof.CNFCache{MemberRows: map[string]*pproof.RowList{
		"fam.Moved":     {Certificates: []string{"k_old", "k_same"}, Plans: []string{"p"}},
		"fam.Lost":      {Certificates: []string{"k_gone", "k_same"}},
		"fam.Untouched": {Certificates: []string{"k_same"}},
	}}
	lost := followRekeys(c, map[string]string{"k_old": "k_new"}, map[string]bool{"k_gone": true})
	if !slices.Equal(lost, []string{"fam.Lost"}) {
		t.Errorf("lost %v, want [fam.Lost]", lost)
	}
	want := map[string]*pproof.RowList{
		"fam.Moved":     {Certificates: []string{"k_new", "k_same"}, Plans: []string{"p"}},
		"fam.Lost":      {Certificates: []string{"k_same"}},
		"fam.Untouched": {Certificates: []string{"k_same"}},
	}
	for member, row := range want {
		if got := c.MemberRows[member]; !slices.Equal(got.GetCertificates(), row.Certificates) || !slices.Equal(got.GetPlans(), row.Plans) {
			t.Errorf("member_rows[%s] = %v, want %v", member, got, row)
		}
	}
}

// TestRenameEntriesInBlob_WaitsForTheWriterAndReadsItsBlob: a rename
// started while another writer holds the blob's directory waits for it,
// and renames in the blob that writer left: the name the writer added
// while the rename waited is carried too, and the writer's row is not
// written over.
func TestRenameEntriesInBlob_WaitsForTheWriterAndReadsItsBlob(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "fam.cnf.pb")
	writeBlob(path, blobWithRecords())

	release, err := cnfblob.Lock(dir, func() { t.Fatal("the first writer waited on a free directory") })
	if err != nil {
		t.Fatal(err)
	}
	done := make(chan struct{})
	go func() {
		renameEntriesInBlob(path, map[string]string{"fam.Old": "fam.B"})
		close(done)
	}()
	select {
	case <-done:
		t.Fatal("the rename ran while another writer held the blob")
	case <-time.After(300 * time.Millisecond):
	}
	recorded := blobWithRecords()
	recorded.MemberDeps["fam.D"] = &pproof.EntryList{Names: []string{"fam.Old"}}
	writeBlob(path, recorded)
	release()
	select {
	case <-done:
	case <-time.After(10 * time.Second):
		t.Fatal("the rename is still waiting after the release")
	}

	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	var got pproof.CNFCache
	if err := proto.Unmarshal(raw, &got); err != nil {
		t.Fatal(err)
	}
	row := got.MemberDeps["fam.D"]
	if row == nil {
		t.Fatalf("the row the other writer added is gone: %v", got.MemberDeps)
	}
	if !slices.Equal(row.Names, []string{"fam.B"}) {
		t.Errorf("fam.D reads %v, want the renamed fam.B", row.Names)
	}
	if _, stale := got.MemberDeps["fam.Old"]; stale {
		t.Errorf("fam.Old's row is still under its old name: %v", got.MemberDeps)
	}
}

// TestRenameAndDropEntries_ReachTheUnfoldRows: the unfold rows name
// entries as the dependency rows do, so a rename moves a member's row
// and the name in every other row, and a drop takes both out.
func TestRenameAndDropEntries_ReachTheUnfoldRows(t *testing.T) {
	c := &pproof.CNFCache{MemberUnfolds: map[string]*pproof.EntryList{
		"fam.A":   {Names: []string{"fam.Old", "other.Def"}},
		"fam.Old": {Names: []string{"other.Def"}},
	}}
	moved, err := renameEntries(c, map[string]string{"fam.Old": "fam.B"})
	if err != nil {
		t.Fatal(err)
	}
	if moved != 2 {
		t.Errorf("moved %d names, want 2 (one row, one name in another)", moved)
	}
	for member, names := range map[string][]string{"fam.A": {"fam.B", "other.Def"}, "fam.B": {"other.Def"}} {
		if got := c.MemberUnfolds[member].GetNames(); !slices.Equal(got, names) {
			t.Errorf("after the rename member_unfolds[%s] = %v, want %v", member, got, names)
		}
	}
	if _, stale := c.MemberUnfolds["fam.Old"]; stale {
		t.Errorf("fam.Old's row is still under its old name: %v", c.MemberUnfolds)
	}
	if dropped := dropEntries(c, map[string]bool{"fam.B": true}); dropped != 2 {
		t.Errorf("dropped %d names, want 2 (fam.B's row, and fam.B in fam.A's)", dropped)
	}
	if got := c.MemberUnfolds["fam.A"].GetNames(); !slices.Equal(got, []string{"other.Def"}) || len(c.MemberUnfolds) != 1 {
		t.Errorf("after the drop member_unfolds = %v, want fam.A: [other.Def]", c.MemberUnfolds)
	}
}

// TestRekeyBlob_WritesTheExactKeys: the re-keying writes the blob's
// exact-key table from the refute props it builds. A certificate filed
// under a key that is not its own is moved to its key and named there
// by the key of its stored goal's cold refute prop; a row left from
// before, naming nothing the blob holds, is gone; and a second run
// changes no byte.
func TestRekeyBlob_WritesTheExactKeys(t *testing.T) {
	a := core.TypeA()
	x, z := ext.Var("x", a), ext.Var("z", a)
	m := ext.Var("m", core.MakeFun(a, core.MakeFun(a, a)))
	Q := ext.Var("Q", core.MakeFun(a, core.TypeBool()))
	xz, zx := m.Apply(x, z), m.Apply(z, x)
	goal := prop.MakeProp(Q.Apply(xz).Core(), Q.Apply(zx).Core(), xz.Eq(zx).Core())

	live := refuter.CreateRefuterFromPreNormalized(t.Context(), goal, pproof.NewCNFNormalizeCache())
	if live == nil {
		t.Fatal("the fixture's refuter does not build")
	}
	certificate := live.Prove(t.Context())
	if certificate == nil {
		t.Fatal("the fixture's goal is not refuted")
	}
	load := registry.GetConstMetaManager().LoadConstMeta
	stored, _ := ext.NewPoolReader(certificate.Pool, load).Prop(certificate.Goal)
	cache := pproof.NewCNFNormalizeCache()
	cold := refuter.CreateRefuterFromPreNormalized(t.Context(), stored, cache)
	wantExact := string(cold.CNF().RefuteProp().AlphaKey())
	wantKey := string(cold.KeyForm(t.Context(), cache).AlphaKey())

	path := filepath.Join(t.TempDir(), "fam.cnf.pb")
	writeBlob(path, &pproof.CNFCache{
		Entries:    map[string]*refuter.CNFRefuteProofProto{"prop_not_its_key": certificate},
		ExactKeys:  map[string]string{"prop_left_behind": "prop_gone"},
		MemberRows: map[string]*pproof.RowList{"fam.A": {Certificates: []string{"prop_not_its_key"}}},
	})
	read := func() (*pproof.CNFCache, []byte) {
		raw, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		var got pproof.CNFCache
		if err := proto.Unmarshal(raw, &got); err != nil {
			t.Fatal(err)
		}
		return &got, raw
	}

	rekeyBlob(path, load)
	got, first := read()
	if keys := slices.Collect(maps.Keys(got.Entries)); !slices.Equal(keys, []string{wantKey}) {
		t.Fatalf("certificates under %v, want the one under its own key %s", keys, wantKey)
	}
	if want := map[string]string{wantExact: wantKey}; !maps.Equal(got.ExactKeys, want) {
		t.Errorf("exact keys %v, want %v", got.ExactKeys, want)
	}
	if row := got.MemberRows["fam.A"].GetCertificates(); !slices.Equal(row, []string{wantKey}) {
		t.Errorf("the member's row names %v, want the moved certificate %s", row, wantKey)
	}

	rekeyBlob(path, load)
	if _, second := read(); !slices.Equal(first, second) {
		t.Errorf("a second re-keying changed the blob")
	}
}
