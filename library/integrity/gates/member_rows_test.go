// member_rows_test.go — the member row record a recording writes and
// the family GC keeps (record_cnf_test.go, "The member row record"):
// what a GC collects from a blob by its rows, and which members it
// measures.

package gates

import (
	"maps"
	"slices"
	"testing"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// row is a member's row record over the given certificate keys and
// plan keys.
func row(certificates, plans []string) *proof.RowList {
	return &proof.RowList{Certificates: certificates, Plans: plans}
}

// TestCollectMemberRows: a GC keeps, for a member whose record the
// blob holds, its records and the rows its row names; measures a
// member with no row, one whose row names a row the blob lacks, and
// one with no capability row; and retires the rows no member's row
// names and the records of a name that is not a member's. An exact
// key stays with the certificate it names and is retired with it.
func TestCollectMemberRows(t *testing.T) {
	before := &proof.CNFCache{
		Entries: map[string]*refuter.CNFRefuteProofProto{"k_kept": {}, "k_shared": {}, "k_garbage": {}, "k_retired": {}},
		Plans:   map[string]*proof.ByConditionPlanProto{"p_kept": {}, "p_garbage": {}},
		MemberCapabilities: map[string]*proof.CapabilityList{
			"f.Kept": {Names: []string{"arith:nat"}}, "f.NoRow": {}, "f.LostRow": {}, "f.Retired": {},
		},
		MemberDeps:    map[string]*proof.EntryList{"f.Kept": {Names: []string{"g.X"}}, "f.Retired": {}},
		MemberUnfolds: map[string]*proof.EntryList{"f.Kept": {Names: []string{"g.Def"}}, "f.Retired": {}},
		MemberRows: map[string]*proof.RowList{
			"f.Kept":    row([]string{"k_kept", "k_shared"}, []string{"p_kept"}),
			"f.LostRow": row([]string{"k_shared", "k_lost"}, nil),
			"f.NoCaps":  row([]string{"k_shared"}, nil),
			"f.Retired": row([]string{"k_retired"}, nil),
		},
		RecordedMembers: []string{"f.Kept", "f.LostRow", "f.NoCaps", "f.NoRow", "f.Retired"},
		ExactKeys: map[string]string{
			"x_kept": "k_kept", "x_shared": "k_shared", "x_garbage": "k_garbage", "x_retired": "k_retired",
		},
	}
	members := []*registry.ProofEntry{{Name: "f.Kept"}, {Name: "f.NoRow"}, {Name: "f.LostRow"}, {Name: "f.NoCaps"}}
	kept, unmeasured := collectMemberRows(before, members)
	if want := map[string]string{"x_kept": "k_kept", "x_shared": "k_shared"}; !maps.Equal(kept.ExactKeys, want) {
		t.Errorf("kept exact keys %v, want those of the kept certificates %v", kept.ExactKeys, want)
	}

	var names []string
	for _, e := range unmeasured {
		names = append(names, e.Name)
	}
	if want := []string{"f.NoRow", "f.LostRow", "f.NoCaps"}; !slices.Equal(names, want) {
		t.Errorf("measured %v, want %v", names, want)
	}
	if keys := slices.Sorted(keysOf(kept.Entries)); !slices.Equal(keys, []string{"k_kept", "k_shared"}) {
		t.Errorf("kept certificates %v, want k_kept and k_shared", keys)
	}
	if keys := slices.Sorted(keysOf(kept.Plans)); !slices.Equal(keys, []string{"p_kept"}) {
		t.Errorf("kept plans %v, want p_kept", keys)
	}
	for table, got := range map[string]int{
		"member_rows": len(kept.MemberRows), "member_capabilities": len(kept.MemberCapabilities),
		"member_deps": len(kept.MemberDeps), "member_unfolds": len(kept.MemberUnfolds),
	} {
		if got != 1 {
			t.Errorf("%s keeps %d record(s), want f.Kept's alone", table, got)
		}
	}
	if !proto.Equal(kept.MemberRows["f.Kept"], before.MemberRows["f.Kept"]) ||
		!proto.Equal(kept.MemberCapabilities["f.Kept"], before.MemberCapabilities["f.Kept"]) ||
		!proto.Equal(kept.MemberDeps["f.Kept"], before.MemberDeps["f.Kept"]) ||
		!proto.Equal(kept.MemberUnfolds["f.Kept"], before.MemberUnfolds["f.Kept"]) {
		t.Errorf("f.Kept's records changed in the collection")
	}
	if dropped := keysDropped(before.Entries, kept.Entries); !slices.Equal(dropped, []string{"k_garbage", "k_retired"}) {
		t.Errorf("retired certificates %v, want k_garbage and k_retired", dropped)
	}
}

// keysOf is the keys of a map, in map order.
func keysOf[R any](m map[string]R) func(func(string) bool) {
	return func(yield func(string) bool) {
		for k := range m {
			if !yield(k) {
				return
			}
		}
	}
}

// TestRowsOf: a run's row record is its touched keys, sorted in each
// table.
func TestRowsOf(t *testing.T) {
	got := rowsOf(&proof.CNFCache{
		Entries: map[string]*refuter.CNFRefuteProofProto{"k_b": {}, "k_a": {}},
		Plans:   map[string]*proof.ByConditionPlanProto{"p_b": {}, "p_a": {}},
	})
	if !slices.Equal(got.Certificates, []string{"k_a", "k_b"}) || !slices.Equal(got.Plans, []string{"p_a", "p_b"}) {
		t.Errorf("rows %v", got)
	}
	if empty := rowsOf(&proof.CNFCache{}); len(empty.Certificates)+len(empty.Plans) != 0 {
		t.Errorf("an empty run's rows: %v", empty)
	}
}

// TestUnionCNFBlobs_RowRecordSupersedes: the overlay's row record for
// a member replaces the base's, and a member the base alone records
// keeps its row; the exact keys union the same way.
func TestUnionCNFBlobs_RowRecordSupersedes(t *testing.T) {
	marshal := func(c *proof.CNFCache) []byte {
		b, err := proto.MarshalOptions{Deterministic: true}.Marshal(c)
		if err != nil {
			t.Fatal(err)
		}
		return b
	}
	base := marshal(&proof.CNFCache{
		MemberRows: map[string]*proof.RowList{"f.A": row([]string{"k_old"}, nil), "f.B": row([]string{"k_b"}, nil)},
		ExactKeys:  map[string]string{"x_a": "k_old", "x_b": "k_b"},
	})
	overlay := marshal(&proof.CNFCache{
		MemberRows: map[string]*proof.RowList{"f.A": row([]string{"k_new"}, []string{"p"})},
		ExactKeys:  map[string]string{"x_a": "k_new"},
	})
	merged, _, err := unionCNFBlobs(base, overlay)
	if err != nil {
		t.Fatal(err)
	}
	var got proof.CNFCache
	if err := proto.Unmarshal(merged, &got); err != nil {
		t.Fatal(err)
	}
	if want := map[string]string{"x_a": "k_new", "x_b": "k_b"}; !maps.Equal(got.ExactKeys, want) {
		t.Errorf("exact keys %v, want the overlay's row over the base's %v", got.ExactKeys, want)
	}
	if a := got.MemberRows["f.A"]; !slices.Equal(a.GetCertificates(), []string{"k_new"}) || !slices.Equal(a.GetPlans(), []string{"p"}) {
		t.Errorf("f.A's row = %v, want the overlay's", a)
	}
	if b := got.MemberRows["f.B"]; !slices.Equal(b.GetCertificates(), []string{"k_b"}) {
		t.Errorf("f.B's row = %v, want the base's", b)
	}
}

// TestRowNames: a row names a key of either table, or none.
func TestRowNames(t *testing.T) {
	r := row([]string{"k"}, []string{"p"})
	if !rowNames(r, map[string]bool{"k": true}) || !rowNames(r, map[string]bool{"p": true}) {
		t.Error("a key the row names is not found")
	}
	if rowNames(r, map[string]bool{"q": true}) || rowNames(nil, map[string]bool{"k": true}) {
		t.Error("a key the row does not name is found")
	}
}
