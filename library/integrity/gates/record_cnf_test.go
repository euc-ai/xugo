// record_cnf_test.go — the CNF recorder (hand-written framework,
// committed; the curate agent runs it, never edits it).
//
// Why this exists: live `CnfRefute()` is inherently nondeterministic
// (parallel clause-space search under CPU contention — measured ~25% flake
// on a 13-refute proof), so a proof must replay from RECORDED
// refute protos, never live. A proof's refutes are recorded
// once, here, and frozen.
//
// # Family recording (ONE shared pb per family package)
//
// This is the ONLY recording path, and a recording is a warm merge:
// existing keys replay from the blob and only new keys run live. A
// cold re-record of everything would have to re-derive refutations
// that no longer close live, which freezes a file against key-changing
// edits.
//
// A family member never carries its own pb — the family package embeds a
// single <family>/<family>.cnf.pb (installed env-side by the replay
// harness) and this recorder MERGES into it:
//
// - XUGO_RECORD_FAMILY_CNF=<NAME> where <NAME> is a family member:
// the member runs with the family pb installed WARM but NON-STRICT
// (old keys replay deterministically, new keys run live and get
// captured), and the union of {existing pb} ∪ {captured} is written
// back to <family>/<family>.cnf.pb. No comment-out step, no embed
// wiring — the family scaffolding did that once. Re-run `go test`
// to re-embed (the running binary keeps the old blob). Before it
// decides whether to write, the member replays strictly against the
// blob it leaves, under every check XUGO_REPLAY_ONE makes
// (verifyRecordedMember) — a recording that passes is the member's
// replay, and one that does not writes nothing.
//
// - XUGO_FAMILY_CNF_GC=<family>: consolidation-phase hygiene —
// the union semantics above only ever ADD keys, so re-curations
// leave retired keys (removed walks, replaced refutes) in the blob
// forever. Every recording also writes the member's ROW — the
// certificate and plan keys its run touched (member_rows, below) —
// so a GC runs no proof: it keeps exactly the rows some member's row
// names, with every member's capability, dependency and row records,
// and drops the rest. A member the blob holds no record for (no row,
// a row naming a row the blob lacks, no capability row) is measured
// in the GC: it runs warm against the committed blob, as a recording
// runs, and its records are written from that run. A member that
// ran, and a member whose kept rows that run re-derived, is replayed
// strictly against the fresh bytes before they are written; the
// other members' rows are the committed bytes their last replay
// read. A GC of a family with no measured member runs every member
// once (a new family's first record); from then on a GC touches no
// proof, and the bundles are installed and warmed only when some
// member runs.
//
// Both modes hold a lock on the family's blob from their read of it to
// their write (lockFamilyPB): two lanes of one tree that record two
// members of one family at once, or a record beside a GC, run one
// after the other, and the second reads the blob the first left. A dry
// run writes nothing and waits for no one.
//
// # The member capability record (the member's declaration)
//
// Every recording also writes what the member's build was OBSERVED to
// use — arith:nat / arith:real / arith:int / int_of_real:<source> —
// into the pb's member_capabilities, keyed by member name. Nothing
// declares a capability: this record IS the member's capability edges
// in the dependency manifest (registry.RecordedCapabilities →
// dag → manifest.Build's complete graph → the policy witness), and the
// replay harness fails a build whose observed use drifts from it. An
// EMPTY entry means "measured, uses nothing"; an absent key means never
// measured. Re-record the member (or GC the family) after changing
// what its proof reaches for, then regenerate the witness.
//
// # The member dependency record (the member's dependencies)
//
// A recording also writes the entries a proved member's build READ —
// every library theorem it read by name that a corpus entry serves: a
// cite, an induction or recursion principle, a served row — into the
// pb's member_deps, keyed by member name. The member's build is served
// the whole corpus on call (newEntryEnv's library, as a session's
// corpus env binds it), so what it reads is observed, not declared:
// this record IS the member's dependencies (ProofEntry.DepEntries),
// read by the DAG, the manifest, the index and the session seam. The
// replay harness serves the member exactly its record and fails a
// build that reads an entry off it or no longer reads one on it
// (checkRecordedDeps); re-record the member after changing what its
// proof cites. A definition door's entry declares its Deps and is
// served exactly those; it has no row. The records name entries by
// their registered names, so an entry renamed in the source is carried
// into the blobs by `rekey_cnf_blob -rename-entries`, which rewrites
// member_deps, member_capabilities and recorded_members and no
// certificate.
//
// # The member unfold record (the definitions a member opens)
//
// A recording also writes the definitions a proved member's build
// OPENED — the entry defining each constant it unfolded, read off the
// member's ProofScope after its build (unfoldedDefiners) — into the
// pb's member_unfolds, keyed by member name. An Unfold reads the
// definition off the constant, so no read serves it and the dependency
// record above does not see it; a proof that opens a constant stands on
// its definition all the same, and this record IS those edges of the
// member's dependency graph (ProofEntry.DepEntries; a build is served
// ProofEntry.ServedDeps, without them). The replay harness fails a
// build whose openings drifted from the row (checkRecordedUnfolds). An
// EMPTY row means "measured, opens nothing"; a member with no row is
// measured by the next GC. The rows name entries, so
// `rekey_cnf_blob -rename-entries` carries a rename into them as it
// does into member_deps.
//
// The record of every OTHER family is read from the compiled-in blobs:
// the bundle warm-up leaves cold the fields resting on the recorded
// family by walking the DAG, whose edges the records are. A run that
// changes a bundle-backing member's reads, or a first recording of a
// family whose own entries back a bundle, may need the recorder run
// again once the written blob is compiled in.
//
// # The member row record (what the GC keeps)
//
// A recording also writes the rows the member's run touched — the
// certificate keys and the plan keys it read or wrote, the capturing
// store's set — into the pb's member_rows, keyed by member name. The
// family's live rows are the union of its members' rows, so the GC
// keeps that union and nothing else, running no proof. The replay
// harness does not hold a member to its row: the By ladder reads the
// bare key before the conditioned plan and certificate, so a replay
// can read a sibling's row in place of the member's own, and every
// row it can read is one some member's row keeps — a GC'd blob
// replays what the committed blob replayed. The one way a replay
// reads a row no row names is through a sibling's row the sibling's
// own re-record no longer holds; the scope replay after the GC misses
// there, names the member, and the member's record refreshes its row.
//
// # The recorded_members marker (why a zero-key recording still writes)
//
// Every write path stamps the recorded member name(s) into the pb's
// recorded_members list (CNFCache proto field 2 — metadata the engine's
// InstallCNFCache never looks at). The point is the empty-blob window:
// the replay harness arms strict mode (RequireCNFCacheHit) only on a
// NON-empty family blob, so while the blob is 0 bytes every refute runs
// live — nondeterministically — behind a green replay. Before the
// marker, a recorder run that captured zero refutes left the blob at
// 0 bytes, so a measured zero-key family stayed in that window forever,
// byte-identical to a never-measured one. Now the first recorder
// run — zero keys or not — makes the blob non-empty, the strict gate
// arms for every member from then on, and lint_test.go's
// TestLintFamilyPBMeasured fails any member-bearing family that has
// never recorded.
package gates

import (
	"bytes"
	"context"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"runtime/debug"
	"slices"
	"strconv"
	"strings"
	"testing"
	"time"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/cnfblob"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// envRecordFamilyCNF names the registry entry to record a .cnf.pb for.
const envRecordFamilyCNF = "XUGO_RECORD_FAMILY_CNF"

// envFamilyCNFGC names the family whose pb gets garbage-collected:
// collected to the rows its members' rows name, no proof run (see
// file header).
const envFamilyCNFGC = "XUGO_FAMILY_CNF_GC"

// envRecordCNFDryRun, set to 1 beside either recording variable, makes
// the run READ-ONLY: the member (or, under a GC, every member the GC
// measures) runs exactly as it would be recorded, the rows it touches
// are listed by leaf, the resulting blob is verified to replay — and
// nothing is written. It answers "does this member reach the refuter,
// and with which keys" and "what would a GC retire" without moving a
// blob.
const envRecordCNFDryRun = "XUGO_RECORD_CNF_DRY_RUN"

// recordCNFDryRun is envRecordCNFDryRun's value read as a boolean
// (dryRunValue). A value that is none stops the run before it reads a
// blob: a run that guessed would write a blob its caller meant to keep,
// or keep one its caller meant to write.
func recordCNFDryRun(t *testing.T) bool {
	t.Helper()
	dry, err := dryRunValue(os.Getenv(envRecordCNFDryRun))
	if err != nil {
		t.Fatalf("%s: %v", envRecordCNFDryRun, err)
	}
	return dry
}

// dryRunValue reads the dry-run switch: unset or a false value (0,
// false) is a run that writes, a true value (1, true) a dry run.
func dryRunValue(value string) (bool, error) {
	if value == "" {
		return false, nil
	}
	dry, err := strconv.ParseBool(value)
	if err != nil {
		return false, fmt.Errorf("%q is not a boolean: set it to 1 for a dry run, and leave it unset to write", value)
	}
	return dry, nil
}

// writeFamilyPB writes a verified blob to the family's pb path
// (cnfblob.Write) — unless the run is a dry run, which writes nothing.
// Reports whether it wrote.
func writeFamilyPB(path string, blob []byte, dryRun bool) (bool, error) {
	if dryRun {
		return false, nil
	}
	if err := cnfblob.Write(path, blob); err != nil {
		return false, err
	}
	return true, nil
}

// lockFamilyPB is the lock a recorder holds from its read of the
// family's blob to its write of it. A recording writes {the blob it
// read} ∪ {the rows it captured}, and a GC the rows it kept of the blob
// it read, each minutes after the read: two of them on one family in one
// tree — two lanes recording two members, a record beside a GC — would
// otherwise each write over what the other added, with nothing said
// until a replay misses the dropped rows. The second recorder waits for
// the first and reads the blob the first left. A dry run writes nothing
// and takes no lock.
func lockFamilyPB(t *testing.T, family *registry.Family) (release func()) {
	t.Helper()
	if recordCNFDryRun(t) {
		return func() {}
	}
	t0 := time.Now()
	waited := false
	release, err := cnfblob.Lock(familyDir(family), func() {
		waited = true
		t.Logf("another recorder holds family %s's blob; waiting for it to write", family.Name)
	})
	if err != nil {
		t.Fatalf("lock family %s's blob: %v", family.Name, err)
	}
	if waited {
		t.Logf("family %s's blob is free after %v", family.Name, time.Since(t0).Round(time.Second))
	}
	return release
}

// _RecorderSetup is what every run of the recorder in one process
// shares: the bundles installed and warmed for the family, and the
// corpus trust frontier (corpusFrontier). A GC prepares it once for
// the family; a member record once for its member, and the verifying
// replay that follows runs on the same one.
type _RecorderSetup struct {
	frontier func(core.Prop) bool
}

// prepareRecorder installs and warms the bundles the way the replay
// harness does (installBundles, warmBundles) and reads the trust
// frontier.
func prepareRecorder(t *testing.T) *_RecorderSetup {
	t.Helper()
	installBundles()
	frontier := corpusFrontier()
	warmBundles(t, frontier)
	return &_RecorderSetup{frontier: frontier}
}

// TestRecordFamilyCNF has three modes:
//
// - XUGO_FAMILY_CNF_GC=<family>: collect the family pb to the rows
// its members' rows name (see file header).
//
// - XUGO_RECORD_FAMILY_CNF=<name>: record that member's live CNF
// refutes and merge them into the family's shared
// <family>/<family>.cnf.pb (warm + non-strict run; see header).
//
// - either of the two with XUGO_RECORD_CNF_DRY_RUN=1: the same run,
// reported, and nothing written (envRecordCNFDryRun).
//
// - no env var (CI): self-test — assert the proof-side install guard
// still fires. Nothing is written to the tree.
func TestRecordFamilyCNF(t *testing.T) {
	if famName := os.Getenv(envFamilyCNFGC); famName != "" {
		gcFamilyCNF(t, famName)
		return
	}

	if name := os.Getenv(envRecordFamilyCNF); name != "" {
		entry, found := registry.ByName(name)
		if !found {
			t.Fatalf("XUGO_RECORD_FAMILY_CNF=%q: not in proof registry", name)
		}
		recordFamilyMemberCNF(t, entry, entry.Family())
		return
	}

	// Self-test (CI, no env var): every entry belongs to a family — the
	// retired legacy population must not silently return (a proof-side
	// InstallCNFCache would bypass the warm-merge recording path; the
	// source-level lint in lint_test.go bans the call textually, and
	// this asserts the registry-level shape).
	for _, e := range registry.All() {
		if e.Family() == nil {
			t.Errorf("entry %s has no family — the legacy flat population is retired; register via a family's family.Add", e.Name)
		}
	}
}

// familyPBPath returns the family's shared pb path relative to the
// package directory (the test cwd): <dir>/<basename(dir)>.cnf.pb,
// where dir is Family.Dir (nested tower-group families) falling back
// to Family.Name (flat families — Name == package dir basename by
// convention; registry.Family doc).
func familyPBPath(family *registry.Family) string {
	dir := familyDir(family)
	base := strings.ToLower(filepath.Base(dir))
	return filepath.Join(dir, base+".cnf.pb")
}

// currentFamilyPB reads the family pb from DISK (fresher than the
// compiled-in Family.CNF when this process already merged once),
// falling back to the embedded blob.
func currentFamilyPB(family *registry.Family) []byte {
	if b, err := os.ReadFile(familyPBPath(family)); err == nil {
		return b
	}
	return family.CNF
}

// recordFamilyMemberCNF records one family member's refutes and merges
// them into the family's shared pb: the member runs with the existing
// family pb installed warm but NON-STRICT (old keys deterministic, new
// keys live + captured), then {existing} ∪ {captured} is written back.
func recordFamilyMemberCNF(t *testing.T, e *registry.ProofEntry, family *registry.Family) {
	if e.ServedAsAxiom() {
		t.Skipf("%s is stated without a proof (a card, or the postulate): nothing refutes under it", e.Name)
	}
	// The bundles are warmed before the lock is taken: they read nothing
	// of the family's blob, and a recorder waiting behind this one waits
	// for the run alone.
	setup := prepareRecorder(t)
	defer lockFamilyPB(t, family)()
	existing := currentFamilyPB(family)
	blob, n, leaves, err := recordFamilyCNF(t, e, existing, setup)
	if err != nil {
		t.Fatalf("record %s (family %s): %v", e.Name, family.Name, err)
	}
	merged, u, err := unionCNFBlobs(existing, blob)
	if err != nil {
		t.Fatalf("merge %s into family %s pb: %v", e.Name, family.Name, err)
	}
	// Every row this member touched, by the LEAF it stands for — the
	// question a "+N new" leaves open is which leaf minted each key,
	// and the plan/certificate split does not say (a plan is charged
	// under the bare leaf, a certificate under the conditioned one).
	// Hits are named too: a member's key demand is the keys it READ,
	// which the counts above never list.
	t.Logf("leaves of %s:\n%s", e.Name, describeTouchedRows(blob, u, leaves))
	logOutsizedCertificates(t, e.Name, blob, u, leaves)
	merged, err = markRecorded(merged, e.Name)
	if err != nil {
		t.Fatalf("stamp %s into family %s recorded_members: %v", e.Name, family.Name, err)
	}
	out := familyPBPath(family)
	// Keys and plans are two channels: a member can record only plans
	// (a conditioned close whose keys the family already holds) and
	// still be load-bearing, so "+0 new" on the keys alone is not
	// "the recorder was not needed". A key the family already held
	// whose certificate this run RE-DERIVED (the warm read missed and
	// the refuter ran live) is named too: the refuter's search is not
	// deterministic, so a re-derived certificate is a different proof
	// of the same key and the blob's bytes move with it — "+0 new" and
	// a moved blob are consistent exactly when this count is not zero.
	before := blobShape(u.total-len(u.added), u.plansTotal-len(u.plansAdded), len(existing))
	after := blobShape(u.total, u.plansTotal, len(merged))
	summary := fmt.Sprintf("+%d new key(s), %d re-derived; +%d new plan(s), %d re-recorded",
		len(u.added), len(u.replaced), len(u.plansAdded), len(u.plansReplaced))
	// The member replays against the blob it leaves — written or not —
	// under every check a replay of it makes, so a recording that passes
	// is the member's replay and needs no second run.
	if verr := verifyRecordedMember(t, e, merged, setup); verr != nil {
		t.Fatalf("record %s: the merged blob does not replay the member: %v — refusing to write it", e.Name, verr)
	}
	t.Logf("replayed %s against the blob it leaves: green", e.Name)
	if bytes.Equal(merged, existing) {
		// Nothing changed: no write. A keyless member, or a member whose
		// every key hit warm, leaves the shared blob's bytes and mtime
		// alone, so a diff or a moved blob means a certificate or plan
		// actually changed.
		t.Logf("recorded %d CNF proto(s) for %s: %s — %s, unchanged: no write",
			n, e.Name, out, after)
		return
	}
	wrote, err := writeFamilyPB(out, merged, recordCNFDryRun(t))
	if err != nil {
		t.Fatalf("write %s: %v", out, err)
	}
	if !wrote {
		t.Logf("dry run: %d CNF proto(s) for %s: %s — %s would become %s; %s — nothing written",
			n, e.Name, out, before, after, summary)
		return
	}
	t.Logf("recorded %d CNF proto(s) for %s: %s — %s → %s; %s",
		n, e.Name, out, before, after, summary)
}

// blobShape is how every recorder line sizes a blob: its certificate
// keys, its plans and its bytes.
func blobShape(keys, plans, size int) string {
	return fmt.Sprintf("%d keys + %d plans (%d bytes)", keys, plans, size)
}

// gcFamilyCNF collects the family pb to the rows its members' rows
// name: each member's capability, dependency and row records are
// carried, the certificates and plans the rows name are kept, and
// every other row is dropped — no proof runs (collectMemberRows). A
// member the blob holds no record for is measured here: it runs warm
// against the committed blob, as a recording runs (recordFamilyCNF),
// and its records come from that run. A member that ran, and a member
// whose kept rows that run re-derived, is replayed strictly against
// the fresh bytes before they replace the committed blob; every other
// member's rows are the committed bytes its last replay read. After a
// GC, `go test -run TestReplayAll` re-embeds and strict-verifies the
// collected blob.
func gcFamilyCNF(t *testing.T, famName string) {
	var family *registry.Family
	for _, f := range registry.Families() {
		if f.Name == famName {
			family = f
			break
		}
	}
	if family == nil {
		t.Fatalf("XUGO_FAMILY_CNF_GC=%q: no such family", famName)
	}
	defer lockFamilyPB(t, family)()
	warm := currentFamilyPB(family)
	var before proof.CNFCache
	if err := proto.Unmarshal(warm, &before); err != nil {
		t.Fatalf("gc %s: unmarshal current pb: %v", famName, err)
	}
	var members []*registry.ProofEntry
	for _, e := range family.Entries() {
		if !e.ServedAsAxiom() { // a card has no proof: nothing to measure, nothing to stamp
			members = append(members, e)
		}
	}
	kept, unmeasured := collectMemberRows(&before, members)
	fresh, err := proto.MarshalOptions{Deterministic: true}.Marshal(kept)
	if err != nil {
		t.Fatalf("gc %s: marshal the kept rows: %v", famName, err)
	}

	// The bundles are installed and warmed only when a member runs.
	var setup *_RecorderSetup
	recorder := func() *_RecorderSetup {
		if setup == nil {
			setup = prepareRecorder(t)
		}
		return setup
	}
	ran := map[*registry.ProofEntry]bool{}
	rederived := map[string]bool{} // the kept rows a run replaced, certificate and plan keys
	noted := map[core.PropKey]core.Prop{}
	for _, e := range unmeasured {
		t.Logf("gc: the committed blob holds no record for %s; it runs for its record", e.Name)
		blob, n, leaves, err := recordFamilyCNF(t, e, warm, recorder())
		if err != nil {
			t.Fatalf("gc %s: member %s: %v", famName, e.Name, err)
		}
		maps.Copy(noted, leaves)
		var u cnfUnion
		fresh, u, err = unionCNFBlobs(fresh, blob)
		if err != nil {
			t.Fatalf("gc %s: union %s: %v", famName, e.Name, err)
		}
		for _, k := range slices.Concat(u.replaced, u.plansReplaced) {
			rederived[k] = true
		}
		ran[e] = true
		// Each row the member touched, by its leaf: its row record with
		// the leaves attached.
		t.Logf("gc: %s touched %d key(s) (+%d new to the blob, total %d; plans +%d, total %d):\n%s",
			e.Name, n, len(u.added), u.total, len(u.plansAdded), u.plansTotal, describeTouchedRows(blob, u, leaves))
	}
	// A GC accounts for EVERY member — kept, or run — so it
	// re-establishes the family's full measurement record: retired
	// members drop with their records, and the collected blob stays
	// non-empty even for an all-zero-key family (the strict-gate
	// marker; see markRecorded).
	names := make([]string, 0, len(members))
	for _, e := range members {
		names = append(names, e.Name)
	}
	if fresh, err = markRecorded(fresh, names...); err != nil {
		t.Fatalf("gc %s: stamp recorded_members: %v", famName, err)
	}

	var after proof.CNFCache
	if err := proto.Unmarshal(fresh, &after); err != nil {
		t.Fatalf("gc %s: unmarshal the collected blob: %v", famName, err)
	}
	// What the GC writes against the committed blob: a certificate the
	// committed blob lacks, or holds as a different proof, is written by
	// this run, and is held to the same size line as a member record's.
	_, written, err := unionCNFBlobs(warm, fresh)
	if err != nil {
		t.Fatalf("gc %s: compare the collected blob with the committed pb: %v", famName, err)
	}
	logOutsizedCertificates(t, famName, fresh, written, noted)
	retiredKeys := keysDropped(before.Entries, after.Entries)
	retiredPlans := keysDropped(before.Plans, after.Plans)
	out := familyPBPath(family)
	beforeShape := blobShape(len(before.Entries), len(before.Plans), len(warm))
	afterShape := blobShape(len(after.Entries), len(after.Plans), len(fresh))
	if bytes.Equal(fresh, warm) {
		t.Logf("gc: %s — %s, unchanged: no write", famName, afterShape)
		return
	}
	// A member that ran replays strictly against the bytes it leaves,
	// as a member record does, and so does a member whose kept rows a
	// run re-derived (the recorder's route is a search and the replay's
	// a lookup; verifyRecordedMember). Every other member's rows are the
	// committed bytes, which its last replay read.
	for _, e := range members {
		if !ran[e] && !rowNames(after.MemberRows[e.Name], rederived) {
			continue
		}
		if verr := verifyRecordedMember(t, e, fresh, recorder()); verr != nil {
			t.Fatalf("gc %s: the collected blob does not replay at member %s: %v — refusing to write it; "+
				"the committed blob stands (GC the family warm, or change the member's route)", famName, e.Name, verr)
		}
	}
	wrote, err := writeFamilyPB(out, fresh, recordCNFDryRun(t))
	if err != nil {
		t.Fatalf("write %s: %v", out, err)
	}
	verb := "→"
	if !wrote {
		verb = "would become"
	}
	t.Logf("gc: %s — %s %s %s; %d member(s) ran; %d retired key(s) and %d retired plan(s) dropped",
		famName, beforeShape, verb, afterShape, len(ran), len(retiredKeys), len(retiredPlans))
	if len(retiredKeys)+len(retiredPlans) > 0 {
		var lines []string
		for _, k := range retiredKeys {
			lines = append(lines, "  retired key "+k)
		}
		for _, k := range retiredPlans {
			lines = append(lines, "  retired plan "+k)
		}
		t.Logf("gc: rows no member's row names:\n%s", strings.Join(lines, "\n"))
	}
	if !wrote {
		t.Logf("gc: dry run — nothing written")
	}
}

// collectMemberRows is the GC's arithmetic over the committed blob:
// for each member whose record the blob holds (holdsRecord), its
// capability, dependency and row records and the certificates and
// plans its row names, with the exact keys of those certificates — and
// nothing else, so a row no member's row names is retired, and so is
// every record under a name that is not a member's. The members whose
// record the blob does not hold are returned for the GC to measure.
func collectMemberRows(before *proof.CNFCache, members []*registry.ProofEntry) (kept *proof.CNFCache, unmeasured []*registry.ProofEntry) {
	kept = &proof.CNFCache{
		Entries:            map[string]*refuter.CNFRefuteProofProto{},
		Plans:              map[string]*proof.ByConditionPlanProto{},
		MemberCapabilities: map[string]*proof.CapabilityList{},
		MemberDeps:         map[string]*proof.EntryList{},
		MemberUnfolds:      map[string]*proof.EntryList{},
		MemberRows:         map[string]*proof.RowList{},
	}
	for _, e := range members {
		if !holdsRecord(before, e) {
			unmeasured = append(unmeasured, e)
			continue
		}
		row := before.MemberRows[e.Name]
		for _, k := range row.GetCertificates() {
			kept.Entries[k] = before.Entries[k]
		}
		for _, k := range row.GetPlans() {
			kept.Plans[k] = before.Plans[k]
		}
		kept.MemberRows[e.Name] = row
		kept.MemberCapabilities[e.Name] = before.MemberCapabilities[e.Name]
		if list, ok := before.MemberDeps[e.Name]; ok {
			kept.MemberDeps[e.Name] = list
		}
		if list, ok := before.MemberUnfolds[e.Name]; ok {
			kept.MemberUnfolds[e.Name] = list
		}
	}
	// An exact key stays with the certificate it names and goes with it:
	// no member's row names one.
	for exact, key := range before.ExactKeys {
		if _, held := kept.Entries[key]; held {
			if kept.ExactKeys == nil {
				kept.ExactKeys = map[string]string{}
			}
			kept.ExactKeys[exact] = key
		}
	}
	return kept, unmeasured
}

// holdsRecord reports whether cache holds the records a GC keeps for a
// member without running it: its row, naming rows the cache holds; its
// capability row; and its dependency and unfold rows when its
// dependencies are recorded (a definition door's are declared).
func holdsRecord(cache *proof.CNFCache, e *registry.ProofEntry) bool {
	row, ok := cache.GetMemberRows()[e.Name]
	if !ok {
		return false
	}
	for _, k := range row.GetCertificates() {
		if _, held := cache.GetEntries()[k]; !held {
			return false
		}
	}
	for _, k := range row.GetPlans() {
		if _, held := cache.GetPlans()[k]; !held {
			return false
		}
	}
	if _, ok := cache.GetMemberCapabilities()[e.Name]; !ok {
		return false
	}
	if !e.DepsRecorded() {
		return true
	}
	if _, ok := cache.GetMemberDeps()[e.Name]; !ok {
		return false
	}
	_, ok = cache.GetMemberUnfolds()[e.Name]
	return ok
}

// rowNames reports whether row names a key of keys.
func rowNames(row *proof.RowList, keys map[string]bool) bool {
	for _, k := range slices.Concat(row.GetCertificates(), row.GetPlans()) {
		if keys[k] {
			return true
		}
	}
	return false
}

// keysDropped lists, sorted, the keys of before that after lacks.
func keysDropped[R any](before, after map[string]R) []string {
	var dropped []string
	for k := range before {
		if _, kept := after[k]; !kept {
			dropped = append(dropped, k)
		}
	}
	slices.Sort(dropped)
	return dropped
}

// cnfUnion is unionCNFBlobs' count of what the overlay did to the
// base, per channel: rows new to the base, rows the base already held
// whose proto the overlay REPLACED with a different one (a re-derived
// certificate, a re-recorded plan), and the totals after the merge.
type cnfUnion struct {
	added, replaced           []string // sorted certificate keys
	plansAdded, plansReplaced []string // sorted plan keys
	total, plansTotal         int
}

// describeTouchedRows lists blob's rows one per line — `new` / `re-derived`
// / `hit` for a certificate key, `new plan` / `re-recorded plan` / `hit
// plan` for a plan key, per what the union did with it — each followed by
// its serialized size and the leaf goal the run noted for it (the sequent
// that reached resolution for a certificate, the bare working leaf for a
// plan), or `(leaf not noted)` for a row the capture saw without a goal
// (the α-variant scan).
func describeTouchedRows(blob []byte, u cnfUnion, leaves map[core.PropKey]core.Prop) string {
	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		return fmt.Sprintf("  (unmarshal: %v)", err)
	}
	var lines []string
	for _, k := range slices.Sorted(maps.Keys(cache.Entries)) {
		lines = append(lines, fmt.Sprintf("  %s key %s (%d bytes) ← %s",
			certificateKind(u, k), k, proto.Size(cache.Entries[k]), leafText(leaves, k)))
	}
	for _, k := range slices.Sorted(maps.Keys(cache.Plans)) {
		kind := "hit"
		switch {
		case slices.Contains(u.plansAdded, k):
			kind = "new"
		case slices.Contains(u.plansReplaced, k):
			kind = "re-recorded"
		}
		lines = append(lines, fmt.Sprintf("  %s plan %s (%d bytes) ← %s",
			kind, k, proto.Size(cache.Plans[k]), leafText(leaves, k)))
	}
	if len(lines) == 0 {
		return "  (no rows touched)"
	}
	return strings.Join(lines, "\n")
}

// rowsOf is the row record of a run whose touched rows are cache: its
// certificate keys and its plan keys, each sorted (the deterministic
// marshal keeps a repeated field in list order).
func rowsOf(cache *proof.CNFCache) *proof.RowList {
	return &proof.RowList{
		Certificates: slices.Sorted(maps.Keys(cache.Entries)),
		Plans:        slices.Sorted(maps.Keys(cache.Plans)),
	}
}

// certificateKind is what the union did with certificate key k: `new`
// to the base, `re-derived` over a different proof the base held, or a
// `hit` that left the base's proof as it was.
func certificateKind(u cnfUnion, k string) string {
	switch {
	case slices.Contains(u.added, k):
		return "new"
	case slices.Contains(u.replaced, k):
		return "re-derived"
	}
	return "hit"
}

// leafText prints the leaf goal the run noted for row k on one line —
// a sequent prints its hyps on their own lines, and a grep for the key
// must return the leaf with it — or `(leaf not noted)`.
func leafText(leaves map[core.PropKey]core.Prop, k string) string {
	if g, ok := leaves[core.PropKey(k)]; ok {
		return strings.Join(strings.Fields(prop.PrintProp(g)), " ")
	}
	return "(leaf not noted)"
}

// A certificate's bytes are live memory in the serve and in every
// replay of its family, and nothing but its size shows what a close
// cost, so the recorder holds each certificate it writes to two lines.
//
// certificateWarnBytes is where a recording names a certificate it
// writes — new to the blob, or re-derived over the one the blob held —
// as outsized. A certificate is typically a kilobyte or two and nearly
// all stay within tens of kilobytes; one above 256 KB is an outlier by
// two orders of magnitude, and its leaf is worth re-reading for a
// smaller close. The few standing certificates above the line are named
// too, whenever a run writes them again, and only then: a hit is the
// committed blob's own bytes and is never named.
//
// certificateCeilingBytes is the size no certificate in a committed
// blob exceeds: TestLintCertificateSize fails a family blob that holds
// one, and every certificate the blobs hold sits under it. The ceiling
// is a gate and not only a warning because the warning is one log line
// in a member's whole recording, which a session can read past; the
// warning is the gate's early word, printed while the leaf is in front
// of its author. A certificate between the two lines lands, named.
const (
	certificateWarnBytes    = 256 << 10
	certificateCeilingBytes = 1 << 20
)

// certificatesAbove returns those of keys whose certificate in cache
// serializes to more than limit bytes, largest first, ties by key.
func certificatesAbove(cache *proof.CNFCache, keys []string, limit int) []string {
	var over []string
	for _, k := range keys {
		if proto.Size(cache.Entries[k]) > limit {
			over = append(over, k)
		}
	}
	slices.SortFunc(over, func(a, b string) int {
		if d := proto.Size(cache.Entries[b]) - proto.Size(cache.Entries[a]); d != 0 {
			return d
		}
		return strings.Compare(a, b)
	})
	return over
}

// outsizedCertificates returns one line per certificate of blob the
// union wrote (u's new and re-derived keys) above certificateWarnBytes,
// largest first, each with its size and its leaf; a certificate above
// certificateCeilingBytes says the lint fails it.
func outsizedCertificates(blob []byte, u cnfUnion, leaves map[core.PropKey]core.Prop) []string {
	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		panic(fmt.Sprintf("outsizedCertificates: unmarshal the recorder's own blob: %v", err))
	}
	var lines []string
	for _, k := range certificatesAbove(&cache, slices.Concat(u.added, u.replaced), certificateWarnBytes) {
		limit := fmt.Sprintf("above the %d-byte warning line", certificateWarnBytes)
		if proto.Size(cache.Entries[k]) > certificateCeilingBytes {
			limit = fmt.Sprintf("above the %d-byte ceiling TestLintCertificateSize fails", certificateCeilingBytes)
		}
		lines = append(lines, fmt.Sprintf("  %s key %s (%d bytes, %s) ← %s",
			certificateKind(u, k), k, proto.Size(cache.Entries[k]), limit, leafText(leaves, k)))
	}
	return lines
}

// logOutsizedCertificates logs outsizedCertificates' lines for what a
// recording of who writes, under one heading; it logs nothing when the
// recording writes no outsized certificate.
func logOutsizedCertificates(t *testing.T, who string, blob []byte, u cnfUnion, leaves map[core.PropKey]core.Prop) {
	t.Helper()
	lines := outsizedCertificates(blob, u, leaves)
	if len(lines) == 0 {
		return
	}
	t.Logf("WARNING: %s writes %d outsized certificate(s) — their bytes are live memory in the serve and in every replay; "+
		"re-read the close at each leaf:\n%s", who, len(lines), strings.Join(lines, "\n"))
}

// unionCNFBlobs merges overlay's entries into base (overlay wins on a
// shared key — same goal AlphaKey means same refutation input, and the
// fresher recording reflects the current engine). The recorded_members
// lists union too, so a merge never loses the family's measurement
// record. Returns the merged deterministic marshal and the per-channel
// counts — a replaced row is counted only when its proto differs, so a
// warm hit (the overlay carries the base's own proto back) counts as
// nothing and the merge of a run that changed nothing marshals to the
// base's own bytes.
func unionCNFBlobs(base, overlay []byte) (merged []byte, u cnfUnion, err error) {
	var b, o proof.CNFCache
	if err := proto.Unmarshal(base, &b); err != nil {
		return nil, u, fmt.Errorf("unmarshal base: %w", err)
	}
	if err := proto.Unmarshal(overlay, &o); err != nil {
		return nil, u, fmt.Errorf("unmarshal overlay: %w", err)
	}
	if b.Entries == nil {
		b.Entries = map[string]*refuter.CNFRefuteProofProto{}
	}
	for k, p := range o.Entries {
		if old, ok := b.Entries[k]; !ok {
			u.added = append(u.added, k)
		} else if !proto.Equal(old, p) {
			u.replaced = append(u.replaced, k)
		}
		b.Entries[k] = p
	}
	// Plan entries union alongside, overlay-wins for the same reason —
	// and a plan must supersede in step with the conditioned-key
	// certificate its own recording run wrote.
	for k, p := range o.Plans {
		if b.Plans == nil {
			b.Plans = map[string]*proof.ByConditionPlanProto{}
		}
		if old, ok := b.Plans[k]; !ok {
			u.plansAdded = append(u.plansAdded, k)
		} else if !proto.Equal(old, p) {
			u.plansReplaced = append(u.plansReplaced, k)
		}
		b.Plans[k] = p
	}
	// The exact keys union with the certificates they name, overlay-wins:
	// the overlay's row names the certificate its own run stored.
	for exact, key := range o.ExactKeys {
		if b.ExactKeys == nil {
			b.ExactKeys = map[string]string{}
		}
		b.ExactKeys[exact] = key
	}
	slices.Sort(u.added)
	slices.Sort(u.replaced)
	slices.Sort(u.plansAdded)
	slices.Sort(u.plansReplaced)
	b.RecordedMembers = mergeRecordedMembers(b.RecordedMembers, o.RecordedMembers...)
	// A member's capability, dependency and row records likewise
	// supersede: the overlay is the fresher observation of that
	// member's build.
	for name, list := range o.MemberCapabilities {
		if b.MemberCapabilities == nil {
			b.MemberCapabilities = map[string]*proof.CapabilityList{}
		}
		b.MemberCapabilities[name] = list
	}
	for name, list := range o.MemberDeps {
		if b.MemberDeps == nil {
			b.MemberDeps = map[string]*proof.EntryList{}
		}
		b.MemberDeps[name] = list
	}
	for name, list := range o.MemberUnfolds {
		if b.MemberUnfolds == nil {
			b.MemberUnfolds = map[string]*proof.EntryList{}
		}
		b.MemberUnfolds[name] = list
	}
	for name, list := range o.MemberRows {
		if b.MemberRows == nil {
			b.MemberRows = map[string]*proof.RowList{}
		}
		b.MemberRows[name] = list
	}
	// Deterministic marshal sorts the entries map's keys so re-recording
	// an unchanged proof produces byte-identical .cnf.pb output (the map
	// otherwise iterates in random order, polluting git diffs). Mirrors
	// emit_proofs' cnf.pb marshal.
	merged, err = proto.MarshalOptions{Deterministic: true}.Marshal(&b)
	if err != nil {
		return nil, u, fmt.Errorf("marshal merged CNFCache: %w", err)
	}
	u.total, u.plansTotal = len(b.Entries), len(b.Plans)
	return merged, u, nil
}

// mergeRecordedMembers returns the sorted union of the two name lists
// (sorted-unique is what keeps the deterministic marshal byte-stable —
// repeated fields marshal in list order).
func mergeRecordedMembers(existing []string, names ...string) []string {
	set := make(map[string]bool, len(existing)+len(names))
	for _, n := range existing {
		set[n] = true
	}
	for _, n := range names {
		set[n] = true
	}
	out := make([]string, 0, len(set))
	for n := range set {
		out = append(out, n)
	}
	slices.Sort(out)
	return out
}

// markRecorded stamps names into blob's recorded_members list. This is
// what makes a zero-refute recording DURABLE: the blob leaves 0 bytes
// on the first recorder run whether or not any key was captured, so the
// replay harness's strict gate arms and "measured, zero keys" stops
// being byte-identical to "never measured".
func markRecorded(blob []byte, names ...string) ([]byte, error) {
	var c proof.CNFCache
	if err := proto.Unmarshal(blob, &c); err != nil {
		return nil, fmt.Errorf("unmarshal for recorded_members stamp: %w", err)
	}
	c.RecordedMembers = mergeRecordedMembers(c.RecordedMembers, names...)
	out, err := proto.MarshalOptions{Deterministic: true}.Marshal(&c)
	if err != nil {
		return nil, fmt.Errorf("marshal for recorded_members stamp: %w", err)
	}
	return out, nil
}

// verifyRecordedMember replays e strictly against blob — the bytes the
// recorder is about to write — under every check a replay of the one
// member makes (replayOne): the Key minted and the built theorem the
// entry's own statement, every refute a cache hit, no divergence
// whistle, the capability use and the entries read what the blob
// records for e, and what the certificates assume within those edges.
// The recorder's route is a search and the replay's a
// lookup, and the two can differ: a cold record can choose conditioning
// plans the merged driver cannot finish within its breadth backstop at
// replay, and a member whose recorded key the current engine cannot
// re-derive fails the record outright. They are also held to different
// things: a search a whistle cut does not stop goes on to its close and
// records its rows, and the replay is held to no cut — that refusal
// describes each cut where it fired (openWhistleGate).
// A blob that does not replay is refused HERE, at the write, instead of
// one whole-corpus replay later; a blob that does is a replay of e.
func verifyRecordedMember(t *testing.T, e *registry.ProofEntry, blob []byte, setup *_RecorderSetup) (err error) {
	var lib *_EntryLibrary
	defer func() {
		if r := recover(); r != nil {
			err = refusedReads(e, lib, fmt.Errorf("panic: %v", r))
		}
	}()
	ctx := context.Background()
	if err := checkKeyMinted(e); err != nil {
		return err
	}
	record, recorded, served := blobDeps(e, blob)
	var env *proof.ProverEnv
	env, lib = newEntryEnv(t, ctx, e, setup.frontier, served)
	env.InstallCNFCache(blob)
	env.RequireCNFCacheHit = true
	env.Scope = proof.NewProofScope(core.PropKey(e.Key))

	whistle := openWhistleGate()
	defer whistle.close()

	top, built := e.Build.Fn(env)
	certs, err := forceMember(ctx, e, top, built, setup.frontier)
	if err != nil {
		return err
	}
	if n, cuts := whistle.fired(); n > 0 {
		return fmt.Errorf("the recorded route fires the divergence whistle %d time(s) at replay:%s", n, cuts)
	}
	capabilities, measured := blobCapabilities(e, blob)
	if err := checkRecordedCapabilities(e, env.Scope.Used(), capabilities, measured); err != nil {
		return err
	}
	if err := checkRecordedDeps(e, lib, record, recorded); err != nil {
		return err
	}
	unfolds, opened := blobUnfolds(e, blob)
	if err := checkRecordedUnfolds(e, unfoldedDefiners(e, env.Scope), unfolds, opened); err != nil {
		return err
	}
	// The member's edges as the blob has them: what it is served, and
	// the definitions it opens.
	edges := slices.Clone(served.only)
	for _, name := range unfolds {
		d, ok := registry.ByName(name)
		if !ok {
			return fmt.Errorf("%s's unfold row names %s, which no entry registers", e.Name, name)
		}
		edges = append(edges, d)
	}
	return checkAssumptions(e, edges, capabilities, certs)
}

// blobUnfolds reads e's unfold row out of blob, sorted, and whether
// blob has one.
func blobUnfolds(e *registry.ProofEntry, blob []byte) ([]string, bool) {
	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		panic(fmt.Sprintf("blobUnfolds(%s): unmarshal: %v", e.Name, err))
	}
	list, ok := cache.GetMemberUnfolds()[e.Name]
	names := append([]string(nil), list.GetNames()...)
	slices.Sort(names)
	return names, ok
}

// blobCapabilities reads e's capability row out of blob, sorted, and
// whether blob has one.
func blobCapabilities(e *registry.ProofEntry, blob []byte) ([]string, bool) {
	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		panic(fmt.Sprintf("blobCapabilities(%s): unmarshal: %v", e.Name, err))
	}
	list, ok := cache.GetMemberCapabilities()[e.Name]
	names := append([]string(nil), list.GetNames()...)
	slices.Sort(names)
	return names, ok
}

// blobDeps reads e's dependency record out of blob — the bytes a
// recorder is about to write, which the compiled-in family blob does
// not hold yet — and what a replay against it serves e: the deps its
// Build constructor makes and the record, for a proved member; its
// declared Deps for any other.
func blobDeps(e *registry.ProofEntry, blob []byte) (record []string, recorded bool, served _EntryDeps) {
	if !e.DepsRecorded() {
		return nil, false, servedDeps(e)
	}
	var cache proof.CNFCache
	if err := proto.Unmarshal(blob, &cache); err != nil {
		panic(fmt.Sprintf("blobDeps(%s): unmarshal: %v", e.Name, err))
	}
	list, recorded := cache.GetMemberDeps()[e.Name]
	record = append([]string(nil), list.GetNames()...)
	seen := map[*registry.ProofEntry]bool{}
	for _, d := range e.Deps {
		if d := d.Entry(); !seen[d] {
			seen[d] = true
			served.only = append(served.only, d)
		}
	}
	for _, name := range record {
		d, ok := registry.ByName(name)
		if !ok {
			panic(fmt.Sprintf("blobDeps(%s): the record names %s, which no entry registers", e.Name, name))
		}
		if !seen[d] {
			seen[d] = true
			served.only = append(served.only, d)
		}
	}
	return record, recorded, served
}

// recordFamilyCNF runs entry's proof with live refutes allowed,
// capturing every CNF refute proof the run produces (or reads), then
// forces every section + Top bounded at the corpus trust frontier (same
// bound as the replay harness) so deferred refutes flush and the proof
// is validated end-to-end in the same run. Returns the marshaled
// CNFCache blob and the number of captured protos.
//
// warm, when non-empty, is installed as a NON-STRICT read-through cache
// before the run (the family merge mode): already-recorded keys replay
// deterministically (and land in the capture via the read hook), keys
// the cache misses run live and get captured via the write hook.
//
// Mirrors replayOne's env/dep setup; diverges only in capture
// flags (no strict mode — recording IS the live run). setup is the
// bundles and the trust frontier the caller prepared once
// (prepareRecorder): a recording run executes the same ministeps
// replay will, so it needs the same capabilities installed, by the
// same call the harness makes. The key the frontier trusts is the
// STATED form's — the form a dep's promise is declared at and the form
// its cert serves, binder names included; a proof that Skolemizes a
// dep mints names off that form, so the recorder and the harness must
// trust the same one or refutes recorded here stop closing there.
func recordFamilyCNF(t *testing.T, e *registry.ProofEntry, warm []byte, setup *_RecorderSetup) (blob []byte, captured int, leaves map[core.PropKey]core.Prop, err error) {
	var lib *_EntryLibrary
	defer func() {
		if r := recover(); r != nil {
			// Keep the stack — see replayOne's matching recover.
			err = refusedReads(e, lib, fmt.Errorf("panic: %v\n%s", r, debug.Stack()))
		}
	}()
	ctx := context.Background()

	// The replay harness's env, by the same constructor: deps in a
	// throwaway env, certs transferred, the induction principles the
	// corpus's (newEntryEnv says why it must be the same one). A proved
	// member is served the whole corpus, and what its build reads is
	// its dependency record; a definition door's entry is served its
	// declared Deps.
	var env *proof.ProverEnv
	env, lib = newEntryEnv(t, ctx, e, setup.frontier, buildDeps(e))

	// Family merge mode: warm cache first (so the capture read-hook below
	// wraps it and old-key hits land in the capture too), then DROP the
	// strict flag the install set — new keys must run live, that's the
	// point of recording.
	if len(warm) > 0 {
		env.InstallCNFCache(warm)
		env.RequireCNFCacheHit = false
	}

	// Capture every row the run writes (a live refute persists its
	// certificate; a fresh grounding search (the manual's S4) its plan) or
	// reads (a warm-cache hit is still part of this proof's refute set) —
	// both tables, one capture (proof.CapturingCNFStore, the same one
	// emit's CollectCNFCache uses). The capture's keys are the member's
	// row record (rowsOf), and the GC keeps what the rows name.
	if env.ProofService == nil {
		env.ProofService = &proof.ProofService{}
	}
	capture := proof.NewCapturingCNFStore(env.ProofService.CNFStore)
	env.ProofService.CNFStore = capture

	// Arm proof identity from the entry (Builds read it via
	// NewScriptForEntry). The scope also OBSERVES the capabilities the
	// build uses; the recording writes them as the member's record.
	scope := proof.NewProofScope(core.PropKey(e.Key))
	env.Scope = scope

	// The economy audit: the recorder is the one place recording IS the
	// live run, so it is the audit's one wirer. Findings are lint-style
	// messages naming the honest spelling — nothing about the recording
	// or the member text changes here; applying a finding stays an
	// authored edit.
	auditFindings := 0
	env.ByAuditReport = func(finding string) {
		auditFindings++
		t.Logf("S7 audit [%s]: %s", e.Name, finding)
	}
	defer func() {
		if auditFindings > 0 {
			t.Logf("S7 audit [%s]: %d finding(s) — the honest spellings above are authored edits, "+
				"re-record + GC after applying them", e.Name, auditFindings)
		}
	}()

	top, builtProof := e.Build.Fn(env)
	dumpProofTree(t, builtProof)

	// A builtProof that installs a CNF cache (its own embedded pb, or a
	// generated.CnfCache_<NAME> borrow) flips the env strict at Build
	// time — its refutes were served from that cache, not run live, so
	// there is nothing new to record. Re-recording such a builtProof means
	// temporarily commenting out its InstallCNFCache line (see the
	// recipe in the file header). Family members never self-install
	// (the harness owns their install), so tripping this guard on a
	// family member means the member's Build wrongly calls
	// InstallCNFCache — remove the call.
	if env.RequireCNFCacheHit {
		return nil, 0, nil, fmt.Errorf(
			"builtProof %s installs a CNF cache during Build (strict mode is on) — "+
				"recording applies to live-refute proofs; comment out its "+
				"InstallCNFCache line to re-record", e.Name)
	}

	// Force everything as the replay harness does (forceMember: bounded
	// at the corpus frontier, excluding self) so lazily-deferred refutes
	// flush into the capture and the builtProof is validated in the same
	// run.
	if _, err := forceMember(ctx, e, top, builtProof, setup.frontier); err != nil {
		return nil, 0, nil, err
	}

	touched := capture.Captured()
	cache := touched.Cache()
	// The member's observed capability use IS its declaration: the
	// dependency manifest reads it from here as the member's capability
	// edges, and the replay harness fails a build whose use drifts from
	// it. A member that used nothing gets an EMPTY record — "measured,
	// none" is a fact, "never measured" is the absent key.
	if cache.MemberCapabilities == nil {
		cache.MemberCapabilities = map[string]*proof.CapabilityList{}
	}
	cache.MemberCapabilities[e.Name] = &proof.CapabilityList{Names: scope.Used()}
	// Likewise the entries its build read ARE its dependencies: the
	// registry reads them from here (ProofEntry.DepEntries), and the
	// replay harness serves exactly these and fails a build that reads
	// off them. A member that reads nothing gets an EMPTY record. A
	// definition door's entry declares its Deps and gets no row; it was
	// served exactly those, and a read off them fails here.
	if e.DepsRecorded() {
		if cache.MemberDeps == nil {
			cache.MemberDeps = map[string]*proof.EntryList{}
		}
		cache.MemberDeps[e.Name] = &proof.EntryList{Names: lib.Read()}
		// And the definitions its build opened are edges of the same
		// graph: a proof that unfolds a constant stands on the entry
		// that defines it, which no read serves it. A member that opens
		// nothing gets an EMPTY record.
		cache.MemberUnfolds = map[string]*proof.EntryList{e.Name: {Names: unfoldedDefiners(e, scope)}}
	} else if err := refusedReads(e, lib, nil); err != nil {
		return nil, 0, nil, err
	}
	// And the rows this run touched ARE the member's rows: the GC keeps
	// the union of the members' rows and runs no proof (file header).
	cache.MemberRows = map[string]*proof.RowList{e.Name: rowsOf(cache)}
	// Deterministic marshal — see unionCNFBlobs for why.
	blob, merr := proto.MarshalOptions{Deterministic: true}.Marshal(cache)
	if merr != nil {
		return nil, 0, nil, fmt.Errorf("marshal CNFCache: %w", merr)
	}
	return blob, touched.Len(), capture.Goals(), nil
}

// TestDryRunValue: the dry-run switch is read as a boolean. Unset and 0
// write, 1 is a dry run, and a value that is neither is refused.
func TestDryRunValue(t *testing.T) {
	for value, want := range map[string]bool{"": false, "0": false, "false": false, "1": true, "true": true} {
		got, err := dryRunValue(value)
		if err != nil || got != want {
			t.Errorf("dryRunValue(%q) = %v, %v; want %v", value, got, err, want)
		}
	}
	for _, value := range []string{"yes", "off", "2", " 1"} {
		if _, err := dryRunValue(value); err == nil {
			t.Errorf("dryRunValue(%q) was read; want it refused", value)
		}
	}
}

// TestWriteFamilyPB_DryRunWritesNothing: the one place a recording
// writes a blob does not write under a dry run.
func TestWriteFamilyPB_DryRunWritesNothing(t *testing.T) {
	path := filepath.Join(t.TempDir(), "family.cnf.pb")

	wrote, err := writeFamilyPB(path, []byte("blob"), true)
	if err != nil || wrote {
		t.Fatalf("dry run: wrote=%v err=%v, want no write", wrote, err)
	}
	if _, statErr := os.Stat(path); !os.IsNotExist(statErr) {
		t.Fatalf("dry run left a file at %s", path)
	}

	wrote, err = writeFamilyPB(path, []byte("blob"), false)
	if err != nil || !wrote {
		t.Fatalf("recording: wrote=%v err=%v, want a write", wrote, err)
	}
	if got, _ := os.ReadFile(path); string(got) != "blob" {
		t.Fatalf("recording wrote %q", got)
	}
}

// TestOutsizedCertificatesNamed: a recording names every certificate it
// writes above the warning line — new or re-derived — with its size and
// leaf, largest first, and the one above the ceiling as the lint's;
// a certificate under the line, and a hit of any size, go unnamed. The
// lint's selection over the same blob is the certificate above the
// ceiling alone, hit or not.
func TestOutsizedCertificatesNamed(t *testing.T) {
	sized := func(n int) *refuter.CNFRefuteProofProto {
		return &refuter.CNFRefuteProofProto{Pool: &ext.PoolProto{Strings: []string{strings.Repeat("x", n)}}}
	}
	cache := &proof.CNFCache{Entries: map[string]*refuter.CNFRefuteProofProto{
		"prop_small":     sized(certificateWarnBytes / 4),
		"prop_warned":    sized(certificateWarnBytes),
		"prop_rederived": sized(certificateWarnBytes * 2),
		"prop_ceiling":   sized(certificateCeilingBytes),
		"prop_hit":       sized(certificateCeilingBytes * 2),
	}}
	blob, err := proto.MarshalOptions{Deterministic: true}.Marshal(cache)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	u := cnfUnion{added: []string{"prop_ceiling", "prop_small", "prop_warned"}, replaced: []string{"prop_rederived"}}
	leaves := map[core.PropKey]core.Prop{"prop_warned": dsl.MustParseProp("∀n:num. n ≤ n * n")}

	lines := outsizedCertificates(blob, u, leaves)
	want := []string{
		fmt.Sprintf("  new key prop_ceiling (%d bytes, above the %d-byte ceiling TestLintCertificateSize fails) ← (leaf not noted)",
			proto.Size(cache.Entries["prop_ceiling"]), certificateCeilingBytes),
		fmt.Sprintf("  re-derived key prop_rederived (%d bytes, above the %d-byte warning line) ← (leaf not noted)",
			proto.Size(cache.Entries["prop_rederived"]), certificateWarnBytes),
		fmt.Sprintf("  new key prop_warned (%d bytes, above the %d-byte warning line) ← %s",
			proto.Size(cache.Entries["prop_warned"]), certificateWarnBytes, leafText(leaves, "prop_warned")),
	}
	if !slices.Equal(lines, want) {
		t.Fatalf("outsized lines:\n%s\nwant:\n%s", strings.Join(lines, "\n"), strings.Join(want, "\n"))
	}
	if !strings.Contains(lines[2], "∀n") {
		t.Errorf("the warned certificate's line does not print its leaf: %s", lines[2])
	}

	if got := outsizedCertificates(blob, cnfUnion{}, leaves); len(got) != 0 {
		t.Errorf("a run that writes no certificate is warned:\n%s", strings.Join(got, "\n"))
	}

	all := slices.Sorted(maps.Keys(cache.Entries))
	if got := certificatesAbove(cache, all, certificateCeilingBytes); !slices.Equal(got, []string{"prop_hit", "prop_ceiling"}) {
		t.Errorf("the ceiling selects %v, want [prop_hit prop_ceiling]", got)
	}

	for _, row := range strings.Split(describeTouchedRows(blob, u, leaves), "\n") {
		if !strings.Contains(row, " bytes) ← ") {
			t.Errorf("a touched row prints no size: %s", row)
		}
	}
}
