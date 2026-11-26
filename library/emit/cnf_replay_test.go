package emit

// CNF-refuter replay infrastructure for the heavy proving tests in this
// package.
//
// Background. These tests drive proof.BuildInductionProof / Searcher,
// which internally invokes prover.tryCNFRefute → refuter.Prove on many
// subgoals. The refuter is the genuinely slow component (and is gated by
// env.CnfRefuterTimeout, making the tests flaky under CPU load). CNF
// refutation is incidental — none of these tests are exercising the
// refuter algorithm itself.
//
// Strategy.
//
// - Success memo on disk. The env's CNFStore (see
// prover/proof/cnf_store.go) is a content-addressed cache for refute
// proofs backed by a gob file. When a key is present, step.go
// reconstructs the proof through the kernel and never invokes the
// live refuter. Persisted as a single gob blob under
// testdata/cnf_replay.gob.
//
// - Tiny replay-mode timeout for cache misses. The search algorithm
// also calls the refuter on many dead-end candidates that no
// amount of caching can predict — they're transient artifacts of
// candidate enumeration. Instead of caching them, we override
// env.CnfRefuterTimeout to a few milliseconds in replay mode so
// each dead-end aborts almost immediately. The tests don't care
// whether dead-ends succeed (they pass with the chosen path,
// whose refutes are in cache); they only care that dead-ends
// don't burn the per-call budget. Recording, in contrast, keeps a
// generous timeout so legitimate proofs aren't dropped.
//
// Workflow.
//
//	# Replay (default): cache is loaded from disk; cache hits skip the
//	# refuter entirely, misses abort within milliseconds.
//	go test ./library/emit/
//
//	# Record: refresh testdata after a normalization / prop-shape
//	# change invalidates existing keys. Uses a generous per-call
//	# timeout so transient CPU spikes don't drop legitimate proofs.
//	XUGO_RECORD_EMIT_CNF=1 go test ./library/emit/

import (
	"encoding/gob"
	"errors"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"sync"
	"testing"
	"time"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

const (
	cnfReplayEnvVar      = "XUGO_RECORD_EMIT_CNF"
	cnfReplayRecordValue = "1"

	// Per-call CNF refuter timeout used while recording. Bumped above
	// the fixtures' default 3s so transient CPU spikes don't drop
	// legitimate proofs. Kept modest because the recording's wall time
	// scales with both successful and unsuccessful refute attempts —
	// at 60s a single contended path can stall the whole run.
	cnfReplayRecordTimeout = 15 * time.Second

	// Per-call CNF refuter timeout used in replay mode. Set to zero so
	// every cache miss aborts on the first ctx check inside r.Prove —
	// no opportunity for hardware luck to admit a proof into a "now
	// passing" run that wouldn't pass on another machine. The
	// contract is sharpened: a test passes if and only if the cache
	// already covers every refute its chosen search path needs.
	// (Cache hits resolve via the store before the timeout context
	// is even constructed, so they're unaffected.)
	cnfReplayReplayTimeout = 0
)

// cnfReplayPath is the single on-disk file holding the success cache.
// Resolved relative to the test binary's working directory, which
// `go test` sets to the package source dir.
func cnfReplayPath() string {
	return filepath.Join("testdata", "cnf_replay.gob")
}

// cnfReplayDisk is the on-disk schema. Keys are stored as plain
// strings (core.PropKey is a defined string type that round-trips
// through gob as `string`). Values are pre-marshaled
// CNFRefuteProofProto bytes — keeping the on-disk form independent of
// the in-memory proto pointer graph makes the format trivial to
// inspect with hexdump and avoids gob needing protobuf reflection.
type cnfReplayDisk struct {
	Proofs map[string][]byte // PropKey → marshaled CNFRefuteProofProto
}

// loadCNFReplay reads the cache file off disk and unmarshals each
// blob into its proto form. Missing file is not an error — it just
// means recording has not been done yet for this package.
func loadCNFReplay(t *testing.T) map[core.PropKey]*refuter.CNFRefuteProofProto {
	t.Helper()
	out := map[core.PropKey]*refuter.CNFRefuteProofProto{}

	f, err := os.Open(cnfReplayPath())
	if err != nil {
		if errors.Is(err, fs.ErrNotExist) {
			return out
		}
		t.Fatalf("cnf replay: open %s: %v", cnfReplayPath(), err)
	}
	defer f.Close()

	var disk cnfReplayDisk
	if err := gob.NewDecoder(f).Decode(&disk); err != nil {
		t.Fatalf("cnf replay: decode %s: %v", cnfReplayPath(), err)
	}
	for k, blob := range disk.Proofs {
		var proof refuter.CNFRefuteProofProto
		if err := proto.Unmarshal(blob, &proof); err != nil {
			t.Fatalf("cnf replay: unmarshal blob for %x: %v", k, err)
		}
		out[core.PropKey(k)] = &proof
	}
	return out
}

// persistCNFReplay rewrites the cache file atomically (write a temp
// file in the same directory, then rename). Caller holds the lock
// guarding the in-memory map.
func persistCNFReplay(t *testing.T, proofs map[core.PropKey]*refuter.CNFRefuteProofProto) {
	t.Helper()
	disk := cnfReplayDisk{Proofs: make(map[string][]byte, len(proofs))}
	for k, p := range proofs {
		data, err := proto.Marshal(p)
		if err != nil {
			t.Errorf("cnf replay: marshal blob for %x: %v", string(k), err)
			return
		}
		disk.Proofs[string(k)] = data
	}

	path := cnfReplayPath()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Errorf("cnf replay: mkdir %s: %v", filepath.Dir(path), err)
		return
	}
	tmp, err := os.CreateTemp(filepath.Dir(path), filepath.Base(path)+".*.tmp")
	if err != nil {
		t.Errorf("cnf replay: create temp: %v", err)
		return
	}
	tmpPath := tmp.Name()
	cleanup := func() { _ = os.Remove(tmpPath) }
	if err := gob.NewEncoder(tmp).Encode(disk); err != nil {
		_ = tmp.Close()
		cleanup()
		t.Errorf("cnf replay: encode %s: %v", tmpPath, err)
		return
	}
	if err := tmp.Close(); err != nil {
		cleanup()
		t.Errorf("cnf replay: close %s: %v", tmpPath, err)
		return
	}
	if err := os.Rename(tmpPath, path); err != nil {
		cleanup()
		t.Errorf("cnf replay: rename %s -> %s: %v", tmpPath, path, err)
		return
	}
}

// installCNFReplay installs the file-backed success cache as env's CNF
// store so prover.tryCNFRefute hits it before invoking refuter.Prove,
// and rewrites the cache file atomically every time a new success lands
// during recording.
//
// Always overrides env.CnfRefuterTimeout: a generous bound while
// recording, a tiny one during replay so cache misses (transient
// dead-ends from the search algorithm's candidate enumeration) abort
// before they can affect wall time.
func installCNFReplay(t *testing.T, env *proof.ProverEnv) {
	t.Helper()
	if env.ProofService == nil {
		t.Fatalf("installCNFReplay: env.ProofService is nil — wire MockConstMetaService first")
	}

	recording := os.Getenv(cnfReplayEnvVar) == cnfReplayRecordValue
	if recording {
		env.CnfRefuterTimeout = cnfReplayRecordTimeout
	} else {
		env.CnfRefuterTimeout = cnfReplayReplayTimeout
	}

	store := &cnfReplayStore{
		MemoryCNFStore: proof.NewMemoryCNFStore(),
		t:              t,
		proofs:         loadCNFReplay(t),
		recording:      recording,
	}
	env.ProofService.CNFStore = store

	t.Cleanup(func() {
		store.mu.Lock()
		n := store.captured
		store.mu.Unlock()
		if n == 0 {
			return
		}
		if recording {
			t.Logf("cnf replay: recorded %d new blob(s) into %s", n, cnfReplayPath())
		} else {
			t.Logf("cnf replay: refuter ran for %d uncached goal(s); "+
				"rerun with %s=%s to refresh %s",
				n, cnfReplayEnvVar, cnfReplayRecordValue, cnfReplayPath())
		}
	})
}

// cnfReplayStore is the file-backed success cache as a proof.CNFStore:
// the certificate table is the gob file's map (first write per key
// wins, persisted while recording); the plan table is the embedded
// in-memory store — not persisted, which this non-strict harness
// tolerates (a plan miss in live mode re-runs the deterministic
// search; the certificate it then needs is in the file).
//
// One mutex over the certificate table so concurrent calls from the
// refuter or from the search algorithm's racer goroutines stay safe.
type cnfReplayStore struct {
	*proof.MemoryCNFStore
	t         *testing.T
	mu        sync.Mutex
	proofs    map[core.PropKey]*refuter.CNFRefuteProofProto
	captured  int
	recording bool
}

func (s *cnfReplayStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.proofs[key]
}

func (s *cnfReplayStore) WriteProof(key core.PropKey, proof *refuter.CNFRefuteProofProto) {
	s.mu.Lock()
	defer s.mu.Unlock()
	if _, ok := s.proofs[key]; ok {
		return
	}
	s.proofs[key] = proof
	s.captured++
	if !s.recording {
		// Replay mode is supposed to be a closed system. A new blob
		// slipping in means the cache is incomplete; we keep it in
		// memory for the rest of this run so any repeat queries within
		// the test still hit, but don't persist — that's the operator's
		// job, via the record flag.
		return
	}
	persistCNFReplay(s.t, s.proofs)
}

// ScanProofs enumerates the file's certificates in sorted key order.
func (s *cnfReplayStore) ScanProofs(yield func(core.PropKey, *refuter.CNFRefuteProofProto) bool) {
	s.mu.Lock()
	snapshot := maps.Clone(s.proofs)
	s.mu.Unlock()
	for _, k := range slices.Sorted(maps.Keys(snapshot)) {
		if !yield(k, snapshot[k]) {
			return
		}
	}
}
