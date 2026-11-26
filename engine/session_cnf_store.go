package engine

import (
	"errors"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sync"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// SessionCNFStore is the sessions' proof.CNFStore: the certificates a
// live refute mints and the conditioning plans a conditioned By
// records, persisted one file per key under the store's directory so
// that what a session closed is read back by `emit-section`'s strict
// re-run (emit.CollectCNFCache) and by `session-create {resume}`'s
// cache-only replay — across serve restarts and across the serves that
// share the data directory.
//
// Layout: cnf_proofs/<key> and cnf_plans/<key>, each file the
// marshalled proto and nothing else, and cnf_exact_keys/<exact key>,
// each file the key of the certificate the row names; a key is core's
// `prop_<hash>`, a file name as it stands. A row is written to a temporary file in
// its table's directory and renamed over its final name, so a file
// holds a whole row or does not exist: a serve killed mid-write leaves
// a `<key>.*.tmp` no reader opens, and the serves sharing the
// directory see each other's rows whole. Writes within one process
// are serialized by a mutex, which makes the certificate table's
// policy exact among the refuter's racer goroutines; two processes
// writing one key at once each leave a valid certificate, and the one
// that lands last is kept.
//
// It is a cache, not a record: a member's certificates live in its
// family's blob (<family>.cnf.pb), written by the family recorder.
// Deleting the directory costs a live re-search, and a lineage
// recorded before the deletion resumes only up to its first refute. A
// change that moves keys (Normalize) is answered by deleting the
// directory, never by re-keying it.
//
// Write policies: the certificate table keeps the smaller of two
// proofs for a key; the plan table keeps the latest (a plan must stay
// in step with the certificate its own run wrote), and so does the
// exact-key table.
type SessionCNFStore struct {
	dir string
	mu  sync.Mutex
}

var _ proof.CNFStore = (*SessionCNFStore)(nil)

const (
	cnfProofsTable    = "cnf_proofs"
	cnfPlansTable     = "cnf_plans"
	cnfExactKeysTable = "cnf_exact_keys"
)

// OpenSessionCNFStore opens (creating when absent) the store at dir.
func OpenSessionCNFStore(dir string) (*SessionCNFStore, error) {
	for _, table := range []string{cnfProofsTable, cnfPlansTable, cnfExactKeysTable} {
		if err := os.MkdirAll(filepath.Join(dir, table), 0o755); err != nil {
			return nil, fmt.Errorf("create %s in %s: %w", table, dir, err)
		}
	}
	return &SessionCNFStore{dir: dir}, nil
}

// ReadProof reads the certificate stored under key; nil when none is.
func (s *SessionCNFStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	data := s.read(cnfProofsTable, key)
	if data == nil {
		return nil
	}
	var p refuter.CNFRefuteProofProto
	s.decode(cnfProofsTable, key, data, &p)
	return &p
}

// WriteProof stores a certificate, keeping the smaller of two proofs
// for one key.
func (s *SessionCNFStore) WriteProof(key core.PropKey, p *refuter.CNFRefuteProofProto) {
	data, err := proto.Marshal(p)
	if err != nil {
		panic(fmt.Sprintf("session CNF store: encode the certificate for %s: %v", key, err))
	}
	s.write(cnfProofsTable, key, data, func(old []byte) bool { return len(data) < len(old) })
}

// ReadPlan reads the conditioning plan stored under key (the bare By
// working leaf's goal AlphaKey); nil when none is.
func (s *SessionCNFStore) ReadPlan(key core.PropKey) *proof.ByConditionPlanProto {
	data := s.read(cnfPlansTable, key)
	if data == nil {
		return nil
	}
	var plan proof.ByConditionPlanProto
	s.decode(cnfPlansTable, key, data, &plan)
	return &plan
}

// WritePlan stores a conditioning plan, latest-wins: keeping an older
// plan would pair a stale conditioning with a certificate that no
// longer exists.
func (s *SessionCNFStore) WritePlan(key core.PropKey, plan *proof.ByConditionPlanProto) {
	data, err := proto.Marshal(plan)
	if err != nil {
		panic(fmt.Sprintf("session CNF store: encode the plan for %s: %v", key, err))
	}
	s.write(cnfPlansTable, key, data, nil)
}

// ReadExactKey reads the key of the certificate stored for the refute
// prop whose own key is exact; "" when the table holds no row.
func (s *SessionCNFStore) ReadExactKey(exact core.PropKey) core.PropKey {
	return core.PropKey(s.read(cnfExactKeysTable, exact))
}

// WriteExactKey stores the row, latest-wins: it names the certificate
// the run that wrote it stored.
func (s *SessionCNFStore) WriteExactKey(exact, key core.PropKey) {
	s.write(cnfExactKeysTable, exact, []byte(key), nil)
}

// ScanProofs enumerates nothing: a full-table decode scan is not an
// inline lookup path, and the store's callers (the live prover, emit)
// run name-faithful to their recorded goals. See proof.CNFStore.
func (s *SessionCNFStore) ScanProofs(func(core.PropKey, *refuter.CNFRefuteProofProto) bool) {}

func (s *SessionCNFStore) rowPath(table string, key core.PropKey) string {
	return filepath.Join(s.dir, table, string(key))
}

// read returns the blob stored under key in table: nil when the row is
// absent, non-nil (possibly empty) when it exists. A row that cannot
// be read is not a miss — a miss would re-search and mint a second
// certificate over a store that is failing — so it panics.
func (s *SessionCNFStore) read(table string, key core.PropKey) []byte {
	data, err := os.ReadFile(s.rowPath(table, key))
	if errors.Is(err, fs.ErrNotExist) {
		return nil
	}
	if err != nil {
		panic(fmt.Sprintf("session CNF store: reading the %s row for %s failed: %v", table, key, err))
	}
	if data == nil {
		return []byte{}
	}
	return data
}

// decode unmarshals a row into m. Every row is written whole by write,
// so a row that does not decode was not written by this store: the
// panic names the file, and removing it is the repair.
func (s *SessionCNFStore) decode(table string, key core.PropKey, data []byte, m proto.Message) {
	if err := proto.Unmarshal(data, m); err != nil {
		panic(fmt.Sprintf("session CNF store: the %s row for %s (%s) does not decode: %v",
			table, key, s.rowPath(table, key), err))
	}
}

// write upserts the blob under key in table; an existing row is
// replaced only when keep, given the row's bytes, returns true (nil:
// always).
//
// A failed write panics: the step that minted the row has closed and
// reports it recorded, so a silently absent row would surface only
// later, as a strict-replay MISS at emit on exactly this key.
func (s *SessionCNFStore) write(table string, key core.PropKey, data []byte, keep func(old []byte) bool) {
	if data == nil {
		data = []byte{}
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if keep != nil {
		if old := s.read(table, key); old != nil && !keep(old) {
			return
		}
	}
	tmp, err := os.CreateTemp(filepath.Join(s.dir, table), string(key)+".*.tmp")
	if err == nil {
		_, err = tmp.Write(data)
		if closeErr := tmp.Close(); err == nil {
			err = closeErr
		}
		if err == nil {
			err = os.Rename(tmp.Name(), s.rowPath(table, key))
		}
		if err != nil {
			os.Remove(tmp.Name())
		}
	}
	if err != nil {
		panic(fmt.Sprintf("session CNF store: writing the %s row for %s failed: %v — the step that "+
			"minted it has closed, but it is NOT persisted; a later strict replay of this section "+
			"will MISS on exactly this key", table, key, err))
	}
}
