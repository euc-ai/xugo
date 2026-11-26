package engine

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
)

// certificateOfSize returns a certificate whose encoding grows with n:
// n strings in its pool.
func certificateOfSize(n int) *refuter.CNFRefuteProofProto {
	p := &refuter.CNFRefuteProofProto{Pool: &ext.PoolProto{}}
	for i := 0; i < n; i++ {
		p.Pool.Strings = append(p.Pool.Strings, strings.Repeat("x", 8)+string(rune('a'+i%26)))
	}
	return p
}

func planWithReplaced(replaced ...uint32) *proof.ByConditionPlanProto {
	return &proof.ByConditionPlanProto{Replaced: replaced}
}

func openStore(t *testing.T, dir string) *SessionCNFStore {
	t.Helper()
	s, err := OpenSessionCNFStore(dir)
	require.NoError(t, err)
	return s
}

func rowFiles(t *testing.T, dir, table string) []string {
	t.Helper()
	entries, err := os.ReadDir(filepath.Join(dir, table))
	require.NoError(t, err)
	var names []string
	for _, e := range entries {
		names = append(names, e.Name())
	}
	return names
}

func TestSessionCNFStore_ReadsBackWhatItWrote(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cnf_cache")
	s := openStore(t, dir)
	const key = core.PropKey("prop_0123456789abcdef")

	require.Nil(t, s.ReadProof(key), "a key never written reads nil")
	require.Nil(t, s.ReadPlan(key))

	s.WriteProof(key, certificateOfSize(3))
	s.WritePlan(key, planWithReplaced(1, 2))
	require.Equal(t, certificateOfSize(3).Pool.Strings, s.ReadProof(key).Pool.Strings)
	require.Equal(t, []uint32{1, 2}, s.ReadPlan(key).Replaced)

	// The row is the marshalled proto and nothing else, under its key.
	require.Equal(t, []string{string(key)}, rowFiles(t, dir, cnfProofsTable), "one row, no temporary file left")
	require.Equal(t, []string{string(key)}, rowFiles(t, dir, cnfPlansTable))

	// An empty message is a row that exists, not a miss.
	const empty = core.PropKey("prop_fedcba9876543210")
	s.WriteProof(empty, &refuter.CNFRefuteProofProto{})
	require.NotNil(t, s.ReadProof(empty))

	// An exact key names its certificate's key, in a table of its own,
	// and the latest write stands.
	const exact = core.PropKey("prop_00000000000000aa")
	require.Empty(t, s.ReadExactKey(exact), "an exact key never written names nothing")
	s.WriteExactKey(exact, empty)
	s.WriteExactKey(exact, key)
	require.Equal(t, key, s.ReadExactKey(exact))
	require.Equal(t, []string{string(exact)}, rowFiles(t, dir, cnfExactKeysTable))
	require.Equal(t, key, openStore(t, dir).ReadExactKey(exact), "a second store on the directory reads the row")
}

func TestSessionCNFStore_KeepsTheSmallerCertificateAndTheLatestPlan(t *testing.T) {
	s := openStore(t, filepath.Join(t.TempDir(), "cnf_cache"))
	const key = core.PropKey("prop_0123456789abcdef")

	s.WriteProof(key, certificateOfSize(5))
	s.WriteProof(key, certificateOfSize(2))
	require.Len(t, s.ReadProof(key).Pool.Strings, 2, "the smaller replaces the larger")
	s.WriteProof(key, certificateOfSize(5))
	require.Len(t, s.ReadProof(key).Pool.Strings, 2, "the larger does not replace the smaller")
	s.WriteProof(key, certificateOfSize(2))
	require.Len(t, s.ReadProof(key).Pool.Strings, 2, "an equal size is not a replacement")

	s.WritePlan(key, planWithReplaced(1, 2, 3))
	s.WritePlan(key, planWithReplaced(9))
	require.Equal(t, []uint32{9}, s.ReadPlan(key).Replaced, "the latest plan wins, whatever its size")
}

// Two serves on one data directory open two stores on one directory:
// a row one writes the other reads, and the certificate policy holds
// across them.
func TestSessionCNFStore_TwoStoresShareOneDirectory(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cnf_cache")
	a, b := openStore(t, dir), openStore(t, dir)
	const key = core.PropKey("prop_0123456789abcdef")

	a.WriteProof(key, certificateOfSize(4))
	a.WritePlan(key, planWithReplaced(4))
	require.Len(t, b.ReadProof(key).Pool.Strings, 4)
	require.Equal(t, []uint32{4}, b.ReadPlan(key).Replaced)

	b.WriteProof(key, certificateOfSize(6))
	require.Len(t, a.ReadProof(key).Pool.Strings, 4, "the other store's smaller certificate is kept")
	b.WriteProof(key, certificateOfSize(1))
	require.Len(t, a.ReadProof(key).Pool.Strings, 1)

	// A third open on the same directory, as a restarted serve, reads it all.
	c := openStore(t, dir)
	require.Len(t, c.ReadProof(key).Pool.Strings, 1)
	require.Equal(t, []uint32{4}, c.ReadPlan(key).Replaced)
}

// The refuter's racer goroutines write through one store at once; the
// smallest certificate of the race is what the key holds afterwards.
func TestSessionCNFStore_ConcurrentWritersKeepTheSmallest(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cnf_cache")
	s := openStore(t, dir)
	const key = core.PropKey("prop_0123456789abcdef")

	var wg sync.WaitGroup
	for i := 1; i <= 32; i++ {
		wg.Add(1)
		go func(n int) {
			defer wg.Done()
			s.WriteProof(key, certificateOfSize(n))
			s.WritePlan(key, planWithReplaced(uint32(n)))
		}(i)
	}
	wg.Wait()
	require.Len(t, s.ReadProof(key).Pool.Strings, 1)
	require.NotNil(t, s.ReadPlan(key))
	require.Equal(t, []string{string(key)}, rowFiles(t, dir, cnfProofsTable), "no temporary file survives a write")
	require.Equal(t, []string{string(key)}, rowFiles(t, dir, cnfPlansTable))
}

// A write a serve did not live to finish is a temporary file, which no
// read opens and no later write is deterred by.
func TestSessionCNFStore_ATornWriteIsNotARow(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cnf_cache")
	s := openStore(t, dir)
	const key = core.PropKey("prop_0123456789abcdef")

	torn := filepath.Join(dir, cnfProofsTable, string(key)+".12345.tmp")
	require.NoError(t, os.WriteFile(torn, []byte{0x0a, 0x01}, 0o644))
	require.Nil(t, s.ReadProof(key))

	s.WriteProof(key, certificateOfSize(2))
	require.Len(t, s.ReadProof(key).Pool.Strings, 2)
	require.ElementsMatch(t, []string{string(key), filepath.Base(torn)}, rowFiles(t, dir, cnfProofsTable))
}

// A row that does not decode was not written by the store: reading it
// panics naming the file, rather than reporting a miss that a live
// re-search would then paper over.
func TestSessionCNFStore_ARowThatDoesNotDecodePanics(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cnf_cache")
	s := openStore(t, dir)
	const key = core.PropKey("prop_0123456789abcdef")

	// Field 1, wire type 7: no such wire type.
	require.NoError(t, os.WriteFile(filepath.Join(dir, cnfProofsTable, string(key)), []byte{0x0f}, 0o644))
	v := panicValue(func() { s.ReadProof(key) })
	require.NotNil(t, v, "reading the row panics")
	require.Contains(t, fmt.Sprint(v), filepath.Join(dir, cnfProofsTable, string(key)))
}

func panicValue(f func()) (v any) {
	defer func() { v = recover() }()
	f()
	return nil
}
