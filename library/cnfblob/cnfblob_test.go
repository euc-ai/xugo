package cnfblob

import (
	"os"
	"path/filepath"
	"testing"
	"time"
)

// TestWrite_ReplacesTheBlobWhole: a write over an existing blob leaves
// the new bytes at its path and nothing beside it.
func TestWrite_ReplacesTheBlobWhole(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "family.cnf.pb")
	for _, blob := range []string{"first", "second, longer"} {
		if err := Write(path, []byte(blob)); err != nil {
			t.Fatalf("write %q: %v", blob, err)
		}
		if got, _ := os.ReadFile(path); string(got) != blob {
			t.Fatalf("the blob reads %q, want %q", got, blob)
		}
	}
	left, err := os.ReadDir(dir)
	if err != nil || len(left) != 1 {
		t.Fatalf("the directory holds %d file(s) after two writes (err=%v), want the blob alone", len(left), err)
	}
	if info, _ := left[0].Info(); info.Mode().Perm() != 0o644 {
		t.Fatalf("the blob's mode is %v, want 0644", info.Mode().Perm())
	}
}

// TestWrite_NoDirectoryWritesNothing: a write into a directory that
// does not exist is an error, and leaves no file.
func TestWrite_NoDirectoryWritesNothing(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "absent")
	if err := Write(filepath.Join(dir, "family.cnf.pb"), []byte("blob")); err == nil {
		t.Fatal("a write into a missing directory returned no error")
	}
	if _, err := os.Stat(dir); !os.IsNotExist(err) {
		t.Fatalf("the write created %s", dir)
	}
}

// TestLock_SecondWriterWaitsForTheFirst: the lock a writer holds over a
// blob's directory keeps a second out until it is released, and the
// second is told it is waiting.
func TestLock_SecondWriterWaitsForTheFirst(t *testing.T) {
	dir := t.TempDir()
	release, err := Lock(dir, func() { t.Fatal("the first writer waited on a free directory") })
	if err != nil {
		t.Fatal(err)
	}
	waiting := make(chan struct{})
	acquired := make(chan error, 1)
	go func() {
		second, err := Lock(dir, func() { close(waiting) })
		if err == nil {
			second()
		}
		acquired <- err
	}()
	select {
	case <-waiting:
	case err := <-acquired:
		t.Fatalf("the second writer took the lock the first holds (err=%v)", err)
	case <-time.After(10 * time.Second):
		t.Fatal("the second writer neither waited nor returned")
	}
	select {
	case err := <-acquired:
		t.Fatalf("the second writer returned while the first held the lock (err=%v)", err)
	case <-time.After(200 * time.Millisecond):
	}
	release()
	select {
	case err := <-acquired:
		if err != nil {
			t.Fatalf("the second writer after the release: %v", err)
		}
	case <-time.After(10 * time.Second):
		t.Fatal("the second writer is still waiting after the release")
	}
}

// TestLock_FreeAgainAfterRelease: a released directory is taken at
// once, with no wait.
func TestLock_FreeAgainAfterRelease(t *testing.T) {
	dir := t.TempDir()
	for range 2 {
		release, err := Lock(dir, func() { t.Fatal("waited on a released directory") })
		if err != nil {
			t.Fatal(err)
		}
		release()
	}
}
