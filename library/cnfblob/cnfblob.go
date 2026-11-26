// Package cnfblob is a family's CNF blob as a file: the lock a writer
// holds over the blob's directory from its read of the blob to its
// write, and the write that replaces the blob whole.
//
// A writer of a blob writes what it read plus what it changed: a
// recording the rows it captured, a GC the rows it kept, a re-keying or
// a rename the rows it moved, a merge another tree's rows. Two writers
// of one blob in one tree that both read before either wrote would each
// write over what the other added, with nothing said until a replay
// misses the dropped rows, so every writer takes Lock before it reads
// and writes with Write before it releases. A run that writes nothing
// takes no lock.
package cnfblob

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"syscall"
)

// Lock takes the exclusive advisory lock (flock) on the directory dir
// and returns its release; onWait runs once if another holder has to
// release it first. The lock is on the open directory, so it ends with
// the release or with the process, however the process ends: a writer
// that was killed leaves nothing to clear.
func Lock(dir string, onWait func()) (release func(), err error) {
	d, err := os.Open(dir)
	if err != nil {
		return nil, err
	}
	fd := int(d.Fd())
	err = syscall.Flock(fd, syscall.LOCK_EX|syscall.LOCK_NB)
	if errors.Is(err, syscall.EWOULDBLOCK) {
		onWait()
		for {
			err = syscall.Flock(fd, syscall.LOCK_EX)
			if !errors.Is(err, syscall.EINTR) {
				break
			}
		}
	}
	if err != nil {
		d.Close()
		return nil, fmt.Errorf("flock %s: %w", dir, err)
	}
	return func() { d.Close() }, nil
}

// Write replaces the blob at path with blob. The bytes are written
// beside the path and renamed onto it, so a build that embeds the blob
// while a writer writes it reads the old bytes or the new, never a part
// of them.
func Write(path string, blob []byte) error {
	tmp, err := os.CreateTemp(filepath.Dir(path), ".cnf-pb-*.tmp")
	if err != nil {
		return err
	}
	_, err = tmp.Write(blob)
	if cerr := tmp.Close(); err == nil {
		err = cerr
	}
	if err == nil {
		err = os.Chmod(tmp.Name(), 0o644)
	}
	if err == nil {
		err = os.Rename(tmp.Name(), path)
	}
	if err != nil {
		os.Remove(tmp.Name())
	}
	return err
}
