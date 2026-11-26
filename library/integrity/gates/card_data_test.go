package gates

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"

	"github.com/euc-ai/xugo/library/carddata/cardgen"
)

// TestCardDataCurrent re-renders from the current registry, including
// card membership and spelling changes that preserve a statement's
// key. Neither the name/key fingerprint nor the generated table is an
// oracle for what a card should display.
func TestCardDataCurrent(t *testing.T) {
	want := cardgen.Render()
	file := filepath.Join("../../carddata", cardgen.File)
	onDisk, err := os.ReadFile(file)
	switch {
	case err != nil:
		t.Fatalf("%s: %v — run go generate ./library/carddata", file, err)
	case !bytes.Equal(want, onDisk):
		t.Fatalf("stale %s — run go generate ./library/carddata", file)
	}
}
