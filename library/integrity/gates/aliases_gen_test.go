// aliases_gen_test.go — the alias generator's drift gate.
//
// Re-render library/authoring's zz_constructors_gen.go and the roster
// of the surface (library/registry/aliasgen's zz_surface_gen.go) with
// the renderer gen_authoring writes with, and demand the on-disk files
// match byte-for-byte. The gaps this closes: a prover constructor is
// added and the bare-name surface every proof file dot-imports does not
// carry it until an emitted body first spells the name — a compile
// error in a session that did not touch the prover; and a name is
// declared by hand in authoring.go while the roster does not list it,
// so the emitter renders a file that spells it without the import.
// TestVocabGenCurrent is the precedent.

package gates

import (
	"bytes"
	"os"
	"path/filepath"
	"testing"

	"github.com/euc-ai/xugo/library/registry/aliasgen"
)

// The three directories the gate reads, relative to THIS package's
// directory (a `go test` binary runs with its package dir as the
// working directory), the way corpusRoot locates the chapters:
// prover/proof, scanned for the constructor surface; library/authoring,
// read for the names declared by hand; and aliasgen's own, where the
// roster is. A wrong anchor is a loud error from the renderer, never an
// empty surface.
const (
	proverSourceDir = "../../../prover/proof"
	authoringDir    = "../../authoring"
	aliasgenDir     = "../../registry/aliasgen"
)

func TestAliasGenCurrent(t *testing.T) {
	candidates, err := aliasgen.Constructors(proverSourceDir)
	if err != nil {
		t.Fatal(err)
	}
	want, err := aliasgen.Render(authoringDir, candidates)
	if err != nil {
		t.Fatal(err)
	}
	for _, product := range []struct {
		path string
		want []byte
	}{
		{filepath.Join(authoringDir, aliasgen.File), want.Constructors},
		{filepath.Join(aliasgenDir, aliasgen.SurfaceFile), want.Surface},
	} {
		onDisk, err := os.ReadFile(product.path)
		switch {
		case err != nil:
			t.Errorf("%s missing — run go generate ./library/authoring/", product.path)
		case !bytes.Equal(product.want, onDisk):
			t.Errorf("stale %s — run go generate ./library/authoring/", product.path)
		}
	}
}
