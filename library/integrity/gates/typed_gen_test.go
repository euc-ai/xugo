// typed_gen_test.go — the typed-wrapper generator's drift gate.
//
// Re-render every family's zz_typed_thms_gen.go with the renderer
// gen_family writes with (library/registry/typedgen) and demand the
// on-disk file match byte-for-byte: a member added or restated without
// a regeneration is a red test naming the command. The renderer orders
// the wrappers by entry name, so only a statement change moves the
// file — registration order would move it under any dependency edit.
// TestVocabGenCurrent is the precedent.
//
// The file has a second input: the title line of the chapter's
// README.md, which the renderer writes as the package's doc comment.
// A title edited without a regeneration is the same red test.

package gates

import (
	"bytes"
	"os"
	"path"
	"path/filepath"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/typedgen"
)

func TestTypedGenCurrent(t *testing.T) {
	for _, fam := range registry.Families() {
		rel := familyRel(fam)
		gloss, err := registry.ChapterGloss(familyDir(fam))
		if err != nil {
			t.Errorf("%s: %v", fam.Name, err)
			continue
		}
		rendered, err := typedgen.Render(fam, path.Base(rel), familyDir(fam), gloss)
		if err != nil {
			t.Errorf("%s: render: %v", fam.Name, err)
			continue
		}
		onDisk, err := os.ReadFile(filepath.Join(familyDir(fam), typedgen.File))
		switch {
		case err != nil:
			t.Errorf("%s: %s missing — run go generate ./library/proofs", fam.Name, typedgen.File)
		case !bytes.Equal(rendered.Source, onDisk):
			t.Errorf("%s: stale %s — run go generate ./library/proofs", fam.Name, typedgen.File)
		}
	}
}
