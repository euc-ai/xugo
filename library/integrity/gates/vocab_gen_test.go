// vocab_gen_test.go — the vocab generator's drift gate.
//
// For every family carrying a VocabSpec, re-render the generated
// surface with the same renderer gen_family writes with and demand the
// on-disk zz_vocab_gen.go match byte-for-byte. The alias and typed
// generators have the same gate (aliases_gen_test.go,
// typed_gen_test.go); the manifest's TestCanonicalDependencyGraph is
// the precedent all three follow — a stale file is a red test naming
// the regeneration command, not a latent divergence.

package gates

import (
	"bytes"
	"os"
	"path"
	"path/filepath"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/vocabgen"
)

func TestVocabGenCurrent(t *testing.T) {
	for _, fam := range registry.Families() {
		dir := familyRel(fam)
		genPath := filepath.Join(familyDir(fam), "zz_vocab_gen.go")
		onDisk, readErr := os.ReadFile(genPath)

		if fam.VocabSpec() == nil {
			if readErr == nil {
				t.Errorf("%s: zz_vocab_gen.go exists but the family has no VocabSpec — remove the file or restore the spec", fam.Name)
			}
			continue
		}

		want, err := vocabgen.Render(fam, path.Base(dir))
		if err != nil {
			t.Errorf("%s: render: %v", fam.Name, err)
			continue
		}
		switch {
		case want == nil && readErr == nil:
			t.Errorf("%s: stale zz_vocab_gen.go (the spec yields no generated surface) — run go generate ./library/proofs", fam.Name)
		case want != nil && readErr != nil:
			t.Errorf("%s: zz_vocab_gen.go missing — run go generate ./library/proofs", fam.Name)
		case want != nil && !bytes.Equal(want, onDisk):
			t.Errorf("%s: stale zz_vocab_gen.go — run go generate ./library/proofs", fam.Name)
		}
	}
}
