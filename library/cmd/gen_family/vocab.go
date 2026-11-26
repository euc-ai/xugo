// vocab.go — the VocabSpec build surface (zz_vocab_gen.go): the
// chapter's programmable-term surface (the ops struct and its
// build-site methods), rendered from the declaration data in vocab.go.
// The renderer lives in library/registry/vocabgen so the
// drift gate (TestVocabGenCurrent) re-renders with the same code this
// command writes with. A family without a VocabSpec, or whose spec
// yields no generated surface (declare-only), writes nothing — and a
// stale file is removed rather than left undetected.

package main

import (
	"errors"
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/vocabgen"
)

const vocabOutFile = "zz_vocab_gen.go"

func genVocab(fam *registry.Family, pkg, dir string) {
	out := filepath.Join(dir, vocabOutFile)
	content, err := vocabgen.Render(fam, pkg)
	if err != nil {
		log.Fatalf("%s: vocab: %v", fam.Name, err)
	}
	if content == nil {
		if err := os.Remove(out); err == nil {
			fmt.Printf("%s: no generated vocab surface — removed %s\n", fam.Name, vocabOutFile)
		} else if !errors.Is(err, os.ErrNotExist) {
			log.Fatalf("remove stale %s: %v", out, err)
		}
		return
	}
	if err := os.WriteFile(out, content, 0o644); err != nil {
		log.Fatalf("write %s: %v", out, err)
	}
	fmt.Printf("%s: wrote %s\n", fam.Name, vocabOutFile)
}
