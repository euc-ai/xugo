// typed.go — the typed theorem-wrapper product (zz_typed_thms_gen.go),
// written from library/registry/typedgen's renderer, and the in-place
// wrap of bare family.Add / family.Define / family.DefineStructure vars
// in the member files (unless -emit-only). The file also carries the package's doc
// comment, the title line of the chapter's README.md. The drift gate
// (TestTypedGenCurrent) re-renders the file with the same code this
// command writes with, so a member restated, a README title edited, or
// another chapter's phantom named or no longer named by the proof files
// without a regeneration is a red test naming the command.

package main

import (
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/registry/typedgen"
)

func genTyped(fam *registry.Family, pkg, dir string, emitOnly bool) {
	gloss, err := registry.ChapterGloss(dir)
	if err != nil {
		log.Fatalf("%s: typed: %v", fam.Name, err)
	}
	rendered, err := typedgen.Render(fam, pkg, dir, gloss)
	if err != nil {
		log.Fatalf("%s: typed: %v", fam.Name, err)
	}
	out := filepath.Join(dir, typedgen.File)
	if err := os.WriteFile(out, rendered.Source, 0o644); err != nil {
		log.Fatalf("write %s: %v", out, err)
	}
	fmt.Printf("%s: wrote %s (%d wrapper(s))\n", fam.Name, typedgen.File, rendered.Wrappers)
	for _, n := range rendered.Notes {
		fmt.Println("  " + n)
	}
	if emitOnly {
		return
	}
	report, err := rendered.ApplyWraps(dir)
	if err != nil {
		log.Fatalf("%s: wrap: %v", fam.Name, err)
	}
	for _, line := range report {
		fmt.Println(line)
	}
}
