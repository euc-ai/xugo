// gen_authoring writes the generated half of the bare-name surface,
// library/authoring's zz_constructors_gen.go, and the roster of the
// whole surface, library/registry/aliasgen's zz_surface_gen.go, both
// from aliasgen's renderer: it scans prover/proof's source for the
// constructors and library/authoring's hand-written file for the names
// declared there. It links no chapter, so it runs while the corpus does
// not compile — after a prover constructor is renamed or removed, the
// stale file it rewrites is what keeps the corpus from compiling, and
// no generated file is edited by hand. The drift gate
// (TestAliasGenCurrent) re-renders with the same code this command
// writes with, so a prover constructor added, or a name declared by
// hand, without a regeneration is a red test naming the command.
//
// Run from anywhere in the module, or through library/authoring's
// go:generate line:
//
//	go run github.com/euc-ai/xugo/library/cmd/gen_authoring
//	go generate ./library/authoring/
package main

import (
	"fmt"
	"log"
	"os"
	"path/filepath"

	"github.com/euc-ai/xugo/library/registry/aliasgen"
)

func main() {
	root := moduleRoot()
	dir := filepath.Join(root, "library", "authoring")
	candidates, err := aliasgen.Constructors(filepath.Join(root, "prover", "proof"))
	if err != nil {
		log.Fatalf("authoring: %v", err)
	}
	rendered, err := aliasgen.Render(dir, candidates)
	if err != nil {
		log.Fatalf("authoring: %v", err)
	}
	for out, src := range map[string][]byte{
		filepath.Join(dir, aliasgen.File):                                            rendered.Constructors,
		filepath.Join(root, "library", "registry", "aliasgen", aliasgen.SurfaceFile): rendered.Surface,
	} {
		if err := os.WriteFile(out, src, 0o644); err != nil {
			log.Fatalf("write %s: %v", out, err)
		}
		fmt.Printf("wrote %s\n", out)
	}
}

// moduleRoot walks up from the working directory to the go.mod.
func moduleRoot() string {
	dir, err := os.Getwd()
	if err != nil {
		log.Fatalf("getwd: %v", err)
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			log.Fatalf("no go.mod above %s", dir)
		}
		dir = parent
	}
}
