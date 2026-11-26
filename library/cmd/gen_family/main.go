// gen_family regenerates a family's generated surface: two products
// from one command, in one run that links the corpus once and reads
// each statement once.
//
//	zz_typed_thms_gen.go the typed theorem wrappers, the phantoms of the
//	 statement letters beyond A–E, and the package's doc comment,
//	 the chapter README's title line (registry/typedgen), and the
//	 in-place wrap of bare family.Add, family.Define and
//	 family.DefineStructure vars
//	zz_vocab_gen.go the VocabSpec build surface (registry/vocabgen)
//
// The bare-name surface every proof file dot-imports belongs to no
// family and is gen_authoring's: it links no chapter.
//
// The two renderers live beside the registry so the gate suite's drift
// gates (TestTypedGenCurrent, TestVocabGenCurrent) re-render with the
// code this command writes with: a stale generated file is a red test
// naming the command.
//
// Run from anywhere in the module:
//
//	go run github.com/euc-ai/xugo/library/cmd/gen_family -pkg arith
//	go run github.com/euc-ai/xugo/library/cmd/gen_family -family words/word_bits
//	go run github.com/euc-ai/xugo/library/cmd/gen_family -all
//
// -pkg and -family take comma-separated lists; -products limits the run
// (default: every product). Output paths are resolved from the module
// root, so the cwd does not matter. The corpus carries one
// //go:generate line, in library/proofs/proofs.go, and it runs -all:
// `go generate ./library/proofs` regenerates every registered family in
// one process. A run's cost is linking the corpus, so -pkg on one
// family costs about what -all does.
//
// The bootstrap ring, stated once: this command links the corpus, so
// the family it regenerates must already compile. A renamed member
// still compiles: its var reads the wrapper type its former name
// rendered, which the generated file declares until the run, and the
// run renders the type under the new name and re-types the var. Only a
// reference no generated file declares any more is unwrapped by hand
// first — the var set to the bare family.Add, family.Define or
// family.DefineStructure call in its member file — and then
// regenerated. No generated file is edited by hand.
package main

import (
	"flag"
	"log"
	"os"
	"path"
	"path/filepath"
	"strings"

	_ "github.com/euc-ai/xugo/library/proofs" // register the corpus
	"github.com/euc-ai/xugo/library/registry"
)

var (
	pkgNames    = flag.String("pkg", "", "family package name(s) (directory basename, comma-separated)")
	familyNames = flag.String("family", "", "full registry family name(s) (e.g. iterate/monoidal, comma-separated) when -pkg is ambiguous")
	all         = flag.Bool("all", false, "regenerate every family")
	products    = flag.String("products", "typed,vocab", "which products to write, comma-separated")
	emitOnly    = flag.Bool("emit-only", false, "typed: write the wrapper file only; do not wrap family.Add vars in member files")
)

func main() {
	flag.Parse()
	root := moduleRoot()
	chapterDir := filepath.Join(root, "library", "proofs")

	fams := resolveFamilies()
	want := map[string]bool{}
	for _, p := range strings.Split(*products, ",") {
		if p = strings.TrimSpace(p); p != "" {
			want[p] = true
		}
	}
	for p := range want {
		switch p {
		case "typed", "vocab":
		default:
			log.Fatalf("unknown product %q (typed, vocab)", p)
		}
	}

	for _, fam := range fams {
		dir := filepath.Join(chapterDir, filepath.FromSlash(familyDir(fam)))
		pkg := path.Base(familyDir(fam))
		if want["typed"] {
			genTyped(fam, pkg, dir, *emitOnly)
		}
		if want["vocab"] {
			genVocab(fam, pkg, dir)
		}
	}
}

// resolveFamilies reads -all / -pkg / -family into the families to
// regenerate, in registration order for -all and in argument order
// otherwise.
func resolveFamilies() []*registry.Family {
	if *all {
		return registry.Families()
	}
	var out []*registry.Family
	for _, name := range splitList(*familyNames) {
		found := false
		for _, f := range registry.Families() {
			if f.Name == name {
				out = append(out, f)
				found = true
			}
		}
		if !found {
			log.Fatalf("no registered family named %q", name)
		}
	}
	for _, pkg := range splitList(*pkgNames) {
		var matches []*registry.Family
		for _, f := range registry.Families() {
			if path.Base(familyDir(f)) == pkg {
				matches = append(matches, f)
			}
		}
		switch len(matches) {
		case 1:
			out = append(out, matches[0])
		case 0:
			log.Fatalf("no registered family with package name %q", pkg)
		default:
			var names []string
			for _, f := range matches {
				names = append(names, f.Name)
			}
			log.Fatalf("package name %q is ambiguous (%s): use -family", pkg, strings.Join(names, ", "))
		}
	}
	if len(out) == 0 {
		log.Fatalf("one of -pkg, -family, -all or -authoring is required")
	}
	return out
}

func splitList(s string) []string {
	var out []string
	for _, part := range strings.Split(s, ",") {
		if part = strings.TrimSpace(part); part != "" {
			out = append(out, part)
		}
	}
	return out
}

// familyDir is the family package directory, relative to library/proofs.
func familyDir(f *registry.Family) string {
	if f.Dir != "" {
		return f.Dir
	}
	return f.Name
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
