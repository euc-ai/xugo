package gates

import (
	"go/parser"
	"go/token"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
)

// TestCorpusIsReachable is this suite's own precondition, and it is here
// because the suite cannot check it any other way. Every gate below reads
// the corpus twice: through registry.All(), populated by package init, and
// through the filesystem, rooted at corpusRoot. Either reach can silently
// go to zero — the registration blank import in gates.go can be dropped,
// or corpusRoot can stop pointing at the chapters — and in both cases the
// gates iterate nothing and the suite passes on nothing.
//
// So the two reaches check each other. Every directory on disk that
// declares a family must appear in the registry, and every registered
// family must have its directory under corpusRoot. Neither side is a
// hard-coded count, so landing a chapter never edits this test; only a
// broken anchor or a missing registration fails it.
func TestCorpusIsReachable(t *testing.T) {
	onDisk := map[string]bool{}
	err := filepath.WalkDir(corpusRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() || !strings.HasSuffix(d.Name(), ".go") {
			return nil
		}
		src, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		if strings.Contains(string(src), "registry.NewFamily") {
			rel, err := filepath.Rel(corpusRoot, filepath.Dir(path))
			if err != nil {
				return err
			}
			onDisk[filepath.ToSlash(rel)] = true
		}
		return nil
	})
	if err != nil {
		t.Fatalf("walk %s: %v — corpusRoot does not reach the chapters", corpusRoot, err)
	}
	if len(onDisk) == 0 {
		t.Fatalf("no family declarations under %s — corpusRoot is wrong, and every "+
			"filesystem gate in this package is passing on an empty file set", corpusRoot)
	}

	registered := map[string]bool{}
	for _, fam := range registry.Families() {
		dir := fam.Dir
		if dir == "" {
			dir = fam.Name
		}
		registered[dir] = true
	}
	if len(registered) == 0 {
		t.Fatalf("registry.Families() is empty — the corpus is not registered in this " +
			"package (see the blank import in gates.go), and every registry gate here " +
			"is passing on an empty corpus")
	}

	for dir := range onDisk {
		if !registered[dir] {
			t.Errorf("%s declares a family that never registers — add it to the chapter "+
				"aggregator, library/proofs/zz_families.go", dir)
		}
	}
	for dir := range registered {
		if !onDisk[dir] {
			t.Errorf("family registered at %q has no declaring file under %s", dir, corpusRoot)
		}
	}
}

// TestCorpusHasNoOrphanPackage: every package under corpusRoot is
// reached from the corpus's own import list (proofs.go), through the
// imports the packages under corpusRoot make of one another.
//
// TestCorpusIsReachable holds this for a chapter, by its registration.
// A package that registers nothing — a domain aggregator, a shared
// alphabet under internal/ — has no registration to miss, so one that
// every chapter has stopped importing stays on disk, builds, carries a
// package comment describing a domain that has moved on, and fails
// nothing. The import graph is read off the source, non-test files
// only: a package only a test imports is not part of the corpus.
func TestCorpusHasNoOrphanPackage(t *testing.T) {
	const corpusImportPath = "github.com/euc-ai/xugo/library/proofs"
	// A package is named by its directory relative to corpusRoot, "."
	// for the root.
	imports := map[string][]string{}
	fset := token.NewFileSet()
	err := filepath.WalkDir(corpusRoot, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() || !strings.HasSuffix(d.Name(), ".go") || strings.HasSuffix(d.Name(), "_test.go") {
			return nil
		}
		af, err := parser.ParseFile(fset, path, nil, parser.ImportsOnly)
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(corpusRoot, filepath.Dir(path))
		if err != nil {
			return err
		}
		pkg := filepath.ToSlash(rel)
		imports[pkg] = imports[pkg]
		for _, spec := range af.Imports {
			target, err := strconv.Unquote(spec.Path.Value)
			if err != nil {
				return err
			}
			if target == corpusImportPath {
				imports[pkg] = append(imports[pkg], ".")
			} else if sub, ok := strings.CutPrefix(target, corpusImportPath+"/"); ok {
				imports[pkg] = append(imports[pkg], sub)
			}
		}
		return nil
	})
	if err != nil {
		t.Fatalf("walk %s: %v", corpusRoot, err)
	}
	if len(imports["."]) == 0 {
		t.Fatalf("the package at %s imports no package of the corpus — corpusRoot is wrong, or proofs.go is empty", corpusRoot)
	}

	reached := map[string]bool{".": true}
	for frontier := []string{"."}; len(frontier) > 0; {
		pkg := frontier[0]
		frontier = frontier[1:]
		for _, target := range imports[pkg] {
			if !reached[target] {
				reached[target] = true
				frontier = append(frontier, target)
			}
		}
	}
	for _, pkg := range slices.Sorted(maps.Keys(imports)) {
		if !reached[pkg] {
			t.Errorf("%s: the corpus's import list (library/proofs/proofs.go) does not reach this package — "+
				"no chapter and no aggregator that the list reaches imports it.\n"+
				"    A package of the corpus nothing imports is dead: delete it, or import it where it is used.", pkg)
		}
	}
}
