// import_graph.go — the import graph of the chapter's packages: which
// families a family's generated file may import.
//
// A generated file may import a package its own package already
// imports, directly or not: that import closes no cycle. The graph is
// read off the import declarations of the hand-written files, never the
// generated ones, so an import a wrapper renders never justifies itself
// and a family regenerates to the same file whatever its generated file
// held before.

package typedgen

import (
	"fmt"
	"go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
)

// importGraph maps each chapter package, by its directory under the
// chapter root as familyDir spells it, to the chapter packages its
// hand-written files import.
type importGraph map[string][]string

// chapterImports is the import graph of the chapter of the module that
// holds the working directory, read once per process.
var chapterImports = sync.OnceValues(func() (importGraph, error) {
	dir, err := os.Getwd()
	if err != nil {
		return nil, err
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return readImportGraph(filepath.Join(dir, "library", "proofs"))
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return nil, fmt.Errorf("typedgen: no go.mod above the working directory")
		}
		dir = parent
	}
})

// readImportGraph reads the import declarations of every package under
// chapterDir, the directory chapterImportPath names. A test file and a
// generated file (`*_gen.go`) are not read, nor a directory the go tool
// ignores (testdata, or a name starting with "." or "_").
func readImportGraph(chapterDir string) (importGraph, error) {
	graph := importGraph{}
	fset := token.NewFileSet()
	err := filepath.WalkDir(chapterDir, func(p string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		name := d.Name()
		if d.IsDir() {
			if p != chapterDir && (name == "testdata" || strings.HasPrefix(name, ".") || strings.HasPrefix(name, "_")) {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") || strings.HasSuffix(name, "_gen.go") {
			return nil
		}
		rel, err := filepath.Rel(chapterDir, filepath.Dir(p))
		if err != nil {
			return err
		}
		af, err := parser.ParseFile(fset, p, nil, parser.ImportsOnly)
		if err != nil {
			return err
		}
		pkg := filepath.ToSlash(rel)
		for _, spec := range af.Imports {
			imported, err := strconv.Unquote(spec.Path.Value)
			if err != nil {
				return err
			}
			if dep, ok := strings.CutPrefix(imported, chapterImportPath); ok {
				graph[pkg] = append(graph[pkg], dep)
			}
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	return graph, nil
}

// closure is the set of chapter packages dir imports, directly or not,
// dir included.
func (g importGraph) closure(dir string) map[string]bool {
	seen := map[string]bool{dir: true}
	queue := []string{dir}
	for len(queue) > 0 {
		next := queue[0]
		queue = queue[1:]
		for _, dep := range g[next] {
			if !seen[dep] {
				seen[dep] = true
				queue = append(queue, dep)
			}
		}
	}
	return seen
}
