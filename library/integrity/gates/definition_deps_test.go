// definition_deps_test.go — every constant a definition's equation
// spells is minted before the equation parses.
//
// A definition's equation is parsed at registration — at the package's
// init — so every constant it spells must already be minted, and what
// orders the mints is Go's initialization: a package after the packages
// it imports, a variable after the variables its initializer
// references. So the rule has two halves. A constant minted in ANOTHER
// package needs the package imported, through any file. A constant
// minted in the SAME package needs a reference: declaration order is
// not enough, because a type door's variable waits for the inhabitation
// proof it references, declared further down, while a definition that
// references nothing initializes at its own position — peano.ZeroDef
// spells mk_num and ran before NumDef the moment its `Deps:
// {NumDef.Retraction}` was removed. The reference is the definition's
// `Deps`, which names only entries of its own family (registration
// refuses another's); a mint of another family is ordered by the import
// alone, and where no file of the family otherwise imports the minting
// package, family.go imports it blank. This gate checks both halves.
// Constants the parser builds on its own — numerals, the arithmetic
// operators at their domains, `&` (dsl.NativeConstNames) — need no
// ordering and are skipped.
package gates

import (
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/index"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// corpusImportPrefix is the import path every chapter package starts
// with; the rest is the family's Dir.
const corpusImportPrefix = "github.com/euc-ai/xugo/library/proofs/"

// packageImports reads the corpus-internal imports of the chapter
// package at dir (relative to corpusRoot), as family Dirs: every
// non-test .go file's import block, ImportsOnly.
func packageImports(t *testing.T, dir string) []string {
	t.Helper()
	entries, err := os.ReadDir(filepath.Join(corpusRoot, filepath.FromSlash(dir)))
	if err != nil {
		t.Fatalf("%s: %v", dir, err)
	}
	seen := map[string]bool{}
	for _, de := range entries {
		name := de.Name()
		if de.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(token.NewFileSet(), filepath.Join(corpusRoot, filepath.FromSlash(dir), name), nil, parser.ImportsOnly)
		if err != nil {
			t.Fatalf("%s/%s: %v", dir, name, err)
		}
		for _, imp := range f.Imports {
			if rest, ok := strings.CutPrefix(strings.Trim(imp.Path.Value, `"`), corpusImportPrefix); ok {
				seen[rest] = true
			}
		}
	}
	out := make([]string, 0, len(seen))
	for d := range seen {
		out = append(out, d)
	}
	sort.Strings(out)
	return out
}

// importClosure answers which corpus packages a chapter package
// imports, directly or through the packages it imports — the packages
// Go initializes before it. The closure passes through every package
// under the corpus, a family's or not (a domain's aggregate, a tower's
// front, a vocabulary). direct lists one package's own imports; each
// package is read once.
type importClosure struct {
	direct func(dir string) []string
	closed map[string]map[string]bool
}

func newImportClosure(direct func(dir string) []string) *importClosure {
	return &importClosure{direct: direct, closed: map[string]map[string]bool{}}
}

// corpusImportClosure is the closure over the chapter packages as they
// stand on disk.
func corpusImportClosure(t *testing.T) *importClosure {
	t.Helper()
	return newImportClosure(func(dir string) []string { return packageImports(t, dir) })
}

// of is the set of package dirs dir imports, transitively; dir itself
// is not in it, since Go refuses an import cycle.
func (ic *importClosure) of(dir string) map[string]bool {
	if got, ok := ic.closed[dir]; ok {
		return got
	}
	out := map[string]bool{}
	ic.closed[dir] = out
	for _, d := range ic.direct(dir) {
		out[d] = true
		for through := range ic.of(d) {
			out[through] = true
		}
	}
	return out
}

func TestLintDefinitionMintsOrdered(t *testing.T) {
	c, err := index.Load(corpusRoot)
	if err != nil {
		t.Fatal(err)
	}
	native := dsl.NativeConstNames()
	dirOf := map[string]string{}
	for _, f := range c.Families {
		dirOf[f.Name] = f.Dir
	}
	closure := corpusImportClosure(t)
	same, foreign := 0, 0
	for _, e := range registry.All() {
		if e.Definition != proof.DefinitionDirect {
			continue
		}
		m, ok := c.Resolve(index.MemberID(e))
		if !ok {
			t.Fatalf("%s is registered and not indexed", e.Name)
		}
		// The same-package members the definition's initializer reaches
		// through Deps, transitively — Go orders a variable after every
		// variable it references, directly or through the ones it
		// references — and the type or datatype doors among them: a door
		// mints several constants through several entries (Retraction,
		// Membership, the kit's rules), and reaching any one of them
		// orders the whole door.
		named := map[string]bool{}
		doors := map[string]bool{}
		var reach func(id string)
		reach = func(id string) {
			if named[id] {
				return
			}
			dm, ok := c.Resolve(id)
			if !ok || dm.Family != m.Family {
				return
			}
			named[id] = true
			if dm.DefinesType != "" {
				doors[dm.DefinesType] = true
			}
			for _, next := range dm.Deps {
				reach(next)
			}
		}
		for _, id := range m.Deps {
			reach(id)
		}
		for _, name := range m.Constants {
			d := c.DefinitionOf(name)
			if d == nil || d.Member == m.ID || native[name] {
				continue
			}
			if d.Family != m.Family {
				foreign++
				if from, to := dirOf[m.Family], dirOf[d.Family]; !closure.of(from)[to] {
					t.Errorf("%s spells `%s`, minted by %s in %s, and %s imports that package through nothing — "+
						"its equation parses at init, before the mint unless the import orders them: add\n\t_ %q\n"+
						"to %s/family.go", m.ID, name, d.Member, d.Family, m.Family, corpusImportPrefix+to, from)
				}
				continue
			}
			same++
			if named[d.Member] {
				continue
			}
			if dm, ok := c.Resolve(d.Member); ok && dm.DefinesType != "" && doors[dm.DefinesType] {
				continue
			}
			t.Errorf("%s spells `%s`, minted by %s in the same package, and its Deps do not reach it — "+
				"declaration order does not initialize the mint first (a type door waits for its inhabitation "+
				"proof); add %s to the Deps", m.ID, name, d.Member, d.Member)
		}
	}
	t.Logf("%d same-package and %d cross-package (definition, spelled constant) pairs checked", same, foreign)
}
