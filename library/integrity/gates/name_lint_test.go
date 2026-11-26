// name_lint_test.go — the names a change hands to a different theorem.
//
// A registered name is the corpus's citation surface: the recorded
// dependencies and a card's `Deps`, `By` premises, session
// `with_lemmas` keys and typed wrappers all
// reach a theorem through it, and nothing else checks what they reach.
// Two entries with the same typed wrapper signature are
// interchangeable to the compiler, so a name re-pointed at a
// DIFFERENT theorem — the recast that renamed FiniteInductStrong's
// theorem to FiniteInductFresh and handed the vacated name to the
// door's weaker principle — builds, vets and lints green. Inside the
// tree the replay of the citers' scope checks every cite; a citer on a
// branch cut before the change is reached by no replay until that
// branch merges.
//
// The report reads the (name, key) pairs every proof file declared at
// a BASE commit (HEAD, or XUGO_GATE_BASE) and compares them with the
// registry this tree links. A name whose key changed while its OLD key
// is still registered under ANOTHER name is listed: the theorem
// survived under a new name and its old name was reused. Re-pointing is
// allowed (chapter_constitution.md §"Inventory and names"); the list is
// what a later merge searches the incoming branch for. A name whose key
// changed because its own statement changed (the old key is gone) is an
// ordinary restatement, checked by the citers' replay, and not listed.
package gates

import (
	"bufio"
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
)

// declaredNameKeys reads every `Name: "…"` / `Key: "…"` pair a Go
// source declares in one composite literal — an entry literal's two
// identity fields. Door literals mint derived entries without a Key
// line and are not read; the hand entries the gate exists for spell
// both. Names are unqualified, as the literal spells them.
func declaredNameKeys(src []byte, file string) (map[string]string, error) {
	af, err := parser.ParseFile(token.NewFileSet(), file, src, 0)
	if err != nil {
		return nil, err
	}
	out := map[string]string{}
	ast.Inspect(af, func(n ast.Node) bool {
		cl, ok := n.(*ast.CompositeLit)
		if !ok {
			return true
		}
		var name, key string
		for _, elt := range cl.Elts {
			kv, ok := elt.(*ast.KeyValueExpr)
			if !ok {
				continue
			}
			id, ok := kv.Key.(*ast.Ident)
			if !ok {
				continue
			}
			lit, ok := kv.Value.(*ast.BasicLit)
			if !ok || lit.Kind != token.STRING {
				continue
			}
			v, err := strconv.Unquote(lit.Value)
			if err != nil {
				continue
			}
			switch id.Name {
			case "Name":
				name = v
			case "Key":
				key = v
			}
		}
		if name != "" && key != "" && !strings.HasPrefix(key, registry.UnmintedKeyPrefix) {
			out[name] = key
		}
		return true
	})
	return out, nil
}

// gitShowAll returns the content of each repo-relative path at ref,
// keyed by path, from ONE `git cat-file --batch` process fed every
// `<ref>:<path>` spec on its stdin; a path the ref does not have is
// absent from the result. One process rather than one `git show` per
// file: 704 of those were 7 s of a gate whose own work is under a
// second. A spec is one line, so a path holding a newline is refused —
// the corpus has none.
func gitShowAll(repo, ref string, rels []string) (map[string][]byte, error) {
	var specs bytes.Buffer
	for _, rel := range rels {
		if strings.Contains(rel, "\n") {
			return nil, fmt.Errorf("path %q holds a newline, which one cat-file spec cannot carry", rel)
		}
		specs.WriteString(ref + ":" + rel + "\n")
	}
	cmd := exec.Command("git", "-C", repo, "cat-file", "--batch")
	cmd.Stdin = &specs
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	out, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("git cat-file --batch: %v: %s", err, strings.TrimSpace(stderr.String()))
	}
	// Each spec answers in order: `<oid> blob <size>`, the bytes, a
	// newline — or `<spec> missing`.
	r := bufio.NewReader(bytes.NewReader(out))
	got := make(map[string][]byte, len(rels))
	for _, rel := range rels {
		header, err := r.ReadString('\n')
		if err != nil {
			return nil, fmt.Errorf("git cat-file --batch: output ends before %s:%s: %v", ref, rel, err)
		}
		header = strings.TrimSuffix(header, "\n")
		if strings.HasSuffix(header, " missing") {
			continue
		}
		fields := strings.Fields(header)
		if len(fields) != 3 || fields[1] != "blob" {
			return nil, fmt.Errorf("git cat-file --batch: %s:%s: unexpected header %q", ref, rel, header)
		}
		size, err := strconv.Atoi(fields[2])
		if err != nil {
			return nil, fmt.Errorf("git cat-file --batch: %s:%s: size in %q: %v", ref, rel, header, err)
		}
		content := make([]byte, size)
		if _, err := io.ReadFull(r, content); err != nil {
			return nil, fmt.Errorf("git cat-file --batch: %s:%s: %d bytes announced, fewer read: %v", ref, rel, size, err)
		}
		if nl, err := r.ReadByte(); err != nil || nl != '\n' {
			return nil, fmt.Errorf("git cat-file --batch: %s:%s: no newline after its %d bytes", ref, rel, size)
		}
		got[rel] = content
	}
	return got, nil
}

// envGateBase names the git ref the gates that compare the tree against
// a commit read — this one and the claim-text gate; HEAD when unset.
// `master` compares a branch against the trunk.
const envGateBase = "XUGO_GATE_BASE"

// gateBase is the repository root and the base commit a comparing gate
// reads, from envGateBase; the gate is skipped where git or a checkout
// is missing, and fails where the ref names no commit.
func gateBase(t *testing.T) (repo, base string) {
	t.Helper()
	if _, err := exec.LookPath("git"); err != nil {
		t.Skip("git is not on PATH — the gate compares the tree against a commit")
	}
	base = os.Getenv(envGateBase)
	if base == "" {
		base = "HEAD"
	}
	repoOut, err := exec.Command("git", "rev-parse", "--show-toplevel").Output()
	if err != nil {
		t.Skipf("not inside a git checkout: %v", err)
	}
	repo = strings.TrimSpace(string(repoOut))
	if out, err := exec.Command("git", "-C", repo, "rev-parse", "--verify", base+"^{commit}").CombinedOutput(); err != nil {
		t.Fatalf("%s=%q names no commit: %s", envGateBase, base, strings.TrimSpace(string(out)))
	}
	return repo, base
}

// chapterFilesAtBase is the content of each chapter proof file at base,
// keyed by the file as chapterProofFiles lists it; a file the base
// does not have is absent.
func chapterFilesAtBase(t *testing.T, repo, base string, files []string) map[string][]byte {
	t.Helper()
	rels := make([]string, len(files))
	for i, f := range files {
		abs, err := filepath.Abs(f)
		if err != nil {
			t.Fatalf("abs %s: %v", f, err)
		}
		rel, err := filepath.Rel(repo, abs)
		if err != nil {
			t.Fatalf("rel %s: %v", abs, err)
		}
		rels[i] = filepath.ToSlash(rel)
	}
	atBase, err := gitShowAll(repo, base, rels)
	if err != nil {
		t.Fatalf("reading the chapter files at %s: %v", base, err)
	}
	byFile := make(map[string][]byte, len(atBase))
	for i, f := range files {
		if src, ok := atBase[rels[i]]; ok {
			byFile[f] = src
		}
	}
	return byFile
}

func TestLintRepointedNames(t *testing.T) {
	repo, base := gateBase(t)

	famByDir := claimFamilyByDir()
	type finding struct {
		name, oldKey, newKey, occupant, file string
	}
	var findings []finding
	compared := 0
	files := chapterProofFiles(t)
	atBase := chapterFilesAtBase(t, repo, base, files)
	for _, f := range files {
		src, exists := atBase[f]
		if !exists {
			continue // a file the base does not have declares nothing there
		}
		declared, err := declaredNameKeys(src, f)
		if err != nil {
			// The base's copy of a file need not parse under the current
			// toolchain's expectations; a file that does not parse
			// declares nothing this gate can read.
			t.Logf("%s at %s does not parse (%v) — skipped", chapterRel(f), base, err)
			continue
		}
		fam := famByDir[path.Dir(filepath.ToSlash(f))]
		if fam == nil {
			continue
		}
		prefix := path.Base(fam.Name) + "."
		for short, oldKey := range declared {
			name := prefix + short
			entry, ok := registry.ByName(name)
			if !ok {
				continue // the name is gone: a rename or a retirement, no citer resolves it
			}
			compared++
			if entry.Key == oldKey {
				continue
			}
			occupant, live := registry.ByKey(oldKey)
			if !live || occupant.Name == name {
				continue // the theorem itself moved key: a restatement, the citers' replay checks it
			}
			findings = append(findings, finding{name: name, oldKey: oldKey, newKey: entry.Key, occupant: occupant.Name, file: chapterRel(f)})
		}
	}
	sort.Slice(findings, func(i, j int) bool { return findings[i].name < findings[j].name })
	for _, x := range findings {
		t.Logf("re-pointed: %s: registered name %s pointed at %s at %s and now resolves to %s, while %s is registered as %s — "+
			"a cite of %s on a branch cut before this change compiles against the new statement: "+
			"say so in the landing, and search a branch merged after it for cites of %s",
			x.file, x.name, x.oldKey, base, x.newKey, x.oldKey, x.occupant, x.name, x.name)
	}
	t.Logf("%d registered names compared against %s; %d re-pointed", compared, base, len(findings))
}

// TestDeclaredNameKeysReadsAnEntryLiteral pins the source reader on the
// two literal shapes the corpus writes: a bare entry and a typed
// wrapper around one, beside a door literal with no Key line.
func TestDeclaredNameKeysReadsAnEntryLiteral(t *testing.T) {
	src := []byte(`package x

var A = family.Add(registry.ProofEntry{
	Name: "Alpha",
	Key:  "prop_0000000000000001",
})

var B = betaThm{family.Add(registry.ProofEntry{
	Name: "Beta",
	Key:  "prop_0000000000000002",
})}

var Unminted = family.Add(registry.ProofEntry{
	Name: "Gamma",
	Key:  "` + registry.UnmintedKeyPrefix + `x",
})

var D = family.DefineData(registry.DataEntry{Name: "List"})
`)
	got, err := declaredNameKeys(src, "x.go")
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]string{"Alpha": "prop_0000000000000001", "Beta": "prop_0000000000000002"}
	if len(got) != len(want) {
		t.Fatalf("got %v, want %v", got, want)
	}
	for k, v := range want {
		if got[k] != v {
			t.Errorf("%s: got %q, want %q", k, got[k], v)
		}
	}
}
