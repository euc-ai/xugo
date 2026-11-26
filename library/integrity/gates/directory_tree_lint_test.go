package gates

import (
	"fmt"
	"path"
	"strings"
	"testing"
)

// A DIRECTORY IS A FAMILY OR A TOPIC, NEVER BOTH. Constitution
// §"Directory organization: the domain tree". A family's directory holds
// its own package and nothing nested; families that belong with a
// family X sit beside it in a topic directory named X, with X itself at
// X/X (`algebra/group/group`, `algebra/field/field`,
// `probability/martingale/martingale`). A topic's Go file, where it has
// one, is its aggregator, which links the families beneath it — a
// family could not, since the families nested with it import it.
func TestLintDirectoryTree(t *testing.T) {
	var families []string
	for _, dir := range familyPackageDirs(t) {
		families = append(families, chapterRel(dir))
	}
	refused := directoryTreeRefusals(families)
	for _, r := range refused {
		t.Error(r)
	}
	if len(families) == 0 {
		t.Fatalf("no family directory found under %s: the gate checked nothing", corpusRoot)
	}
	t.Logf("%d family directories, none nested in another", len(families))
}

// directoryTreeRefusals returns one refusal per family (a
// corpus-relative directory) that sits beneath another family's
// directory.
func directoryTreeRefusals(families []string) []string {
	var refused []string
	for _, g := range families {
		for _, f := range families {
			if !strings.HasPrefix(g, f+"/") {
				continue
			}
			refused = append(refused, fmt.Sprintf("%s sits in the directory of the family %s.\n"+
				"    A directory is a family or a topic, never both (constitution §\"Directory organization\"): "+
				"move %s's own files down into %s/%s, so that %s is a topic holding both.",
				g, f, path.Base(f), f, path.Base(f), f))
		}
	}
	return refused
}

// TestLintDirectoryTreeRefuses holds the check to a corpus of four
// families: the topic `dom/tree` holds `dom/tree/tree` and
// `dom/tree/trie`, and the family `dom/stack` holds `dom/stack/queue`.
func TestLintDirectoryTreeRefuses(t *testing.T) {
	refused := directoryTreeRefusals([]string{"dom/tree/tree", "dom/tree/trie", "dom/stack", "dom/stack/queue"})
	want := "dom/stack/queue sits in the directory of the family dom/stack."
	if len(refused) != 1 || !strings.HasPrefix(refused[0], want) {
		t.Fatalf("refusals = %q, want one opening %q", refused, want)
	}
}
