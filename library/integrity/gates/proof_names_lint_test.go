// proof_names_lint_test.go — a proof names only members its replay
// recorded.
//
// A proved member's deps are recorded: the entries its replay read by
// name and the definitions it opened (registry.ProofEntry.DepEntries,
// written by the recorder). Its
// text — the Go narration of the argument — names members too,
// directly in a step's proof or through a local a `:=` bound to a
// citation (index.Outline). The rule: what the text names is among
// what the replay recorded. A name the record lacks is decoration — a
// witness whose evidence no closer consumed, a lemma passed and never
// used — and misleads a reader of the proof and of the outline alike;
// the author drops it, or makes a step use it. The other direction is
// free: a replay records reads the text never spells, a reading's laws
// or a simp set, and the lint asks nothing of them.
//
// A member whose chapter file cannot be read — it does not parse, or
// declares nothing at the member's registered line — is reported, once
// per refusal, and the lint goes on to the members whose files stand:
// in a tree several lanes edit, one lane's half-written file fails the
// lint for that file and not for every other member.
package gates

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/index"
)

func TestLintProofNamesRecordedDeps(t *testing.T) {
	c, err := index.Load(corpusRoot)
	if err != nil {
		t.Fatal(err)
	}
	refused := map[string]bool{}
	for _, m := range c.Members {
		steps, err := c.Outline(m)
		if err != nil {
			if reason := err.Error(); !refused[reason] {
				refused[reason] = true
				t.Error(reason)
			}
			continue
		}
		if len(steps) == 0 {
			continue
		}
		recorded := map[string]bool{}
		for _, id := range m.Deps {
			recorded[id] = true
		}
		file, _, _ := strings.Cut(m.Source, ":")
		for _, s := range steps {
			for _, id := range s.Cites {
				if !recorded[id] {
					t.Errorf("%s names %s at %s:%d, and its replay recorded no read or opening of it — the name is decoration: drop it, or make the step use it",
						m.ID, id, file, s.Line)
				}
			}
		}
	}
}
