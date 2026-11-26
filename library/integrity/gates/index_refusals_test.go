// index_refusals_test.go — what the corpus index refuses, held against
// the corpus as it stands.
//
// The index writes no file: `xugo query` and `xugo browse` answer from
// the registry as they are asked. What a chapter can break there is
// what the index refuses where the registry alone cannot see: a family
// graph with a cycle. A family's checkpoint runs this battery and not
// library/index's tests, so the refusal is a gate here under its own
// name.

package gates

import (
	"testing"

	"github.com/euc-ai/xugo/library/index"
)

// TestFamilyGraphAcyclic names the gate the index's Load runs: the
// family graph — a family depends on the families its members cite
// and on the families whose constants its statements spell — has no
// cycle. A citation is a Go import and cannot cycle; a stated constant
// is a name, and a card stated over a constant of a chapter that
// stands on the card's chapter would cycle through it. Load refuses
// such a corpus naming the cycle edge by edge, so this is that refusal
// under its own name.
func TestFamilyGraphAcyclic(t *testing.T) {
	if _, err := index.Load(corpusRoot); err != nil {
		t.Fatal(err)
	}
}
