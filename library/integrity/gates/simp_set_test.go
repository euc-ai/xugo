package gates

import (
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/tactic"
)

// TestSimpRuleEntriesAreRules checks what a chapter's simp set may hold
// (registry.ProofEntry.Simp): a theorem the simp driver reads as a rule
// — a rewrite (an equation or an ⇔, under ∀ and under Horn antecedents)
// or a closure rule (an atom under the antecedents, `finite(s) ⇒
// finite(insert(x, s))`, which discharges the side conditions of the
// set's rewrites; tactic.ClosureSimpClauses). A card and a definition
// are refused. The census per family is logged, the closure rules
// named.
func TestSimpRuleEntriesAreRules(t *testing.T) {
	perFamily := map[string]int{}
	for _, e := range registry.All() {
		if !e.Simp {
			continue
		}
		perFamily[e.Family().Name]++
		if e.ServedAsAxiom() {
			t.Errorf("%s: a card or the postulate is no simp rule — a rule rests on a proof", e.Name)
			continue
		}
		if e.Definition != 0 {
			t.Errorf("%s: a definition's rules are installed by its shape already; Simp is for theorems", e.Name)
			continue
		}
		if closures := tactic.ClosureSimpClauses(e.Statement().Prop); len(closures) > 0 {
			t.Logf("%s: a closure rule of its set: %v", e.Name, closures)
		}
	}
	for fam, n := range perFamily {
		t.Logf("simp set: %s holds %d rule(s)", fam, n)
	}
}
