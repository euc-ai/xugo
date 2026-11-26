package serve

import (
	"testing"

	"github.com/euc-ai/xugo/prover/tactic"
)

// TestRecursionPrincipleCorpusShapes pins tactic.AnalyzeRecursionPrinciple
// against the REAL stored statements of the three bootstrap recursion
// schemas, exactly as they reach every env through the corpus
// LibraryThms loop (InductionPrinciples returns the whole map, so the
// serve and the harnesses serve these under the same names). This is
// the drift detector for the equation compiler: an emit regeneration
// that changes a schema's surface arrangement must fail HERE, not
// inside a define session.
//
// The list and option schemas serve from the chapters (datatypes/list,
// datatypes/option), so what is pinned here is those entries'
// headlines. Both close over their parameters, so their cases'
// ParamBound is true.
func TestRecursionPrincipleCorpusShapes(t *testing.T) {
	thms := InductionPrinciples()
	for _, tc := range []struct {
		name   string
		unique bool
		ctors  []string
		bound  bool // params ∀-bound — every served schema closes over them
	}{
		{"num_recursion", true, []string{"_0", "suc"}, true},
		{"list_recursion", false, []string{"nil", "cons"}, true},
		{"option_recursion", false, []string{"none", "some"}, true},
	} {
		thm, ok := thms[tc.name]
		if !ok || thm == nil {
			t.Fatalf("%s: missing from the corpus LibraryThms map", tc.name)
		}
		tmpl, err := tactic.AnalyzeRecursionPrinciple(thm)
		if err != nil {
			t.Fatalf("%s: %v", tc.name, err)
		}
		if tmpl.Unique != tc.unique {
			t.Errorf("%s: Unique = %v, want %v", tc.name, tmpl.Unique, tc.unique)
		}
		if len(tmpl.Cases) != len(tc.ctors) {
			t.Fatalf("%s: %d cases, want %d", tc.name, len(tmpl.Cases), len(tc.ctors))
		}
		for i, want := range tc.ctors {
			if got := string(tmpl.Cases[i].Constructor.Name()); got != want {
				t.Errorf("%s: case %d constructor = %q, want %q", tc.name, i, got, want)
			}
			if tmpl.Cases[i].ParamBound != tc.bound {
				t.Errorf("%s: case %d ParamBound = %v, want %v",
					tc.name, i, tmpl.Cases[i].ParamBound, tc.bound)
			}
		}
		// Dispatch closes the loop: the carrier's first name candidate
		// resolves back to a served principle.
		cands := tactic.RecursionPrincipleNameCandidates(tmpl.CarrierType)
		if len(cands) == 0 {
			t.Fatalf("%s: no name candidates for carrier", tc.name)
		}
		if thms[cands[0]] == nil {
			t.Errorf("%s: candidate %q not served in LibraryThms", tc.name, cands[0])
		}
	}
}
