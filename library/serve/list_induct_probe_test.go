package serve

// The list-induction principle's serving contract. The datatype door
// derives the principle and the corpus list.Induction backs it:
//
//	(a) tactic.AnalyzeInductionPrinciple ACCEPTS the chapter's entry as
//	 stated — the datatype door derives it in the standard form;
//	(b) it ACCEPTS tactic.ListInductProp(), the engine's own spelling of
//	 that form;
//	(c) Normalize(ListInductProp()) is the entry's own key — the two
//	 spellings are one statement;
//	(d) PromiseForGeneral over the Go spelling forces end-to-end to a
//	 kernel cert of that shape.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"

	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/prover/tactic"
)

// The entry is analyzer-ready as stated: the datatype door derives the
// principle in the standard form, so the corpus serves it raw, with no
// bridge (the bridge remains for num_induction, whose chapter headline
// is the chapter's own spelling).
func TestProbe_ListInduct_EntryFormAnalyzerReady(t *testing.T) {
	headline := prop.WrapProp(EntryThm(env(), list.Induction))
	tmpl, err := tactic.AnalyzeInductionPrinciple(headline)
	if err != nil {
		t.Fatalf("the chapter's list_induction entry is not analyzer-ready: %v", err)
	}
	if got := len(tmpl.Cases); got != 2 {
		t.Fatalf("expected 2 cases (nil, cons), got %d", got)
	}
}

func TestProbe_ListInduct_GoSpellingAccepted(t *testing.T) {
	principle := tactic.ListInductProp()
	tmpl, err := tactic.AnalyzeInductionPrinciple(principle)
	if err != nil {
		t.Fatalf("ListInductProp rejected: %v", err)
	}
	if got := len(tmpl.Cases); got != 2 {
		t.Fatalf("expected 2 cases (nil, cons), got %d", got)
	}
	t.Logf("accepted: index=%v cases=%d", tmpl.IndexVar, len(tmpl.Cases))
}

func TestProbe_ListInduct_NormalizeKeyMatchesEntryKey(t *testing.T) {
	principle := tactic.ListInductProp()
	normalized, _ := prop.Normalize(principle)
	own := core.PropKey(list.Induction.Entry().Key)
	t.Logf("Normalize(ListInductProp) key: %s", normalized.AlphaKey())
	t.Logf("list.Induction own key:        %s", own)

	// The entry's own key is its normalized key, and the analyzer's
	// spelling normalizes to the same key: the two spellings are one
	// statement.
	if normalized.AlphaKey() != own {
		t.Fatal("no key path connects ListInductProp to list.Induction — bridge blocked")
	}
}

// End-to-end: PromiseForGeneral over the Go spelling forces to a real
// kernel cert — through list.Induction (the corpus bootstrap and the
// by-key channel both answer for the row) — and reconstructs back to
// that spelling, so LibraryThms["list_induction"] is corpus-backed
// with zero TestThm trust and the analyzer's shape at once.
func TestListInduct_PromiseForGeneralForces(t *testing.T) {
	principle := tactic.ListInductProp()
	p := PromiseForGeneral(principle)
	if _, err := tactic.AnalyzeInductionPrinciple(p); err != nil {
		t.Fatalf("promise-backed principle rejected by analyzer: %v", err)
	}
	cert := core.Force(context.Background(), core.AsThm(p))
	if cert.IsZero() || !cert.Proved() {
		t.Fatal("PromiseForGeneral(ListInductProp) did not force to a proved cert")
	}
	if !cert.Conclusion().AlphaEquals(principle.Conclusion()) {
		t.Fatalf("cert conclusion %v ≠ principle conclusion %v",
			cert.Conclusion(), principle.Conclusion())
	}
}

// Regression: InductionPrinciples must expose analyzer-ready
// principles for every corpus-covered inductive type. This is what the
// serve engine overlays onto LibraryThms — if a name here regresses to
// an unanalyzable shape, `induction` breaks for that type again.
func TestInductionPrinciples_AnalyzerReady(t *testing.T) {
	principles := InductionPrinciples()
	for _, name := range []string{"num_induction", "list_induction", "option_induction"} {
		thm, ok := principles[name]
		if !ok || thm == nil {
			t.Fatalf("%s missing from InductionPrinciples()", name)
		}
		tmpl, err := tactic.AnalyzeInductionPrinciple(thm)
		if err != nil {
			t.Fatalf("%s: not analyzer-ready: %v", name, err)
		}
		if len(tmpl.Cases) == 0 {
			t.Fatalf("%s: template has no cases", name)
		}
		t.Logf("%s: %d cases, index type %v", name, len(tmpl.Cases), tmpl.IndexType)
	}
}
