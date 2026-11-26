// Negative controls for the domain vocabulary table.
//
// The checks exist because the failure modes here are SILENT. An
// undeclared set constructor still parses (the text-DSL has its own
// def-less meta), so a chapter that loses a declaration does not fail
// to build — set_tac simply finds nothing to unfold and reports a
// residual.
package setvocab

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
)

// TestDeclareRejectsUnknownName pins the panic. Without it, a typo'd
// name would be the one input to this package that could fail open.
//
// The message is checked, not merely the fact of a panic: this calls
// Declare with a nil Script, so a panic proves nothing on its own —
// a KNOWN name would panic too, on the nil deref, and the test would
// pass while checking nothing. It is non-vacuous only because the
// lookup — the table, then the mint fallback — runs first and names
// the offending constructor.
func TestDeclareRejectsUnknownName(t *testing.T) {
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("Declare accepted an unknown set constructor — it must panic, since an " +
				"undeclared name still parses and the chapter would silently lose its def-carrying meta")
		}
		msg, ok := r.(string)
		if !ok || !strings.Contains(msg, "NOT_A_SET_CONSTRUCTOR") {
			t.Fatalf("panicked, but not on the unknown name — got %v; "+
				"if this is the nil-Script deref, the check is vacuous", r)
		}
	}()
	Declare(nil, "NOT_A_SET_CONSTRUCTOR")
}

// TestStandardVocabularyIsNotMutable guards the one hazard of exporting
// a slice: a caller appending to or reordering the returned list must
// not reach the next caller's.
func TestStandardVocabularyIsNotMutable(t *testing.T) {
	first := proof.StandardSetVocabulary()
	if len(first) == 0 {
		t.Fatal("StandardSetVocabulary is empty")
	}
	first[0] = "CLOBBERED"
	if second := proof.StandardSetVocabulary(); second[0] == "CLOBBERED" {
		t.Fatal("StandardSetVocabulary returns shared backing storage " +
			"— one caller's mutation reaches every later set_tac call")
	}
}
