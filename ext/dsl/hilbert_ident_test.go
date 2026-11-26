package dsl

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
)

// A bare `ε` is the VARIABLE ε; `εx.` is the Hilbert binder. The ε-δ
// vocabulary of analysis is written with its own letters, and the
// binder keeps its spelling (`εy:real. …`, the printers').
func TestEpsilonVariableBesideHilbertBinder(t *testing.T) {
	vars := map[string]core.HolType{"f": core.MakeFun(RealType, RealType), "c": RealType, "l": RealType}
	res := ParsePropTextInScope("∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀x:real. real_abs(x - c) < δ ⇒ real_abs(f(x) - l) < ε",
		&ParseScope{Vars: vars})
	if len(res.Errors) > 0 {
		t.Fatalf("ε as a variable: %v", res.Errors)
	}
	// The Hilbert binder, with and without a type annotation, and a
	// Skolem-subscripted ε — the normalizer's `ε₀` is `ε_0`.
	for _, text := range []string{
		"∀c:real. (εy:real. y = c) = c",
		"∀ε₀:real. &0 < ε₀ ⇒ (εy:real. y < ε₀) < ε₀",
	} {
		if r := ParsePropTextInScope(text, &ParseScope{Vars: vars}); len(r.Errors) > 0 {
			t.Fatalf("%q: %v", text, r.Errors)
		}
	}
	// The scope-free formatter round-trips both spellings.
	out, err := FormatStmtText("∀ε:real. &0 < ε ⇒ (εy:real. y < ε) < ε")
	if err != nil || !strings.Contains(out, "∀ε:real. &0 < ε ⇒ (εy:real. y < ε) < ε") {
		t.Fatalf("FormatStmtText: %q (%v)", out, err)
	}
}
