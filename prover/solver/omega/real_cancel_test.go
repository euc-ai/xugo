package omega

// The hypothesis-side positive-factor cancellation (real_cancel.go): a
// hypothesis comparing two products that share a factor yields the cancelled
// comparison once the factor is provably STRICTLY positive. Since the
// monomial-basis landing `P·a` and `P·b` are two distinct monomial unknowns, so
// nothing below this handler relates them — cancelling scales a premise by a
// VARIABLE, which the Farkas fragment does not do.
//
// These rows run under the placeholder bundle (bundle.go), so what they pin is
// the kernel COMPOSITION and the handler's decline boundary; the soundness of
// the leaves is pinned by TestInstallRealBundleBindingStructural in
// library/serve, which runs fabricator-free against the real corpus theorems.

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// TestRealCancelMul_ClosesAndDeclines drives the whole handler through the
// public decider. `close` says whether the goal must collapse to ⊤.
func TestRealCancelMul_ClosesAndDeclines(t *testing.T) {
	rows := []struct {
		name  string
		hyps  []string
		goal  string
		close bool
	}{
		// The probe: the shared factor on the LEFT of both sides.
		{"left factor, non-strict",
			[]string{"&0 < p", "p * a <= p * b"}, "a <= b", true},
		{"left factor, strict",
			[]string{"&0 < p", "p * a < p * b"}, "a < b", true},
		// The RIGHT-factor spelling goes through the same two lemmas, both
		// sides commuted (no right-factor field).
		{"right factor, non-strict",
			[]string{"&0 < p", "a * p <= b * p"}, "a <= b", true},
		{"right factor, strict",
			[]string{"&0 < p", "a * p < b * p"}, "a < b", true},
		// The `>` / `≥` spellings of the same hypothesis bridge to `<` / `≤`,
		// so the capability does not depend on how the fact was written.
		{"the hypothesis spelled with ≥",
			[]string{"&0 < p", "p * b >= p * a"}, "a <= b", true},
		{"the hypothesis spelled with >",
			[]string{"&0 < p", "p * b > p * a"}, "a < b", true},
		// The cancelled comparison is an ordinary linear row once derived, so
		// it combines with the other hypotheses.
		{"the cancelled row combines linearly",
			[]string{"&0 < p", "p * a <= p * b", "b <= c"}, "a <= c", true},
		// The factor's positivity may itself need the hypotheses, not just a
		// resident `&0 < p` echo.
		{"the factor's sign derived, not resident",
			[]string{"&1 <= p", "p * a <= p * b"}, "a <= b", true},
		// A compound shared factor is cancelled the same way — the sign side
		// condition rides the sign-of-product handler.
		{"a compound shared factor",
			[]string{"&0 < p", "&0 < q", "(p * q) * a <= (p * q) * b"}, "a <= b", true},

		// ── The decline boundary. ──
		// No sign fact at all: the two products stay unrelated unknowns.
		{"boundary: no sign fact resident",
			[]string{"p * a <= p * b"}, "a <= b", false},
		// A factor known NEGATIVE does not cancel in this direction (the
		// comparison would flip); the handler asks for `&0 < p` and declines.
		{"boundary: the shared factor is negative",
			[]string{"p < &0", "p * a <= p * b"}, "a <= b", false},
		// THE SOUNDNESS TRAP: `&0 ≤ p` is NOT enough. `&0 · a ≤ &0 · b` holds
		// for every a and b, so a nonnegative factor cancels nothing.
		{"boundary: &0 ≤ p is not enough (non-strict)",
			[]string{"&0 <= p", "p * a <= p * b"}, "a <= b", false},
		// A nonnegative factor with a STRICT product is valid (p = 0 makes
		// the hypothesis false) and closes — by the products pass
		// (real_products.go), not by the cancellation: p ≥ 0 times the
		// negated goal's a − b ≥ 0.
		{"&0 ≤ p with a strict product: valid, closed by the products pass",
			[]string{"&0 <= p", "p * a < p * b"}, "a < b", true},
		// Nor is the WRONG conclusion available from a right cancellation: a
		// positive factor gives `a ≤ b`, never `b ≤ a`.
		{"boundary: the cancelled comparison is not symmetric",
			[]string{"&0 < p", "p * a <= p * b"}, "b <= a", false},
		// The two sides must share a factor; distinct factors are two
		// unrelated monomials and cancel to nothing.
		{"boundary: no shared factor",
			[]string{"&0 < p", "&0 < q", "p * a <= q * b"}, "a <= b", false},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			hyps := make([]Term, len(r.hyps))
			for i, h := range r.hyps {
				hyps[i] = rb(h)
			}
			w := RealArithDecideWithHyps(hyps)(rb(r.goal))
			closed := w != nil && prop.Rhs(w).Equals(prop.T)
			if closed != r.close {
				t.Errorf("closed=%v, want %v (rewrite %v)", closed, r.close, w)
			}
		})
	}
}

// TestRealCancelMul_DeclinesWithoutTheShape pins the cheap decline: a
// hypothesis set with no product-vs-product comparison produces no candidate
// and no fact, so the handler does no proof work at all.
func TestRealCancelMul_DeclinesWithoutTheShape(t *testing.T) {
	hyps := []Term{rb("&0 < p"), rb("a <= b"), rb("&0 <= p * a")}
	if cands := realCancelCandidates(hyps); len(cands) != 0 {
		t.Errorf("realCancelCandidates(%v) = %v, want none", hyps, cands)
	}
	if facts := realCancelFacts(hyps); len(facts) != 0 {
		t.Errorf("realCancelFacts(%v) = %v, want none", hyps, facts)
	}
	if _, ok := realProveCancelMul(hyps, rb("a <= b")); ok {
		t.Error("realProveCancelMul closed a goal with no cancellable hypothesis")
	}
}

// TestRealCancelMul_FactHypsSubsetOfGoal: the derived fact is a real proof
// whose hypotheses are a subset of the goal's (the IsStronger contract that
// makes enrichAndCut's cut-back legitimate), and the handler's own result
// carries no injected conclusion.
func TestRealCancelMul_FactHypsSubsetOfGoal(t *testing.T) {
	hyps := []Term{rb("&1 <= p"), rb("p * a <= p * b")}
	facts := realCancelFacts(hyps)
	if len(facts) != 1 {
		t.Fatalf("realCancelFacts = %d facts, want 1", len(facts))
	}
	want := rb("a <= b")
	if !facts[0].Conclusion().AlphaEquals(want) {
		t.Errorf("fact conclusion %v, want %v", facts[0].Conclusion(), want)
	}
	for _, h := range facts[0].Hyps() {
		if !containsAlpha(hyps, h) {
			t.Errorf("fact hyp %v is not one of the goal's hyps %v", h, hyps)
		}
	}
	w, ok := realProveCancelMul(hyps, rb("a <= b"))
	if !ok {
		t.Fatal("realProveCancelMul declined the probe")
	}
	for _, h := range w.Hyps() {
		if !containsAlpha(hyps, h) {
			t.Errorf("result hyp %v is not one of the goal's hyps %v", h, hyps)
		}
	}
}

func containsAlpha(ts []Term, t Term) bool {
	for _, x := range ts {
		if x.AlphaEquals(t) {
			return true
		}
	}
	return false
}
