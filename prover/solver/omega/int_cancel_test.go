package omega

// The hypothesis-side positive-factor cancellation over ℤ (int_cancel.go) —
// the twin of real_cancel_test.go. Since the monomial basis `P·a` and `P·b`
// are two distinct monomial unknowns, so nothing below this handler relates
// them: cancelling scales a premise by a VARIABLE, which the Farkas fragment
// does not do.
//
// These rows run under the placeholder bundle (bundle.go), so what they pin is
// the kernel COMPOSITION and the handler's decline boundary. The soundness of
// the leaves is pinned by TestInstallIntLemmaBundleBindingSignedProduct in
// library/serve, which runs fabricator-free against the lifted ℝ theorems.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

func intCancelDecides(t *testing.T, hyps []Term, goal Term) bool {
	t.Helper()
	w := IntArithDecideWithHyps(hyps)(goal)
	return w != nil && prop.Rhs(w).Equals(prop.T)
}

// TestIntCancelMul_ClosesAndDeclines drives the handler through the public
// decider. The `&0 ≤ c` rows are the soundness boundary: a nonnegative factor
// cancels nothing, since `&0·a ≤ &0·b` holds for every a and b.
func TestIntCancelMul_ClosesAndDeclines(t *testing.T) {
	installTestBundle(t)
	a, b, c, x, y := intVar("a"), intVar("b"), intVar("c"), intVar("x"), intVar("y")
	z := intLit(0)
	rows := []struct {
		name  string
		hyps  []Term
		goal  Term
		close bool
	}{
		{"shared factor on the LEFT",
			[]Term{intLtT(z, c), intLeT(intStarT(c, a), intStarT(c, b))}, intLeT(a, b), true},
		{"strict",
			[]Term{intLtT(z, c), intLtT(intStarT(c, a), intStarT(c, b))}, intLtT(a, b), true},
		{"shared factor on the RIGHT, read through MulSym",
			[]Term{intLtT(z, c), intLeT(intStarT(a, c), intStarT(b, c))}, intLeT(a, b), true},
		{"strict, right factor",
			[]Term{intLtT(z, c), intLtT(intStarT(a, c), intStarT(b, c))}, intLtT(a, b), true},
		{"a ≥ spelling bridges to ≤",
			[]Term{intLtT(z, c), intGeT(intStarT(c, b), intStarT(c, a))}, intLeT(a, b), true},
		{"the factor's positivity is DERIVED, not resident",
			[]Term{intLtT(z, x), intLtT(z, y), intLeT(intStarT(intStarT(x, y), a), intStarT(intStarT(x, y), b))},
			intLeT(a, b), true},
		{"the cancelled fact feeds a further linear step",
			[]Term{intLtT(z, c), intLeT(intStarT(c, a), intStarT(c, b))}, intLeT(a, intPlusT(b, intLit(1))), true},

		// The soundness boundary: nonnegative is NOT enough for the
		// cancellation (c = 0 makes c·a ≤ c·b say nothing).
		{"BOUNDARY: &0 ≤ c does not cancel",
			[]Term{intLeT(z, c), intLeT(intStarT(c, a), intStarT(c, b))}, intLeT(a, b), false},
		// The strict twin IS valid (c = 0 makes the hypothesis false) and
		// closes, not by cancellation but by the products pass
		// (int_products.go): c ≥ 0 times the negated goal's a − b ≥ 0.
		{"&0 ≤ c with a strict product: valid, closed by the products pass",
			[]Term{intLeT(z, c), intLtT(intStarT(c, a), intStarT(c, b))}, intLtT(a, b), true},
		{"no sign for the factor at all",
			[]Term{intLeT(intStarT(c, a), intStarT(c, b))}, intLeT(a, b), false},
		{"the factors are not shared",
			[]Term{intLtT(z, c), intLeT(intStarT(c, a), intStarT(x, b))}, intLeT(a, b), false},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if got := intCancelDecides(t, r.hyps, r.goal); got != r.close {
				t.Errorf("closed=%v, want %v", got, r.close)
			}
		})
	}
}

// TestIntCancelMul_DeclinesWithoutTheShape: the cheap structural decline — a
// hypothesis set with no product-vs-product comparison produces no candidate,
// so the handler costs one walk of the hyp list.
func TestIntCancelMul_DeclinesWithoutTheShape(t *testing.T) {
	installTestBundle(t)
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	hyps := []Term{intLtT(intLit(0), c), intLeT(a, b)}
	if cands := intCancelCandidates(hyps); len(cands) != 0 {
		t.Errorf("got %d candidates from a product-free hyp set; want none", len(cands))
	}
	if _, ok := intProveCancelMul(hyps, intLeT(a, b)); ok {
		t.Error("the handler must decline when no hypothesis compares two products")
	}
}

// TestIntCancelMul_FactHypsSubsetOfGoal is the provenance contract: each
// derived fact's hypotheses are the sign proof's plus the one product
// hypothesis it cancelled, all drawn from the goal's own — which is what lets
// enrichAndCut's cut-back leave the result's hypotheses ⊆ the goal's.
func TestIntCancelMul_FactHypsSubsetOfGoal(t *testing.T) {
	installTestBundle(t)
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	hyps := []Term{intLtT(intLit(0), c), intLeT(intStarT(c, a), intStarT(c, b))}
	facts := intCancelFacts(hyps)
	if len(facts) != 1 {
		t.Fatalf("got %d derived facts; want 1", len(facts))
	}
	for h := range facts[0].HypIter() {
		if !slices.ContainsFunc(hyps, h.AlphaEquals) {
			t.Errorf("stray hypothesis %v — not one of the goal's", h)
		}
	}
}
