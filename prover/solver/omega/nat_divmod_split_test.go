package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// installDivModSplitBundle is the nat_div/nat_mod test bundle over the
// integer-cut leaves (a strict row `0 < r` is read as `1 ≤ r` through
// them), with the trichotomy the `≠`-hypothesis split reads in its normal
// form `∀a b. ((a < b) ∨ (b < a)) ∨ (a = b)`.
func installDivModSplitBundle(t *testing.T) {
	t.Helper()
	installTestBundle(t)
	restore := installDivModTestBundle(t)
	t.Cleanup(restore)
	a, b := numVar("a"), numVar("b")
	bundle := *natLemmaBundle
	bundle.LessThanTrichotomy = prop.WrapProp(core.TestThm(
		ext.ForAll(a, b)(or(or(lt(a, b), lt(b, a)), eqT(a, b)))))
	SetNatLemmaBundle(&bundle)
}

// TestProveDecAtom_HypSplitReadsDivModBounds: a decision that needs a
// hypothesis split AND a bound of a nat_mod atom. The `≠` hypothesis is
// read by the split alone and `nat_mod(n, 2) ≤ n` is a fact of the
// enrichment alone, so each row is closed only where a split branch holds
// the bounds.
func TestProveDecAtom_HypSplitReadsDivModBounds(t *testing.T) {
	installDivModSplitBundle(t)
	n := numVar("n")
	one, two := Numeral(1), Numeral(2)
	odd := not(eqT(natZero, modT(n, two))) // 0 ≠ nat_mod(n, 2)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"an odd number is not 0", []Term{odd}, not(eqT(n, natZero))},
		{"an odd number is at least 1", []Term{odd}, le(one, n)},
		{"the remainder's zero on the other side", []Term{not(eqT(modT(n, two), natZero))}, le(one, n)},
		{"an odd number other than 1 exceeds 1", []Term{not(eqT(n, one)), odd}, lt(one, n)},
		{"a positive remainder beside a ≠ on the dividend", []Term{lt(natZero, modT(n, two)), not(eqT(n, one))}, lt(one, n)},
		{"a nonzero quotient", []Term{not(eqT(natZero, divT(n, two)))}, not(eqT(n, natZero))},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			w, ok := proveDecAtom(slices.Values(r.hyps), r.goal)
			if !ok {
				t.Fatalf("not decided: the goal %s", ext.PrintTerm(r.goal))
			}
			if !w.Conclusion().AlphaEquals(r.goal) {
				t.Errorf("conclusion %s, want %s", ext.PrintTerm(w.Conclusion()), ext.PrintTerm(r.goal))
			}
			for _, h := range w.Hyps() {
				if !slices.ContainsFunc(r.hyps, h.AlphaEquals) {
					t.Errorf("the proof carries %s, which is no hypothesis of the row", ext.PrintTerm(h))
				}
			}
		})
	}
	// False at n = 1: the split with the bounds must not close it.
	if _, ok := proveDecAtom(slices.Values([]Term{odd}), le(two, n)); ok {
		t.Error("0 ≠ nat_mod(n, 2) ⊢ 2 ≤ n decided, and it is false at n = 1")
	}
}
