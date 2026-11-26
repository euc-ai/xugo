package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A split whose two arms carry one guard is one case: `p ∨ p`, `a ≠ a` read
// as `a < a ∨ a < a`, `p ⇒ ¬p` read as `¬p ∨ ¬p`. ByCases at one guard holds
// one implication, which the one arm's proof discharges.

// requireProves fails unless w is `Γ ⊢ goal` with Γ among hyps.
func requireProves(t *testing.T, name string, w *prop.PropWrapper, ok bool, hyps []Term, goal Term) {
	t.Helper()
	if !ok {
		t.Errorf("%s: not proved", name)
		return
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("%s: conclusion = %v, want %v", name, w.Conclusion(), goal)
	}
	for h := range w.HypIter() {
		if !slices.ContainsFunc(hyps, h.AlphaEquals) {
			t.Errorf("%s: hypothesis %v is not among the inputs", name, h)
		}
	}
}

// TestSplitByCases_CoincidentGuards holds the assembly itself to it, on a
// hypothesis `p ∨ p` and a branch prover that is `p ⊢ p`: the result is
// `p ∨ p ⊢ p`, and the one case is proved once.
func TestSplitByCases_CoincidentGuards(t *testing.T) {
	p := ext.Var("p", ext.TypeBool)
	h := or(p, p)
	sa, ok := hypSplittable(h)
	if !ok {
		t.Fatal("hypSplittable declined a disjunction hyp")
	}
	calls := 0
	w, ok := splitByCases(sa, []Term{h}, p, func(hs []Term) (*prop.PropWrapper, bool) {
		calls++
		if !slices.ContainsFunc(hs, p.AlphaEquals) {
			t.Errorf("the branch was not given its guard: %v", hs)
		}
		return prop.Assume(p), true
	})
	requireProves(t, "p ∨ p ⊢ p", w, ok, []Term{h}, p)
	if ok && !w.HasHyp(h) {
		t.Errorf("the split's hypothesis is gone: %v", w)
	}
	if calls != 1 {
		t.Errorf("the one case was proved %d times", calls)
	}
}

// TestSplitCoincidentGuards_Nat runs the three hypothesis kinds through the
// num prover. Each hypothesis is absurd, so any goal follows from it.
func TestSplitCoincidentGuards_Nat(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")
	ltc := ext.ForAll(a, b)(or(or(lt(a, b), lt(b, a)), eqT(a, b)))
	SetNatLemmaBundle(&NatLemmaBundle{LessThanTrichotomy: prop.WrapProp(core.TestThm(ltc))})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
	goal := lt(b, c)
	for _, row := range []struct {
		name string
		hyp  Term
	}{
		{"a ≠ a", not(eqT(a, a))},
		{"a < a ∨ a < a", or(lt(a, a), lt(a, a))},
		{"a = a ⇒ a ≠ a", imply(eqT(a, a), not(eqT(a, a)))},
	} {
		hyps := []Term{row.hyp}
		w, ok := proveSplit(proveLinThenInt, nil, hyps, goal, nil)
		requireProves(t, row.name, w, ok, hyps, goal)
	}
}

// TestSplitCoincidentGuards_Int is the ℤ twin.
func TestSplitCoincidentGuards_Int(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	goal := intLtT(y, z)
	for _, row := range []struct {
		name string
		hyp  Term
	}{
		{"x ≠ x", not(eqT(x, x))},
		{"x < x ∨ x < x", or(intLtT(x, x), intLtT(x, x))},
		{"x = x ⇒ x ≠ x", imply(eqT(x, x), not(eqT(x, x)))},
	} {
		hyps := []Term{row.hyp}
		w, ok := intProveSplit(IntLinProve, nil, hyps, goal, nil)
		requireProves(t, row.name, w, ok, hyps, goal)
	}
}

// TestSplitCoincidentGuards_Real is the ℝ twin.
func TestSplitCoincidentGuards_Real(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	goal := realLtT(y, z)
	for _, row := range []struct {
		name string
		hyp  Term
	}{
		{"x ≠ x", not(eqT(x, x))},
		{"x < x ∨ x < x", or(realLtT(x, x), realLtT(x, x))},
		{"x = x ⇒ x ≠ x", imply(eqT(x, x), not(eqT(x, x)))},
	} {
		hyps := []Term{row.hyp}
		w, ok := realProveSplit(RealLinProve, nil, hyps, goal, nil)
		requireProves(t, row.name, w, ok, hyps, goal)
	}
}
