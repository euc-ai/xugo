package omega

// The num facts read in ℝ and ℤ through their casts (domain.go liftHyp): a
// comparison of num images closes from the num facts the context holds —
// stated over num, or over the images themselves — and the result's
// hypotheses are the goal's. The hyp-free drop (realProveOfNum) is unchanged.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

func TestOfNumDrop_UnderNumHyps(t *testing.T) {
	installTestBundle(t)
	a, b := numVar("a"), numVar("b")
	A, B := realOfNumT(a), realOfNumT(b)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a ≤ b ⊢ &a ≤ &b", []Term{le(a, b)}, realLeT(A, B)},
		{"a < b ⊢ &a < &b", []Term{lt(a, b)}, realLtT(A, B)},
		{"a = b ⊢ &a = &b", []Term{eqT(a, b)}, eqT(A, B)},
		{"b < a + 1 ⊢ &b ≤ &a, an integrality step", []Term{lt(b, plus(a, Numeral(1)))}, realLeT(B, A)},
		{"&a ≤ &b ⊢ &a < &b + &1, a hypothesis over the images", []Term{realLeT(A, B)}, realLtT(A, realPlusT(B, realLit(1)))},
		{"hyp-free as before", nil, realLeT(A, realPlusT(A, realLit(1)))},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	if realDecides(t, []Term{le(a, b)}, realLtT(A, B)) {
		t.Error("a ≤ b must not decide &a < &b")
	}
}

// TestOfNumDrop_HypSubset: a hypothesis stated over the images is read through
// its num drop, and the result rests on the hypothesis itself, never on the
// derived num reading.
func TestOfNumDrop_HypSubset(t *testing.T) {
	installTestBundle(t)
	a, b := numVar("a"), numVar("b")
	A, B := realOfNumT(a), realOfNumT(b)
	hyps := []Term{realLeT(A, B)}
	w := RealArithDecideWithHyps(hyps)(realLtT(A, realPlusT(B, realLit(1))))
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		t.Fatal("declined &a ≤ &b ⊢ &a < &b + &1")
	}
	for i := 0; i < w.NumHyps(); i++ {
		if !slices.ContainsFunc(hyps, w.Hyp(i).AlphaEquals) {
			t.Errorf("stray hypothesis %v not among the goal's", w.Hyp(i))
		}
	}
}

// TestOfNumDrop_IntTwin: the same over int_of_num images.
func TestOfNumDrop_IntTwin(t *testing.T) {
	installTestBundle(t)
	a, b := numVar("a"), numVar("b")
	A, B := intOfNumT(a), intOfNumT(b)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a ≤ b ⊢ &a ≤ &b", []Term{le(a, b)}, intLeT(A, B)},
		{"a < b ⊢ &a < &b", []Term{lt(a, b)}, intLtT(A, B)},
		{"a = b ⊢ &a = &b", []Term{eqT(a, b)}, eqT(A, B)},
		{"&a ≤ &b ⊢ &a < &b + &1", []Term{intLeT(A, B)}, intLtT(A, intPlusT(B, intLit(1)))},
		{"b < a + 1 ⊢ &b ≤ &a, an integrality step", []Term{lt(b, plus(a, Numeral(1)))}, intLeT(B, A)},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !intDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	if intDecides(t, []Term{le(a, b)}, intLtT(A, B)) {
		t.Error("a ≤ b must not decide &a < &b over int")
	}
}

// TestOfNumLift_Rows: a num hypothesis is a row over the images (domain.go
// liftHyp), so the linear layer alone — no drop — combines it with the real
// facts: `4 ≤ n ∧ x·x ≤ &4 ⊢ x·x ≤ &n`, the shape a divisor's bound takes
// in real_trigonometry.CosTaylorBounds.
func TestOfNumLift_Rows(t *testing.T) {
	installTestBundle(t)
	a, b, n := numVar("a"), numVar("b"), numVar("n")
	A, B, N := realOfNumT(a), realOfNumT(b), realOfNumT(n)
	x := rr("x")
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a ≤ b lifts", []Term{le(a, b)}, realLeT(A, B)},
		{"a > b lifts through the bridge", []Term{gt(a, b)}, realLtT(B, A)},
		{"a = b lifts", []Term{eqT(a, b)}, realLeT(B, A)},
		{"a divisor's bound: 4 ≤ n ∧ x·x ≤ &4 ⊢ x·x ≤ &n",
			[]Term{le(Numeral(4), n), realLeT(realStarT(x, x), realLit(4))}, realLeT(realStarT(x, x), N)},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			w, ok := RealLinProve(slices.Values(r.hyps), r.goal)
			if !ok {
				t.Fatalf("RealLinProve declined %v under %v", r.goal, r.hyps)
			}
			for i := 0; i < w.NumHyps(); i++ {
				if !slices.ContainsFunc(r.hyps, w.Hyp(i).AlphaEquals) {
					t.Errorf("stray hypothesis %v", w.Hyp(i))
				}
			}
		})
	}
	// The int twin.
	IA, IB := intOfNumT(a), intOfNumT(b)
	if _, ok := IntLinProve(slices.Values([]Term{lt(a, b)}), intLtT(IA, IB)); !ok {
		t.Error("IntLinProve declined a < b ⊢ &a < &b")
	}
	if _, ok := RealLinProve(slices.Values([]Term{le(a, b)}), realLtT(A, B)); ok {
		t.Error("a ≤ b must not give &a < &b")
	}
}
