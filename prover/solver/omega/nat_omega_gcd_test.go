package omega

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// A single gcd-unsat equality with variables on both sides — `m + m =
// n + n + 3`, gcd 2 ∤ 3 — is refuted through its two ≤ rows: the
// rounding cuts tighten them to m ≤ n + 1 and n + 2 ≤ m, which
// Fourier–Motzkin adds to 1 ≤ 0, each cut proved by roundedCut. The
// grounded one-side-constant route (groundedGcdEq) declines this shape;
// the proof below is the fall-through from it.
func TestIntRefuteProof_TwoSidedGcdEquality(t *testing.T) {
	installTestBundle(t)
	for _, tc := range []struct {
		name string
		cs   []LinConstraint
	}{
		{"m+m = n+n+3", []LinConstraint{con(tn("m + m"), tn("n + n + 3"), opEQ)}},
		{"n+n+3 = m+m", []LinConstraint{con(tn("n + n + 3"), tn("m + m"), opEQ)}},
		{"m+m+k+k = n+n+7", []LinConstraint{con(tn("m + m + k + k"), tn("n + n + 7"), opEQ)}},
		// The grounded route, for comparison: one side a pure constant.
		{"m+m = 3", []LinConstraint{con(tn("m + m"), tn("3"), opEQ)}},
	} {
		w, ok := IntRefuteProof(tc.cs)
		if !ok {
			t.Fatalf("%s: expected an integer refutation, got none", tc.name)
		}
		if !w.Conclusion().Equals(prop.F) {
			t.Errorf("%s: conclusion = %v, want ⊥", tc.name, w.Conclusion())
		}
		hypsAmong(t, tc.name, w, []Term{constraintTerm(tc.cs[0])})
	}
	// Satisfiable (m = n + 2): neither the verdict nor the proof.
	sat := []LinConstraint{con(tn("m + m"), tn("n + n + 4"), opEQ)}
	if unsat, ok := IntUnsat(sat); ok && unsat {
		t.Errorf("m+m = n+n+4 must NOT be unsat (m = n + 2)")
	}
	if _, ok := IntRefuteProof(sat); ok {
		t.Errorf("m+m = n+n+4 must NOT be refutable (m = n + 2)")
	}
}
