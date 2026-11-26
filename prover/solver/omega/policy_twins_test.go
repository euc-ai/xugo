package omega

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// The WithPolicy twins of the pre-policy-seam entries (IntArithDecideWithHyps,
// the RingProveFull family). Contract under test: gated OFF they decline cleanly — never reaching the
// bundle — and gated ON they are the ungated original, byte for byte. The
// "off" policies below disable ONLY the domain under test, so a twin reading
// the wrong policy field fails the test rather than passing vacuously.

var (
	allOn   = ArithPolicy{Nat: true, Real: true, Int: true}
	natOff  = ArithPolicy{Nat: false, Real: true, Int: true}
	realOff = ArithPolicy{Nat: true, Real: false, Int: true}
	intOff  = ArithPolicy{Nat: true, Real: true, Int: false}
)

// checkRingTwin drives one ring twin against its ungated original on a pair the
// original closes: the twin must decline under offPolicy and reproduce the
// original's conclusion under allOn.
func checkRingTwin(
	t *testing.T, name string, l, r Term,
	original func(Term, Term) (*prop.PropWrapper, bool),
	twin func(Term, Term, ArithPolicy) (*prop.PropWrapper, bool),
	offPolicy ArithPolicy,
) {
	t.Helper()
	want, ok := original(l, r)
	if !ok {
		t.Fatalf("%s: ungated original failed to close the fixture pair", name)
	}
	if _, ok := twin(l, r, offPolicy); ok {
		t.Errorf("%s: twin proved under a policy that forbids its domain", name)
	}
	got, ok := twin(l, r, allOn)
	if !ok {
		t.Fatalf("%s: twin declined under an allowing policy", name)
	}
	if !got.Conclusion().AlphaEquals(want.Conclusion()) {
		t.Errorf("%s: twin proved %v, original proved %v", name, got, want)
	}
}

func TestRingProveFullWithPolicyGate(t *testing.T) {
	checkRingTwin(t, "nat", tn("a + b"), tn("b + a"),
		RingProveFull, RingProveFullWithPolicy, natOff)
}

func TestIntRingProveFullWithPolicyGate(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	checkRingTwin(t, "int", intPlusT(x, y), intPlusT(y, x),
		IntRingProveFull, IntRingProveFullWithPolicy, intOff)
}

func TestRealRingProveFullWithPolicyGate(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	checkRingTwin(t, "real", realPlusT(x, y), realPlusT(y, x),
		RealRingProveFull, RealRingProveFullWithPolicy, realOff)
}

func TestIntArithDecideWithHypsWithPolicyGate(t *testing.T) {
	x := intVar("x")
	hyps := []Term{intLtT(x, intLit(3))}
	target := intLtT(x, intLit(5)) // decidable from the hyp by transitivity

	want := IntArithDecideWithHyps(hyps)(target)
	if want == nil || !prop.Rhs(want).Equals(prop.T) {
		t.Fatalf("ungated IntArithDecideWithHyps failed to decide the fixture: %v", want)
	}
	if w := IntArithDecideWithHypsWithPolicy(hyps, intOff)(target); w != nil {
		t.Errorf("gated-off twin decided %v under policy.Int=false", w)
	}
	got := IntArithDecideWithHypsWithPolicy(hyps, allOn)(target)
	if got == nil {
		t.Fatal("gated-on twin declined where the original decided")
	}
	if !got.Conclusion().AlphaEquals(want.Conclusion()) {
		t.Errorf("gated-on twin decided %v, original decided %v", got, want)
	}
}
