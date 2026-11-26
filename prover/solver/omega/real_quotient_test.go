package omega

// A quotient by a numeral beside another summand (real_quotient.go): the
// ε/2 shapes of an ε argument, which the whole-side clearing never reached.

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

func TestRealLiteralQuotient_BesideASummand(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"half of a positive added", []Term{pb("&0 < e")}, pb("x < x + e / &2")},
		{"half of a positive subtracted", []Term{pb("&0 < e")}, pb("x - e / &2 < x")},
		{"the quotient in a hypothesis beside an atom",
			[]Term{pb("&0 < e"), pb("s - e / &2 < y"), pb("y <= s")},
			realLtT(realAbsT(realSubT(rr("y"), rr("s"))), realDivT(rr("e"), realLit(2)))},
		{"the midpoint offset, an equation", nil, pb("(c + d / &2) - c = d / &2")},
		{"the cancellation itself", nil, pb("&2 * (m / &2) = m")},
		{"a halved point's ball fact", []Term{pb("&0 < d")},
			realLtT(realAbsT(realSubT(realPlusT(rr("c"), realDivT(rr("d"), realLit(2))), rr("c"))), rr("d"))},
		{"a third and two thirds", []Term{pb("&0 < e")}, pb("e / &3 + e / &3 < e")},
		{"nested literal divisors", []Term{pb("&0 < e")}, pb("(e / &2) / &2 < e")},
		{"the whole-side shape still closes", []Term{pb("&0 < e")}, pb("&0 < e / &2")},
		{"the halved triangle still closes",
			[]Term{
				realLtT(realAbsT(realSubT(rr("a"), rr("l"))), realDivT(rr("e"), realLit(2))),
				realLtT(realAbsT(realSubT(rr("b"), rr("l"))), realDivT(rr("e"), realLit(2)))},
			realLtT(realAbsT(realSubT(rr("a"), rr("b"))), rr("e"))},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// Without the sign of e the half is unrelated to anything: decline.
	if realDecides(t, nil, pb("x < x + e / &2")) {
		t.Error("closed `x < x + e/&2` with no sign for e")
	}
}

// TestRealLiteralQuotient_DefiningEquation pins the injected row: a closed
// theorem `y = (y/&k)·&k`, and no row for a symbolic or zero divisor.
// A quotient by a numeral that MULTIPLIES: the monomial q·R is tied to R·y
// by the defining equation times its cofactor, in the goal and in a
// hypothesis alike.
func TestRealLiteralQuotient_AsAFactor(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a left factor in the goal", []Term{pb("&2 * a <= d")}, pb("a <= &1 / &2 * d")},
		{"a right factor in the goal", []Term{pb("&2 * a <= d")}, pb("a <= d * (&1 / &2)")},
		{"a factor in the hypothesis", []Term{pb("&1 / &2 * d <= a")}, pb("d <= &2 * a")},
		{"two halves make the whole", nil, pb("&1 / &2 * d + &1 / &2 * d = d")},
		{"a quotient of an atom, multiplied", []Term{pb("&0 <= c * d")}, pb("d / &2 * c <= c * d")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// The reading invents nothing: a bound the facts do not give is declined.
	if realDecides(t, []Term{pb("&2 * a <= d")}, pb("a <= &1 / &3 * d")) {
		t.Errorf("a third is not a half")
	}
}

func TestRealLiteralQuotient_DefiningEquation(t *testing.T) {
	installTestBundle(t)
	eq := realQuotientDefiningEq(rr("e / &2"))
	if eq == nil {
		t.Fatal("no defining equation for e / &2")
	}
	if eq.NumHyps() != 0 {
		t.Errorf("the defining equation carries hypotheses: %v", eq.Conclusion())
	}
	if want := rb("e = (e / &2) * &2"); !eq.Conclusion().AlphaEquals(want) {
		t.Errorf("defining equation reads %v; want %v", eq.Conclusion(), want)
	}
	if qs := realLiteralQuotients([]Term{rb("x < e / z + e / &0")}); len(qs) != 0 {
		t.Errorf("collected a symbolic or zero divisor: %v", qs)
	}
	// Under a binder the quotient mentions the bound variable: not collected.
	if qs := realLiteralQuotients([]Term{rb("∀x:real. x / &2 < x")}); len(qs) != 0 {
		t.Errorf("collected a quotient under its binder: %v", qs)
	}
	// Resident equations are not injected twice.
	hyps := []Term{pb("&0 < e"), eq.Conclusion()}
	if facts := realQuotientFacts(hyps, pb("x < x + e / &2")); len(facts) != 0 {
		t.Errorf("re-injected a resident defining equation: %d fact(s)", len(facts))
	}
	_ = prop.T
}

// TestRealQuotientBasis_SymbolicDivisor: a quotient by a symbolic divisor is
// read as the monomial u·inv(v) (quotient_basis.go), so quotients over one
// divisor combine — the difference-quotient identities of the derivative
// rules — and a quotient is linear beside the facts that name it.
func TestRealQuotientBasis_SymbolicDivisor(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a sum over a common divisor", nil, pb("(a + b) / v = a / v + b / v")},
		{"the difference quotient of a sum", nil,
			pb("(f + g - (p + q)) / (x - c) = (f - p) / (x - c) + (g - q) / (x - c)")},
		{"of a scalar multiple", nil, pb("(k * f - k * p) / (x - c) = k * ((f - p) / (x - c))")},
		{"of a negative", nil, pb("(-f - -p) / (x - c) = -((f - p) / (x - c))")},
		{"of a product", nil,
			pb("(f * g - p * q) / (x - c) = f * ((g - q) / (x - c)) + q * ((f - p) / (x - c))")},
		{"of a constant", nil, pb("(k - k) / (x - c) = &0")},
		{"the quotient meets the written inverse", nil,
			eqT(rr("a / v"), realStarT(rr("a"), realInvT(rr("v"))))},
		{"linear in quotients a hypothesis names",
			[]Term{pb("q = a / v"), pb("r = b / v")}, pb("(a + b) / v = q + r")},
		{"an order through a shared divisor", []Term{pb("a / v <= b / v")}, pb("(a - b) / v <= &0")},
		// The field handler goes on meeting the `/` the author wrote.
		{"a positive divisor cleared from the goal",
			[]Term{pb("&0 < v"), pb("a <= b * v")}, pb("a / v <= b")},
		{"the sign of a quotient", []Term{pb("&0 < a"), pb("&0 < v")}, pb("&0 < a / v")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// Nothing is read that the definition does not say: two quotients over
	// one divisor are equal only when their numerators are.
	if realDecides(t, nil, pb("(a + b) / v = a / v")) {
		t.Error("closed `(a + b) / v = a / v`")
	}
	// Cancelling the divisor needs it nonzero.
	if realDecides(t, nil, pb("a / v * v = a")) {
		t.Error("closed `a / v * v = a` with no evidence that v is nonzero")
	}
}

// TestRealQuotientBasis_Readers pins the lockstep: the model reads the
// quotient as the product it denotes, the certificate proves that reading
// with no hypothesis, and a LITERAL divisor stays the unknown the
// literal-quotient pass ties to its numerator.
func TestRealQuotientBasis_Readers(t *testing.T) {
	installTestBundle(t)
	quotient, product := rr("(a + b) / v"), realStarT(rr("a + b"), realInvT(rr("v")))
	lq, ok1 := realDomain.linOf(quotient)
	lp, ok2 := realDomain.linOf(product)
	if !ok1 || !ok2 || !sameLinForm(lq, lp) {
		t.Fatalf("linOf reads the quotient and the product apart: %v vs %v", lq, lp)
	}
	lf, w, ok := realRing.normalizeProof(quotient)
	if !ok || !sameLinForm(lf, lq) {
		t.Fatalf("normalizeProof diverged from linOf on the quotient: %v vs %v", lf, lq)
	}
	if w.NumHyps() != 0 || !prop.Lhs(w).AlphaEquals(quotient) {
		t.Errorf("the certificate is not a closed equation of the quotient: %v", w.Conclusion())
	}
	half := rr("e / &2")
	lh, ok := realDomain.linOf(half)
	if !ok || len(lh.monos) != 1 || !lh.monos[0].atom.AlphaEquals(half) {
		t.Errorf("a literal divisor is no longer its own unknown: %v", lh)
	}
}
