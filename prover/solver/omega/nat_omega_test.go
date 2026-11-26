package omega

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// Soundness: every system IntUnsat reports must be brute-force unsatisfiable
// over ℕ. Power: integer-gap systems that ℚ-Farkas cannot refute must be caught.

func mustUnsat(t *testing.T, name string, cs []LinConstraint) {
	t.Helper()
	unsat, ok := IntUnsat(cs)
	if !ok {
		t.Fatalf("%s: declined (nonlinear?)", name)
	}
	if !unsat {
		t.Errorf("%s: expected integer-unsat, got sat", name)
	}
}

func mustSat(t *testing.T, name string, cs []LinConstraint, a, b, c Term) {
	t.Helper()
	unsat, ok := IntUnsat(cs)
	if !ok {
		t.Fatalf("%s: declined", name)
	}
	if unsat {
		t.Errorf("%s: reported unsat, but...", name)
	}
	if !satisfiable(cs, a, b, c, 12) {
		t.Errorf("%s: test bug — claimed SAT but brute UNSAT", name)
	}
}

func TestIntUnsatSoundAndPowerful(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")

	// integer-unsat the ℚ relaxation cannot see
	intGap := []struct {
		name string
		cs   []LinConstraint
	}{
		{"2a<=1, 1<=2a", []LinConstraint{con(tn("2 * a"), tn("1"), opLE), con(tn("1"), tn("2 * a"), opLE)}},
		{"2a=1", []LinConstraint{con(tn("2 * a"), tn("1"), opEQ)}},
		{"3a=2", []LinConstraint{con(tn("3 * a"), tn("2"), opEQ)}},
		{"2a+2b=1", []LinConstraint{con(tn("2 * a + 2 * b"), tn("1"), opEQ)}},
		{"2a<=2b+1, 2b+1<=2a", []LinConstraint{
			con(tn("2 * a"), tn("2 * b + 1"), opLE),
			con(tn("2 * b + 1"), tn("2 * a"), opLE)}},
		{"2a<2", []LinConstraint{con(tn("2 * a"), tn("2"), opLT), con(tn("1"), tn("a"), opLE)}}, // a<1 and a>=1
	}
	for _, tc := range intGap {
		mustUnsat(t, tc.name, tc.cs)
		if satisfiable(tc.cs, a, b, c, 12) {
			t.Errorf("%s: reported/expected unsat but brute SAT", tc.name)
		}
	}

	// ℚ-unsat must still be caught
	qUnsat := [][]LinConstraint{
		{con(tn("a"), tn("a"), opLT)},
		{con(tn("a"), tn("b"), opLE), con(tn("b"), tn("a"), opLT)},
		{con(tn("a + 1"), tn("a"), opLE)},
	}
	for i, cs := range qUnsat {
		mustUnsat(t, "qUnsat", cs)
		_ = i
	}

	// integer-SAT must not be over-claimed
	sat := []struct {
		name string
		cs   []LinConstraint
	}{
		{"2a<=3", []LinConstraint{con(tn("2 * a"), tn("3"), opLE)}},
		{"2a=4", []LinConstraint{con(tn("2 * a"), tn("4"), opEQ)}},
		{"2a+2b=6", []LinConstraint{con(tn("2 * a + 2 * b"), tn("6"), opEQ)}},
		{"a<=b", []LinConstraint{con(tn("a"), tn("b"), opLE)}},
		{"3a=6,a<=b", []LinConstraint{con(tn("3 * a"), tn("6"), opEQ), con(tn("a"), tn("b"), opLE)}},
	}
	for _, tc := range sat {
		mustSat(t, tc.name, tc.cs, a, b, c)
	}
}

// Exhaustive soundness sweep: random-ish small systems, assert IntUnsat ⇒ brute
// unsat (never a false UNSAT). Deterministic generation.
func TestIntUnsatSoundnessSweep(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	n := func(k uint64) Term { return Numeral(k) }
	coeffs := []uint64{1, 2, 3}
	bounds := []uint64{0, 1, 2, 3, 4}
	count := 0
	for _, ca := range coeffs {
		for _, cb := range coeffs {
			for _, k1 := range bounds {
				for _, k2 := range bounds {
					cs := []LinConstraint{
						con(plus(star(n(ca), a), star(n(cb), b)), n(k1), opLE),
						con(n(k2), plus(star(n(ca), a), star(n(cb), b)), opLE),
					}
					unsat, ok := IntUnsat(cs)
					if ok && unsat && satisfiable(cs, a, b, b, 10) {
						t.Errorf("false UNSAT: %d a + %d b in [%d,%d]", ca, cb, k2, k1)
					}
					count++
				}
			}
		}
	}
	t.Logf("soundness sweep over %d systems", count)
}

func checkIntRefuteProof(t *testing.T, name string, cs []LinConstraint) {
	t.Helper()
	w, ok := IntRefuteProof(cs)
	if !ok {
		t.Fatalf("%s: expected an integer refutation proof, got none", name)
	}
	if !w.Conclusion().Equals(prop.F) {
		t.Errorf("%s: conclusion = %v, want ⊥", name, w.Conclusion())
	}
	allowed := make([]Term, len(cs))
	for i, c := range cs {
		allowed[i] = constraintTerm(c)
	}
	for i := 0; i < w.NumHyps(); i++ {
		h := w.Hyp(i)
		found := false
		for _, a := range allowed {
			if h.AlphaEquals(a) {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("%s: stray hypothesis %v", name, h)
		}
	}
}

func TestIntRefuteProof(t *testing.T) {
	installTestBundle(t) // integer cut / divmod / divisibility leaves (TestThm stand-ins)
	cases := []struct {
		name string
		cs   []LinConstraint
	}{
		// integer-gap (rounding cut)
		{"2a<=1,1<=2a", []LinConstraint{con(tn("2 * a"), tn("1"), opLE), con(tn("1"), tn("2 * a"), opLE)}},
		{"2a<2,a>=1", []LinConstraint{con(tn("2 * a"), tn("2"), opLT), con(tn("1"), tn("a"), opLE)}},
		{"2a<=2b+1,2b+1<=2a", []LinConstraint{
			con(tn("2 * a"), tn("2 * b + 1"), opLE),
			con(tn("2 * b + 1"), tn("2 * a"), opLE)}},
		// GCD-equality
		{"2a=1", []LinConstraint{con(tn("2 * a"), tn("1"), opEQ)}},
		{"3a=2", []LinConstraint{con(tn("3 * a"), tn("2"), opEQ)}},
		{"2a+2b=1", []LinConstraint{con(tn("2 * a + 2 * b"), tn("1"), opEQ)}},
		// plain ℚ-unsat still discharged through the integer path
		{"a<b,b<a", []LinConstraint{con(tn("a"), tn("b"), opLT), con(tn("b"), tn("a"), opLT)}},
		{"cycle", []LinConstraint{con(tn("a"), tn("b"), opLE), con(tn("b"), tn("c"), opLE), con(tn("c"), tn("a"), opLT)}},
	}
	for _, tc := range cases {
		checkIntRefuteProof(t, tc.name, tc.cs)
	}
}

func TestGroundedGcdEqExercised(t *testing.T) {
	installTestBundle(t) // ModEqZero + DivModUniq for the notDivides bottom (TestThm stand-ins)
	cases := []intExt{
		{lhs: tn("2 * a"), rhs: tn("1"), op: opEQ},         // 2a=1
		{lhs: tn("2"), rhs: tn("3 * a"), op: opEQ},         // 2=3a (flipped)
		{lhs: tn("2 * a + 2 * b"), rhs: tn("1"), op: opEQ}, // 2a+2b=1
	}
	for _, e := range cases {
		w, ok := groundedGcdEq(e)
		if !ok {
			t.Errorf("groundedGcdEq fell back for %v = %v", e.lhs, e.rhs)
			continue
		}
		if !w.Conclusion().Equals(prop.F) {
			t.Errorf("grounded proof concl = %v, want ⊥", w.Conclusion())
		}
		if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(eqT(e.lhs, e.rhs)) {
			t.Errorf("grounded proof hyps = %d (want the eq only)", w.NumHyps())
		}
	}
}

// With the bundle's DivModUniq installed, NormNatDiv / NormNatMod compose the
// q·n+r witness and discharge it to the exact nat_div/nat_mod equation; n = 0 is declined.
func TestNormNatDivMod(t *testing.T) {
	installTestBundle(t) // supplies DivModUniq + the arith leaves the witness needs

	for mv := uint64(0); mv <= 13; mv++ {
		for nv := uint64(1); nv <= 5; nv++ {
			m, n := Numeral(mv), Numeral(nv)
			dw, ok := NormNatDiv(m, n)
			if !ok || !dw.Conclusion().AlphaEquals(eqT(divT(m, n), Numeral(mv/nv))) {
				t.Errorf("NormNatDiv(%d,%d): ok=%v concl=%v", mv, nv, ok, dw)
			}
			mw, ok := NormNatMod(m, n)
			if !ok || !mw.Conclusion().AlphaEquals(eqT(modT(m, n), Numeral(mv%nv))) {
				t.Errorf("NormNatMod(%d,%d): ok=%v concl=%v", mv, nv, ok, mw)
			}
		}
	}
	// n = 0 is declined (no division-by-zero witness).
	if _, ok := NormNatMod(tn("7"), tn("0")); ok {
		t.Error("NormNatMod(7,0): want ok=false")
	}
}

func TestNormNatDivides(t *testing.T) {
	installTestBundle(t) // notDivides bottoms on ModEqZero + DivModUniq (TestThm stand-ins)
	for dv := uint64(1); dv <= 6; dv++ {
		for nv := uint64(0); nv <= 14; nv++ {
			d, n := Numeral(dv), Numeral(nv)
			w, holds, ok := NormNatDivides(d, n)
			if !ok {
				t.Fatalf("declined %d|%d", dv, nv)
			}
			want := nv%dv == 0
			if holds != want {
				t.Errorf("%d|%d: holds=%v want %v", dv, nv, holds, want)
			}
			if holds && !w.Conclusion().AlphaEquals(dvd(d, n)) {
				t.Errorf("%d|%d: positive concl %v", dv, nv, w.Conclusion())
			}
			if !holds && !w.Conclusion().AlphaEquals(prop.Not(dvd(d, n))) {
				t.Errorf("%d|%d: negative concl %v", dv, nv, w.Conclusion())
			}
		}
	}
}

// A strict hypothesis read ahead of a sum brings the sum's atoms into the
// refutation's table in an order other than their Compare order (`i < q`
// enters q before `p + q ≤ 1` enters p). The two sides of every cut row
// are built from that table, and the rounding cut's identity holds them to
// the linForm invariant — monomials sorted by atom — so a side built in
// table order failed the canonical-form check and the whole refutation
// declined: `i < q, p + q ≤ 1 ⊢ p + q ≤ 1` under OmegaProve, and with it
// the `=` decision `1 = p + q`, whose halves the integer core proves in
// turn once ℚ-Farkas has declined the first. The same atoms met in Compare
// order never saw it.
func TestOmegaProve_CutRowOverAtomsMetOutOfOrder(t *testing.T) {
	installTestBundle(t) // the cut rows need the integer cut leaves
	strictThenSum := []Term{tb("i < q"), tb("p + q <= 1")}
	checkProveWith(t, "OmegaProve i<q, p+q<=1 ⊢ p+q<=1", OmegaProve, strictThenSum, tb("p + q <= 1"), true)
	checkProveWith(t, "OmegaProve i<q, p+q<=1 ⊢ 1<=p+q", OmegaProve, strictThenSum, tb("1 <= p + q"), true)
	checkProveWith(t, "OmegaProve i<q, p+q<=1 ⊢ 1=p+q", OmegaProve, strictThenSum, tb("1 = p + q"), true)
	sumThenStrict := []Term{tb("p + q <= 1"), tb("i < q")}
	checkProveWith(t, "OmegaProve p+q<=1, i<q ⊢ 1=p+q", OmegaProve, sumThenStrict, tb("1 = p + q"), true)

	// The decision leaf on the truncation branch of `i < q ⊢ p + q − 1 + 1 = p + q`.
	w := ArithDecideWithHyps(strictThenSum)(tb("1 = p + q"))
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("ArithDecideWithHyps([i<q, p+q<=1])(1 = p+q) = %v, want ⊤", w)
	}
}
