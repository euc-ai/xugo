package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// Numerals, coefficients and products past a machine word. The proof side
// evaluates numerals on their bit-trees at any size; these pin that the model
// computes the same values, so the two meet in every kernel step — at 2⁶³,
// where a signed word ends, at 2⁶⁴, where an unsigned one does, and beyond.

const (
	twoTo61     = "2305843009213693952"
	twoTo63     = "9223372036854775808"
	twoTo64     = "18446744073709551616"
	factorial20 = "2432902008176640000" // below 2⁶³
	factorial25 = "15511210043330985984000000"

	// k · 20!: 4, 5 and 7 land between 2⁶³ and 2⁶⁴, 8 and up past 2⁶⁴.
	fourTimes      = "9731608032706560000"
	fiveTimes      = "12164510040883200000"
	sevenTimes     = "17030314057236480000"
	eightTimes     = "19463216065413120000"
	sixteenTimes   = "38926432130826240000"
	twentyOneTimes = "51090942171709440000"
)

// decideUnder is the arith decision of goal under hyps: "⊤", "⊥", "" when
// the decider leaves the goal standing, "residual" when it rewrites it to
// something else.
func decideUnder(hyps []string, goal string) string {
	var hs []Term
	for _, h := range hyps {
		hs = append(hs, tb(h))
	}
	w := ArithDecideWithHyps(hs)(tb(goal))
	switch {
	case w == nil:
		return ""
	case prop.Rhs(w).AlphaEquals(prop.T):
		return "⊤"
	case prop.Rhs(w).AlphaEquals(prop.F):
		return "⊥"
	}
	return "residual"
}

// A product of a hypothesis-pinned variable by a literal, at every position
// relative to 2⁶³ and 2⁶⁴: below both, across the first, across the second.
func TestWideNumeralProductsDecide(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []string
		goal string
	}{
		{"4·2⁶¹ = 2⁶³", []string{"x = " + twoTo61}, "4 * x = " + twoTo63},
		{"4·(2⁶¹−1), below 2⁶³", []string{"x = 2305843009213693951"}, "4 * x = 9223372036854775804"},
		{"8·2⁶¹ = 2⁶⁴", []string{"x = " + twoTo61}, "8 * x = " + twoTo64},
		{"2·20!", []string{"x = " + factorial20}, "2 * x = 4865804016353280000"},
		{"3·20!", []string{"x = " + factorial20}, "3 * x = 7298706024529920000"},
		{"4·20!, past 2⁶³", []string{"x = " + factorial20}, "4 * x = " + fourTimes},
		{"5·20!", []string{"x = " + factorial20}, "5 * x = " + fiveTimes},
		{"7·20!", []string{"x = " + factorial20}, "7 * x = " + sevenTimes},
		{"8·20!, past 2⁶⁴", []string{"x = " + factorial20}, "8 * x = " + eightTimes},
		{"16·20!", []string{"x = " + factorial20}, "16 * x = " + sixteenTimes},
		{"21·20!", []string{"x = " + factorial20}, "21 * x = " + twentyOneTimes},
		{"a chain through two products", []string{"a = " + factorial20, "b = 21 * a"}, "22 * b = 1124000727777607680000"},
		{"a strict bound across 2⁶⁴", []string{"x = " + factorial20}, "7 * x < 8 * x"},
		{"a bound between wide literals", []string{twoTo64 + " <= x"}, "18446744073709551615 < x"},
		{"a sum crossing 2⁶⁴", []string{"x = 18446744073709551615"}, "x + 1 = " + twoTo64},
		{"25! from 24!", []string{"x = 620448401733239439360000"}, "25 * x = " + factorial25},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if got := decideUnder(r.hyps, r.goal); got != "⊤" {
				t.Errorf("%v ⊢ %s decided %q, want ⊤", r.hyps, r.goal, got)
			}
		})
	}
}

// A false goal over the same numerals is not proved, and the attempt ends in
// a verdict — the model hands the kernel no step it refuses.
func TestWideNumeralFalseGoalsFailCleanly(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []string
		goal string
	}{
		{"b = 21·20! is not 1", []string{"a = " + factorial20 + " /\\ b = 21 * a"}, "b = 1"},
		{"4·20! off by one", []string{"x = " + factorial20}, "4 * x = 9731608032706560001"},
		{"8·20! off by one", []string{"x = " + factorial20}, "8 * x = 19463216065413120001"},
		{"4·2⁶¹ is not 2⁶³−1", []string{"x = " + twoTo61}, "4 * x = 9223372036854775807"},
		{"the value a wrapped word would hold", []string{"x = " + twoTo61}, "8 * x = 0"},
		{"a wide bound the wrong way", []string{twoTo64 + " <= x"}, "x < " + twoTo64},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if got := decideUnder(r.hyps, r.goal); got == "⊤" {
				t.Errorf("%v ⊢ %s was decided ⊤", r.hyps, r.goal)
			}
		})
	}
}

// The linear provers on their own, each side of the two boundaries: the ℚ
// refutation (LinProve) and the integer one with its rounding cuts
// (OmegaProve).
func TestWideNumeralLinearProvers(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		hyps []string
		goal string
	}{
		{[]string{"x = " + twoTo61}, "4 * x = " + twoTo63},
		{[]string{"x = " + factorial20}, "7 * x = " + sevenTimes},
		{[]string{"x = " + factorial20}, "21 * x = " + twentyOneTimes},
		{[]string{"x <= " + factorial20, factorial20 + " <= y"}, "4 * x <= 4 * y"},
		{[]string{"3 * x <= " + twoTo64}, "x <= 6148914691236517205"},
		{[]string{twoTo63 + " * x <= " + twoTo64 + " + 5"}, "x <= 2"},
	}
	for _, r := range rows {
		var hyps []Term
		for _, h := range r.hyps {
			hyps = append(hyps, tb(h))
		}
		goal := tb(r.goal)
		w, ok := OmegaProve(slices.Values(hyps), goal)
		if !ok || !w.Conclusion().AlphaEquals(goal) {
			t.Errorf("OmegaProve(%v ⊢ %s): ok=%v", r.hyps, r.goal, ok)
		}
	}
	// The two that need no integrality close by ℚ-Farkas alone.
	for _, r := range rows[:4] {
		var hyps []Term
		for _, h := range r.hyps {
			hyps = append(hyps, tb(h))
		}
		goal := tb(r.goal)
		w, ok := LinProve(slices.Values(hyps), goal)
		if !ok || !w.Conclusion().AlphaEquals(goal) {
			t.Errorf("LinProve(%v ⊢ %s): ok=%v", r.hyps, r.goal, ok)
		}
	}
	if _, ok := OmegaProve(slices.Values([]Term{tb("x = " + factorial20)}), tb("4 * x = 9731608032706560001")); ok {
		t.Error("OmegaProve proved 4·20! = 4·20! + 1")
	}
}

// The model's forms carry the exact values, and the normalizer proves the
// term equal to the form's canonical term.
func TestWideNumeralLinearForms(t *testing.T) {
	a := numVar("a")
	rows := []struct {
		text string
		want linForm
	}{
		{"4 * " + twoTo61, linForm{konst: decimal(twoTo63)}},
		{"8 * " + twoTo61, linForm{konst: decimal(twoTo64)}},
		{"21 * " + factorial20, linForm{konst: decimal(twentyOneTimes)}},
		{twoTo64, linForm{konst: decimal(twoTo64)}},
		{"18446744073709551615 + 1", linForm{konst: decimal(twoTo64)}},
		{twoTo61 + " * a + " + twoTo61 + " * a + " + twoTo61 + " * a + " + twoTo61 + " * a",
			linForm{monos: []monomialL{{coeff: decimal(twoTo63), atom: a}}}},
		{"25 * (24 * (23 * (22 * (21 * " + factorial20 + "))))", linForm{konst: decimal(factorial25)}},
		{"4294967296 * (4294967296 * a) + 5", linForm{konst: integerOf(5), monos: []monomialL{{coeff: decimal(twoTo64), atom: a}}}},
	}
	for _, r := range rows {
		term := tn(r.text)
		got, ok := linOf(term)
		if !ok || !sameLinForm(got, r.want) {
			t.Errorf("linOf(%s) = %+v ok=%v, want %+v", r.text, got, ok, r.want)
		}
		checkNormalize(t, term)
		if !sameLinForm(mpolyOf(term), r.want) {
			t.Errorf("mpolyOf(%s) = %+v, want %+v", r.text, mpolyOf(term), r.want)
		}
	}
}

func TestWideNumeralRingIdentities(t *testing.T) {
	for _, r := range [][2]string{
		{"(a + 4294967296) * (a + 4294967296)", "a * a + 8589934592 * a + " + twoTo64},
		{"(3037000500 * a) * (3037000500 * b)", "9223372037000250000 * (a * b)"},
		{twoTo63 + " * a + " + twoTo63 + " * a", twoTo64 + " * a"},
		{"25 * (24 * (23 * (22 * (21 * " + factorial20 + "))))", factorial25},
	} {
		l, rhs := tn(r[0]), tn(r[1])
		if w, ok := RingProveFull(l, rhs); !ok || !w.Conclusion().AlphaEquals(eqT(l, rhs)) {
			t.Errorf("RingProveFull(%s = %s): ok=%v", r[0], r[1], ok)
		}
	}
	if _, ok := RingProveFull(tn(twoTo63+" * a + "+twoTo63+" * a"), tn("0 * a")); ok {
		t.Error("RingProveFull proved 2⁶⁴·a = 0·a, the identity a wrapped word would give")
	}
}

// Fourier–Motzkin over rows whose entries, multipliers and certificate pass
// a word: the certificate is checked exactly against the input rows.
func TestWideNumeralFourierMotzkin(t *testing.T) {
	wide := decimal(twoTo64)
	rows := []row{
		{coeffs: vectorOf([]_Integer{wide.neg()}), konst: decimal(factorial25)},         // 25! ≤ 2⁶⁴·x
		{coeffs: vectorOf([]_Integer{decimal(twoTo63)}), konst: decimal(twoTo61).neg()}, // 2⁶³·x ≤ 2⁶¹
	}
	lambda, ok := refute(1, rows)
	if !ok || !checkCert(rows, lambda) {
		t.Fatalf("wide refutation: lambda=%v ok=%v", lambda, ok)
	}
	if !slices.ContainsFunc(lambda, func(l _Integer) bool { return l.wide != nil }) {
		t.Errorf("certificate %v stayed in a word; the rows were meant to force it past one", lambda)
	}
	// Satisfiable with the same magnitudes: x ≤ 2⁶⁴ and 2⁶⁴ ≤ x.
	satisfiable := []row{
		{coeffs: vector(1), konst: wide.neg()},
		{coeffs: vector(-1), konst: wide},
	}
	if lambda, ok := refute(1, satisfiable); ok {
		t.Errorf("a satisfiable wide system was refuted with %v", lambda)
	}
}

// The gcd tests and the rounding cut on wide rows.
func TestWideNumeralIntegerCuts(t *testing.T) {
	g := decimal(twoTo64)
	// 2⁶⁴·x − 3·2⁶⁴·y + (2⁶⁴ + 5) ≤ 0 rounds to x − 3y + 2 ≤ 0.
	coeffs := []_Integer{g, g.mul(integerOf(-3))}
	nc, nk, changed := tightenLe(coeffs, g.add(integerOf(5)))
	if !changed || !slices.EqualFunc(nc, integers(1, -3), _Integer.equal) || !nk.equal(integerOf(2)) {
		t.Errorf("tightenLe = %v, %v, changed=%v; want [1 -3], 2, true", nc, nk, changed)
	}
	if _, _, changed := tightenLe(coeffs, g.mul(integerOf(7))); changed {
		t.Error("tightenLe reported a rounding where 2⁶⁴ divides the constant")
	}
	if !eqGCDUnsat(coeffs, g.add(integerOne)) {
		t.Error("2⁶⁴·x − 3·2⁶⁴·y + 2⁶⁴ + 1 = 0 was not refuted by the gcd test")
	}
	if eqGCDUnsat(coeffs, g.mul(integerOf(5))) {
		t.Error("2⁶⁴·x − 3·2⁶⁴·y + 5·2⁶⁴ = 0 was refuted by the gcd test")
	}
	key, konst := reduceForKey(vectorOf(coeffs), g.mul(integerOf(4)))
	reducedKey, reducedKonst := reduceForKey(vector(1, -3), integerOf(4))
	if key != reducedKey || konst.cmp(reducedKonst) != 0 {
		t.Error("a row and its 2⁶⁴-multiple got different canonical directions")
	}
}

func TestWideNumeralDivModAndDivides(t *testing.T) {
	installTestBundle(t)
	m, n := tn(factorial25), tn(factorial20)
	if w, ok := NormNatDiv(m, n); !ok || !w.Conclusion().AlphaEquals(eqT(divT(m, n), tn("6375600"))) {
		t.Errorf("NormNatDiv(25!, 20!): ok=%v", ok)
	}
	if w, ok := NormNatMod(tn(factorial25+" + 7"), n); ok {
		t.Errorf("NormNatMod of a non-literal was evaluated: %v", w)
	}
	odd := tn("15511210043330985984000007")
	if w, ok := NormNatMod(odd, n); !ok || !w.Conclusion().AlphaEquals(eqT(modT(odd, n), tn("7"))) {
		t.Errorf("NormNatMod(25! + 7, 20!): ok=%v", ok)
	}
	if w, holds, ok := NormNatDivides(n, m); !ok || !holds || !w.Conclusion().AlphaEquals(dvd(n, m)) {
		t.Errorf("20! divides 25!: ok=%v holds=%v", ok, holds)
	}
	if w, holds, ok := NormNatDivides(n, odd); !ok || holds || !w.Conclusion().AlphaEquals(prop.Not(dvd(n, odd))) {
		t.Errorf("20! divides 25! + 7: ok=%v holds=%v", ok, holds)
	}
	if w, holds, ok := NormNatDivides(tn(twoTo64), tn("0")); !ok || !holds || !w.Conclusion().AlphaEquals(dvd(tn(twoTo64), tn("0"))) {
		t.Errorf("2⁶⁴ divides 0: ok=%v holds=%v", ok, holds)
	}
}

// The real and int twins read the same literals through their casts.
func TestWideNumeralRealAndIntForms(t *testing.T) {
	product := rr("&4294967296 * (&4294967296 * x) + &" + twoTo64)
	lf, ok := realDomain.linOf(product)
	if !ok || !lf.konst.equal(decimal(twoTo64)) || len(lf.monos) != 1 || !lf.monos[0].coeff.equal(decimal(twoTo64)) {
		t.Errorf("real linOf = %+v ok=%v", lf, ok)
	}
	checkRealNormalize(t, product)

	hyps := []Term{rb("x = &" + factorial20)}
	goal := rb("&21 * x = &" + twentyOneTimes)
	if w, ok := RealLinProve(slices.Values(hyps), goal); !ok || !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("RealLinProve(x = &20! ⊢ &21·x = &(21·20!)): ok=%v", ok)
	}
	if _, ok := RealLinProve(slices.Values(hyps), rb("&21 * x = &1")); ok {
		t.Error("RealLinProve proved &21·&20! = &1")
	}
}
