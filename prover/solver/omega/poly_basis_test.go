package omega

// The monomial-basis extraction (domain.go polyMul / ring.go natPolyMul):
// linarith reads every num comparison as a polynomial over canonical monomial
// atoms, so hypothesis equations with polynomial content combine under Farkas.
// The north-star instance is transcript A5's induction leaf — IH `2·A = n·S`
// against goal `2·(A+S) = S·SS` (S = suc n) — one unit-λ combination once both
// sides live in the shared basis {A, n·n, n}.
//
// These tests pin, in order: the untrusted model's canonical forms and their
// lockstep with the proof-side normalizeProof (the discharge replay depends on
// the two coinciding), the fuse fallback (overflow / monomial-count cap →
// opaque atom, mirrored on both sides), the new LinProve/OmegaProve power, the
// fragment boundary (what deliberately stays out), and the unified decider
// (ArithDecideWithHyps) end-to-end.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// ── the untrusted model ──────────────────────────────────────────────────────

// TestPolyBasisCanonicalForms pins linOf's expansion against hand-computed
// canonical forms via the toTerm rendering (equal forms ⇒ equal terms).
func TestPolyBasisCanonicalForms(t *testing.T) {
	cases := []struct{ in, canon string }{
		{"a * b", "b * a"},                             // commutation collapses
		{"(a * b) * c", "a * (b * c)"},                 // association collapses
		{"n * suc(n)", "n * n + n"},                    // suc folds inside products
		{"suc(n) * suc(suc(n))", "n * n + 3 * n + 2"},  // the A5 right side
		{"(a + 1) * (b + 2)", "a * b + 2 * a + b + 2"}, // konst cross terms
		{"(a + b) * (a + b)", "a * a + 2 * (a * b) + b * b"},
		{"2 * (a * b) + 3 * (b * a)", "5 * (a * b)"}, // like monomials merge
		{"suc(a) * suc(a) * suc(a)", "a * a * a + 3 * (a * a) + 3 * a + 1"},
	}
	for _, tc := range cases {
		lfIn, ok1 := linOf(tn(tc.in))
		lfCanon, ok2 := linOf(tn(tc.canon))
		if !ok1 || !ok2 {
			t.Errorf("linOf declined %q or %q", tc.in, tc.canon)
			continue
		}
		if !lfIn.toTerm().AlphaEquals(lfCanon.toTerm()) {
			t.Errorf("linOf(%q) = %v; want the form of %q = %v",
				tc.in, lfIn.toTerm(), tc.canon, lfCanon.toTerm())
		}
	}
}

// TestPolyBasisRoundTrip: the toTerm rendering of an extracted form re-extracts
// to the same form — the canonicality invariant the gcd/cut paths rely on
// (their model terms are toTerm-shaped and must be fixed points).
func TestPolyBasisRoundTrip(t *testing.T) {
	for _, s := range []string{
		"a * b", "suc(n) * suc(suc(n))", "(a + b) * (c + 1)", "2 * (a * b) + 3 * c + 7",
	} {
		lf, ok := linOf(tn(s))
		if !ok {
			t.Fatalf("linOf declined %q", s)
		}
		lf2, ok := linOf(lf.toTerm())
		if !ok {
			t.Errorf("linOf declined its own rendering %v", lf.toTerm())
			continue
		}
		if !lf.toTerm().AlphaEquals(lf2.toTerm()) {
			t.Errorf("round trip moved %q: %v → %v", s, lf.toTerm(), lf2.toTerm())
		}
	}
}

// TestPolyBasisNormalizeProofLockstep: the proof-side normalizeProof must
// produce the model's exact form on polynomial terms — the discharge replay
// (nat_linarith.go replay) cancels the accumulated sides only when the two
// coincide. checkNormalize asserts Lhs/Rhs shape AND the linOf cross-check.
func TestPolyBasisNormalizeProofLockstep(t *testing.T) {
	for _, s := range []string{
		"a * b",
		"b * a",
		"n * suc(n)",
		"suc(n) * suc(suc(n))",
		"(a + 1) * (b + 2)",
		"(a + b) * (a + b)",
		"(a * b) * c",
		"2 * (a * b) + 3 * (b * a)",
		"2 * (A + suc(n))",
		"suc(a) * suc(a) * suc(a)",
	} {
		checkNormalize(t, tn(s))
	}
}

// ── coefficients past a machine word, and the monomial-count cap ─────────────

// TestPolyBasisWideCoefficients: a product whose coefficients pass the int64
// and the uint64 range expands exactly, on the model AND the proof side
// alike (checkNormalize pins the lockstep).
func TestPolyBasisWideCoefficients(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	// 4e9 · 4e9 = 1.6e19, between 2⁶³ and 2⁶⁴.
	product := tn("(4000000000 * a) * (4000000000 * b)")
	lf, ok := linOf(product)
	want := linForm{monos: []monomialL{{coeff: integerOfUint(16000000000000000000), atom: monoMulTerm(a, b)}}}
	if !ok || !sameLinForm(lf, want) {
		t.Errorf("wide-coefficient product = %+v ok=%v; want 16000000000000000000·(a·b)", lf, ok)
	}
	checkNormalize(t, product)

	// The constant through the cross terms: 3e9 · 4e9 = 1.2e19.
	cross := tn("(a + 3000000000) * (b + 4000000000)")
	lf, ok = linOf(cross)
	if !ok || !lf.konst.equal(integerOfUint(12000000000000000000)) || len(lf.monos) != 3 {
		t.Errorf("wide-constant product = %+v ok=%v; want constant 12000000000000000000 and three monomials", lf, ok)
	}
	checkNormalize(t, cross)

	// Past 2⁶⁴: 5e9 · 5e9 = 2.5e19.
	past := tn("(5000000000 * a) * (5000000000 * b)")
	lf, ok = linOf(past)
	if !ok || len(lf.monos) != 1 || lf.monos[0].coeff.String() != "25000000000000000000" {
		t.Errorf("product past 2^64 = %+v ok=%v; want 25000000000000000000·(a·b)", lf, ok)
	}
	checkNormalize(t, past)
}

// TestPolyBasisFuseFallback: a product whose expansion trips the
// monomial-count cap falls back to the pre-basis reading — the WHOLE product
// as one opaque atom — on the model AND the proof side alike (checkNormalize
// pins the lockstep).
func TestPolyBasisFuseFallback(t *testing.T) {

	// Monomial-count cap: (a₁+…+a₉)·(b₁+…+b₉) is 81 > _polyMulMonoCap monomials.
	sum := func(prefix string, n int) Term {
		res := numVar(prefix + "0")
		for i := 1; i < n; i++ {
			res = plus(res, numVar(prefix+string(rune('0'+i))))
		}
		return res
	}
	capped := star(sum("x", 9), sum("y", 9))
	lf, ok := linOf(capped)
	if !ok || len(lf.monos) != 1 || !lf.monos[0].atom.AlphaEquals(capped) {
		t.Errorf("capped product: monos=%d ok=%v; want opaque-atom fallback", len(lf.monos), ok)
	}
	checkNormalize(t, capped)

	// Boundary sanity: 8·8 = 64 monomials is exactly the cap — expands.
	within := star(sum("x", 8), sum("y", 8))
	lf, ok = linOf(within)
	if !ok || len(lf.monos) != 64 {
		t.Errorf("64-monomial product: monos=%d ok=%v; want full expansion", len(lf.monos), ok)
	}
}

// ── LinProve over the monomial basis ─────────────────────────────────────────

func TestLinProvePolynomialValid(t *testing.T) {
	cases := []struct {
		name string
		hyps []string
		goal string
	}{
		// The A5 north star: IH combines with the goal in the shared basis.
		{"A5 gauss step", []string{"2 * A = n * suc(n)"},
			"2 * (A + suc(n)) = suc(n) * suc(suc(n))"},
		// Same fact under a ≠ goal.
		{"A5 disequality", []string{"2 * A = n * suc(n)"},
			"~(2 * A + 1 = n * suc(n))"},
		// Inequality version of the induction step.
		{"gauss step <=", []string{"2 * S <= n * suc(n)"},
			"2 * (S + suc(n)) <= suc(n) * suc(suc(n))"},
		// Sum of odd numbers: s = n² ⊢ s + (2n+1) = (n+1)².
		{"sum of odds", []string{"s = n * n"},
			"s + (2 * n + 1) = suc(n) * suc(n)"},
		// Cube growth: c = a³ ⊢ c + 3a² + 3a + 1 = (a+1)³.
		{"cube step", []string{"c = a * a * a"},
			"c + 3 * (a * a) + 3 * a + 1 = suc(a) * suc(a) * suc(a)"},
		// Commuted spellings are the same unknown.
		{"commutation, no hyps", nil, "a * b = b * a"},
		{"commutation through hyp", []string{"a * b < c"}, "b * a < c + 1"},
		{"assoc through hyp", []string{"(a * b) * c <= d"}, "a * (b * c) <= d"},
		// A monomial is a nonnegative unknown (the injected 0 ≤ b·c row).
		{"monomial nonneg", nil, "a <= a + b * c"},
		// Conjunction hyp carrying the polynomial fact.
		{"conjunction hyp", []string{"0 < k ∧ 2 * A = n * suc(n)"},
			"2 * (A + suc(n)) = suc(n) * suc(suc(n))"},
		// The eudoxus_slope.LessEqTotal cancel residual (real/tower): a negated
		// scaled bound refuted by the two Cauchy legs + the scaled margin —
		// pure Farkas once the products share the monomial basis.
		{"slope cancel residual",
			[]string{
				"~(a * x1 <= a * (y1 + (b0 + b1)))",
				"~(a = 0)",
				"(x0 + (b0 + b1)) < y0",
				"(a * x1) <= ((c * x0) + (b0 * (a + c)))",
				"(c * (x0 + (b0 + b1))) <= (c * y0)",
				"(c * y0) <= ((a * y1) + (b1 * (a + c)))",
			},
			"x1 <= (y1 + (b0 + b1))"},
	}
	for _, tc := range cases {
		var hyps []Term
		for _, h := range tc.hyps {
			hyps = append(hyps, tb(h))
		}
		checkProve(t, tc.name, hyps, tb(tc.goal), true)
	}
}

// TestLinProvePolynomialUnprovable pins the fragment boundary: linear
// combinations of the premises over the monomial basis, nothing more. Scaling
// an equation by a variable (Gröbner territory) and sign-free square
// monotonicity (true RCF) deliberately stay out.
func TestLinProvePolynomialUnprovable(t *testing.T) {
	cases := []struct {
		name string
		hyps []string
		goal string
	}{
		{"no equation scaling", []string{"a = b"}, "a * c = b * c"},
		{"no square monotonicity", []string{"a <= b"}, "a * a <= b * b"},
		{"contingent polynomial", nil, "a * b <= a + b"},
	}
	for _, tc := range cases {
		var hyps []Term
		for _, h := range tc.hyps {
			hyps = append(hyps, tb(h))
		}
		checkProve(t, tc.name, hyps, tb(tc.goal), false)
	}
}

// ── OmegaProve over the monomial basis ───────────────────────────────────────

// TestOmegaProvePolynomial: the integer layer's rows now carry monomial atoms —
// the rank-1 rounding cut and the canonicalization (g=1) cut both run over
// them. Needs the DivModUniq/LessEqRightDivEq stand-ins (installTestBundle).
func TestOmegaProvePolynomial(t *testing.T) {
	installTestBundle(t)
	cases := []struct {
		name string
		hyps []string
		goal string
	}{
		// Rank-1 rounding cut on a monomial: 2ab < 2c+2 ⟶ ab ≤ c.
		{"rounding cut over monomial", []string{"2 * (a * b) < 2 * c + 2"}, "a * b <= c"},
		// The A5 leaf through the integer path (g=1 canonicalization cuts).
		{"A5 via omega", []string{"2 * A = n * suc(n)"},
			"2 * (A + suc(n)) = suc(n) * suc(suc(n))"},
		// Strict-to-weak over ℤ with a commuted monomial.
		{"discreteness over monomial", []string{"b * a < suc(c)"}, "a * b <= c"},
	}
	for _, tc := range cases {
		var hyps []Term
		for _, h := range tc.hyps {
			hyps = append(hyps, tb(h))
		}
		checkProveWith(t, "OmegaProve "+tc.name, OmegaProve, hyps, tb(tc.goal), true)
	}
}

// ── handler composition: monus and the split engine over monomials ───────────

// TestPolyBasisMonusModel: the monus layer already lives on the polynomial
// model (monusReducible / linSub pivot on mpolyOf) — the basis change aligns
// linarith's extraction with it. Bundle-free model checks: spelling variants
// of the same polynomial now reduce (difference 0), genuinely mixed products
// stay case-split candidates, and the split candidate collection still sees
// the monus. (The end-to-end `m·n − p·q ≤ m·n` close runs under the real
// corpus bundle — library/serve TestInstallNatBundleBindingSub class.)
func TestPolyBasisMonusModel(t *testing.T) {
	if !monusReducible(tn("a * b"), tn("b * a")) {
		t.Errorf("a*b − b*a: want reducible (same monomial, difference 0)")
	}
	if monusReducible(tn("m * n"), tn("p * q")) {
		t.Errorf("m*n − p*q: want irreducible (mixed sign; the case split owns it)")
	}
	if got := collectSplitCandidates([]Term{tn("m * n - p * q")}); len(got) != 1 {
		t.Errorf("collectSplitCandidates = %v, want the one monus", got)
	}
}

// ── the unified decider ──────────────────────────────────────────────────────

// TestArithDecidePolynomialHyps: ArithDecideWithHyps — the engine move behind
// the `arith` closer — decides the A5 conclusion to ⊤ under the IH, and does
// NOT decide the contingent IH from nothing.
func TestArithDecidePolynomialHyps(t *testing.T) {
	ih := tb("2 * A = n * suc(n)")
	concl := tb("2 * (A + suc(n)) = suc(n) * suc(suc(n))")
	w := ArithDecideWithHyps([]Term{ih})(concl)
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		t.Errorf("ArithDecideWithHyps({IH})(A5 concl) = %v; want ⊤", w)
	}
	// Hyps of the decision stay ⊆ {IH} (the IsStronger contract).
	if w != nil {
		for h := range w.HypIter() {
			if !h.AlphaEquals(ih) {
				t.Errorf("decision carries stray hyp %v", h)
			}
		}
	}
	if w := ArithDecideWithHyps(nil)(ih); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("contingent IH decided ⊤ with no hyps")
	}
}

// TestLinProvePolynomialHypSubset: on the A5 close the refutation's hypotheses
// are exactly the named premise — nothing fabricated, nothing dropped.
func TestLinProvePolynomialHypSubset(t *testing.T) {
	ih := tb("2 * A = n * suc(n)")
	goal := tb("2 * (A + suc(n)) = suc(n) * suc(suc(n))")
	w, ok := LinProve(slices.Values([]Term{ih}), goal)
	if !ok {
		t.Fatalf("LinProve declined the A5 leaf")
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("conclusion = %v; want %v", w.Conclusion(), goal)
	}
	for h := range w.HypIter() {
		if !h.AlphaEquals(ih) {
			t.Errorf("stray hypothesis %v", h)
		}
	}
}

// ── the ring residual (unchanged muscle, kept as the A5 companion pin) ───────

// TestRingProveFullA5Residual: the manual spectrum's final step — the pure ring
// identity left after `rw IH` — closes via RingProveFull (pre-existing power;
// pinned here because the A5 story leans on it).
func TestRingProveFullA5Residual(t *testing.T) {
	l := tn("n * suc(n) + 2 * suc(n)")
	r := tn("suc(n) * suc(suc(n))")
	if _, ok := RingProveFull(l, r); !ok {
		t.Errorf("RingProveFull declined the post-rw A5 residual")
	}
}
