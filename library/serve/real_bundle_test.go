package serve

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// Binding tests for the REAL bundle (InstallRealBundle). With both bundles
// installed and no placeholder fabricator in this test binary, every leaf a proof
// exercises MUST bind its bundle field — any degrade to a placeholder panics, so
// a green run proves the wiring (orientation, binder order, the const-def routes,
// the of_num bridge over the nat numeral evaluator, the fromGeneral clause↔curried
// adapters). Every real field now binds a REAL theorem (InstallRealBundle), so
// these are end-to-end SOUND, not just shape pins.

// installRealForTest installs BOTH bundles — the real leaves delegate numeral
// work to the num evaluator (the of_num bridge), so the nat bundle must be live
// for the full composition to be corpus-backed.
func installRealForTest(t *testing.T) {
	t.Helper()
	InstallNatBundle()
	InstallRealBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
		omega.SetRealLemmaBundle(nil)
	})
}

// TestInstallRealBundleBindingLinarith: RealLinProve end-to-end with both bundles
// installed. The goal set covers every read-now leaf family: duality (NotLessThan/NotLessEq),
// the `>` definitional bridge, `=` antisymmetry, the *Add2 sum family, additive
// cancellation, the positive-scale leaf incl. its `&0 ≤ &c` side-condition
// discharge through the of_num bridge, and the ring normalizer (like-term
// merge + coefficient folding).
func TestInstallRealBundleBindingLinarith(t *testing.T) {
	installRealForTest(t)
	cases := []struct {
		goal string
		hyps []string
	}{
		{"x < z", []string{"x < y", "y < z"}},    // < transitivity (LessThanAdd2 path)
		{"x <= y", []string{"x < y"}},            // strict ⇒ non-strict (duality)
		{"x = y", []string{"x <= y", "y <= x"}},  // antisymmetry close (=)
		{"&1 <= x", []string{"&2 <= x"}},         // numeral close via of_num bridge
		{"y > x", []string{"x < y"}},             // `>` goal via the real_gt def
		{"y >= x", []string{"x <= y"}},           // `≥` goal via the real_ge def
		{"&2 * x <= &2 * y", []string{"x <= y"}}, // λ=2 certificate → scale leaf + side cond
		{"x + x <= &2 * x", nil},                 // like-term merge through realRing
		{"x + &1 <= y", []string{"x + &1 <= y"}}, // hyp echo (additive cancel + const fold)
	}
	for _, tc := range cases {
		name := fmt.Sprintf("%v ⊢ %s", tc.hyps, tc.goal)
		t.Run(name, func(t *testing.T) {
			goal := rParse(t, tc.goal, core.TypeBool())
			hyps := make([]core.Term, len(tc.hyps))
			for i, h := range tc.hyps {
				hyps[i] = rParse(t, h, core.TypeBool())
			}
			w, ok := omega.RealLinProve(seqOfTerms(hyps...), goal)
			if !ok {
				t.Fatalf("RealLinProve declined: %s", name)
			}
			if !w.Conclusion().AlphaEquals(goal) {
				t.Errorf("conclusion %v, want %v", w.Conclusion(), goal)
			}
		})
	}
}

// TestInstallRealBundleBindingRing: RealRingProve with both bundles installed —
// the nine ring leaves plus of_num coefficient folding (combineMono/scaleMono run
// the bridge over the nat numeral evaluator).
func TestInstallRealBundleBindingRing(t *testing.T) {
	installRealForTest(t)
	pairs := [][2]string{
		{"x + y", "y + x"},
		{"(x + y) + z", "x + (y + z)"},
		{"&2 * (x + y)", "&2 * x + &2 * y"},
		{"&3 * x + &2 * x", "&5 * x"},
		{"(x + &3) + (y + &4)", "(x + y) + &7"},
		{"x", "&1 * x + &0"},
		{"&0 * (x + y) + x", "x"},
	}
	for _, p := range pairs {
		t.Run(p[0]+" = "+p[1], func(t *testing.T) {
			l := rParse(t, p[0], dsl.RealType)
			r := rParse(t, p[1], dsl.RealType)
			w, ok := omega.RealRingProve(l, r)
			if !ok {
				t.Fatalf("RealRingProve declined: %s = %s", p[0], p[1])
			}
			if !w.Conclusion().AlphaEquals(core.Eq(l, r)) {
				t.Errorf("conclusion %v, want %s = %s", w.Conclusion(), p[0], p[1])
			}
		})
	}
}

// TestInstallRealBundleBindingRefute: the refutation surface, driven ex falso —
// each hyp set is unsatisfiable, so the numerically-false goal `&1 ≤ &0`
// follows; closing it forces a full Farkas refutation of the set with every
// leaf bound. (RealLinRefuteProof's LinConstraint surface is package-internal,
// so the forward prover is the public route.)
func TestInstallRealBundleBindingRefute(t *testing.T) {
	installRealForTest(t)
	sets := [][]string{
		{"x < y", "y < x"},
		{"&2 <= x", "x <= &1"},
		{"x + y <= &1", "&2 <= x + y"},
	}
	for _, hyps := range sets {
		t.Run(fmt.Sprintf("%v", hyps), func(t *testing.T) {
			goal := rParse(t, "&1 <= &0", core.TypeBool())
			parsed := make([]core.Term, len(hyps))
			for i, h := range hyps {
				parsed[i] = rParse(t, h, core.TypeBool())
			}
			w, ok := omega.RealLinProve(seqOfTerms(parsed...), goal)
			if !ok {
				t.Fatalf("RealLinProve could not exploit the contradictory hyps %v", hyps)
			}
			if !w.Conclusion().AlphaEquals(goal) {
				t.Errorf("conclusion %v, want %v", w.Conclusion(), goal)
			}
		})
	}
}

// TestInstallRealBundleBindingStructural: the real structural handlers
// (omega/real_ops.go: case splits + sign-known nonlinear) driven
// through RealArithDecideWithHyps with the real bundle installed (fabricator-free).
// Every leaf binds a proved theorem over ℝ (no fabricator), so each case
// validates its binding SOUND — a shape mismatch against the bound theorem
// panics at the leaf.
func TestInstallRealBundleBindingStructural(t *testing.T) {
	installRealForTest(t)
	real := dsl.RealType
	rv := func(n string) core.Term { return ext.Var(ext.TermName(n), real) }
	rstar := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealStarMeta.Term(), a, b) }
	rle := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealLeMeta.Term(), a, b) }
	rlt := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealLtMeta.Term(), a, b) }
	rabs := func(a core.Term) core.Term { return ext.Apply(dsl.RealAbsMeta.Term(), a) }
	rmax := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealMaxMeta.Term(), a, b) }
	rmin := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealMinMeta.Term(), a, b) }
	rsgn := func(a core.Term) core.Term { return ext.Apply(dsl.RealSgnMeta.Term(), a) }
	rpow := func(m, n core.Term) core.Term { return ext.Apply(dsl.RealPowMeta.Term(), m, n) }
	rdiv := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealDivMeta.Term(), a, b) }
	rinv := func(a core.Term) core.Term { return ext.Apply(dsl.RealInvMeta.Term(), a) }
	rlit := func(n uint64) core.Term { return ext.Apply(dsl.RealOfNumMeta.Term(), omega.Numeral(n)) }
	ron := func(t core.Term) core.Term { return ext.Apply(dsl.RealOfNumMeta.Term(), t) } // `&t` for a num term
	rneg := func(a core.Term) core.Term { return ext.Apply(dsl.RealNegMeta.Term(), a) }
	rsub := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealSubMeta.Term(), a, b) }
	rplus := func(a, b core.Term) core.Term { return ext.Apply(dsl.RealPlusMeta.Term(), a, b) }
	nLe := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatLeMeta.Term(), a, b) }
	nStar := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatStarMeta.Term(), a, b) }
	notT := func(a core.Term) core.Term { return ext.Apply(prop.NOT, a) }
	eqT := core.Eq
	x, y, c, d := rv("x"), rv("y"), rv("c"), rv("d")
	a, b := rv("a"), rv("b")
	nn := ext.Var(ext.TermName("n"), dsl.NumType) // a num-typed variable (exponent / `&n`)
	mm := ext.Var(ext.TermName("m"), dsl.NumType)
	z := rlit(0)

	cases := []struct {
		name string
		goal core.Term
		hyps []core.Term
	}{
		// ── Operator case splits (omega/real_ops.go), defs. ──
		{"0≤|x|", rle(z, rabs(x)), nil},
		{"x≤|x|", rle(x, rabs(x)), nil},
		{"a≤max(a,b)", rle(a, rmax(a, b)), nil},
		{"min(a,b)≤b", rle(rmin(a, b), b), nil},
		{"sgn x ≤ &1", rle(rsgn(x), rlit(1)), nil},
		// ── Monotone scaling (LessEqMulLeft) + sign-of-product (LessEqMul). ──
		{"a≤b,0≤c⊢c·a≤c·b", rle(rstar(c, a), rstar(c, b)), []core.Term{rle(a, b), rle(z, c)}},
		{"0≤x,0≤y⊢0≤x·y", rle(z, rstar(x, y)), []core.Term{rle(z, x), rle(z, y)}},
		// ── Positive-factor cancellation OUT of a hypothesis (LessEqCancelMulLeft /
		// LessThanCancelMulLeft) — the scaling read backwards, so the sign premise
		// is strict. The right-factor spellings ride the same two fields with both
		// sides commuted through MulSym. ──
		{"0<c,c·a≤c·b⊢a≤b [LessEqCancelMulLeft]", rle(a, b),
			[]core.Term{rlt(z, c), rle(rstar(c, a), rstar(c, b))}},
		{"0<c,c·a<c·b⊢a<b [LessThanCancelMulLeft]", rlt(a, b),
			[]core.Term{rlt(z, c), rlt(rstar(c, a), rstar(c, b))}},
		{"0<c,a·c≤b·c⊢a≤b [LessEqCancelMulLeft+MulSym]", rle(a, b),
			[]core.Term{rlt(z, c), rle(rstar(a, c), rstar(b, c))}},
		{"0<c,a·c<b·c⊢a<b [LessThanCancelMulLeft+MulSym]", rlt(a, b),
			[]core.Term{rlt(z, c), rlt(rstar(a, c), rstar(b, c))}},
		// ── Two-sided product bound (LessEqTrans, derived). ──
		{"0≤a,a≤b,0≤c,c≤d⊢a·c≤b·d", rle(rstar(a, c), rstar(b, d)),
			[]core.Term{rle(z, a), rle(a, b), rle(z, c), rle(c, d)}},
		// ── Integral domain (MulEqZero). ──
		{"x·x=&0⊢x=&0", eqT(x, z), []core.Term{eqT(rstar(x, x), z)}},
		{"x·y=&0,x≠&0⊢y=&0", eqT(y, z), []core.Term{eqT(rstar(x, y), z), notT(eqT(x, z))}},
		// ── MulPos / NegNonnegativeIffNonpositive / LessThanTrichotomy. ──
		{"0<x,0<y⊢0<x·y [MulPos]", rlt(z, rstar(x, y)), []core.Term{rlt(z, x), rlt(z, y)}},
		{"x≤&0,0≤y⊢x·y≤&0 [NegNonnegativeIffNonpositive]", rle(rstar(x, y), z), []core.Term{rle(x, z), rle(z, y)}},
		{"x≠y,x≤y⊢x<y [LessThanTrichotomy]", rlt(x, y), []core.Term{notT(eqT(x, y)), rle(x, y)}},
		{"x≠&0⊢&0<x·x [MulPos+LessThanTrichotomy]", rlt(z, rstar(x, x)), []core.Term{notT(eqT(x, z))}},
		// ── real_pow c≤1 auto-fold (PowZero/PowSuc). ──
		{"real_pow x 0=&1 [PowZero]", eqT(rpow(x, omega.Numeral(0)), rlit(1)), nil},
		{"real_pow x 1=x [PowSuc]", eqT(rpow(x, omega.Numeral(1)), x), nil},
		// ── field layer: folds, cancellation, denominator clearing. ──
		{"x/&1=x [DivOne]", eqT(rdiv(x, rlit(1)), x), nil},
		{"&6/&2=&3 [clear literal]", eqT(rdiv(rlit(6), rlit(2)), rlit(3)), nil},
		{"x≠&0⊢x·inv x=&1 [MulRightInverse]", eqT(rstar(x, rinv(x)), rlit(1)), []core.Term{notT(eqT(x, z))}},
		{"x≠&0⊢x/x=&1 [DivRefl]", eqT(rdiv(x, x), rlit(1)), []core.Term{notT(eqT(x, z))}},
		{"0<c,x·c≤y⊢x≤y/c [LessEqDivMulLeft]", rle(x, rdiv(y, c)), []core.Term{rlt(z, c), rle(rstar(x, c), y)}},
		// ── All six negative-divisor field-clearing iffs (no entry states them;
		// derived by instantiating at (z:=-z, y:=-y) + neg-algebra rewrites — see
		// real_bundle_neg_div.go). Each one closes a goal under (c<&0) by
		// reducing the divisor-side atom to the corresponding cleared form.
		{"c<&0,y≤x·c⊢x≤y/c [LessEqDivMulLeftNeg]", rle(x, rdiv(y, c)), []core.Term{rlt(c, z), rle(y, rstar(x, c))}},
		{"c<&0,y<x·c⊢x<y/c [LessThanDivMulLeftNeg]", rlt(x, rdiv(y, c)), []core.Term{rlt(c, z), rlt(y, rstar(x, c))}},
		{"c<&0,y=x·c⊢x=y/c [EqDivMulLeftNeg]", eqT(x, rdiv(y, c)), []core.Term{rlt(c, z), eqT(y, rstar(x, c))}},
		{"c<&0,x·c≤y⊢y/c≤x [LessEqDivMulRightNeg]", rle(rdiv(y, c), x), []core.Term{rlt(c, z), rle(rstar(x, c), y)}},
		{"c<&0,x·c<y⊢y/c<x [LessThanDivMulRightNeg]", rlt(rdiv(y, c), x), []core.Term{rlt(c, z), rlt(rstar(x, c), y)}},
		{"c<&0,y=x·c⊢y/c=x [EqDivMulRightNeg]", eqT(rdiv(y, c), x), []core.Term{rlt(c, z), eqT(y, rstar(x, c))}},
		// ── No-hyp square (SquareNonneg) / real_pow sign (PowTwoNonneg/PowNonneg/PowPos). ──
		{"&0≤x·x [SquareNonneg]", rle(z, rstar(x, x)), nil},
		{"&0≤x^2 [PowTwoNonneg]", rle(z, rpow(x, omega.Numeral(2))), nil},
		{"&0≤x⊢&0≤x^n [PowNonneg]", rle(z, rpow(x, nn)), []core.Term{rle(z, x)}},
		{"&0<x⊢&0<x^n [PowPos]", rlt(z, rpow(x, nn)), []core.Term{rlt(z, x)}},
		// ── Abs nonneg (AbsNonneg) — direct close + sign-of-
		// product side-condition payoff via realLinProveSigned. ──
		{"&0≤|x| [AbsNonneg]", rle(z, rabs(x)), nil},
		{"&0≤|x|·|y| [AbsNonneg⊢LessEqMul]", rle(z, rstar(rabs(x), rabs(y))), nil},
		// ── Literal even-pow nonneg (PowAdd) — k≥2 closes via
		// the perfect-square split x^(2k) = x^k · x^k + SquareNonneg. ──
		{"&0≤x^4 [PowAdd⊢SquareNonneg]", rle(z, rpow(x, omega.Numeral(4))), nil},
		{"&0≤x^6 [PowAdd⊢SquareNonneg]", rle(z, rpow(x, omega.Numeral(6))), nil},
		// ── real_of_num homomorphism collapse (omega/real_ops.go), OfNum*/Neg*. ──
		{"&0≤&n [of_num drop]", rle(z, ron(nn)), nil},
		{"&0≤&n·&n [of_num collapse]", rle(z, rstar(ron(nn), ron(nn))), nil},
		{"&n·&n=&(n·n) [of_num =]", eqT(rstar(ron(nn), ron(nn)), ron(ext.Apply(dsl.NatStarMeta.Term(), nn, nn))), nil},
		// ── abs / sgn algebraic laws (omega/real_ops.go). ──
		{"|x·y|=|x|·|y| [AbsMul]", eqT(rabs(rstar(x, y)), rstar(rabs(x), rabs(y))), nil},
		{"|−x|=|x| [AbsEven]", eqT(rabs(rneg(x)), rabs(x)), nil},
		{"|&n|=&n [AbsOfNum]", eqT(rabs(ron(nn)), ron(nn)), nil},
		{"sgn(x·y)=sgn x·sgn y [SgnMul]", eqT(rsgn(rstar(x, y)), rstar(rsgn(x), rsgn(y))), nil},
		{"sgn(−x)=−sgn x [SgnOdd]", eqT(rsgn(rneg(x)), rneg(rsgn(x))), nil},
		// ── NegPositiveIffNegative (the strict neg-order-flip, twin of NegNonnegativeIffNonpositive) — closes sign-mixed
		// strict product (sign-of-product reduction routes the negated factor through
		// NegPositiveIffNegative). ──
		{"x<&0,&0<y⊢x·y<&0 [NegPositiveIffNegative]", rlt(rstar(x, y), z), []core.Term{rlt(x, z), rlt(z, y)}},
		// ── Move-across ({LessEq,LessThan}SubAdd{Left,Right} and EqSub{Left,Right}Add). Each leaf rewrites a
		// sub-carrying comparison atom to the positive form linarith eats. Test:
		// goal carries the sub, hyp the positivized form (hyp-echo after re-write). ──
		{"x≤z+y⊢x−y≤z [LessEqSubAddRight]", rle(rsub(x, y), z), []core.Term{rle(x, rplus(z, y))}},
		{"x+z≤y⊢x≤y−z [LessEqSubAddLeft]", rle(x, rsub(y, z)), []core.Term{rle(rplus(x, z), y)}},
		{"x<z+y⊢x−y<z [LessThanSubAddRight]", rlt(rsub(x, y), z), []core.Term{rlt(x, rplus(z, y))}},
		{"x+z<y⊢x<y−z [LessThanSubAddLeft]", rlt(x, rsub(y, z)), []core.Term{rlt(rplus(x, z), y)}},
		{"x=z+y⊢x−y=z [EqSubRightAdd]", eqT(rsub(x, y), z), []core.Term{eqT(x, rplus(z, y))}},
		{"x+z=y⊢x=y−z [EqSubLeftAdd]", eqT(x, rsub(y, z)), []core.Term{eqT(rplus(x, z), y)}},
		// ── Abs algebraic laws (AbsIdempotent, AbsDiv, AbsInv, AbsPow) — the simp folds, so the
		// goal closes as reflexivity after both sides normalize. ──
		{"||x||=|x| [AbsIdempotent]", eqT(rabs(rabs(x)), rabs(x)), nil},
		{"|x/y|=|x|/|y| [AbsDiv]", eqT(rabs(rdiv(x, y)), rdiv(rabs(x), rabs(y))), nil},
		{"|inv x|=inv|x| [AbsInv]", eqT(rabs(rinv(x)), rinv(rabs(x))), nil},
		{"|x^n|=|x|^n [AbsPow]", eqT(rabs(rpow(x, nn)), rpow(rabs(x), nn)), nil},
		// ── Sgn algebra (SgnPreservedByInv). ──
		{"sgn(inv x)=sgn x [SgnPreservedByInv]", eqT(rsgn(rinv(x)), rsgn(x)), nil},
		// ── Field layer — positive-divisor clearing + InvOne + MulLeftInverse. ──
		{"inv &1=&1 [InvOne]", eqT(rinv(rlit(1)), rlit(1)), nil},
		{"x≠&0⊢inv x·x=&1 [MulLeftInverse]", eqT(rstar(rinv(x), x), rlit(1)), []core.Term{notT(eqT(x, z))}},
		{"0<c,y=x·c⊢x=y/c [EqDivMulLeft]", eqT(x, rdiv(y, c)), []core.Term{rlt(z, c), eqT(y, rstar(x, c))}},
		{"0<c,x·c<y⊢x<y/c [LessThanDivMulLeft]", rlt(x, rdiv(y, c)), []core.Term{rlt(z, c), rlt(rstar(x, c), y)}},
		{"0<c,x≤y·c⊢x/c≤y [LessEqDivMulRight]", rle(rdiv(x, c), y), []core.Term{rlt(z, c), rle(x, rstar(y, c))}},
		{"0<c,x<y·c⊢x/c<y [LessThanDivMulRight]", rlt(rdiv(x, c), y), []core.Term{rlt(z, c), rlt(x, rstar(y, c))}},
		{"0<c,y=x·c⊢y/c=x [EqDivMulRight]", eqT(rdiv(y, c), x), []core.Term{rlt(z, c), eqT(y, rstar(x, c))}},
		// ── Inv algebraic laws (Inv{Mul,Inv,Neg,Div,Pow}) — simp folds. ──
		{"inv(x·y)=inv x·inv y [InvMul]", eqT(rinv(rstar(x, y)), rstar(rinv(x), rinv(y))), nil},
		{"inv(inv x)=x [InvInv]", eqT(rinv(rinv(x)), x), nil},
		{"inv(−x)=−inv x [InvNeg]", eqT(rinv(rneg(x)), rneg(rinv(x))), nil},
		{"inv(x/y)=y/x [InvDiv]", eqT(rinv(rdiv(x, y)), rdiv(y, x)), nil},
		{"inv(x^n)=inv x^n [InvPow]", eqT(rinv(rpow(x, nn)), rpow(rinv(x), nn)), nil},
		// ── Inv sign monotonicity (InvPos, InvNonneg, InvEqZero) — goal-side
		// rewrites the inv-rooted comparison/equality atom to bare x. ──
		{"&0<x⊢&0<inv x [InvPos]", rlt(z, rinv(x)), []core.Term{rlt(z, x)}},
		{"&0≤x⊢&0≤inv x [InvNonneg]", rle(z, rinv(x)), []core.Term{rle(z, x)}},
		{"x=&0⊢inv x=&0 [InvEqZero]", eqT(rinv(x), z), []core.Term{eqT(x, z)}},
		// ── Neg / square ↔ abs interchange (NegEqZero, SquareOfAbs, SquarePos). ──
		{"x=&0⊢−x=&0 [NegEqZero]", eqT(rneg(x), z), []core.Term{eqT(x, z)}},
		{"|x|^2=x^2 [SquareOfAbs]", eqT(rpow(rabs(x), omega.Numeral(2)), rpow(x, omega.Numeral(2))), nil},
		{"&0<x·x⊢x≠&0 [SquarePos]", notT(eqT(x, z)), []core.Term{rlt(z, rstar(x, x))}},
		// ── Pow distribution (MulPowDistrib, DivPow, PowPow, OnePow) — simp folds. ──
		{"(x·y)^n=x^n·y^n [MulPowDistrib]", eqT(rpow(rstar(x, y), nn), rstar(rpow(x, nn), rpow(y, nn))), nil},
		{"(x/y)^n=x^n/y^n [DivPow]", eqT(rpow(rdiv(x, y), nn), rdiv(rpow(x, nn), rpow(y, nn))), nil},
		{"(x^m)^n=x^(m·n) [PowPow]", eqT(rpow(rpow(x, mm), nn), rpow(x, nStar(mm, nn))), nil},
		{"&1^n=&1 [OnePow]", eqT(rpow(rlit(1), nn), rlit(1)), nil},
		// ── Sgn extras (SgnOfZero, SgnDiv, SgnPow). ──
		{"sgn &0=&0 [SgnOfZero]", eqT(rsgn(z), z), nil},
		{"sgn(x/y)=sgn x/sgn y [SgnDiv]", eqT(rsgn(rdiv(x, y)), rdiv(rsgn(x), rsgn(y))), nil},
		{"sgn(x^n)=sgn x^n [SgnPow]", eqT(rsgn(rpow(x, nn)), rpow(rsgn(x), nn)), nil},
		// ── Square ↔ abs ordering interchange + abs triangle. ──
		{"|x|≤|y|⊢x^2≤y^2 [AbsLessEqIffPowTwoLessEq]",
			rle(rpow(x, omega.Numeral(2)), rpow(y, omega.Numeral(2))),
			[]core.Term{rle(rabs(x), rabs(y))}},
		{"|x+y|≤|x|+|y| [AbsTriangle]",
			rle(rabs(rplus(x, y)), rplus(rabs(x), rabs(y))), nil},
		// ── Pow base/exponent monotonicity (PowMonoBase, PowMonoBaseStrict, PowMonoExp). ──
		{"0≤x ∧ x≤y ⊢ x^n≤y^n [PowMonoBase]",
			rle(rpow(x, nn), rpow(y, nn)),
			[]core.Term{rle(z, x), rle(x, y)}},
		{"n≠0 ∧ 0≤x ∧ x<y ⊢ x^n<y^n [PowMonoBaseStrict]",
			rlt(rpow(x, nn), rpow(y, nn)),
			[]core.Term{notT(eqT(nn, dsl.ZeroMeta.Term())), rle(z, x), rlt(x, y)}},
		{"1≤x ∧ m≤n ⊢ x^m≤x^n [PowMonoExp]",
			rle(rpow(x, mm), rpow(x, nn)),
			[]core.Term{rle(rlit(1), x), nLe(mm, nn)}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			w := omega.RealArithDecideWithHyps(tc.hyps)(tc.goal)
			if w == nil {
				t.Fatalf("%s: RealArithDecideWithHyps = nil, want ⊤", tc.name)
			}
			if !prop.Rhs(w).AlphaEquals(prop.T) {
				t.Errorf("%s: → %v, want ⊤", tc.name, prop.Rhs(w))
			}
		})
	}
}
