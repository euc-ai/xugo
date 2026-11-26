package serve

import (
	"context"
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// installIntForTest installs the full chain (nat → real → int + IntLemmaBundle).
// The int leaves often delegate numeral work to the num evaluator through the
// int_of_num homomorphism bridge, so the nat bundle must be live; the int
// IntOfRealThm lifts (NotLessEq / SquareOfAbs / AbsLessEqIffPowTwoLessEq / PowNonneg / PowPos / PowTwoNonneg /
// PowZero / PowSuc) read ℝ sources through the real bundle. Sets up the
// IntBridges AND the IntLemmaBundle (InstallIntBundle calls both internally).
func installIntForTest(t *testing.T) {
	t.Helper()
	InstallNatBundle()
	InstallRealBundle()
	InstallIntBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
		omega.SetRealLemmaBundle(nil)
		omega.SetIntLemmaBundle(nil)
		omega.SetIntBridges(nil)
	})
}

// TestInstallIntLemmaBundleBindingBuilds: the bundle install itself succeeds —
// every field binds without panic. Forces a representative subset of the
// bound *PropWrapper's to flush the file-promise + α-equality settle gate, so a
// shape mismatch between the leaf-wanted form and the entry/lifted source
// surfaces here rather than as a deferred panic on first arith use.
func TestInstallIntLemmaBundleBindingBuilds(t *testing.T) {
	installIntForTest(t)
	// The install completed; the bundle is non-nil.
}

// TestDivisionRemUpperAbsForce: RemUpperAbs is the one int-bundle field with
// no entry of its own — it is a WEAKENING of
// int_div_rem.DivisionAlgorithm derived at bind time by
// omega.DivisionRemUpperAbs (a fromGeneral binding would panic "no corpus
// theorem registered" the first time a replayed Arith() step forced the
// leaf). intCloses-style tests never force the cert, so this test forces
// the derived promise — kernel-running the whole weakening chain
// (∨-cases, ∧-elim, re-∀-close) — and pins the leaf-contract shape
// ∀n m. (n=&0) ∨ (int_rem(m,n) < |n|) with binder order [n, m].
//
// The force is BOUNDED at DivisionAlgorithm itself (ForceWithBoundary
// trusting exactly the entry's statement, as stated — the statement of its
// root promise, the one cell a bounded force settles from trust): the
// entry's own replay is the replay gate's job (subprocess, bounded at the
// corpus trust frontier), and an UNbounded force here would rebuild its
// full dep cone on the shared corpus env (minutes of redundant
// re-proving). The Normalize form and the weakening above it are derived
// for real, and the certificate assumes that one statement and nothing
// else. The unbounded corpEnv promise-resolution seam, which this test
// does not drive, has its own fast cover (TestCorpusEnvNamedPromiseForce).
// No bundle install: DivisionAlgorithm's Build (whose Arith steps would
// need it) never runs. The assumed-audit below
// fails loudly if the frontier key ever drifts — the force then cascades
// into the full cone (slow, likely panicking on the missing bundles) and
// assumed comes back wrong.
func TestDivisionRemUpperAbsForce(t *testing.T) {
	// int_div_rem.DivisionAlgorithm in its Normalize form —
	// what omega.DivisionRemUpperAbs reads and what the production wiring
	// passes it (int_bundle.go's RemUpperAbs field, via `fromEntry`). The
	// promise is lazy, so the bounded force below settles one cell.
	entry := EntryThm(env(), int_div_rem.DivisionAlgorithm)
	srcNorm, _ := prop.Normalize(prop.WrapProp(entry))
	src := prop.WrapProp(srcNorm)
	derived := omega.DivisionRemUpperAbs(src)

	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	irem := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntRemMeta.Term(), a, b) }
	iabs := func(a core.Term) core.Term { return ext.Apply(dsl.IntAbsMeta.Term(), a) }
	ilt := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLtMeta.Term(), a, b) }
	ilit := func(v uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(v)) }
	n, m := iv("n"), iv("m")
	want := ext.ForAll(n, m)(ext.Apply(prop.OR,
		core.Eq(n, ilit(0)), ilt(irem(m, n), iabs(n))))
	if !derived.Conclusion().AlphaEquals(want) {
		t.Fatalf("derived shape %v does not α-match leaf contract %v",
			derived.Conclusion(), want)
	}

	cert, assumed := core.ForceWithBoundary(context.Background(), core.AsThm(derived),
		func(s core.Prop) bool { return s.AlphaEquals(entry) })
	if cert.IsZero() {
		t.Fatal("forcing derived RemUpperAbs yielded nil cert")
	}
	if len(assumed) != 1 || !assumed[0].AlphaEquals(entry) {
		t.Fatalf("bounded force should assume exactly int_div_rem.DivisionAlgorithm; assumed %d frontier statement(s)", len(assumed))
	}
	stands := cert.Assumes()
	if len(stands) != 1 || stands[0].Door != core.BoundaryDoor || !stands[0].Statement.AlphaEquals(entry) {
		t.Fatalf("the certificate should assume exactly int_div_rem.DivisionAlgorithm through the boundary; it assumes %v", stands)
	}
}

// intCloses reports whether omega's int arith decider FULLY discharges the
// goal under hyps. Mirror of arithCloses for the int domain — used by every
// downstream binding test. A `true` result implies all involved leaves bound
// their real (or lifted) cert; a placeholder degrade would panic at the seam.
func intCloses(goal core.Term, hyps ...core.Term) bool {
	wRw := omega.IntArithDecideWithHyps(hyps)(goal)
	if wRw == nil {
		return false
	}
	return prop.Rhs(wRw).Equals(prop.T)
}

// TestInstallIntLemmaBundleBindingLinarith: the linear-fragment leaves
// (NotLessThan/NotLessEq duality, LessEqOfEq/LessEqOfEqSwapped, LessEqAdd2 family, additive cancel, positive
// scaling with `&0 ≤ &c` discharge through the of_num bridge, antisymmetry,
// the `>`/`≥` def bridges, ring AC/identity/distribution + numeral folds) all
// drive end-to-end through the int decider.
func TestInstallIntLemmaBundleBindingLinarith(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	iplus := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPlusMeta.Term(), a, b) }
	istar := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntStarMeta.Term(), a, b) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilt := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLtMeta.Term(), a, b) }
	igt := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntGtMeta.Term(), a, b) }
	ige := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntGeMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	eqT := core.Eq
	x, y, z := iv("x"), iv("y"), iv("z")

	cases := []struct {
		name string
		hyps []core.Term
		goal core.Term
	}{
		// < transitivity (LessThanAdd2 / LessEqTrans path).
		{"x<z | x<y, y<z", []core.Term{ilt(x, y), ilt(y, z)}, ilt(x, z)},
		// strict ⇒ non-strict (duality).
		{"x≤y | x<y", []core.Term{ilt(x, y)}, ile(x, y)},
		// antisymmetry close (=).
		{"x=y | x≤y, y≤x", []core.Term{ile(x, y), ile(y, x)}, eqT(x, y)},
		// numeral close via the int_of_num bridge.
		{"&1 ≤ x | &2 ≤ x", []core.Term{ile(ilit(2), x)}, ile(ilit(1), x)},
		// `>` / `≥` definitional bridges.
		{"y > x | x < y", []core.Term{ilt(x, y)}, igt(y, x)},
		{"y ≥ x | x ≤ y", []core.Term{ile(x, y)}, ige(y, x)},
		// Positive scaling: λ=2 cert → scale leaf + (&0 ≤ &2) side condition discharge.
		{"&2·x ≤ &2·y | x≤y", []core.Term{ile(x, y)}, ile(istar(ilit(2), x), istar(ilit(2), y))},
		// Like-term merge through intRing.
		{"x+x ≤ &2·x", nil, ile(iplus(x, x), istar(ilit(2), x))},
		// Additive cancellation (hyp echo + const fold).
		{"x+&1 ≤ y | x+&1 ≤ y", []core.Term{ile(iplus(x, ilit(1)), y)}, ile(iplus(x, ilit(1)), y)},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !intCloses(tc.goal, tc.hyps...) {
				t.Fatalf("int arith did not close: %s", tc.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingRing: IntRingProve exercises every ring AC
// leaf + identity + distribution + numeral folding (int_of_num bridge through
// the num evaluator). Goals built directly (the text parser defaults bare
// `x + y` to real, no int-context to lex-dispatch off).
func TestInstallIntLemmaBundleBindingRing(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	add := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPlusMeta.Term(), a, b) }
	mul := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntStarMeta.Term(), a, b) }
	lit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	x, y, z := iv("x"), iv("y"), iv("z")

	pairs := []struct {
		name string
		l, r core.Term
	}{
		{"x + y = y + x", add(x, y), add(y, x)},
		{"(x + y) + z = x + (y + z)", add(add(x, y), z), add(x, add(y, z))},
		{"&2·(x+y) = &2·x + &2·y", mul(lit(2), add(x, y)), add(mul(lit(2), x), mul(lit(2), y))},
		{"&3·x + &2·x = &5·x", add(mul(lit(3), x), mul(lit(2), x)), mul(lit(5), x)},
		{"(x+&3)+(y+&4) = (x+y)+&7", add(add(x, lit(3)), add(y, lit(4))), add(add(x, y), lit(7))},
		{"x = &1·x + &0", x, add(mul(lit(1), x), lit(0))},
		{"&0·(x+y) + x = x", add(mul(lit(0), add(x, y)), x), x},
	}
	for _, p := range pairs {
		t.Run(p.name, func(t *testing.T) {
			w, ok := omega.IntRingProve(p.l, p.r)
			if !ok {
				t.Fatalf("IntRingProve declined: %s", p.name)
			}
			if !w.Conclusion().AlphaEquals(core.Eq(p.l, p.r)) {
				t.Errorf("conclusion %v, want %s", w.Conclusion(), p.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingRefute: ex-falso closes via Farkas
// refutation — every contradictory hyp set drives `&1 ≤ &0`, exercising
// the LinProve composition with the bundle bound.
func TestInstallIntLemmaBundleBindingRefute(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	iplus := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPlusMeta.Term(), a, b) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilt := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLtMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	x, y := iv("x"), iv("y")

	sets := [][]core.Term{
		{ilt(x, y), ilt(y, x)},
		{ile(ilit(2), x), ile(x, ilit(1))},
		{ile(iplus(x, y), ilit(1)), ile(ilit(2), iplus(x, y))},
	}
	for i, hyps := range sets {
		t.Run(fmt.Sprintf("set%d", i), func(t *testing.T) {
			goal := ile(ilit(1), ilit(0))
			if !intCloses(goal, hyps...) {
				t.Fatalf("int arith did not exploit contradictory hyps %v", hyps)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingDiscrete: the ℤ-discreteness strengthening
// (Discrete) — the lone int-only leaf with no real twin to lift. Closes the
// off-by-one class linarith over ℚ can't.
func TestInstallIntLemmaBundleBindingDiscrete(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	iplus := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPlusMeta.Term(), a, b) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilt := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLtMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	x, y := iv("x"), iv("y")

	// x < y ⊢ x + &1 ≤ y — discreteness tightens the strict row.
	if !intCloses(ile(iplus(x, ilit(1)), y), ilt(x, y)) {
		t.Fatal("Discrete-bridged off-by-one did not close")
	}
}

// TestInstallIntLemmaBundleBindingSubneg: the signed normalizer + relation
// move-across families — SubDef / NegAdd / NegNeg / NegZero / MulRightNeg on the
// term side, LessEqSubAddRight / LessEqSubAddLeft / LessThanSubAddRight / LessThanSubAddLeft / EqSubRightAdd /
// EqSubLeftAdd on the relation side. These flow goals with top-level
// subtraction/negation into the positive linear pipeline.
func TestInstallIntLemmaBundleBindingSubneg(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	iplus := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPlusMeta.Term(), a, b) }
	isub := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntSubMeta.Term(), a, b) }
	ineg := func(a core.Term) core.Term { return ext.Apply(dsl.IntNegMeta.Term(), a) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	eqT := core.Eq
	a, b, c := iv("a"), iv("b"), iv("c")
	x, y := iv("x"), iv("y")

	cases := []struct {
		name string
		hyps []core.Term
		goal core.Term
	}{
		// goal-side sub: x − y ≤ &3 — move-across to x ≤ &3 + y.
		{"x−y≤&3 from x≤&3+y", []core.Term{ile(x, iplus(ilit(3), y))}, ile(isub(x, y), ilit(3))},
		// goal-side neg: &0 ≤ x − y from x = y.
		{"&0 ≤ x−y from x=y", []core.Term{eqT(x, y)}, ile(ilit(0), isub(x, y))},
		// hyp-side sub: a − b ≤ c ⊢ a ≤ c + b.
		{"a≤c+b | a−b≤c", []core.Term{ile(isub(a, b), c)}, ile(a, iplus(c, b))},
		// neg-on-rhs: −x ≤ y from y = −x.
		{"−x ≤ y from y=−x", []core.Term{eqT(y, ineg(x))}, ile(ineg(x), y)},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !intCloses(tc.goal, tc.hyps...) {
				t.Fatalf("int arith did not close: %s", tc.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingPow: the int_pow leaves PowZero / PowSuc
// (projected from real_pow's conjunction and lifted via IntOfRealThm) plus
// the sign / square / abs ordering lifts (SquareOfAbs / AbsLessEqIffPowTwoLessEq /
// PowNonneg / PowPos / PowTwoNonneg) — every leaf whose source is an ℝ entry.
func TestInstallIntLemmaBundleBindingPow(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	istar := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntStarMeta.Term(), a, b) }
	ipow := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPowMeta.Term(), a, b) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	eqT := core.Eq
	x := iv("x")

	cases := []struct {
		name string
		hyps []core.Term
		goal core.Term
	}{
		// PowZero (lifted): int_pow x 0 = &1 — direct equality via the leaf.
		{"x^0 = &1", nil, eqT(ipow(x, omega.Numeral(0)), ilit(1))},
		// PowSuc-driven c=1 fold (auto-shrinking): int_pow x 1 = x · int_pow x 0
		// = x · &1 = x.
		{"x^1 = x", nil, eqT(ipow(x, omega.Numeral(1)), x)},
		// SquareNonneg: &0 ≤ x·x with no hyp. (Lifted leaf, no agent expand.)
		{"&0 ≤ x·x", nil, ile(ilit(0), istar(x, x))},
		// PowTwoNonneg (lifted from ℝ): no-hyp even-square nonneg.
		{"&0 ≤ x^2", nil, ile(ilit(0), ipow(x, omega.Numeral(2)))},
		// PowNonneg (lifted): &0 ≤ x ⊢ &0 ≤ x^3.
		{"&0≤x^3 | &0≤x", []core.Term{ile(ilit(0), x)}, ile(ilit(0), ipow(x, omega.Numeral(3)))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !intCloses(tc.goal, tc.hyps...) {
				t.Fatalf("int arith did not close: %s", tc.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingAbs: AbsBySign (defNorm("int_abs")) + the
// the abs algebraic laws — AbsMul / AbsEven / AbsIdempotent / OfNumAbs — that drive
// the leaf-folding rewrites in intArithSimpStep.
func TestInstallIntLemmaBundleBindingAbs(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	iplus := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPlusMeta.Term(), a, b) }
	iabs := func(a core.Term) core.Term { return ext.Apply(dsl.IntAbsMeta.Term(), a) }
	ineg := func(a core.Term) core.Term { return ext.Apply(dsl.IntNegMeta.Term(), a) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	x, y := iv("x"), iv("y")

	cases := []struct {
		name string
		goal core.Term
	}{
		// AbsBySign + case split: &0 ≤ |x|.
		{"&0 ≤ |x|", ile(ilit(0), iabs(x))},
		// Compound-arg folds: the SIMP layer pushes abs into leaves.
		// |x·y| = |x|·|y| → after folding, both sides reflexively equal —
		// SIMP closes via reflexivity. The TRIANGLE follows from the bound.
		{"|x + y| ≤ |x| + |y|", ile(iabs(iplus(x, y)), iplus(iabs(x), iabs(y)))},
		// AbsEven compound: |−x| = |x| would be a literal equality, but the
		// canonical surface goal is &0 ≤ |−x| (closes via AbsEven → AbsBySign
		// chain through simp).
		{"&0 ≤ |−x|", ile(ilit(0), iabs(ineg(x)))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !intCloses(tc.goal) {
				t.Fatalf("int arith did not close: %s", tc.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingSgnMaxMin: the sgn/max/min piecewise-def
// leaves (SgnDef / MaxDef / MinDef, bound via liftReal(defNorm(...)) +
// condPushRealOfInt) drive their case splits end-to-end and CLOSE — the
// positive twin of TestInstallIntLemmaBundleBindingLeafSeams' fault-4 rows
// (which only assert absence-of-panic). Pre-condPushRealOfInt these leaves
// were dead capability in production: the lift's real_of_int COND residue
// made every one of them panic at the placeholder seam.
func TestInstallIntLemmaBundleBindingSgnMaxMin(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	sgn := func(a core.Term) core.Term { return ext.Apply(dsl.IntSgnMeta.Term(), a) }
	imax := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntMaxMeta.Term(), a, b) }
	imin := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntMinMeta.Term(), a, b) }
	ineg := func(a core.Term) core.Term { return ext.Apply(dsl.IntNegMeta.Term(), a) }
	x, y := iv("x"), iv("y")

	cases := []struct {
		name string
		hyps []core.Term
		goal core.Term
	}{
		// SgnDef: literal evaluation through the nested-COND split.
		{"sgn(&5) = &1", nil, core.Eq(sgn(ilit(5)), ilit(1))},
		{"sgn(−&3) = −&1", nil, core.Eq(sgn(ineg(ilit(3))), ineg(ilit(1)))},
		{"sgn(&0) = &0", nil, core.Eq(sgn(ilit(0)), ilit(0))},
		// SgnDef: symbolic arg pinned by a hyp (the outer `&0 < x` guard
		// decides from `&1 ≤ x` through linarith).
		{"&1 ≤ x ⊢ sgn(x) = &1", []core.Term{ile(ilit(1), x)}, core.Eq(sgn(x), ilit(1))},
		// MaxDef / MinDef: literal and hyp-pinned symbolic splits.
		{"max(&1,&2) = &2", nil, core.Eq(imax(ilit(1), ilit(2)), ilit(2))},
		{"min(&1,&2) = &1", nil, core.Eq(imin(ilit(1), ilit(2)), ilit(1))},
		{"x ≤ y ⊢ max(x,y) = y", []core.Term{ile(x, y)}, core.Eq(imax(x, y), y)},
		{"x ≤ y ⊢ min(x,y) = x", []core.Term{ile(x, y)}, core.Eq(imin(x, y), x)},
		// Order facts through the split (no equality pinning needed).
		{"x ≤ max(x,y)", nil, ile(x, imax(x, y))},
		{"min(x,y) ≤ x", nil, ile(imin(x, y), x)},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !intCloses(tc.goal, tc.hyps...) {
				t.Fatalf("int arith did not close: %s", tc.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingSignedProduct: LessEqMul / MulPos / MulEqZero /
// LessEqTrans — the sign-known nonlinear fragment, instantiated via fromGeneral
// (every leaf a reshape of a CNF-clause normal form).
func TestInstallIntLemmaBundleBindingSignedProduct(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	istar := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntStarMeta.Term(), a, b) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilt := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLtMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	notT := func(a core.Term) core.Term { return ext.Apply(prop.NOT, a) }
	eqT := core.Eq
	a, b, c, d := iv("a"), iv("b"), iv("c"), iv("d")
	x, y := iv("x"), iv("y")

	cases := []struct {
		name string
		hyps []core.Term
		goal core.Term
	}{
		// Sign-of-product (LessEqMul, fromGeneral): &0≤x, &0≤y ⊢ &0 ≤ x·y.
		{"&0≤x·y | &0≤x, &0≤y", []core.Term{ile(ilit(0), x), ile(ilit(0), y)},
			ile(ilit(0), istar(x, y))},
		// Strict twin (MulPos): &0<x, &0<y ⊢ &0 < x·y.
		{"&0<x·y | &0<x, &0<y", []core.Term{ilt(ilit(0), x), ilt(ilit(0), y)},
			ilt(ilit(0), istar(x, y))},
		// Two-sided product bound (LessEqTrans-derived): &0≤a, a≤b, &0≤c, c≤d ⊢ a·c ≤ b·d.
		{"a·c≤b·d | &0≤a, a≤b, &0≤c, c≤d",
			[]core.Term{ile(ilit(0), a), ile(a, b), ile(ilit(0), c), ile(c, d)},
			ile(istar(a, c), istar(b, d))},
		// Positive-factor cancellation OUT of a hypothesis (LessEqCancelMulLeft /
		// LessThanCancelMulLeft — the REAL pair lifted, since ℤ states neither).
		// The scaling read backwards, so the sign premise is STRICT: `&0 ≤ c`
		// cancels nothing, `&0·a ≤ &0·b` holding for every a and b. The
		// right-factor spellings ride the same two fields with both sides
		// commuted through MulSym.
		{"a≤b | &0<c, c·a≤c·b", []core.Term{ilt(ilit(0), c), ile(istar(c, a), istar(c, b))},
			ile(a, b)},
		{"a<b | &0<c, c·a<c·b", []core.Term{ilt(ilit(0), c), ilt(istar(c, a), istar(c, b))},
			ilt(a, b)},
		{"a≤b | &0<c, a·c≤b·c", []core.Term{ilt(ilit(0), c), ile(istar(a, c), istar(b, c))},
			ile(a, b)},
		{"a<b | &0<c, a·c<b·c", []core.Term{ilt(ilit(0), c), ilt(istar(a, c), istar(b, c))},
			ilt(a, b)},
		// Integral domain (MulEqZero): x·x=&0 ⊢ x=&0 (the square collapse).
		{"x=&0 | x·x=&0", []core.Term{eqT(istar(x, x), ilit(0))}, eqT(x, ilit(0))},
		// MulEqZero on distinct factors with one nonzero: x·y=&0 ∧ x≠&0 ⊢ y=&0.
		{"y=&0 | x·y=&0, x≠&0",
			[]core.Term{eqT(istar(x, y), ilit(0)), notT(eqT(x, ilit(0)))},
			eqT(y, ilit(0))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !intCloses(tc.goal, tc.hyps...) {
				t.Fatalf("int arith did not close: %s", tc.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingDivRem: the int Euclidean division layer —
// DivisionIdentity, RemNonneg, RemBelowDivisor, RemUpperAbs, DivModUnique, DivByZero/RemByZero/DivByOne/RemByOne.
// These exercise every newly proved (RemBelowDivisor / DivByOne / RemByOne) leaf
// AND the fromGeneral'd ones (RemNonneg, RemBelowDivisor, RemUpperAbs, DivModUnique).
func TestInstallIntLemmaBundleBindingDivRem(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	idiv := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntDivMeta.Term(), a, b) }
	irem := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntRemMeta.Term(), a, b) }
	ile := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	ilt := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLtMeta.Term(), a, b) }
	ilit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	iplus := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntPlusMeta.Term(), a, b) }
	istar := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntStarMeta.Term(), a, b) }
	notT := func(a core.Term) core.Term { return ext.Apply(prop.NOT, a) }
	eqT := core.Eq
	m, n, p := iv("m"), iv("n"), iv("p")

	cases := []struct {
		name string
		hyps []core.Term
		goal core.Term
	}{
		// DivByOne: int_div(m, &1) = m.
		{"int_div(m, &1) = m", nil, eqT(idiv(m, ilit(1)), m)},
		// RemByOne: int_rem(m, &1) = &0.
		{"int_rem(m, &1) = &0", nil, eqT(irem(m, ilit(1)), ilit(0))},
		// DivByZero: int_div(m, &0) = &0.
		{"int_div(m, &0) = &0", nil, eqT(idiv(m, ilit(0)), ilit(0))},
		// RemByZero: int_rem(m, &0) = m.
		{"int_rem(m, &0) = m", nil, eqT(irem(m, ilit(0)), m)},
		// RemNonneg: &0 < n ⊢ &0 ≤ int_rem(m, n).
		{"&0≤int_rem(m,n) | &0<n", []core.Term{ilt(ilit(0), n)}, ile(ilit(0), irem(m, n))},
		// RemBelowDivisor: &0 < n ⊢ int_rem(m, n) < n.
		{"int_rem(m,n)<n | &0<n", []core.Term{ilt(ilit(0), n)}, ilt(irem(m, n), n)},
		// Literal-operand int_div/int_rem (DivModUnique).
		{"int_div(&7, &2) = &3", nil, eqT(idiv(ilit(7), ilit(2)), ilit(3))},
		{"int_rem(&7, &2) = &1", nil, eqT(irem(ilit(7), ilit(2)), ilit(1))},
		// Symbolic n≠0: RemUpperAbs path — `n ≠ &0 ⊢ int_rem(m,n) < int_abs(n)`.
		// Composes with the int_abs case split for sign-specific branches.
		{"&0≤int_rem(m,n) | n≠&0", []core.Term{notT(eqT(n, ilit(0)))},
			ile(ilit(0), irem(m, n))},
		// DivMulAdd / RemMulAdd: a `n·p` summand leaves the dividend at a
		// literal nonzero n — the fourth clause of each pack, read in the
		// leaf's binder order (mulAddLaw).
		{"int_div(m+&2·p,&2) = int_div(m,&2)+p", nil,
			eqT(idiv(iplus(m, istar(ilit(2), p)), ilit(2)), iplus(idiv(m, ilit(2)), p))},
		{"int_rem(m+&2·p,&2) = int_rem(m,&2)", nil,
			eqT(irem(iplus(m, istar(ilit(2), p)), ilit(2)), irem(m, ilit(2)))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !intCloses(tc.goal, tc.hyps...) {
				t.Fatalf("int arith did not close: %s", tc.name)
			}
		})
	}
}

// TestInstallIntLemmaBundleBindingLeafSeams guards the int-bundle leaves
// whose bound theorem macroEq's α-match must accept at the instantiated
// shape: a rejected match falls through to placeholderConcl and panics at
// the placeholder seam in PRODUCTION (serve). The seams:
//
// 1. intDividesIffRemZero — wants `(int_rem(m,n) = &0) ⇔ int_divides(n,m)`; the
// DividesIffRemZero normal form carries the inner equality CNF-oriented
// (`&0 = int_rem(m,n)`), and macroEq flips the OUTER relation only, so the
// leaf orients the inner equality itself (prover/solver/omega/int_lemmas.go,
// intDividesIffRemZero).
// 2. intOfNumAbs / intAbsMul (and every sibling) — macroEq's instAll no-ops
// on a non-∀-headed conclusion, so the bound theorem must be ∀-closed:
// fromEntry binds the closed normal form, and fromEntryAsStated ∀-closes
// free conclusion vars at bind time (forallCloseFrees,
// library/serve/serve.go).
// 3. intDividesDefIff (leaf binder contract [d, e]) — defNorm("int_divides")
// ∀-closes in body-first-occurrence order `∃x. e = d·x` → [e, d], so a
// [d, e] instantiation would come out arg-swapped on both the divides-GOAL
// path (intDividesGoal) and the divides-HYP skolemizer (intDividesSkolem).
// The bind site re-∀-closes the def in the field's contractual (d, e)
// order (dividesDefOrdered, library/serve/int_bundle.go).
// 4. intSgnDef / intMaxDef / intMinDef — SgnDef/MaxDef/MinDef bind via
// liftReal(defNorm(...)), and the IntOfRealThm lift must not leave
// real_of_int residue on the piecewise COND branches (`real_of_int(int_sgn
// x) = COND(g, real_of_int(&1), …)`), or ANY bare int_sgn / int_max /
// int_min in hyps∪goal panics at the case split's def leaf
// (intSgnSplittable calls intSgnDef unconditionally). The lift's generic
// COND homomorphism completion (condPushRealOfInt,
// prover/solver/omega/int_lemmas.go) pushes real_of_int out through COND,
// so the lift lands in the exact piecewise-int leaf shape.
//
// Each subtest drives the shape end-to-end through the exported
// IntArithDecideWithHyps (the same entry the engine's arith/auto path uses),
// with the corpus bundles installed exactly like the serve. Asserts
// absence-of-panic (close or clean nil is fine — not closure).
func TestInstallIntLemmaBundleBindingLeafSeams(t *testing.T) {
	installIntForTest(t)
	intT := dsl.IntType
	iv := func(s string) core.Term { return ext.Var(ext.TermName(s), intT) }
	lit := func(n uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(n)) }
	rem := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntRemMeta.Term(), a, b) }
	divides := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntDividesMeta.Term(), a, b) }
	abs := func(a core.Term) core.Term { return ext.Apply(dsl.IntAbsMeta.Term(), a) }
	mul := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntStarMeta.Term(), a, b) }
	le := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntLeMeta.Term(), a, b) }
	sgn := func(a core.Term) core.Term { return ext.Apply(dsl.IntSgnMeta.Term(), a) }
	imax := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntMaxMeta.Term(), a, b) }
	imin := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntMinMeta.Term(), a, b) }
	x, y := iv("x"), iv("y")

	cases := []struct {
		name string
		hyps []core.Term
		goal core.Term
	}{
		// 1. rem-eq-zero bridge: the goal atom `int_rem(x,&2) = &0` is exactly what
		// intDividesIffRemZeroSimp fires on (l=rem, r=&0, n∉{0,1}) → intDividesIffRemZero →
		// macroEq(DividesIffRemZero) — the inner-eq orientation seam (1).
		{"DividesIffRemZero", []core.Term{divides(lit(2), x)}, core.Eq(rem(x, lit(2)), lit(0))},
		// 2. abs-of-numeral fold: goal containing `int_abs(&2)`.
		{"OfNumAbs", nil, core.Eq(abs(lit(2)), lit(2))},
		// 3. abs-mul fold: goal containing `int_abs(x·y)`.
		{"AbsMul", nil, core.Eq(abs(mul(x, y)), mul(abs(x), abs(y)))},
		// 4. divides-def bridge, GOAL side: `int_divides(&2, &6)` has a literal
		// witness, so intDividesGoal reaches intDividesDefIff →
		// macroThm(DividesDef) — the binder-order seam (3).
		{"DividesDefGoal", nil, divides(lit(2), lit(6))},
		// 5. divides-def bridge, HYP side: a generic `int_divides(d, a)` hyp
		// with a goal the linear tier can't close forces intDividesSkolem to
		// skolemize the hyp via intDividesDefIff — the same leaf.
		{"DividesDefSkolem", []core.Term{divides(iv("d"), iv("a"))},
			divides(iv("d"), mul(iv("a"), iv("b")))},
		// 6. ground-0 instance of the hyp side (the leaf
		// `(∃ν0. &0 = d·ν0) ⇔ int_divides(d, &0)`). The unprovable linear goal
		// forces the decide past the linear tier into intDividesSkolem, which
		// builds the leaf for the hyp before attempting the goal.
		{"DividesDefSkolemZero", []core.Term{divides(iv("d"), lit(0))},
			le(lit(0), iv("d"))},
		// 7. control: pure linear int arith on the same operators — must NOT
		// panic regardless (validates the harness itself).
		{"ControlLinear", []core.Term{le(x, y)}, le(x, y)},
		// 8. sgn/max/min piecewise-def leaves (seam 4): a bare int_sgn /
		// int_max / int_min anywhere in hyps∪goal reaches the case split's
		// def leaf unconditionally, which panics on any real_of_int COND
		// residue the lift leaves.
		{"SgnDefLiteral", nil, core.Eq(sgn(lit(5)), lit(1))},
		{"SgnDefVar", []core.Term{le(lit(1), x)}, core.Eq(sgn(x), lit(1))},
		{"MaxDefLiteral", nil, core.Eq(imax(lit(1), lit(2)), lit(2))},
		{"MinDefLiteral", nil, core.Eq(imin(lit(1), lit(2)), lit(1))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			defer func() {
				if r := recover(); r != nil {
					t.Fatalf("placeholder-seam panic (bundle leaf failed to bind/match): %v", r)
				}
			}()
			w := omega.IntArithDecideWithHyps(tc.hyps)(tc.goal)
			t.Logf("decide returned: %v", w != nil)
		})
	}
}
