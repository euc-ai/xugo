package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// installExpTestBundle gives expUnfold a hand-crafted nat_pow bundle in the
// normal-form shape (equations reversed), which the leaves must
// auto-orient:
//
//	nat_pow   : ∀m n. (1 = nat_pow(m, 0)) ∧ (m · nat_pow(m, n) = nat_pow(m, suc n))
//	PowOne : ∀n. n = nat_pow(n, 1)
//	PowTwo : ∀n. n · n = nat_pow(n, 2)
//
// Same TestThm-shape-pin pattern as TestPreBridge / TestDivCommonFactor — a unit
// guard against shape drift that doesn't need the corpus build to run.
func installExpTestBundle(t *testing.T, includeShortcuts bool) func() {
	t.Helper()
	m, n := numVar("m"), numVar("n")
	mk := func(c core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }

	prev := natLemmaBundle
	b := &NatLemmaBundle{}
	if prev != nil {
		*b = *prev
	}
	// AddClauses backing (sucBits needs it for the suc(c-1) → c evaluation
	// inside expStep — without it the recursion declines).
	b.AddClauses = mk(ext.ForAll(m)(and(
		eqT(plus(m, natZero), m),
		eqT(plus(m, sucT(n)), sucT(plus(m, n))))))
	// nat_pow recursion.
	b.NatPow = mk(ext.ForAll(m, n)(and(
		eqT(Numeral(1), expT(m, natZero)),
		eqT(star(m, expT(m, n)), expT(m, sucT(n))))))
	// NumeralSuc backing for sucBits' bit-recursion. Match the bound form's flat
	// conjunction of per-bit suc rules.
	a := numVar("a")
	b.NumeralSuc = mk(ext.ForAll(a)(and(
		eqT(sucT(natZero), bit1(natZero)),
		and(eqT(sucT(bit0(a)), bit1(a)),
			eqT(sucT(bit1(a)), bit0(sucT(a)))))))
	if includeShortcuts {
		b.PowOne = mk(ext.ForAll(n)(eqT(n, expT(n, Numeral(1)))))
		b.PowTwo = mk(ext.ForAll(n)(eqT(star(n, n), expT(n, Numeral(2)))))
	}

	SetNatLemmaBundle(b)
	return func() { SetNatLemmaBundle(prev) }
}

// TestExpUnfoldBase: c=0 uses the nat_pow recursion clause 1.
func TestExpUnfoldBase(t *testing.T) {
	defer installExpTestBundle(t, true)()
	m := numVar("m")
	w := expUnfold(m, 0)
	if w == nil {
		t.Fatal("expUnfold(m, 0) returned nil")
	}
	if want := eqT(expT(m, natZero), Numeral(1)); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("c=0: got %v, want %v", w.Conclusion(), want)
	}
}

// TestExpUnfoldShortcuts: c=1 uses PowOne, c=2 uses PowTwo.
func TestExpUnfoldShortcuts(t *testing.T) {
	defer installExpTestBundle(t, true)()
	m := numVar("m")

	w1 := expUnfold(m, 1)
	if want := eqT(expT(m, Numeral(1)), m); w1 == nil || !w1.Conclusion().AlphaEquals(want) {
		t.Errorf("c=1: got %v, want %v", w1, want)
	}
	w2 := expUnfold(m, 2)
	if want := eqT(expT(m, Numeral(2)), star(m, m)); w2 == nil || !w2.Conclusion().AlphaEquals(want) {
		t.Errorf("c=2: got %v, want %v", w2, want)
	}
}

// TestExpUnfoldRecursion: c≥3 goes through the recursion step.
func TestExpUnfoldRecursion(t *testing.T) {
	defer installExpTestBundle(t, true)()
	m := numVar("m")
	// c=3: nat_pow(m, 3) = m · (m · m).
	w := expUnfold(m, 3)
	if w == nil {
		t.Fatal("expUnfold(m, 3) returned nil")
	}
	want := eqT(expT(m, Numeral(3)), star(m, star(m, m)))
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("c=3: got %v, want %v", w.Conclusion(), want)
	}
}

// TestExpUnfoldNoShortcuts: without PowOne/PowTwo the recursion still terminates
// (c=1 falls through to recursion step that bottoms at c=0; c=2 to c=1 to c=0).
func TestExpUnfoldNoShortcuts(t *testing.T) {
	defer installExpTestBundle(t, false)()
	m := numVar("m")
	for _, c := range []uint64{1, 2, 3} {
		if w := expUnfold(m, c); w == nil {
			t.Errorf("c=%d: expUnfold returned nil with no PowOne/PowTwo shortcuts", c)
		}
	}
}

// TestExpUnfoldCap: exponents beyond the cap return nil rather than DOSing on
// recursion / proof size.
func TestExpUnfoldCap(t *testing.T) {
	defer installExpTestBundle(t, true)()
	m := numVar("m")
	if got := expUnfold(m, expUnfoldMax+1); got != nil {
		t.Errorf("expUnfold beyond cap should be nil, got %v", got.Conclusion())
	}
}

// TestExpSimpNonLiteral: non-literal exponent is left opaque.
func TestExpSimpNonLiteral(t *testing.T) {
	defer installExpTestBundle(t, true)()
	m, n := numVar("m"), numVar("n") // n is a free var, not a bit-tree
	if got := expSimp(expT(m, n)); got != nil {
		t.Errorf("expSimp on nat_pow(m, n) (n free) should be nil, got %v", got.Conclusion())
	}
}

// TestOnePowZeroPow: special-base rewrites for symbolic n fire when OnePow/ZeroPow
// are bundled. OnePow shape: ∀n. 1 = nat_pow(1, n). ZeroPow: ∀n. nat_pow(0, n) =
// COND(n=0, 1, 0).
func TestOnePowZeroPow(t *testing.T) {
	defer installExpTestBundle(t, true)()
	m, n := numVar("m"), numVar("n")
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	natLemmaBundle.OnePow = mk(ext.ForAll(n)(eqT(Numeral(1), expT(Numeral(1), n))))
	natLemmaBundle.ZeroPow = mk(ext.ForAll(n)(eqT(
		expT(natZero, n),
		ext.Cond(eqT(n, natZero), Numeral(1), natZero))))

	// nat_pow(1, n) → 1
	w1 := onePow(n)
	if want := eqT(expT(Numeral(1), n), Numeral(1)); w1 == nil || !w1.Conclusion().AlphaEquals(want) {
		t.Errorf("onePow(n): got %v, want %v", w1, want)
	}
	// nat_pow(0, n) → COND(n=0, 1, 0)
	w0 := zeroPow(n)
	wantRhs := ext.Cond(eqT(n, natZero), Numeral(1), natZero)
	if want := eqT(expT(natZero, n), wantRhs); w0 == nil || !w0.Conclusion().AlphaEquals(want) {
		t.Errorf("zeroPow(n): got %v, want %v", w0, want)
	}

	// expSimp dispatch: symbolic n with special base fires the right leaf.
	if got := expSimp(expT(Numeral(1), n)); got == nil {
		t.Error("expSimp(nat_pow(1, n)) declined — OnePow should fire")
	}
	if got := expSimp(expT(natZero, n)); got == nil {
		t.Error("expSimp(nat_pow(0, n)) declined — ZeroPow should fire")
	}
	// Non-special base + symbolic n: still nil (opaque).
	if got := expSimp(expT(m, n)); got != nil {
		t.Errorf("expSimp(nat_pow(m, n)) should be nil with non-special base, got %v", got.Conclusion())
	}
}

// Bounded-variable enumeration (nat_exp.go). Leaves are TestThm placeholders of the
// real LessEqSplit / LessThanSucIffLessEq statements (the gate needs them non-nil); the rest of
// the per-value evaluation runs on the standard placeholder simp stack. We
// validate the kernel COMPOSITION: proveBoundedEnum concludes the goal with hyps
// drawn only from the inputs. End-to-end soundness against the real corpus bundle
// is covered in library/serve.

func installEnumBundle(t *testing.T) {
	t.Helper()
	m, n := numVar("m"), numVar("n")
	lessEqSplit := ext.ForAll(m, n)(eqT(le(m, n), or(lt(m, n), eqT(m, n)))) // (m≤n)⇔((m<n)∨(m=n))
	lessThanSucIffLessEq := ext.ForAll(m, n)(eqT(lt(m, sucT(n)), le(m, n))) // (m<suc n)⇔(m≤n)
	SetNatLemmaBundle(&NatLemmaBundle{
		LessEqSplit:          prop.WrapProp(core.TestThm(lessEqSplit)),
		LessThanSucIffLessEq: prop.WrapProp(core.TestThm(lessThanSucIffLessEq)),
	})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
}

func TestEnumLeDisj(t *testing.T) {
	installEnumBundle(t)
	x := numVar("x")
	// {x≤2} ⊢ (x=0) ∨ (x=1) ∨ (x=2), in foldl (left-nested) Or form.
	w, ok := enumLeDisj(x, 2)
	if !ok {
		t.Fatal("enumLeDisj(x, 2) failed")
	}
	want := or(or(eqT(x, Numeral(0)), eqT(x, Numeral(1))), eqT(x, Numeral(2)))
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("enumLeDisj(x,2): got %v, want %v", w.Conclusion(), want)
	}
	if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(le(x, Numeral(2))) {
		t.Errorf("enumLeDisj(x,2): hyps = %v, want {x≤2}", w.Conclusion())
	}
}

func TestProveBoundedEnum(t *testing.T) {
	installEnumBundle(t)
	n := numVar("n")
	// n ≤ 2 ⊢ n*n ≤ 4 : nonlinear in n, linarith declines; enumeration over
	// n ∈ {0,1,2} evaluates 0,1,4 ≤ 4.
	hyps := []Term{le(n, Numeral(2))}
	goal := le(star(n, n), Numeral(4))

	w, ok := proveBoundedEnum(hyps, goal)
	if !ok {
		t.Fatal("proveBoundedEnum did not close {n≤2} ⊢ n*n ≤ 4")
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("conclusion = %v, want %v", w.Conclusion(), goal)
	}
	for i := 0; i < w.NumHyps(); i++ {
		if !slices.ContainsFunc(hyps, w.Hyp(i).AlphaEquals) {
			t.Errorf("stray hypothesis %v not among inputs", w.Hyp(i))
		}
	}

	// A `<` bound works too: n < 3 ⊢ n*n ≤ 4 (enumerates n ∈ {0,1,2}).
	if _, ok := proveBoundedEnum([]Term{lt(n, Numeral(3))}, goal); !ok {
		t.Error("proveBoundedEnum did not close {n<3} ⊢ n*n ≤ 4")
	}

	// DERIVED bound (no syntactic literal bound on n): m≤n, n≤2 ⊢ n*n ≤ 4 — wait,
	// the bounded var must be the one occurring nonlinearly. Use m: m≤n, n≤2 imply
	// m≤2 transitively (ℚ-linarith), enabling enumeration of m ∈ {0,1,2}.
	m := numVar("m")
	if _, ok := proveBoundedEnum(
		[]Term{le(m, n), le(n, Numeral(2))}, le(star(m, m), Numeral(4))); !ok {
		t.Error("proveBoundedEnum did not derive m≤2 from {m≤n, n≤2} to close m*m ≤ 4")
	}

	// Linear goal: enumeration declines (ComparisonSidesLinear gate) — linarith's job.
	if _, ok := proveBoundedEnum([]Term{le(n, Numeral(2))}, le(n, Numeral(5))); ok {
		t.Error("proveBoundedEnum fired on a purely-linear goal")
	}
	// No bounded var occurring nonlinearly: declines.
	if _, ok := proveBoundedEnum(nil, goal); ok {
		t.Error("proveBoundedEnum fired without a bounding hypothesis")
	}
}

func TestProveBoundedEnumIgnoresNonNumVars(t *testing.T) {
	installEnumBundle(t)

	f := ext.Var("f", core.MakeFun(dsl.NumType, dsl.NumType))
	fn := ext.Apply(f, Numeral(0))
	goal := le(star(fn, fn), Numeral(4))

	if fvs := freeNumVars(goal); slices.ContainsFunc(fvs, f.AlphaEquals) {
		t.Fatalf("freeNumVars included non-num variable %v in %v", f, fvs)
	}
	if _, ok := proveBoundedEnum(nil, goal); ok {
		t.Fatal("proveBoundedEnum fired without a num bound")
	}
	if _, ok := enumLeDisj(f, 0); ok {
		t.Fatal("enumLeDisj accepted a non-num variable")
	}
}

// Bounded existential witness search (proveBoundedExists) — the ∃-dual of
// proveBoundedEnum. Like the enumeration tests above, this validates the kernel COMPOSITION on the
// standard placeholder simp stack (no bundle installed): proveBoundedExists finds
// the witness, instantiates the per-value body through the arith decider, and
// ∃-introduces, with hyps drawn only from the inputs. RingProveFull's normal-form
// self-check means only the GENUINELY-satisfying value closes even on placeholders
// (a wrong value's `v·v = c` has mismatched normal forms and is rejected), so the
// search logic is exercised for real. End-to-end soundness against the real corpus
// bundle would be a corpus/engine test once the move is exposed.

// existsNum builds `∃i. body` over a fresh num-typed bound var, returning the
// existential goal and the bound var (so the test can build the body with it).
func existsNum(name string, mkBody func(i Term) Term) Term {
	i := ext.Var(ext.TermName(name), dsl.NumType)
	return prop.Exists(i)(mkBody(i))
}

func TestProveBoundedExists(t *testing.T) {
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	// ∃i. i < 3 ∧ i·i = 4 : witness i=2 (0·0=0, 1·1=1 are rejected by ring's
	// normal-form check; only 2·2=4 closes). Nonlinear body — the witness-side
	// analogue of proveBoundedEnum's n·n ≤ 4.
	goal := existsNum("i", func(i Term) Term {
		return and(lt(i, Numeral(3)), eqT(star(i, i), Numeral(4)))
	})
	w, ok := proveBoundedExists(nil, goal)
	if !ok {
		t.Fatal("proveBoundedExists did not close ⊢ ∃i. i<3 ∧ i·i=4 (witness 2)")
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("conclusion = %v, want %v", w.Conclusion(), goal)
	}
	if w.NumHyps() != 0 {
		t.Errorf("expected no hypotheses, got %d", w.NumHyps())
	}

	// Hyp-subset contract: a body that needs a hypothesis. n≥10 ⊢ ∃i. i<3 ∧ n+i = n+2
	// — witness i=2; the body `n+2 = n+2` closes by ring, the n≥10 hyp is irrelevant
	// but the returned proof's hyps must be ⊆ inputs.
	n := numVar("n")
	hyps := []Term{le(Numeral(10), n)}
	goal2 := existsNum("i", func(i Term) Term {
		return and(lt(i, Numeral(3)), eqT(plus(n, i), plus(n, Numeral(2))))
	})
	w2, ok := proveBoundedExists(hyps, goal2)
	if !ok {
		t.Fatal("proveBoundedExists did not close {10≤n} ⊢ ∃i. i<3 ∧ n+i = n+2")
	}
	for i := 0; i < w2.NumHyps(); i++ {
		if !slices.ContainsFunc(hyps, w2.Hyp(i).AlphaEquals) {
			t.Errorf("stray hypothesis %v not among inputs", w2.Hyp(i))
		}
	}

	// `≤` bound and a left-literal `c > i` bound both drive the range.
	if _, ok := proveBoundedExists(nil, existsNum("i", func(i Term) Term {
		return and(le(i, Numeral(4)), eqT(star(i, i), Numeral(9))) // i≤4, witness 3
	})); !ok {
		t.Error("proveBoundedExists did not close ∃i. i≤4 ∧ i·i=9 (witness 3)")
	}
	if _, ok := proveBoundedExists(nil, existsNum("i", func(i Term) Term {
		return and(gt(Numeral(5), i), eqT(star(i, i), Numeral(16))) // 5>i, witness 4
	})); !ok {
		t.Error("proveBoundedExists did not close ∃i. 5>i ∧ i·i=16 (witness 4)")
	}

	// Nested bounded ∃: ∃i. i<3 ∧ ∃j. j<3 ∧ i+j = 3 — witness i=1 (then j=2), via
	// the recursive proveExistsBody. (i=0 needs j=3 ∉ range; i=1 finds j=2.)
	if _, ok := proveBoundedExists(nil, existsNum("i", func(i Term) Term {
		return and(lt(i, Numeral(3)), existsNum("j", func(j Term) Term {
			return and(lt(j, Numeral(3)), eqT(plus(i, j), Numeral(3)))
		}))
	})); !ok {
		t.Error("proveBoundedExists did not close the nested ∃i.∃j bounded goal")
	}

	// NEGATIVE: no witness in range. ∃i. i<3 ∧ i·i = 9 — needs i=3, out of {0,1,2}.
	if _, ok := proveBoundedExists(nil, existsNum("i", func(i Term) Term {
		return and(lt(i, Numeral(3)), eqT(star(i, i), Numeral(9)))
	})); ok {
		t.Error("proveBoundedExists wrongly closed ∃i. i<3 ∧ i·i=9 (witness 3 is out of range)")
	}

	// NEGATIVE: no literal bound conjunct on the ∃-var ⇒ declines (not a bounded ∃).
	if _, ok := proveBoundedExists(nil, existsNum("i", func(i Term) Term {
		return eqT(star(i, i), Numeral(4))
	})); ok {
		t.Error("proveBoundedExists fired on an unbounded ∃ (no range conjunct)")
	}

	// NEGATIVE: not an existential at all ⇒ declines.
	if _, ok := proveBoundedExists(nil, eqT(star(n, n), Numeral(4))); ok {
		t.Error("proveBoundedExists fired on a non-∃ goal")
	}
}
