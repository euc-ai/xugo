package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Pure (bundle-free) unit coverage for the subtraction layer's untrusted model:
// the MatchesMinus matcher, the linSub componentwise classifier and
// monusReducible. The proof-producing leaves (subCancel/subTrunc/the case
// split) are exercised end-to-end against the real corpus bundle in
// library/serve (TestInstallNatBundleBindingSub).

func TestMatchesMinus(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	if l, r, ok := MatchesMinus(tn("a - b")); !ok || !l.AlphaEquals(a) || !r.AlphaEquals(b) {
		t.Errorf("MatchesMinus(a-b) = (%v,%v,%v)", l, r, ok)
	}
	if _, _, ok := MatchesMinus(tn("a + b")); ok {
		t.Error("MatchesMinus matched a+b")
	}
}

func TestMatchesMaxMin(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	if l, r, ok := MatchesMax(tn("nat_max(a, b)")); !ok || !l.AlphaEquals(a) || !r.AlphaEquals(b) {
		t.Errorf("MatchesMax(nat_max(a,b)) = (%v,%v,%v)", l, r, ok)
	}
	if l, r, ok := MatchesMin(tn("nat_min(a, b)")); !ok || !l.AlphaEquals(a) || !r.AlphaEquals(b) {
		t.Errorf("MatchesMin(nat_min(a,b)) = (%v,%v,%v)", l, r, ok)
	}
	if _, _, ok := MatchesMax(tn("nat_min(a, b)")); ok {
		t.Error("MatchesMax matched nat_min")
	}
}

// TestPreBridge guards the predecessor→(n-1) derivation against the stated Sub
// shape — per-conjunct ∀ and reversed orientation `(∀m. m-0=m) ∧
// (∀m n. m-suc n=predecessor(m-n))` (an earlier version assumed top-level ∀ + the
// opposite orientation and silently produced nil against the real corpus).
func TestPreBridge(t *testing.T) {
	m, k := numVar("m"), numVar("k")
	c1 := ext.ForAll(m)(eqT(minus(m, natZero), m))                    // ∀m. (m-0) = m
	c2 := ext.ForAll(m, k)(eqT(minus(m, sucT(k)), preT(minus(m, k)))) // ∀m k. (m-suc k) = predecessor(m-k)
	SetNatLemmaBundle(&NatLemmaBundle{Sub: prop.WrapProp(core.TestThm(and(c1, c2)))})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	a := numVar("a")
	w := preBridge(a)
	if w == nil {
		t.Fatal("preBridge returned nil against the real Sub shape")
	}
	if want := eqT(preT(a), minus(a, Numeral(1))); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("preBridge(a):\n  got  %v\n  want %v", w.Conclusion(), want)
	}
	if x, ok := MatchesPre(preT(a)); !ok || !x.AlphaEquals(a) {
		t.Errorf("MatchesPre(predecessor a) = (%v, %v)", x, ok)
	}
}

// linSub: x − y succeeds iff x ≥ y componentwise (the num-representable case).
func TestLinSub(t *testing.T) {
	mp := func(s string) linForm { return mpolyOf(tn(s)) }
	cases := []struct {
		x, y   string
		ok     bool
		result string // expected toTerm() of the difference, when ok
	}{
		{"a + b", "a", true, "b"},         // (a+b)-a = b
		{"a + b + c", "a", true, "b + c"}, // compositional
		{"a", "a", true, "0"},             // a-a = 0
		{"a", "0", true, "a"},             // a-0 = a
		{"5", "3", true, "2"},             // numeric
		{"a", "b", false, ""},             // incomparable (mixed sign)
		{"a", "a + b", false, ""},         // y dominates → not representable
		{"2 * a", "a", true, "a"},         // 2a - a = a
		{"a", "2 * a", false, ""},         // a - 2a not representable
	}
	for _, c := range cases {
		d, ok := linSub(mp(c.x), mp(c.y))
		if ok != c.ok {
			t.Errorf("linSub(%s, %s) ok = %v, want %v", c.x, c.y, ok, c.ok)
			continue
		}
		if ok && !d.toTerm().AlphaEquals(mp(c.result).toTerm()) {
			t.Errorf("linSub(%s, %s) = %v, want %s", c.x, c.y, d.toTerm(), c.result)
		}
	}
}

// monusReducible: true exactly when one operand dominates (subCancel/subTrunc can
// rewrite it); false for a genuinely mixed-sign monus (needs the case split).
func TestMonusReducible(t *testing.T) {
	cases := []struct {
		a, b string
		want bool
	}{
		{"a + b", "a", true},  // cancellation
		{"a", "a + b", true},  // truncation
		{"a", "a", true},      // degenerate → 0
		{"a", "b", false},     // mixed
		{"2 * a", "b", false}, // mixed
	}
	for _, c := range cases {
		if got := monusReducible(tn(c.a), tn(c.b)); got != c.want {
			t.Errorf("monusReducible(%s, %s) = %v, want %v", c.a, c.b, got, c.want)
		}
	}
}

// collectSplitCandidates finds the distinct splittable subterms (monus/nat_max/nat_min),
// including nested ones, and dedups α-equal occurrences.
func TestCollectSplitCandidates(t *testing.T) {
	// `(a - b) + (a - b) + nat_max(c, a)` — two distinct candidates (one monus, one nat_max).
	got := collectSplitCandidates([]Term{tn("(a - b) + (a - b) + nat_max(c, a)")})
	if len(got) != 2 {
		t.Fatalf("collectSplitCandidates found %d, want 2: %v", len(got), got)
	}
	// A term with no splittable operator yields none.
	if got := collectSplitCandidates([]Term{tn("a + b * c")}); len(got) != 0 {
		t.Errorf("collectSplitCandidates(a+b*c) = %v, want empty", got)
	}
}

// ── Split-engine clients: hypothesis splits, nat_max / nat_min, raw COND ──────

// negComparison maps a `<`/`≤` guard to its complementary positive comparison +
// the `{¬guard} ⊢ negPos` bridge; ok=false for any other shape.
func TestNegComparison(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	if neg, _, ok := negComparison(le(a, b)); !ok || !neg.AlphaEquals(lt(b, a)) {
		t.Errorf("negComparison(a≤b) = (%v, _, %v), want (b<a, _, true)", neg, ok)
	}
	if neg, _, ok := negComparison(lt(a, b)); !ok || !neg.AlphaEquals(le(b, a)) {
		t.Errorf("negComparison(a<b) = (%v, _, %v), want (b≤a, _, true)", neg, ok)
	}
	if _, _, ok := negComparison(eqT(a, b)); ok {
		t.Error("negComparison(a=b) should decline (not a < / ≤)")
	}
}

// isSplitCandidate / collectSplitCandidates now also recognize a num-typed COND.
func TestCondSplitCandidate(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	cNum := ext.Cond(le(a, b), b, a) // COND(a≤b, b, a) : num
	if !isSplitCandidate(cNum) {
		t.Error("isSplitCandidate declined a num COND")
	}
	// A bool-typed COND (branches are props) is NOT an arith split candidate.
	cBool := ext.Cond(le(a, b), le(a, b), le(b, a))
	if isSplitCandidate(cBool) {
		t.Error("isSplitCandidate matched a bool COND")
	}
}

// hypSplittable on a disjunction hyp: branches guarded by each disjunct, disjProof
// is the hyp itself (Assume) — no lemma, so this works bundle-free.
func TestHypSplittableDisj(t *testing.T) {
	a := numVar("a")
	h := or(eqT(a, Numeral(1)), eqT(a, Numeral(2))) // (a=1) ∨ (a=2)
	sa, ok := hypSplittable(h)
	if !ok {
		t.Fatal("hypSplittable declined a disjunction hyp")
	}
	if !sa.atom.AlphaEquals(h) {
		t.Errorf("atom = %v, want %v", sa.atom, h)
	}
	if !sa.disjProof.Conclusion().AlphaEquals(h) {
		t.Errorf("disjProof concl = %v, want %v", sa.disjProof.Conclusion(), h)
	}
	if !sa.branches[0].guard.AlphaEquals(eqT(a, Numeral(1))) ||
		!sa.branches[1].guard.AlphaEquals(eqT(a, Numeral(2))) {
		t.Errorf("branch guards = (%v, %v)", sa.branches[0].guard, sa.branches[1].guard)
	}
	// A non-disjunctive, non-≠ hyp declines.
	if _, ok := hypSplittable(le(a, Numeral(1))); ok {
		t.Error("hypSplittable matched a plain comparison hyp")
	}
}

// trichotomyNeq derives `{¬(a=b)} ⊢ (a<b) ∨ (b<a)` from LessThanTrichotomy, and the ≠ hyp
// kind builds the matching split. Guards the LEFT-associated LessThanTrichotomy shape
// `((a<b) ∨ (b<a)) ∨ (a=b)` (the normalized form) + graceful nil
// when LessThanTrichotomy is unbundled.
func TestTrichotomyNeq(t *testing.T) {
	if trichotomyNeq(numVar("a"), numVar("b")) != nil {
		t.Fatal("trichotomyNeq should be nil with no bundle (LessThanTrichotomy unbundled)")
	}
	a, b := numVar("a"), numVar("b")
	ltc := ext.ForAll(a, b)(or(or(lt(a, b), lt(b, a)), eqT(a, b))) // ∀a b. ((a<b)∨(b<a))∨(a=b)
	SetNatLemmaBundle(&NatLemmaBundle{LessThanTrichotomy: prop.WrapProp(core.TestThm(ltc))})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	w := trichotomyNeq(a, b)
	if w == nil {
		t.Fatal("trichotomyNeq returned nil against the real LessThanTrichotomy shape")
	}
	if want := or(lt(a, b), lt(b, a)); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("trichotomyNeq concl = %v, want %v", w.Conclusion(), want)
	}
	if !w.HasHyp(not(eqT(a, b))) {
		t.Errorf("trichotomyNeq must carry the ¬(a=b) hyp; hyps = %v", w.Conclusion())
	}
	// The ≠-hyp kind wires it into a split on a<b / b<a.
	sa, ok := hypSplittable(not(eqT(a, b)))
	if !ok {
		t.Fatal("hypSplittable declined a ≠ hyp with LessThanTrichotomy bundled")
	}
	if !sa.branches[0].guard.AlphaEquals(lt(a, b)) || !sa.branches[1].guard.AlphaEquals(lt(b, a)) {
		t.Errorf("≠ split guards = (%v, %v), want (a<b, b<a)", sa.branches[0].guard, sa.branches[1].guard)
	}
}

// ── Parity bridge (nat_sub.go) ─────────────────────────────────────────────

// evenBridge/oddBridge rewrite nat_even/nat_odd to their nat_mod-2 forms; parityBridge
// dispatches. evenBridge is EvenIffModTwoZero direct; oddBridge composes OddIffNotEven with
// EvenIffModTwoZero to the ¬-form. Guarded against the bundle TestThm shapes.
func TestParityBridge(t *testing.T) {
	n := numVar("n")
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	evenIffModTwoZero := ext.ForAll(n)(eqT(evenT(n), eqT(natZero, modT(n, Numeral(2))))) // ∀n. nat_even n ⇔ (0 = nat_mod(n, 2))
	oddIffNotEven := ext.ForAll(n)(eqT(oddT(n), not(evenT(n))))                          // ∀n. nat_odd n ⇔ ¬nat_even n
	SetNatLemmaBundle(&NatLemmaBundle{EvenIffModTwoZero: mk(evenIffModTwoZero), OddIffNotEven: mk(oddIffNotEven)})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	zeroMod := eqT(natZero, modT(n, Numeral(2)))
	if w := evenBridge(n); w == nil || !w.Conclusion().AlphaEquals(eqT(evenT(n), zeroMod)) {
		t.Errorf("evenBridge(n) = %v, want nat_even n ⇔ (0 = nat_mod(n, 2))", w)
	}
	if w := oddBridge(n); w == nil || !w.Conclusion().AlphaEquals(eqT(oddT(n), not(zeroMod))) {
		t.Errorf("oddBridge(n) = %v, want nat_odd n ⇔ ¬(0 = nat_mod(n, 2))", w)
	}
	if parityBridge(evenT(n)) == nil || parityBridge(oddT(n)) == nil {
		t.Error("parityBridge declined a nat_even/nat_odd atom")
	}
	if parityBridge(le(n, Numeral(2))) != nil {
		t.Error("parityBridge matched a non-parity atom")
	}
	// MatchesEven/MatchesOdd round-trip.
	if x, ok := MatchesEven(evenT(n)); !ok || !x.AlphaEquals(n) {
		t.Errorf("MatchesEven(nat_even n) = (%v, %v)", x, ok)
	}
	if x, ok := MatchesOdd(oddT(n)); !ok || !x.AlphaEquals(n) {
		t.Errorf("MatchesOdd(nat_odd n) = (%v, %v)", x, ok)
	}
}

// TestEvenStructural pins the nonlinear-parity decomposition shapes (EvenMul /
// EvenAdd), the route a parity over a product/sum takes BEFORE the nat_mod-2 bridge.
// End-to-end closure of `nat_even(n·n) ⇔ nat_even n` etc. is in library/serve
// (TestInstallNatBundleBindingParity).
func TestEvenStructural(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	x, y := numVar("x"), numVar("y")
	SetNatLemmaBundle(&NatLemmaBundle{
		EvenMul:       mk(ext.ForAll(x, y)(eqT(evenT(star(x, y)), or(evenT(x), evenT(y))))),
		EvenAdd:       mk(ext.ForAll(x, y)(eqT(evenT(plus(x, y)), eqT(evenT(x), evenT(y))))),
		OddIffNotEven: mk(ext.ForAll(x)(eqT(oddT(x), not(evenT(x))))),
	})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	// nat_even(a·b) ⇔ nat_even a ∨ nat_even b   [EvenMul]
	if w := parityBridge(evenT(star(a, b))); w == nil ||
		!w.Conclusion().AlphaEquals(eqT(evenT(star(a, b)), or(evenT(a), evenT(b)))) {
		t.Errorf("nat_even(a·b) structural = %v", w)
	}
	// nat_even(a+b) ⇔ (nat_even a ⇔ nat_even b)   [EvenAdd]
	if w := parityBridge(evenT(plus(a, b))); w == nil ||
		!w.Conclusion().AlphaEquals(eqT(evenT(plus(a, b)), eqT(evenT(a), evenT(b)))) {
		t.Errorf("nat_even(a+b) structural = %v", w)
	}
	// nat_odd(a·b) ⇔ ¬(nat_even a ∨ nat_even b)   [via OddIffNotEven]
	if w := parityBridge(oddT(star(a, b))); w == nil ||
		!w.Conclusion().AlphaEquals(eqT(oddT(star(a, b)), not(or(evenT(a), evenT(b))))) {
		t.Errorf("nat_odd(a·b) structural = %v", w)
	}
	// evenStructural declines a bare variable (no product/sum) — falls to nat_mod-2.
	if w := evenStructural(a); w != nil {
		t.Errorf("evenStructural(a) should decline a bare var, got %v", w)
	}
}

// TestMatchesDistLiteralPairOnly guards MatchesDist's comma-constructor check:
// dist's type only pins its argument to prod(num,num), so any two-level
// application chain of that type reaches the matcher. Before the check, a free
// `pair : num→num→prod` variable applied to (m, n) was mis-decomposed as a
// literal pair; distBridge then instantiated Dist at (m, n) — an equation
// about the DIFFERENT term `nat_dist(,(m,n))` — and the deep rewrite produced a
// witness whose LHS was not the goal's conclusion, tripping makeSubGoalsAt's
// IsStronger assert as a "Should not happen." panic (via inspect / auto /
// CloseByAuto on any goal whose conclusion carried the non-literal-pair dist).
func TestMatchesDistLiteralPairOnly(t *testing.T) {
	m, n := numVar("m"), numVar("n")
	pairNN := ext.MakeProdType(ext.NumType, ext.NumType)

	// Literal pair: nat_dist(,(m, n)) — matches.
	commaNN := ext.Const(ext.CommaConstMeta,
		ext.MakeFun(ext.NumType, ext.MakeFun(ext.NumType, pairNN)))
	distLit := ext.Apply(natDist, ext.Apply(commaNN, m, n))
	if l, r, ok := MatchesDist(distLit); !ok || !l.AlphaEquals(m) || !r.AlphaEquals(n) {
		t.Errorf("MatchesDist(nat_dist(,(m,n))) = (%v,%v,%v), want (m,n,true)", l, r, ok)
	}

	// Free pair-typed function variable: nat_dist(pair(m, n)) — must DECLINE.
	pairVar := ext.Var("pair", ext.MakeFun(ext.NumType, ext.MakeFun(ext.NumType, pairNN)))
	distVarPair := ext.Apply(natDist, ext.Apply(pairVar, m, n))
	if _, _, ok := MatchesDist(distVarPair); ok {
		t.Error("MatchesDist matched nat_dist(pair(m,n)) with pair a free variable")
	}

	// Bare prod-typed variable: nat_dist(p) — must decline (no application to peel).
	pVar := ext.Var("p", pairNN)
	if _, _, ok := MatchesDist(ext.Apply(natDist, pVar)); ok {
		t.Error("MatchesDist matched nat_dist(p) with p a bare pair variable")
	}
}
