package omega

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

func checkBinop(t *testing.T, name string, l, r Term, want uint64,
	f func(Term, Term) (*prop.PropWrapper, bool)) {
	t.Helper()
	w, ok := f(l, r)
	if !ok {
		t.Fatalf("%s: evaluator declined", name)
	}
	if !prop.Lhs(w).AlphaEquals(applyOp(name, l, r)) {
		t.Errorf("%s: Lhs = %v", name, prop.Lhs(w))
	}
	rhs := prop.Rhs(w)
	gotTree, ok := asNumeral(rhs)
	if !ok {
		t.Fatalf("%s: Rhs not a numeral: %v", name, rhs)
	}
	// Semantic check: value matches.
	got, ok := BitsToUint(gotTree)
	if !ok || got != want {
		t.Errorf("%s: value = %d (ok=%v), want %d", name, got, ok, want)
	}
	// Canonicity check: result is the canonical literal for `want`.
	if !rhs.AlphaEquals(Numeral(want)) {
		t.Errorf("%s: non-canonical result %v, want %v", name, rhs, Numeral(want))
	}
}

func applyOp(name string, l, r Term) Term {
	switch name {
	case "mul":
		return star(l, r)
	case "exp":
		return expT(l, r)
	}
	return plus(l, r)
}

func TestNormNatAddRange(t *testing.T) {
	for i := uint64(0); i <= 40; i++ {
		for j := uint64(0); j <= 40; j++ {
			checkBinop(t, "add", Numeral(i), Numeral(j), i+j, NormNatAdd)
		}
	}
}

func TestNormNatMulRange(t *testing.T) {
	for i := uint64(0); i <= 30; i++ {
		for j := uint64(0); j <= 30; j++ {
			checkBinop(t, "mul", Numeral(i), Numeral(j), i*j, NormNatMul)
		}
	}
}

func TestNormNatCarryHeavy(t *testing.T) {
	// Powers-of-two boundaries and all-ones exercise the suc carry cascade.
	cases := []struct{ a, b uint64 }{
		{255, 1}, {1, 255}, {255, 255}, {256, 256},
		{1023, 1}, {65535, 1}, {12345, 67890}, {0, 0},
	}
	for _, c := range cases {
		checkBinop(t, "add", Numeral(c.a), Numeral(c.b), c.a+c.b, NormNatAdd)
	}
	for _, c := range cases {
		checkBinop(t, "mul", Numeral(c.a), Numeral(c.b), c.a*c.b, NormNatMul)
	}
}

func TestNormNatDeclinesNonLiteral(t *testing.T) {
	if _, ok := NormNatAdd(tn("a"), tn("3")); ok {
		t.Error("NormNatAdd accepted a non-literal operand")
	}
	if _, ok := NormNatMul(tn("3"), tn("a")); ok {
		t.Error("NormNatMul accepted a non-literal operand")
	}
	if _, ok := NormNatExp(tn("a"), Numeral(3)); ok {
		t.Error("NormNatExp accepted a non-literal base")
	}
	if _, ok := NormNatExp(Numeral(3), tn("a")); ok {
		t.Error("NormNatExp accepted a non-literal exponent")
	}
}

// NormNatExp pinned end-to-end against Go's math: literal m^n folds to a
// single literal via expUnfold + the literal product-chain fold. Soundness
// rides on both pieces — expUnfold proves the chain via nat_pow-recursion, the
// fold via NormNatMul + congruence. The expUnfoldMax cap (= 32) bounds the
// exponent we exercise here. Needs the nat_pow bundle (and NumeralSuc for sucBits)
// — installExpTestBundle fabricates the placeholder leaves.
func TestNormNatExpRange(t *testing.T) {
	defer installExpTestBundle(t, true)()
	// Modest range: each (m,n) costs ~n NormNatMul calls. Keep m·n small.
	cases := []struct{ m, n uint64 }{
		{0, 0}, {0, 1}, {0, 5}, // 0^n
		{1, 0}, {1, 1}, {1, 10}, // 1^n
		{2, 0}, {2, 1}, {2, 2}, {2, 3}, {2, 10}, // powers of two
		{3, 0}, {3, 1}, {3, 4}, {3, 5}, // 3^k
		{5, 3}, {7, 2}, {10, 3}, {12, 2}, // misc
	}
	for _, c := range cases {
		var want uint64 = 1
		for i := uint64(0); i < c.n; i++ {
			want *= c.m
		}
		checkBinop(t, "exp", Numeral(c.m), Numeral(c.n), want, NormNatExp)
	}
}

// Validates the comparison recursion against Go's </<=/==. Base equivalences are
// TestThm placeholders, but the ⊤/⊥ verdict is produced entirely by the
// recursive descent (and EqTrans enforces every intermediate ⇔ lines up), so a
// mis-structured reduction yields the wrong leaf and fails the cross-check.

func wantBool(b bool) Term {
	if b {
		return prop.T
	}
	return prop.F
}

func checkCmp(t *testing.T, name string, l, r, goal Term, want bool,
	f func(Term, Term) (*prop.PropWrapper, bool)) {
	t.Helper()
	w, ok := f(l, r)
	if !ok {
		t.Fatalf("%s: evaluator declined", name)
	}
	if !prop.Lhs(w).AlphaEquals(goal) {
		t.Errorf("%s: Lhs = %v, want %v", name, prop.Lhs(w), goal)
	}
	if !prop.Rhs(w).AlphaEquals(wantBool(want)) {
		t.Errorf("%s(%v): verdict = %v, want %v", name, goal, prop.Rhs(w), wantBool(want))
	}
}

func TestNormNatCmpRange(t *testing.T) {
	const N = 36
	for i := uint64(0); i <= N; i++ {
		for j := uint64(0); j <= N; j++ {
			li, lj := Numeral(i), Numeral(j)
			checkCmp(t, "lt", li, lj, lt(li, lj), i < j, NormNatLt)
			checkCmp(t, "le", li, lj, le(li, lj), i <= j, NormNatLe)
			checkCmp(t, "eq", li, lj, eqT(li, lj), i == j, NormNatEq)
		}
	}
}

func TestNormNatCmpBoundaries(t *testing.T) {
	cases := []struct{ a, b uint64 }{
		{0, 0}, {0, 1}, {1, 0}, {255, 256}, {256, 255}, {256, 256},
		{1023, 1024}, {65535, 65536}, {12345, 12345}, {12345, 12346},
	}
	for _, c := range cases {
		la, lb := Numeral(c.a), Numeral(c.b)
		checkCmp(t, "lt", la, lb, lt(la, lb), c.a < c.b, NormNatLt)
		checkCmp(t, "le", la, lb, le(la, lb), c.a <= c.b, NormNatLe)
		checkCmp(t, "eq", la, lb, eqT(la, lb), c.a == c.b, NormNatEq)
	}
}

func TestNormNatCmpDeclinesNonLiteral(t *testing.T) {
	if _, ok := NormNatLt(tn("a"), tn("3")); ok {
		t.Error("NormNatLt accepted a non-literal operand")
	}
	if _, ok := NormNatEq(tn("3"), tn("a")); ok {
		t.Error("NormNatEq accepted a non-literal operand")
	}
}

// >, ≥, ≠ cross-checked against Go, same scheme as the primitive comparisons.
// The ≠ goal is ¬(l = r) (≠ has no const — it is notation for ¬(=)).

func TestNormNatDerivedCmpRange(t *testing.T) {
	const N = 36
	for i := uint64(0); i <= N; i++ {
		for j := uint64(0); j <= N; j++ {
			li, lj := Numeral(i), Numeral(j)
			checkCmp(t, "gt", li, lj, gt(li, lj), i > j, NormNatGt)
			checkCmp(t, "ge", li, lj, ge(li, lj), i >= j, NormNatGe)
			checkCmp(t, "ne", li, lj, prop.Not(eqT(li, lj)), i != j, NormNatNe)
		}
	}
}

func TestNormNatDerivedCmpBoundaries(t *testing.T) {
	cases := []struct{ a, b uint64 }{
		{0, 0}, {0, 1}, {1, 0}, {255, 256}, {256, 255}, {256, 256},
		{65535, 65536}, {12345, 12345}, {12345, 12346},
	}
	for _, c := range cases {
		la, lb := Numeral(c.a), Numeral(c.b)
		checkCmp(t, "gt", la, lb, gt(la, lb), c.a > c.b, NormNatGt)
		checkCmp(t, "ge", la, lb, ge(la, lb), c.a >= c.b, NormNatGe)
		checkCmp(t, "ne", la, lb, prop.Not(eqT(la, lb)), c.a != c.b, NormNatNe)
	}
}

func TestNormNatDerivedCmpDeclinesNonLiteral(t *testing.T) {
	if _, ok := NormNatGt(tn("a"), tn("3")); ok {
		t.Error("NormNatGt accepted a non-literal operand")
	}
	if _, ok := NormNatNe(tn("3"), tn("a")); ok {
		t.Error("NormNatNe accepted a non-literal operand")
	}
}

// Real norm_num bridge tests. The evaluators must lift the num
// verdict through the real_of_num bridge and land the exact
// `⊢ &m ⋆ &n = &k` / `⊢ (&m ⋈ &n) ⇔ ⊤/⊥` statement — first in placeholder mode
// (no real bundle: the bridge leaf is a TestThm, the composition around it is
// real), then with a TestThm-backed RealLemmaBundle stated in the normal-form
// orientation (reversed relative to the bridge direction), which exercises
// eqLeaf's instantiate-and-flip against the shapes the bundle actually binds.

// checkRealNormEval runs one evaluator case and checks conclusion shape.
func checkRealNormEval(t *testing.T, name string, w *prop.PropWrapper, ok bool, want Term) {
	t.Helper()
	if !ok {
		t.Fatalf("%s: ok=false, want a proof", name)
	}
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("%s: got\n  %v\nwant\n  %v", name, w.Conclusion(), want)
	}
}

func runRealNormNumCases(t *testing.T) {
	t.Helper()
	cases := []struct {
		name string
		run  func() (*prop.PropWrapper, bool)
		want Term
	}{
		{"add 3+4", func() (*prop.PropWrapper, bool) { return realNormNatAdd(rr("&3"), rr("&4")) },
			eqT(rr("&3 + &4"), rr("&7"))},
		{"add 0+5", func() (*prop.PropWrapper, bool) { return realNormNatAdd(rr("&0"), rr("&5")) },
			eqT(rr("&0 + &5"), rr("&5"))},
		{"mul 3*4", func() (*prop.PropWrapper, bool) { return realNormNatMul(rr("&3"), rr("&4")) },
			eqT(rr("&3 * &4"), rr("&12"))},
		{"mul 0*5", func() (*prop.PropWrapper, bool) { return realNormNatMul(rr("&0"), rr("&5")) },
			eqT(rr("&0 * &5"), rr("&0"))},
		{"lt 3<4 ⊤", func() (*prop.PropWrapper, bool) { return realNormNatLt(rr("&3"), rr("&4")) },
			eqT(rb("&3 < &4"), prop.T)},
		{"lt 4<3 ⊥", func() (*prop.PropWrapper, bool) { return realNormNatLt(rr("&4"), rr("&3")) },
			eqT(rb("&4 < &3"), prop.F)},
		{"lt 3<3 ⊥", func() (*prop.PropWrapper, bool) { return realNormNatLt(rr("&3"), rr("&3")) },
			eqT(rb("&3 < &3"), prop.F)},
		{"le 3≤3 ⊤", func() (*prop.PropWrapper, bool) { return realNormNatLe(rr("&3"), rr("&3")) },
			eqT(rb("&3 <= &3"), prop.T)},
		{"le 4≤3 ⊥", func() (*prop.PropWrapper, bool) { return realNormNatLe(rr("&4"), rr("&3")) },
			eqT(rb("&4 <= &3"), prop.F)},
		{"eq 4=4 ⊤", func() (*prop.PropWrapper, bool) { return realNormNatEq(rr("&4"), rr("&4")) },
			eqT(eqT(rr("&4"), rr("&4")), prop.T)},
		{"eq 3=4 ⊥", func() (*prop.PropWrapper, bool) { return realNormNatEq(rr("&3"), rr("&4")) },
			eqT(eqT(rr("&3"), rr("&4")), prop.F)},
	}
	for _, c := range cases {
		w, ok := c.run()
		checkRealNormEval(t, c.name, w, ok, c.want)
	}
}
