package omega

import (
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

// Abstract-layer tests: validate linOf/linAdd/linScale/toTerm semantically by
// cross-checking against a direct evaluator over concrete atom assignments.
// No proofs here — this pins the algorithm before the proof layer is added.

func evalLin(lf linForm, env func(Term) uint64) uint64 {
	s := word(lf.konst)
	for _, m := range lf.monos {
		s += word(m.coeff) * env(m.atom)
	}
	return s
}

func evalExpr(t Term, env func(Term) uint64) (uint64, bool) {
	if x, ok := asNumeral(t); ok {
		return BitsToUint(x)
	}
	if l, r, ok := MatchesPlus(t); ok {
		a, o1 := evalExpr(l, env)
		b, o2 := evalExpr(r, env)
		return a + b, o1 && o2
	}
	if l, r, ok := MatchesStar(t); ok {
		a, o1 := evalExpr(l, env)
		b, o2 := evalExpr(r, env)
		return a * b, o1 && o2
	}
	return env(t), true
}

// envOf maps known atoms a,b,c to values; others panic (test bug).
func envOf(a, b, c Term, va, vb, vc uint64) func(Term) uint64 {
	return func(x Term) uint64 {
		switch {
		case x.AlphaEquals(a):
			return va
		case x.AlphaEquals(b):
			return vb
		case x.AlphaEquals(c):
			return vc
		}
		panic("unknown atom")
	}
}

func TestLinOfSemantics(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")

	exprs := []Term{
		tn("a"),
		tn("a + b"),
		tn("(a + b) + c"),
		tn("a + a"),                   // like-term
		tn("3 * a"),                   // scalar
		tn("a * 3"),                   // scalar on right
		tn("2 * a + 3 * a"),           // 2a+3a = 5a
		tn("2 * (a + b)"),             // distribute: 2a+2b
		tn("2 * (a + b) + 7"),         // 2a+2b+7
		tn("2 * (3 * a)"),             // 6a
		tn("5 + 7"),                   // constants
		tn("2 * a + (3 * b + 4 * a)"), // 6a+3b
	}

	assigns := []struct{ va, vb, vc uint64 }{
		{0, 0, 0}, {1, 2, 3}, {7, 0, 5}, {10, 20, 30}, {255, 1, 2},
	}
	for _, e := range exprs {
		lf, ok := linOf(e)
		if !ok {
			t.Fatalf("linOf declined %v", e)
		}
		// Canonical term round-trips to the same form.
		lf2, ok := linOf(lf.toTerm())
		if !ok || evalLinNeq(lf, lf2) {
			t.Errorf("toTerm not idempotent for %v", e)
		}
		for _, as := range assigns {
			env := envOf(a, b, c, as.va, as.vb, as.vc)
			want, _ := evalExpr(e, env)
			if got := evalLin(lf, env); got != want {
				t.Errorf("%v @ %v: linForm=%d want %d", e, as, got, want)
			}
		}
	}
}

func evalLinNeq(x, y linForm) bool { return !sameLinForm(x, y) }

// TestLinOfExpandsNonlinear: linOf does not fold a nonlinear product into one
// opaque spelling-keyed atom — it distributes it over canonical monomial atoms
// (domain.go polyMul), the full ring's normal form (mpolyOf agreement pinned
// below). This is what lets linarith combine polynomial facts across different
// spellings: `a·b` and `b·a` are the SAME unknown. genuinelyLinear still
// distinguishes any
// monomial-carrying form from a true linear form.
func TestLinOfExpandsNonlinear(t *testing.T) {
	for _, s := range []string{
		"a * b",
		"(a + b) * a",
		"b * a",             // commuted spelling, same basis
		"a * suc(a)",        // suc folds inside the product: a² + a
		"(a + 1) * (b + 2)", // konst cross terms: ab + 2a + b + 2
		"(a * b) * c",       // nested product flattens to one sorted monomial
	} {
		lf, ok := linOf(tn(s))
		if !ok {
			t.Errorf("linOf(%q) rejected; want monomial expansion", s)
			continue
		}
		if evalLinNeq(lf, mpolyOf(tn(s))) {
			t.Errorf("linOf(%q) = %+v disagrees with mpolyOf", s, lf)
		}
		if genuinelyLinear(tn(s)) {
			t.Errorf("genuinelyLinear(%q) = true; want false (monomial atom)", s)
		}
	}
	// The commuted spellings land on the identical canonical form.
	ab, _ := linOf(tn("a * b"))
	ba, _ := linOf(tn("b * a"))
	if !ab.toTerm().AlphaEquals(ba.toTerm()) {
		t.Errorf("a*b and b*a extract to different forms: %v vs %v", ab.toTerm(), ba.toTerm())
	}
}

// evalMPoly evaluates a multivariate linForm: konst + Σ coeff·(monomial product),
// where each monomial atom is a `*`-chain of base atoms evaluated via evalExpr.
func evalMPoly(lf linForm, env func(Term) uint64) uint64 {
	s := word(lf.konst)
	for _, m := range lf.monos {
		v, _ := evalExpr(m.atom, env)
		s += word(m.coeff) * v
	}
	return s
}

func TestMpolyOfSemantics(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")

	exprs := []Term{
		tn("a * b"),
		tn("a * a"),                     // power a²
		tn("(a + b) * (c + a)"),         // (a+b)(c+a)
		tn("(a + 1) * (b + 1)"),         // ab+a+b+1
		tn("2 * (a * b)"),               // 2ab
		tn("(a + b) * (a + b)"),         // a²+2ab+b²
		tn("a * (b + c)"),               // ab+ac
		tn("(a + b) * c"),               // ac+bc
		tn("3 * (a * b) + 2 * (b * a)"), // 3ab+2ba=5ab
		tn("(a * b) * c"),               // abc
		tn("a * b + a * c"),             // distributed form equal to a(b+c)
	}
	assigns := []struct{ va, vb, vc uint64 }{
		{0, 0, 0}, {1, 2, 3}, {5, 0, 2}, {4, 7, 1}, {10, 10, 10},
	}
	for _, e := range exprs {
		lf := mpolyOf(e)
		// idempotence of the canonical term
		lf2 := mpolyOf(lf.toTerm())
		if evalLinNeq(lf, lf2) {
			t.Errorf("toTerm not idempotent for %v", e)
		}
		for _, as := range assigns {
			env := envOf(a, b, c, as.va, as.vb, as.vc)
			want, _ := evalExpr(e, env)
			if got := evalMPoly(lf, env); got != want {
				t.Errorf("%v @ %v: mpoly=%d want %d", e, as, got, want)
			}
		}
	}
}

// Equal polynomials must produce identical canonical forms (the decision basis).
func TestMpolyCanonicalAgreement(t *testing.T) {
	equalPairs := []struct{ l, r Term }{
		{tn("a * b"), tn("b * a")},
		{tn("a * (b + c)"), tn("a * b + a * c")},
		{tn("(a + b) * (a + b)"), tn("(a * a + 2 * (a * b)) + b * b")},
		{tn("(a + 1) * (a + 1)"), tn("(a * a + 2 * a) + 1")},
	}
	for _, p := range equalPairs {
		if evalLinNeq(mpolyOf(p.l), mpolyOf(p.r)) {
			t.Errorf("canonical forms differ for equal polys: %v vs %v", p.l, p.r)
		}
	}
}

// Proof-layer tests. Leaves are placeholders, but the kernel enforces that every
// EqTrans/congruence in normalizeProof lines up (a mis-oriented lemma panics),
// and we assert Lhs = t, Rhs = toTerm(linOf(t)). So this validates the proof
// PLUMBING; the abstract correctness is pinned separately in this file.

func checkNormalize(t *testing.T, e Term) {
	t.Helper()
	lf, w, ok := natRing.normalizeProof(e)
	if !ok {
		t.Fatalf("normalizeProof declined %v", e)
	}
	if !prop.Lhs(w).AlphaEquals(e) {
		t.Errorf("Lhs = %v, want %v", prop.Lhs(w), e)
	}
	if !prop.Rhs(w).AlphaEquals(lf.toTerm()) {
		t.Errorf("Rhs = %v, want toTerm %v", prop.Rhs(w), lf.toTerm())
	}
	// cross-check the form matches the untrusted model
	if ref, _ := linOf(e); evalLinNeq(lf, ref) {
		t.Errorf("normalizeProof form disagrees with linOf for %v", e)
	}
}

// TestNormalizeProofDeclinesNonCanonicalNumeral pins the canonicality gate on
// the literal branch (asLiteral → literalValue, domain.go). A well-formed but
// NON-canonical BIT-tower (bit0(_0)) accepted as a literal with a Refl(t)
// proof would diverge from lf.toTerm(), which rebuilds the canonical
// Numeral(n), and the EqTrans assert in the certificate replay
// (nat_linarith.go) would panic with "Should not happen." (an NumeralEq
// instantiation can manufacture bit0(_0)). The branch declines: shaped, !ok
// — same handling as a ≥2^64 overflow.
func TestNormalizeProofDeclinesNonCanonicalNumeral(t *testing.T) {
	cases := []struct {
		name string
		term Term // ground, well-formed, NON-canonical BIT-tower
	}{
		{"bit0(_0)", bit0(natZero)},
		{"bit1(bit0(_0))", bit1(bit0(natZero))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if _, _, ok := natRing.normalizeProof(tc.term); ok {
				t.Errorf("normalizeProof accepted non-canonical literal %v; must decline (lockstep with linOf)", tc.term)
			}
			if _, ok := linOf(tc.term); ok {
				t.Errorf("linOf accepted non-canonical literal %v; must decline (lockstep with normalizeProof)", tc.term)
			}
			// The always-succeeding pair (mpolyOf / normalizeFull) must also agree:
			// both treat the non-canonical tower as an opaque atom, not a constant.
			mp := mpolyOf(tc.term)
			lf, w := natRing.normalizeFull(tc.term)
			if evalLinNeq(mp, lf) {
				t.Errorf("mpolyOf and normalizeFull disagree on %v: %v vs %v", tc.term, mp, lf)
			}
			if mp.isConst() {
				t.Errorf("mpolyOf read non-canonical %v as a constant; must atomize", tc.term)
			}
			if !lf.toTerm().AlphaEquals(prop.Rhs(w)) {
				t.Errorf("normalizeFull invariant broken on %v: toTerm %v vs proof RHS %v",
					tc.term, lf.toTerm(), prop.Rhs(w))
			}
		})
	}
}

func TestNormalizeProofPlumbing(t *testing.T) {
	exprs := []Term{
		tn("5"),
		tn("a"),
		tn("a + b"),
		tn("b + a"),
		tn("(a + b) + c"),
		tn("a + (b + c)"),
		tn("a + a"),
		tn("2 * a + 3 * a"),
		tn("3 * a"),
		tn("a * 3"),
		tn("2 * (a + b)"),
		tn("2 * (a + b) + 7"),
		tn("2 * (3 * a)"),
		tn("5 + 7"),
		tn("(2 * a + 3 * b) + 4 * a"),
		tn("(a + 3) + (b + 4)"),
		tn("0 * (a + b)"), // scale by 0 → 0
		tn("(c + b) + a"), // reverse order, exercises bubbling
	}
	for _, e := range exprs {
		checkNormalize(t, e)
	}
}

func TestRingProveClosesEqual(t *testing.T) {
	pairs := []struct{ l, r Term }{
		{tn("(a + b) + c"), tn("a + (b + c)")},
		{tn("a + b"), tn("b + a")},
		{tn("2 * (a + b)"), tn("2 * a + 2 * b")},
		{tn("(a + 3) + (b + 4)"), tn("(a + b) + 7")},
		{tn("3 * a + 2 * a"), tn("5 * a")},
		{tn("a"), tn("1 * a + 0")},
		{tn("(a + b) * 3"), tn("3 * a + 3 * b")},
		{tn("(c + b) + a"), tn("(a + b) + c")},
	}
	for _, p := range pairs {
		w, ok := RingProve(p.l, p.r)
		if !ok {
			t.Errorf("RingProve failed to close %v = %v", p.l, p.r)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(p.l) || !prop.Rhs(w).AlphaEquals(p.r) {
			t.Errorf("RingProve(%v,%v): proof is %v = %v", p.l, p.r, prop.Lhs(w), prop.Rhs(w))
		}
	}
}

// Generated coverage: build many distinct linear expressions over {a,b,c} and
// assert (1) normalizeProof closes e to its canonical form, and (2) RingProve
// closes e against that canonical term. Deterministic (no rand).
func TestRingGeneratedExpressions(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")
	atoms := []Term{a, b, c}
	n := func(k uint64) Term { return Numeral(k) }

	var exprs []Term
	// scalar·atom + scalar·atom + const, over all atom/coeff combos
	for i, x := range atoms {
		for j, y := range atoms {
			for _, cx := range []uint64{1, 2, 5} {
				for _, cy := range []uint64{1, 3} {
					for _, k := range []uint64{0, 4} {
						e := plus(plus(star(n(cx), x), star(n(cy), y)), n(k))
						exprs = append(exprs, e)
						_ = i
						_ = j
					}
				}
			}
		}
	}
	// distributed forms: cx·(x+y)
	for _, x := range atoms {
		for _, y := range atoms {
			exprs = append(exprs, star(n(4), plus(x, y)))
			exprs = append(exprs, plus(star(n(2), plus(x, y)), star(n(3), x)))
		}
	}

	for _, e := range exprs {
		checkNormalize(t, e)
		lf, _ := linOf(e)
		w, ok := RingProve(e, lf.toTerm())
		if !ok {
			t.Errorf("RingProve(e, canon(e)) failed for %v", e)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(e) || !prop.Rhs(w).AlphaEquals(lf.toTerm()) {
			t.Errorf("RingProve(e,canon) shape wrong for %v", e)
		}
	}
	t.Logf("exercised %d generated expressions", len(exprs))
}

func TestRingProveRejectsUnequalAndNonlinear(t *testing.T) {
	if _, ok := RingProve(tn("a + b"), tn("a + c")); ok {
		t.Error("RingProve closed a+b = a+c")
	}
	if _, ok := RingProve(tn("2 * a"), tn("3 * a")); ok {
		t.Error("RingProve closed 2a = 3a")
	}
	if _, ok := RingProve(tn("a * b"), tn("a + b")); ok {
		t.Error("RingProve accepted nonlinear a*b")
	}
}

func checkNormalizeFull(t *testing.T, e Term) {
	t.Helper()
	lf, w := natRing.normalizeFull(e)
	if !prop.Lhs(w).AlphaEquals(e) {
		t.Errorf("Lhs = %v, want %v", prop.Lhs(w), e)
	}
	if !prop.Rhs(w).AlphaEquals(lf.toTerm()) {
		t.Errorf("Rhs = %v, want toTerm %v", prop.Rhs(w), lf.toTerm())
	}
	if evalLinNeq(lf, mpolyOf(e)) {
		t.Errorf("normalizeFull form disagrees with mpolyOf for %v", e)
	}
}

func TestNormalizeFullPlumbing(t *testing.T) {
	exprs := []Term{
		tn("a * b"),
		tn("a * a"),
		tn("b * a"), // commuted
		tn("a * (b + c)"),
		tn("(a + b) * c"),
		tn("(a + b) * (c + a)"),
		tn("(a + 1) * (b + 1)"),
		tn("2 * (a * b)"),
		tn("(a + b) * (a + b)"),
		tn("(a * b) * c"),
		tn("a * b + a * b"),
		tn("3 * (a * b) + 2 * (b * a)"),
		tn("((a + b) + 1) * (a + 2)"),
	}
	for _, e := range exprs {
		checkNormalizeFull(t, e)
	}
}

// Generated: products and sums of small factors over {a,b,c}, exercising
// distribution, monomial multiplication, like-monomial collection, and the
// multiply-by-zero/constant paths. Each must normalize to mpolyOf and
// RingProveFull(e, canon(e)) must close.
func TestRingFullGenerated(t *testing.T) {
	factors := []Term{tn("a"), tn("b"), tn("c"), tn("a + b"), tn("b + c"), tn("a + 1"), tn("2 * a + 3"), tn("0")}

	var exprs []Term
	for _, x := range factors {
		for _, y := range factors {
			exprs = append(exprs, star(x, y))
			exprs = append(exprs, plus(star(x, y), star(y, x))) // 2xy
		}
	}
	for _, x := range factors[:4] {
		for _, y := range factors[:4] {
			for _, z := range factors[:4] {
				exprs = append(exprs, star(star(x, y), z)) // degree 3
			}
		}
	}
	for _, e := range exprs {
		checkNormalizeFull(t, e)
		canon := mpolyOf(e).toTerm()
		w, ok := RingProveFull(e, canon)
		if !ok {
			t.Errorf("RingProveFull(e, canon) failed for %v", e)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(e) || !prop.Rhs(w).AlphaEquals(canon) {
			t.Errorf("RingProveFull shape wrong for %v", e)
		}
	}
	t.Logf("exercised %d generated product/sum expressions", len(exprs))
}

func TestRingProveFull(t *testing.T) {
	equal := []struct{ l, r Term }{
		{tn("a * b"), tn("b * a")},
		{tn("a * (b + c)"), tn("a * b + a * c")},
		{tn("(a + b) * c"), tn("a * c + b * c")},
		{tn("(a + b) * (a + b)"), tn("(a * a + 2 * (a * b)) + b * b")},
		{tn("(a + 1) * (a + 1)"), tn("(a * a + 2 * a) + 1")},
		{tn("(a + b) * (c + a)"), tn("((a * c + a * b) + a * a) + b * c")},
	}
	for _, p := range equal {
		w, ok := RingProveFull(p.l, p.r)
		if !ok {
			t.Errorf("RingProveFull failed to close %v = %v", p.l, p.r)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(p.l) || !prop.Rhs(w).AlphaEquals(p.r) {
			t.Errorf("RingProveFull(%v,%v): proof shape wrong", p.l, p.r)
		}
	}

	// unequal polynomials must be rejected
	if _, ok := RingProveFull(tn("a * b"), tn("a * c")); ok {
		t.Error("closed ab = ac")
	}
	if _, ok := RingProveFull(tn("(a + b) * (a + b)"), tn("a * a + b * b")); ok {
		t.Error("closed (a+b)² = a²+b² (missing 2ab)")
	}
}
