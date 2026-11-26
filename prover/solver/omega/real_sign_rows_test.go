package omega

// The monomial sign rows (real_sign_rows.go): over ℝ a product atom is an
// unknown with no sign, so the refutation needs a row saying `&0 ≤ a·b` — from
// the factors' stated signs, or unconditionally when the monomial is a square.
// These tests pin what the pass supplies, what it declines, and the provenance
// contract (a derived row's hypotheses are its sources', never the conjuncts a
// source was projected out of).

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

func realDecides(t *testing.T, hyps []Term, goal Term) bool {
	t.Helper()
	w := RealArithDecideWithHyps(hyps)(goal)
	return w != nil && prop.Rhs(w).Equals(prop.T)
}

// TestRealSignRows_FromFactorSigns: a monomial whose factors' signs the
// context states gets its own sign row, so a bound stated over the monomial
// reaches the goal.
func TestRealSignRows_FromFactorSigns(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"two positive factors", []Term{pb("&0 < a"), pb("&0 < b"), pb("a * b <= c")}, pb("&0 < c")},
		{"three positive factors", []Term{pb("&0 < a"), pb("&0 < b"), pb("&0 < c"), pb("a * b * c <= d")}, pb("&0 < d")},
		{"two nonneg factors", []Term{pb("&0 <= a"), pb("&0 <= b"), pb("a * b <= c")}, pb("&0 <= c")},
		{"mixed signs make the product nonpositive",
			[]Term{pb("a <= &0"), pb("&0 <= b"), pb("&0 < a * b + c")}, pb("&0 < c")},
		{"two negative factors make it nonnegative",
			[]Term{pb("a <= &0"), pb("b <= &0"), pb("a * b <= c")}, pb("&0 <= c")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
}

// TestRealSignRows_SquareIsUnconditional: an all-even monomial is a square, so
// its nonnegativity needs no hypothesis at all — the ring proves the
// regrouping and SquareNonneg prices it.
func TestRealSignRows_SquareIsUnconditional(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a bare square", []Term{pb("x * x <= y")}, pb("&0 <= y")},
		{"a square in an equation", []Term{pb("x * x + y * y = &0")}, pb("x * x = &0")},
		{"a regrouped even monomial", []Term{pb("a * a * (b * b) <= z")}, pb("&0 <= z")},
		{"an even monomial spelled out of order", []Term{pb("b * a * (a * b) <= z")}, pb("&0 <= z")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
}

// TestRealSignRows_Declines pins the boundary. A sign the context does not
// state is not invented; an odd monomial is not a square; nonneg factors do
// not give a STRICT bound (`&0 ≤ a` and `&0 ≤ b` leave `a·b = &0` open); and
// the converse direction — a factor's sign read off the monomial's — is not
// this pass's business but the cancel handler's.
func TestRealSignRows_Declines(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"no factor sign is stated", []Term{pb("a * b <= c")}, pb("&0 < c")},
		{"only one factor is signed", []Term{pb("&0 < a"), pb("a * b <= c")}, pb("&0 < c")},
		{"nonneg factors give no strict bound",
			[]Term{pb("&0 <= a"), pb("&0 <= b"), pb("a * b <= c")}, pb("&0 < c")},
		{"an odd monomial is not a square", []Term{pb("x * x * x <= y")}, pb("&0 <= y")},
	}
	// The converse direction — a factor's sign off the monomial's — is
	// not a sign row; it closes through the products pass instead
	// (real_products.go, TestRealProducts_NlinarithShapes).
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if realDecides(t, r.hyps, r.goal) {
				t.Errorf("closed %v under %v — the pass must decline this", r.goal, r.hyps)
			}
		})
	}
}

// TestRealSignRows_MixedStrictnessFolds: `&0 < a` beside `&0 ≤ b` prices a·b
// non-strictly, the strict fact weakened first, whichever factor is the
// strict one and whichever sign each carries.
func TestRealSignRows_MixedStrictnessFolds(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name   string
		hyps   []Term
		nonneg bool
	}{
		{"positive · nonnegative", []Term{pb("&0 < a"), pb("&0 <= b"), pb("a * b <= c")}, true},
		{"nonnegative · positive", []Term{pb("&0 <= a"), pb("&0 < b"), pb("a * b <= c")}, true},
		{"negative · nonnegative", []Term{pb("a < &0"), pb("&0 <= b"), pb("c <= a * b")}, false},
		{"nonpositive · negative", []Term{pb("a <= &0"), pb("b < &0"), pb("a * b <= c")}, true},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			cs := realDomain.hypConstraints(slices.Values(r.hyps))
			var saw bool
			for _, c := range realMonomialSignConstraints(cs) {
				if c.Op != opLE {
					t.Errorf("row %v %v: a mixed pair must fold non-strictly", c.Lhs, c.Rhs)
				}
				if isRealZero(c.Lhs) == r.nonneg && c.HypProof != nil {
					saw = true
				}
			}
			if !saw {
				t.Error("no sign row for a·b")
			}
		})
	}
	hyps := []Term{pb("&0 < a"), pb("&0 <= b"), pb("a * b <= c")}
	if !realDecides(t, hyps, pb("&0 <= c")) {
		t.Error("mixed strictness must close")
	}
}

// TestRealSignRows_LoneInverse: an inverse standing alone in a linear form
// takes its sign from its argument's, so a quotient with a compound
// numerator — a sum of a product monomial and a bare inverse — is priced.
func TestRealSignRows_LoneInverse(t *testing.T) {
	installTestBundle(t)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a bare inverse", []Term{pb("&0 < x")}, realLtT(realLit(0), realInvT(realVar("x")))},
		{"inside a sum, compound numerator", []Term{pb("&0 <= M"), pb("&0 < x")}, pb("&1 <= (M + &1) / x + &1")},
		{"inside a sum", []Term{pb("&0 <= M"), pb("&0 < x")}, pb("&1 <= M / x + &1")},
		{"through an equation", []Term{pb("s = x / p"), pb("&0 < p"), pb("&0 <= x")}, pb("&0 <= s")},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// The argument's sign unknown: no row, and the claim does not follow.
	if realDecides(t, []Term{pb("&0 <= M")}, pb("&1 <= (M + &1) / x + &1")) {
		t.Error("decided a quotient's sign with nothing stated about the divisor")
	}
}

// TestRealSignRows_SquareDoesNotPreemptTheFold: an even monomial whose
// factors are positive is strictly positive, and the square reading alone
// gives `&0 ≤ m`. Both rows are emitted — real_sqrt.ApproachFromAbove's last
// step is the corpus witness, and it needs the strict one.
func TestRealSignRows_SquareDoesNotPreemptTheFold(t *testing.T) {
	installTestBundle(t)
	if !realDecides(t, []Term{pb("&0 < w"), pb("w * w <= c")}, pb("&0 < c")) {
		t.Error("a positive factor must still give the STRICT row for its square")
	}
	cs := realDomain.hypConstraints(slices.Values([]Term{pb("&0 < w"), pb("w * w <= c")}))
	extra := realMonomialSignConstraints(cs)
	var sawStrict, sawSquare bool
	for _, c := range extra {
		if c.Op == opLT {
			sawStrict = true
		}
		if c.Op == opLE {
			sawSquare = true
		}
	}
	if !sawStrict || !sawSquare {
		t.Errorf("want both readings of w·w; got strict=%v square=%v", sawStrict, sawSquare)
	}
}

// TestRealSignRows_HypSubset is the provenance contract. The sign facts are
// projected out of ONE conjunctive hypothesis, so the derived row's proof must
// carry that conjunction — not the conjuncts — or the refutation's hypotheses
// would not be a subset of the goal's and the tactic could not close through
// it (IsStronger).
func TestRealSignRows_HypSubset(t *testing.T) {
	installTestBundle(t)
	conj := pb("&0 < a ∧ &0 < b")
	bound := pb("a * b <= c")
	goal := pb("&0 < c")
	w, ok := RealLinProve(slices.Values([]Term{conj, bound}), goal)
	if !ok {
		t.Fatal("RealLinProve declined the conjunctive spelling")
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("conclusion = %v; want %v", w.Conclusion(), goal)
	}
	for h := range w.HypIter() {
		if !h.AlphaEquals(conj) && !h.AlphaEquals(bound) {
			t.Errorf("stray hypothesis %v — a projected conjunct escaped as its own hypothesis", h)
		}
	}
}

// TestRealSignRows_LinearGoalsUntouched: the pass costs one linOf sweep and
// returns nothing when no product monomial is present, so a purely linear
// refutation is byte-for-byte what it was.
func TestRealSignRows_LinearGoalsUntouched(t *testing.T) {
	installTestBundle(t)
	cs := realDomain.hypConstraints(slices.Values([]Term{pb("&0 < a"), pb("a <= b")}))
	if extra := realMonomialSignConstraints(cs); len(extra) != 0 {
		t.Errorf("a linear constraint set produced %d sign rows; want none", len(extra))
	}
}

// TestRealSignRows_InvFactor: a product with a `real_inv` factor takes its
// sign from the inverse's ARGUMENT. The hyp pre-simp rewrites a resident
// `&0 ⋈ inv t` into `&0 ⋈ t` (realInvSignSimp), so by the time the
// sign-of-product handler asks for the factor `inv t` its sign is stated
// about `t`; the handler has to look through the inverse the same way it
// descends a product. Measured before this: both rows declined at either
// strictness, while the variable-only controls closed (`convex.
// PositiveCombination`).
func TestRealSignRows_InvFactor(t *testing.T) {
	installTestBundle(t)
	a, tt := realVar("a"), realVar("t")
	zero := realLit(0)
	inv := realInvT(tt)
	// nonneg · nonneg-inverse
	realDecidesTrue(t, "0≤a, 0≤inv t ⊢ 0≤a·inv t",
		realLeT(zero, realStarT(a, inv)), realLeT(zero, a), realLeT(zero, inv))
	// nonneg · positive-inverse (the shape the chapter hit)
	realDecidesTrue(t, "0≤a, 0<inv t ⊢ 0≤a·inv t",
		realLeT(zero, realStarT(a, inv)), realLeT(zero, a), realLtT(zero, inv))
	// positive · positive-inverse, strict
	realDecidesTrue(t, "0<a, 0<inv t ⊢ 0<a·inv t",
		realLtT(zero, realStarT(a, inv)), realLtT(zero, a), realLtT(zero, inv))
	// the sign stated about the ARGUMENT directly, no inv in any premise
	realDecidesTrue(t, "0≤a, 0<t ⊢ 0≤a·inv t",
		realLeT(zero, realStarT(a, inv)), realLeT(zero, a), realLtT(zero, tt))
	// control: the variable-only twin closes today and must keep closing
	b := realVar("b")
	realDecidesTrue(t, "0≤a, 0<b ⊢ 0≤a·b (control)",
		realLeT(zero, realStarT(a, b)), realLeT(zero, a), realLtT(zero, b))
}

// TestRealSignRows_Pieces: a sign the context states about a product or a
// quotient prices every monomial that product divides, and an inverse atom
// takes its sign from its argument's.
func TestRealSignRows_Pieces(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a product's sign as a piece",
			[]Term{pb("&0 < a * b"), pb("&0 < a"), pb("a * a * b <= c")}, pb("&0 < c")},
		// The product-of-limits tolerance e / (e + l + m + 1): its sign is
		// stated about the quotient, and no sign of the divisor is in sight.
		{"a quotient's sign as a piece",
			[]Term{pb("e = (e + l + m + &1) * (e / (e + l + m + &1))"), pb("&0 < e"),
				pb("&0 < e / (e + l + m + &1)")},
			pb("e / (e + l + m + &1) * (l + m + &1) < e")},
		{"an inverse priced from its argument",
			[]Term{pb("&0 < a"), pb("&0 < v"), pb("a / v <= c")}, pb("&0 < c")},
		{"a piece used twice",
			[]Term{pb("&0 < a * b"), pb("(a * b) * (a * b) <= c")}, pb("&0 <= c")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// A piece that does not divide the monomial prices nothing of it.
	if realDecides(t, []Term{pb("&0 < a * b"), pb("a * a * b <= c")}, pb("&0 < c")) {
		t.Error("priced a·a·b from the sign of a·b alone")
	}
	// An inverse takes no sign from an argument the context does not price.
	if realDecides(t, []Term{pb("&0 < a"), pb("a / v <= c")}, pb("&0 < c")) {
		t.Error("priced a / v with no sign for v")
	}
}

// TestRealSignRows_PiecesHypSubset: a row folded from pieces carries the
// pieces' hypotheses and no other.
func TestRealSignRows_PiecesHypSubset(t *testing.T) {
	installTestBundle(t)
	hyps := []Term{pb("&0 < a * b"), pb("&0 < a"), pb("a * a * b <= c"), pb("&0 < unrelated")}
	w := RealArithDecideWithHyps(hyps)(pb("&0 < c"))
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		t.Fatal("declined")
	}
	for _, h := range w.Hyps() {
		if !slices.ContainsFunc(hyps[:3], h.AlphaEquals) {
			t.Errorf("the proof rests on %v, which the fold did not use", h)
		}
	}
}

// TestRealExpansionRows: a product whose only subtraction sits inside a
// square is one unknown to the linear layer (subneg.go's guard), which
// keeps its sign; the expansion row gives it its polynomial as well, so an
// identity that needs the square multiplied out closes — and the sign facts
// the guard protects still close beside it.
func TestRealExpansionRows(t *testing.T) {
	installTestBundle(t)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a square of a difference, identity", nil, pb("(x - y) * (x - y) + &2 * (x * y) = x * x + y * y")},
		{"two squares of differences", nil, pb("(x - y) * (x - y) + (x + y) * (x + y) = &2 * (x * x) + &2 * (y * y)")},
		{"the two-squares identity",
			nil, pb("(x * z - y * w) * (x * z - y * w) + (x * w + y * z) * (x * w + y * z) = (x * x + y * y) * (z * z + w * w)")},
		// the negative control: the guard's own case, the square's sign
		{"the square keeps its sign", []Term{pb("(x - y) * (x - y) <= c")}, pb("&0 <= c")},
		{"a bare difference squared is nonnegative", nil, pb("&0 <= (x - y) * (x - y)")},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
}

// TestRealSignRows_InverseOfAProduct: the inverse basis reads inv(a·b) as
// the monomial inv(a)·inv(b), and a sign the context states of a·b — which
// prices neither factor alone — prices that pair of atoms together.
func TestRealSignRows_InverseOfAProduct(t *testing.T) {
	installTestBundle(t)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a quotient by a positive product", []Term{pb("&0 < a * b"), pb("&0 <= x")}, pb("&0 <= x / (a * b)")},
		{"through an equation, the divisor a numeral times a sum",
			[]Term{pb("h = p / (&8 * (y + &1))"), pb("&0 < &8 * (y + &1)"), pb("&0 < p")}, pb("&0 < h")},
		{"beside another factor", []Term{pb("&0 < a * b"), pb("&0 < c"), pb("&0 <= x")}, pb("&0 <= x * c / (a * b)")},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// The product's sign says nothing of one factor's inverse.
	a := realVar("a")
	if realDecides(t, []Term{pb("&0 < a * b")}, realLtT(realLit(0), realInvT(a))) {
		t.Error("decided the sign of inv(a) from the sign of a·b")
	}
}

// TestExpansionRow_MemoizedPerMonomial: the expansion row of a monomial is
// built once (subneg.go expansionRow). Asked again it is the row it was,
// its proof the same derivation; a monomial with no sub/neg has no row and
// leaves no entry; and a bundle swap drops the rows with the constraint
// memos, since each is built from the bundle in force.
func TestExpansionRow_MemoizedPerMonomial(t *testing.T) {
	installTestBundle(t)
	square := rr("(x - y) * (x - y)")
	first, ok := realSubneg.expansionRow(square)
	if !ok {
		t.Fatalf("no expansion row for %s", ext.PrintTerm(square))
	}
	again, ok := realSubneg.expansionRow(square)
	if !ok || again.HypProof != first.HypProof || !again.Lhs.Equals(first.Lhs) || !again.Rhs.Equals(first.Rhs) {
		t.Errorf("the second ask built the row again: %s = %s, then %s = %s",
			ext.PrintTerm(first.Lhs), ext.PrintTerm(first.Rhs), ext.PrintTerm(again.Lhs), ext.PrintTerm(again.Rhs))
	}
	// The row is the uncached one.
	fresh, ok := realSubneg.expansionRowOf(square)
	if !ok || !fresh.Lhs.Equals(first.Lhs) || !fresh.Rhs.Equals(first.Rhs) || fresh.Op != first.Op ||
		!fresh.HypProof.Conclusion().Equals(first.HypProof.Conclusion()) {
		t.Errorf("the memoized row is not the one the normalizer builds: %s = %s against %s = %s",
			ext.PrintTerm(first.Lhs), ext.PrintTerm(first.Rhs), ext.PrintTerm(fresh.Lhs), ext.PrintTerm(fresh.Rhs))
	}

	plain := rr("x * y")
	if _, ok := realSubneg.expansionRow(plain); ok {
		t.Errorf("an expansion row for %s, which carries no sub/neg", ext.PrintTerm(plain))
	}
	if _, held := realSubneg.expansions.lookup(plain); held {
		t.Errorf("an entry for %s, which the normalizer is never asked about", ext.PrintTerm(plain))
	}

	if _, held := realSubneg.expansions.lookup(square); !held {
		t.Fatal("the row is not held before the bundle swap")
	}
	resetConstraintMemos()
	if _, held := realSubneg.expansions.lookup(square); held {
		t.Error("the row outlived the bundle it was built from")
	}
}

// TestSquareSign_MemoizedPerMonomial: the sign of a square monomial is
// proved once (realSquareSign, intSquareSign). Asked again it is the proof
// it was; a monomial that is no square has no sign and leaves no entry; and
// a bundle swap drops the signs with the constraint memos.
func TestSquareSign_MemoizedPerMonomial(t *testing.T) {
	installTestBundle(t)
	square := rr("(x * y) * (y * x)")
	first, ok := realSquareSign(square)
	if !ok {
		t.Fatalf("no sign for the square %s", ext.PrintTerm(square))
	}
	if !first.Conclusion().AlphaEquals(realLeT(realLit(0), square)) || first.NumHyps() != 0 {
		t.Errorf("the sign is %s under %d hypotheses", ext.PrintTerm(first.Conclusion()), first.NumHyps())
	}
	if again, ok := realSquareSign(square); !ok || again != first {
		t.Error("the second ask proved the sign again")
	}
	odd := rr("x * y")
	if _, ok := realSquareSign(odd); ok {
		t.Errorf("a square's sign for %s", ext.PrintTerm(odd))
	}
	if _, held := realSquareSigns.lookup(odd); held {
		t.Errorf("an entry for %s, which is no square", ext.PrintTerm(odd))
	}

	u := intVar("u")
	intSquare := intStarT(u, u)
	intFirst, ok := intSquareSign(intSquare)
	if !ok {
		t.Fatalf("no sign for the square %s", ext.PrintTerm(intSquare))
	}
	if again, ok := intSquareSign(intSquare); !ok || again != intFirst {
		t.Error("the second ask proved the int sign again")
	}

	resetConstraintMemos()
	if _, held := realSquareSigns.lookup(square); held {
		t.Error("the real sign outlived the bundle it was proved from")
	}
	if _, held := intSquareSigns.lookup(intSquare); held {
		t.Error("the int sign outlived the bundle it was proved from")
	}
}
