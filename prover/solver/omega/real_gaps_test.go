package omega

// Three ℝ shapes at the fragment's edge, and the asymmetry underneath two of
// them: a division in a HYPOTHESIS (the field handler proves goals only), a
// `&n` coercion (which linOf atomizes rather than declining outright), and a
// SQUARE, which the signed normalizer must not dissolve before the handler
// that prices it sees it.

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

func realSub2(a, b Term) Term { return realSubT(a, b) }

// TestRealLiteralDivisorInHypothesis: a division by a positive literal clears
// wherever the simp step runs, so a quotient in a HYPOTHESIS reaches linarith
// as the cleared comparison. Before, only a quotient in the GOAL did — the
// field handler PROVES a goal, it does not rewrite a hypothesis — and linarith
// read `x/&2` as an atom unrelated to `x`.
func TestRealLiteralDivisorInHypothesis(t *testing.T) {
	installTestBundle(t)
	x, y := rr("x"), rr("y")
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"the quotient is a hypothesis", []Term{realLeT(realDivT(x, realLit(2)), y)}, pb("x <= &2 * y")},
		{"strict", []Term{realLtT(realDivT(x, realLit(3)), y)}, pb("x < &3 * y")},
		{"the quotient on the right of the hypothesis",
			[]Term{realLeT(y, realDivT(x, realLit(2)))}, pb("&2 * y <= x")},
		{"the goal-side spelling still closes", []Term{pb("x <= &2 * y")},
			realLeT(realDivT(x, realLit(2)), y)},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// A SYMBOLIC divisor is not a rewrite's business — its sign is a proof
	// obligation, which is the handler's. The rewrite must decline.
	if w := realClearLiteralDivSimp(realLeT(realDivT(x, rr("z")), y)); w != nil {
		t.Errorf("cleared a symbolic divisor: %v", prop.Rhs(w))
	}
	if w := realClearLiteralDivSimp(realLeT(realDivT(x, realLit(0)), y)); w != nil {
		t.Errorf("cleared a ZERO divisor: %v", prop.Rhs(w))
	}
}

// TestRealOfNumIsAnAtomAndNonnegative: `&n` with a symbolic n is an opaque real
// term, so linOf atomizes it and a sign row prices it. `shaped` is answered on
// the coerced argument: answered on the coercion head it would make linOf
// DECLINE and drop the whole constraint carrying it.
func TestRealOfNumIsAnAtomAndNonnegative(t *testing.T) {
	installTestBundle(t)
	n := ext.Var(ext.TermName("n"), dsl.NumType)
	coerced := realOfNumT(n)
	lf, ok := realDomain.linOf(coerced)
	if !ok {
		t.Fatal("linOf still declines a symbolic `&n`")
	}
	if len(lf.monos) != 1 || !lf.monos[0].atom.AlphaEquals(coerced) {
		t.Errorf("`&n` read as %v; want the opaque atom", realDomain.buildTerm(lf))
	}
	if !realDecides(t, []Term{realLeT(coerced, rr("x"))}, realLeT(realLit(0), rr("x"))) {
		t.Error("`&n ≤ x ⊢ &0 ≤ x` declined — the nonnegativity row is missing")
	}
	// The contract's other two cases still decline: a MALFORMED numeral is
	// shaped-but-not-exact, because the Refl bridge the normalizers build for a
	// literal would be invalid for it.
	if _, _, ok := realRing.normalizeProof(realLit(3)); !ok {
		t.Error("a canonical literal must still normalize")
	}
	if _, shaped, exact := realDomain.asLiteral(realLit(3)); !shaped || !exact {
		t.Error("a canonical `&3` must read as an exact literal")
	}
	if _, shaped, _ := realDomain.asLiteral(coerced); shaped {
		t.Error("`&n` with a symbolic argument must not be numeral-shaped")
	}
}

// TestIntOfNumIsAnAtom: the ℤ twin of the coercion fix. Atomizing keeps the
// constraint carrying `&n`, which a dropped one could not do, and the int
// sign-rows pass then prices the atom.
func TestIntOfNumIsAnAtom(t *testing.T) {
	installTestBundle(t)
	n := ext.Var(ext.TermName("n"), dsl.NumType)
	coerced := intOfNumT(n)
	lf, ok := intDomain.linOf(coerced)
	if !ok {
		t.Fatal("int linOf still declines a symbolic `&n`")
	}
	if len(lf.monos) != 1 || !lf.monos[0].atom.AlphaEquals(coerced) {
		t.Errorf("int `&n` read as %v; want the opaque atom", intDomain.buildTerm(lf))
	}
	x, y := intVar("x"), intVar("y")
	w := IntArithDecideWithHyps([]Term{intLeT(coerced, x), intLeT(x, y)})(intLeT(coerced, y))
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		t.Error("`&n ≤ x, x ≤ y ⊢ &n ≤ y` declined — the coercion constraint is still dropped")
	}
	w2 := IntArithDecideWithHyps([]Term{intLeT(coerced, x)})(intLeT(intLit(0), x))
	if w2 == nil || !prop.Rhs(w2).Equals(prop.T) {
		t.Error("`&n ≤ x ⊢ &0 ≤ x` declined over ℤ — the coercion's nonnegativity row is missing")
	}
}

// TestRealSquareSurvivesPositivization: the signed normalizer positivizes a
// sub in the additive spine and not one inside a product: running its FOIL
// over `(x−y)·(x−y)` would dissolve the square into `x² − 2xy + y²`, whose
// nonnegativity is a sum-of-squares fact and outside the fragment. A square
// survives, so the handler and the sign rows that price it unconditionally
// can act.
func TestRealSquareSurvivesPositivization(t *testing.T) {
	installTestBundle(t)
	x, y, c := rr("x"), rr("y"), rr("c")
	sq := realStarT(realSub2(x, y), realSub2(x, y))
	if !realDecides(t, nil, realLeT(realLit(0), sq)) {
		t.Error("`⊢ &0 ≤ (x−y)·(x−y)` declined")
	}
	if !realDecides(t, []Term{realLeT(sq, c)}, realLeT(realLit(0), c)) {
		t.Error("`(x−y)·(x−y) ≤ c ⊢ &0 ≤ c` declined — the square's sign row is missing")
	}
	if realSubneg.moveAcrossCmp(realLeT(realLit(0), sq)) != nil {
		t.Error("move-across still dissolves a square")
	}
}

// TestRealNonSquareProductStillExpands is the other half of the boundary: only
// a SQUARE is protected. Every other product carrying a sub still runs through
// the FOIL, because there the expansion is what relates the product to its
// factors and nothing else does.
func TestRealNonSquareProductStillExpands(t *testing.T) {
	installTestBundle(t)
	x, y, a, b, c := rr("x"), rr("y"), rr("a"), rr("b"), rr("c")
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"a product with one sub factor expands",
			[]Term{realLeT(realStarT(x, realSub2(a, b)), c)},
			realLeT(realStarT(x, a), realPlusT(c, realStarT(x, b)))},
		{"a difference of squares",
			nil, eqT(realStarT(realSub2(x, y), realPlusT(x, y)),
				realSub2(realStarT(x, x), realStarT(y, y)))},
		{"the square's own expansion is still an identity",
			nil, eqT(realStarT(realSub2(x, y), realSub2(x, y)),
				realPlusT(realSub2(realStarT(x, x), realStarT(realLit(2), realStarT(x, y))),
					realStarT(y, y)))},
		{"a sub in the additive spine still moves across",
			[]Term{realLeT(realSub2(x, y), c)}, realLeT(x, realPlusT(c, y))},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	if realSubneg.moveAcrossCmp(realLeT(realStarT(rr("x"), realSub2(a, b)), c)) == nil {
		t.Error("move-across declined a NON-square product — only squares are protected")
	}
}

// TestIntSquareSurvivesPositivization: moveAcrossCmp is shared by ℝ and ℤ, so
// ℤ keeps its squares too — and its own sign-rows pass then prices them, in
// the goal and in a hypothesis alike.
func TestIntSquareSurvivesPositivization(t *testing.T) {
	installTestBundle(t)
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	sq := intStarT(intSubT(a, b), intSubT(a, b))
	if intSubneg.moveAcrossCmp(intLeT(intLit(0), sq)) != nil {
		t.Error("int move-across still dissolves a square")
	}
	w := IntArithDecideWithHyps(nil)(intLeT(intLit(0), sq))
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		t.Error("`⊢ &0 ≤ (a−b)·(a−b)` declined over ℤ")
	}
	w2 := IntArithDecideWithHyps([]Term{intLeT(sq, c)})(intLeT(intLit(0), c))
	if w2 == nil || !prop.Rhs(w2).Equals(prop.T) {
		t.Error("`(a−b)·(a−b) ≤ c ⊢ &0 ≤ c` declined over ℤ — the square's sign row is missing")
	}
}
