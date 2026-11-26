package omega

// The pow basis (pow_basis.go, domain.go powChainOf, ring.go's mirrored
// branch): a literal-exponent `real_pow`/`int_pow` is read as the monomial it
// denotes, so a power and a written-out product are one unknown. These tests
// pin the two spellings meeting, the lockstep between the model and the
// unfold, the boundary (symbolic exponent), num's twin, and that the term
// itself is untouched so the pow handlers still see what the author wrote.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// TestPowBasis_SpellingsMeet: the two spellings of a square are one atom, in
// either direction, and the wave's own mixed-spelling leaf closes.
func TestPowBasis_SpellingsMeet(t *testing.T) {
	installTestBundle(t)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"pow in the hypothesis, product in the goal",
			[]Term{pb("real_pow(x, 2) <= y")}, pb("x * x <= y")},
		{"product in the hypothesis, pow in the goal",
			[]Term{pb("x * x <= y")}, pb("real_pow(x, 2) <= y")},
		{"a cube expands too",
			[]Term{pb("real_pow(x, 3) <= y")}, pb("x * x * x <= y")},
		{"a power of a sum expands",
			[]Term{pb("real_pow(x + y, 2) <= z")}, pb("x * x + &2 * (x * y) + y * y <= z")},
		{"the SquareRootExists leaf, whose two facts were spelled differently",
			[]Term{pb("&0 < y"), pb("&0 <= x"), pb("real_pow(x, 2) <= y"), pb("&2 * x <= x * x + &1")},
			pb("x <= y + &1")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
}

// TestPowBasis_SquareSignRow: an even power is an even monomial, so the sign
// rows (real_sign_rows.go) price it with no hypothesis — the two passes meet.
func TestPowBasis_SquareSignRow(t *testing.T) {
	installTestBundle(t)
	if !realDecides(t, []Term{pb("real_pow(x, 2) <= y")}, pb("&0 <= y")) {
		t.Error("an even power must carry its own nonnegativity into the rows")
	}
}

// TestPowBasis_SymbolicExponentStaysOpaque: only a canonical literal exponent
// within the cap expands; a symbolic one is the atom it always was.
func TestPowBasis_SymbolicExponentStaysOpaque(t *testing.T) {
	installTestBundle(t)
	n := ext.Var(ext.TermName("n"), dsl.NumType)
	hyp := realLeT(realPowT(rr("x"), n), rr("y"))
	if realDecides(t, []Term{hyp}, pb("x * x <= y")) {
		t.Error("a symbolic exponent must not expand")
	}
	if _, ok := realDomain.powChainOf(realPowT(rr("x"), n)); ok {
		t.Error("powChainOf accepted a symbolic exponent")
	}
	if _, ok := realDomain.powChainOf(realPowT(rr("x"), Numeral(powChainMax+1))); ok {
		t.Error("powChainOf accepted an exponent past the cap")
	}
}

// TestPowBasis_SubNegBaseStaysOpaque: a base carrying subtraction is NOT read
// as a monomial. linOf never expands a sub — that is the signed normalizer's
// job, and it runs on hypotheses only — so such a power would read expanded on
// one side of a refutation and unexpanded on the other. The corpus witness is
// real_sqrt.ApproachFromAbove, whose hypothesis linking `real_pow(x−w, 2)` to
// its expansion becomes a tautology the moment the power expands too, leaving
// the goal's own copy unlinked.
func TestPowBasis_SubNegBaseStaysOpaque(t *testing.T) {
	installTestBundle(t)
	for _, base := range []string{"x - w", "-x", "(x - w) * y", "x + (y - w)"} {
		term := realPowT(rr(base), Numeral(2))
		if _, ok := realDomain.powChainOf(term); ok {
			t.Errorf("powChainOf expanded a base carrying sub/neg: %s", base)
		}
		lf, ok := realDomain.linOf(term)
		if !ok {
			t.Fatalf("linOf declined real_pow(%s, 2)", base)
		}
		if len(lf.monos) != 1 || !lf.monos[0].atom.AlphaEquals(term) {
			t.Errorf("real_pow(%s, 2) read as %v; want the opaque atom", base, realDomain.buildTerm(lf))
		}
	}
	// A sub-free base still expands — the guard is about sub, not about
	// compound bases.
	if _, ok := realDomain.powChainOf(realPowT(rr("x + y"), Numeral(2))); !ok {
		t.Error("a sub-free compound base must still expand")
	}
}

// TestPowBasis_ModelProofLockstep is the contract the runtime asserts: each
// domain's unfold proves the power equal to the chain the extraction reads.
// A drift here is a panic inside normalizeProof, so exercise both halves
// directly on the shapes the corpus carries.
func TestPowBasis_ModelProofLockstep(t *testing.T) {
	installTestBundle(t)
	for c := uint64(0); c <= 4; c++ {
		base := rr("x")
		powTerm := realPowT(base, Numeral(c))
		chain, ok := realDomain.powChainOf(powTerm)
		if !ok {
			t.Fatalf("powChainOf declined real_pow(x, %d)", c)
		}
		unfold := realPowUnfold(base, c)
		if unfold == nil {
			t.Fatalf("realPowUnfold declined c=%d inside the cap", c)
		}
		if !prop.Rhs(unfold).AlphaEquals(chain) {
			t.Errorf("c=%d: the unfold proves %v, the basis reads %v", c, prop.Rhs(unfold), chain)
		}
		lf, w, ok := realRing.normalizeProof(powTerm)
		if !ok {
			t.Fatalf("normalizeProof declined real_pow(x, %d)", c)
		}
		if !prop.Lhs(w).AlphaEquals(powTerm) {
			t.Errorf("c=%d: normalizeProof proves about %v, want %v", c, prop.Lhs(w), powTerm)
		}
		model, ok := realDomain.linOf(powTerm)
		if !ok {
			t.Fatalf("linOf declined real_pow(x, %d)", c)
		}
		if !sameLinForm(model, lf) {
			t.Errorf("c=%d: model form %v, proof form %v", c, realDomain.buildTerm(model), realDomain.buildTerm(lf))
		}
	}
}

// TestPowBasis_IntTwin: int_pow reads the same way, through intRing's unfold.
func TestPowBasis_IntTwin(t *testing.T) {
	installTestBundle(t)
	x, y := intVar("x"), intVar("y")
	sq := intStarT(x, x)
	hyp := intLeT(intPowT(x, Numeral(2)), y)
	if _, ok := IntLinProve(slices.Values([]Term{hyp}), intLeT(sq, y)); !ok {
		t.Error("IntLinProve declined int_pow(x,2) ≤ y ⊢ x·x ≤ y")
	}
	lf, w, ok := intRing.normalizeProof(intPowT(x, Numeral(2)))
	if !ok {
		t.Fatal("intRing.normalizeProof declined int_pow(x, 2)")
	}
	model, ok := intDomain.linOf(intPowT(x, Numeral(2)))
	if !ok || !sameLinForm(model, lf) {
		t.Error("the int model and proof forms diverge on int_pow(x, 2)")
	}
	if !prop.Lhs(w).AlphaEquals(intPowT(x, Numeral(2))) {
		t.Errorf("normalizeProof proves about %v", prop.Lhs(w))
	}
}

// TestPowBasis_NumTwin: nat_pow reads the same way, through natRing's chain
// unfold (nat_exp.go natPowChainUnfold) — a power and a written-out product
// are one unknown over num, the model and the unfold agree chain for chain,
// the simp step's own unfold keeps its c=2 shortcut, and the bounded-variable
// enumeration still fires on a comparison the basis reads as a product.
func TestPowBasis_NumTwin(t *testing.T) {
	installTestBundle(t)
	installEnumBundle(t)
	restore := installExpTestBundle(t, true)
	defer restore()
	a := numVar("a")
	for c := uint64(0); c <= 4; c++ {
		powTerm := ext.Apply(natExp, a, Numeral(c))
		chain, ok := natDomain.powChainOf(powTerm)
		if !ok {
			t.Fatalf("powChainOf declined nat_pow(a, %d)", c)
		}
		unfold := natPowChainUnfold(a, c)
		if unfold == nil {
			t.Fatalf("natPowChainUnfold declined c=%d inside the cap", c)
		}
		if !prop.Rhs(unfold).AlphaEquals(chain) {
			t.Errorf("c=%d: the unfold proves %v, the basis reads %v", c, prop.Rhs(unfold), chain)
		}
		lf, w, ok := natRing.normalizeProof(powTerm)
		if !ok {
			t.Fatalf("normalizeProof declined nat_pow(a, %d)", c)
		}
		if !prop.Lhs(w).AlphaEquals(powTerm) {
			t.Errorf("c=%d: normalizeProof proves about %v, want %v", c, prop.Lhs(w), powTerm)
		}
		model, ok := natDomain.linOf(powTerm)
		if !ok || !sameLinForm(model, lf) {
			t.Errorf("c=%d: the num model and proof forms diverge on nat_pow(a, %d)", c, c)
		}
	}
	// The simp step's unfold is untouched: c=2 is still the shortcut `a·a`.
	if w := expUnfold(a, 2); w == nil || !prop.Rhs(w).AlphaEquals(star(a, a)) {
		t.Error("expUnfold must keep its c=2 shortcut `a·a` beside the chain unfold")
	}
	b, x, y := numVar("b"), numVar("x"), numVar("y")
	sq := func(t Term) Term { return expT(t, Numeral(2)) }
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"the binomial square, bare", nil,
			eqT(sq(plus(a, b)), plus(plus(sq(a), star(star(Numeral(2), a), b)), sq(b)))},
		{"pow in the hypothesis, product in the goal", []Term{le(sq(x), y)}, le(star(x, x), y)},
		{"product in the hypothesis, pow in the goal", []Term{le(star(x, x), y)}, le(sq(x), y)},
		{"a cube beside its product", []Term{le(expT(x, Numeral(3)), y)}, le(star(star(x, x), x), y)},
		{"bounded enumeration still fires on the square", []Term{le(x, Numeral(2))}, le(sq(x), Numeral(4))},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			w := ArithDecideWithHyps(r.hyps)(r.goal)
			if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// A symbolic exponent is the atom it always was.
	n := numVar("n")
	if _, ok := natDomain.powChainOf(ext.Apply(natExp, a, n)); ok {
		t.Error("powChainOf accepted a symbolic num exponent")
	}
}

// TestPowBasis_SubNegBaseExpansionRow: a power whose base carries sub/neg
// stays one unknown (TestPowBasis_SubNegBaseStaysOpaque) and so keeps the
// sign an even power has; beside it the expansion row gives the same unknown
// its polynomial, as a square written as a product gets (subneg.go
// expansionRow), so an identity that needs the power multiplied out closes —
// in either spelling of the square.
func TestPowBasis_SubNegBaseExpansionRow(t *testing.T) {
	installTestBundle(t)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"an even power forgets a negation", nil, pb("real_pow(-x, 2) = real_pow(x, 2)")},
		{"the power of a negation against the product", nil, pb("real_pow(-x, 2) = x * x")},
		{"a negated literal squared", nil, pb("real_pow(-&1, 2) = &1")},
		{"an odd power keeps it", nil, pb("real_pow(-x, 3) = -(x * x * x)")},
		{"a square of a difference, identity", nil, pb("real_pow(x - y, 2) + &2 * (x * y) = x * x + y * y")},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
}

// TestPowBasis_SubNegBaseExpansionRowIntTwin: the same row over ℤ.
func TestPowBasis_SubNegBaseExpansionRowIntTwin(t *testing.T) {
	installTestBundle(t)
	x := intVar("x")
	goal := eqT(intPowT(intNegT(x), Numeral(2)), intStarT(x, x))
	if !intDecides(t, nil, goal) {
		t.Errorf("declined %v", goal)
	}
}
