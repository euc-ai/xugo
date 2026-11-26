package omega

import (
	"slices"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Integer GCD-equality test (int_linarith.go): single equalities `Σcᵢxᵢ = k` with
// gcd(cᵢ) ∤ k are integer-unsat though ℚ-satisfiable. Closed by the sign split
// on the reduced form M = V/g against q = ⌊k/g⌋ + ℤ-discreteness — reusing the
// existing int discharge, no divisibility predicate. Placeholder-backed.

func TestIntGcdEq_Refutes(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	twoX := intStarT(intLit(2), x)
	threeX := intStarT(intLit(3), x)
	// 2x + 4y
	twoX4y := intPlusT(twoX, intStarT(intLit(4), y))

	cases := []struct {
		name string
		cs   []LinConstraint
	}{
		// the canonical example: 2·x = &1 has the ℚ solution x = 1/2, no integer one.
		{"2x=1", []LinConstraint{intCon(twoX, intLit(1), opEQ)}},
		// reversed orientation: &1 = 2·x.
		{"1=2x", []LinConstraint{intCon(intLit(1), twoX, opEQ)}},
		// odd RHS for an even form: 3·x = &7 (gcd 3 ∤ 7).
		{"3x=7", []LinConstraint{intCon(threeX, intLit(7), opEQ)}},
		// multivariate: 2x + 4y = &3 (gcd 2 ∤ 3).
		{"2x+4y=3", []LinConstraint{intCon(twoX4y, intLit(3), opEQ)}},
	}
	for _, tc := range cases {
		checkIntRefute(t, tc.name, tc.cs)
	}
}

func TestIntGcdEq_Satisfiable(t *testing.T) {
	x := intVar("x")
	twoX := intStarT(intLit(2), x)
	// 2·x = &4 IS integer-satisfiable (x = 2): gcd 2 ∣ 4, the GCD test declines
	// and ℚ-Farkas cannot refute either, so no refutation exists.
	if _, ok := IntLinRefuteProof([]LinConstraint{intCon(twoX, intLit(4), opEQ)}); ok {
		t.Errorf("2x=&4 must NOT be refutable (x=2 is a solution)")
	}
	// 2·x = &2 likewise (x = 1).
	if _, ok := IntLinRefuteProof([]LinConstraint{intCon(twoX, intLit(2), opEQ)}); ok {
		t.Errorf("2x=&2 must NOT be refutable (x=1 is a solution)")
	}
}

// TestIntGcdEq_ForwardAndDecide drives the GCD test through the public surfaces:
// the `≠` forward goal (IntLinProve) and the equality-atom decision
// (IntArithDecide collapses `2·x = &1` to ⊥).
func TestIntGcdEq_ForwardAndDecide(t *testing.T) {
	x := intVar("x")
	twoX := intStarT(intLit(2), x)

	// 2·x ≠ &1 is provable (the negation refutes via the GCD test).
	checkIntProve(t, "2x≠1", not(eqT(twoX, intLit(1))))

	// the equality atom decides to ⊥.
	w := IntArithDecide(eqT(twoX, intLit(1)))
	if w == nil {
		t.Fatalf("IntArithDecide(2x=&1) = nil, want ⊥")
	}
	if !prop.Rhs(w).Equals(prop.F) {
		t.Errorf("IntArithDecide(2x=&1) → %v, want ⊥", prop.Rhs(w))
	}
}

// General two-sided GCD-equality (intGroundedGcdEq) and the rank-1 gcd rounding
// cut (intRoundingCutRefute) — both ℤ-unique flat (rank-1) integer reasoning, built on
// discreteness, no int division.

func TestIntGcdEq_General(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	two := intLit(2)
	twoX := intStarT(two, x)
	twoY := intStarT(two, y)

	cases := []struct {
		name string
		cs   []LinConstraint
	}{
		// general two-sided: 2x = 2y+1  (2x−2y=1, gcd 2 ∤ 1) — NOT common-shape.
		{"2x=2y+1", []LinConstraint{intCon(twoX, intPlusT(twoY, intLit(1)), opEQ)}},
		// q<0 orientation: 2x+1 = 2y  (2x−2y=−1).
		{"2x+1=2y", []LinConstraint{intCon(intPlusT(twoX, intLit(1)), twoY, opEQ)}},
		// 4x + 6y = 3  (gcd 2 ∤ 3), multivariate two-sided.
		{"4x+6y=3", []LinConstraint{
			intCon(intPlusT(intStarT(intLit(4), x), intStarT(intLit(6), y)), intLit(3), opEQ)}},
	}
	for _, tc := range cases {
		checkIntRefute(t, tc.name, tc.cs)
	}

	// satisfiable: 2x = 2y+2  (gcd 2 ∣ 2, x=y+1 works) — must NOT refute.
	if _, ok := IntLinRefuteProof([]LinConstraint{
		intCon(twoX, intPlusT(twoY, two), opEQ)}); ok {
		t.Errorf("2x=2y+2 must NOT be refutable (x=y+1)")
	}
}

func TestIntRoundingCut(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	three, four, five := intLit(3), intLit(4), intLit(5)
	threeX := intStarT(three, x)

	cases := []struct {
		name string
		cs   []LinConstraint
	}{
		// the canonical gap: 4 ≤ 3x ∧ 3x ≤ 5  (x ∈ [4/3,5/3] over ℚ, no integer).
		{"4≤3x≤5", []LinConstraint{
			intCon(four, threeX, opLE), intCon(threeX, five, opLE)}},
		// order swapped.
		{"3x≤5,4≤3x", []LinConstraint{
			intCon(threeX, five, opLE), intCon(four, threeX, opLE)}},
		// multivariate: 4 ≤ 3(x+y) ∧ 3(x+y) ≤ 5.
		{"4≤3x+3y≤5", []LinConstraint{
			intCon(four, intPlusT(threeX, intStarT(three, y)), opLE),
			intCon(intPlusT(threeX, intStarT(three, y)), five, opLE)}},
	}
	for _, tc := range cases {
		checkIntRefute(t, tc.name, tc.cs)
	}

	// satisfiable: 3 ≤ 3x ∧ 3x ≤ 6  (x ∈ {1,2}) — exact bounds, must NOT refute.
	if _, ok := IntLinRefuteProof([]LinConstraint{
		intCon(three, threeX, opLE), intCon(threeX, intLit(6), opLE)}); ok {
		t.Errorf("3≤3x≤6 must NOT be refutable (x∈{1,2})")
	}
}

// TestIntGcdEq_SignedSides: the signed-normalizer pre-pass (intPositivizeConstraints,
// int_linarith.go) lets the GCD-equality test and the rounding cut see through
// top-level int_sub/int_neg. Without it, linOf atomizes a raw `a − b` into one
// opaque atom whose gcd collapses to 1, so an integer-unsat system written with
// explicit subtraction silently declines. Each case below carries int_sub in a
// constraint reaching the refuter directly (the `≠` goal / direct-entry path that
// bypasses hypConstraints' move-across).
func TestIntGcdEq_SignedSides(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	twoX, twoY := intStarT(intLit(2), x), intStarT(intLit(2), y)
	xMinusY := intSubT(x, y)

	// gcd-equality with explicit subtraction:
	//   2x − 2y = 1   and   2(x−y) = 1   (both 2(x−y)=1, gcd 2 ∤ 1).
	checkIntRefute(t, "2x−2y=1", []LinConstraint{intCon(intSubT(twoX, twoY), intLit(1), opEQ)})
	checkIntRefute(t, "2(x−y)=1", []LinConstraint{intCon(intStarT(intLit(2), xMinusY), intLit(1), opEQ)})

	// rounding cut with subtraction inside the scaled term:
	//   4 ≤ 3(x−y) ∧ 3(x−y) ≤ 5   (3(x−y) ∈ [4/3,5/3] over ℚ, no integer).
	threeXmY := intStarT(intLit(3), xMinusY)
	checkIntRefute(t, "4≤3(x−y)≤5", []LinConstraint{
		intCon(intLit(4), threeXmY, opLE), intCon(threeXmY, intLit(5), opLE)})

	// forward `≠` goal: ⊢ 2x − 2y ≠ 1 (the negation is the gcd-unsat equality).
	// Also asserts the IsStronger contract — the proof is hyp-free.
	checkIntProve(t, "⊢2x−2y≠1", not(eqT(intSubT(twoX, twoY), intLit(1))))

	// satisfiable guard: 2(x−y) = 2 (gcd 2 ∣ 2, x=y+1 works) — must NOT refute,
	// even though it carries subtraction (the positivize pass must not mis-fire).
	if _, ok := IntLinRefuteProof([]LinConstraint{
		intCon(intStarT(intLit(2), xMinusY), intLit(2), opEQ)}); ok {
		t.Errorf("2(x−y)=2 must NOT be refutable (x=y+1)")
	}
}

// TestIntCoeffEq_LinearCancel: the SAT counterpart of the GCD-equality test —
// `c·x = k` (c∣k) pins x to k/c, and all LINEAR consequences close via
// discreteness (no division). checkIntProve also asserts the IsStronger contract
// (the proof's hyps ⊆ {2x=4}).
func TestIntCoeffEq_LinearCancel(t *testing.T) {
	x := intVar("x")
	twoX := intStarT(intLit(2), x)
	eq := eqT(twoX, intLit(4)) // 2x = 4
	checkIntProve(t, "2x=4⊢x=2", eqT(x, intLit(2)), eq)
	checkIntProve(t, "2x=4⊢x≤2", intLeT(x, intLit(2)), eq)
	checkIntProve(t, "2x=4⊢2≤x", intLeT(intLit(2), x), eq)
	checkIntProve(t, "2x=4⊢x≠3", not(eqT(x, intLit(3))), eq)
	// 6x = 12 likewise pins x = 2.
	checkIntProve(t, "6x=12⊢x=2", eqT(x, intLit(2)), eqT(intStarT(intLit(6), x), intLit(12)))
}

// Integer certificate-replay tests — the twin of the real ones in real_test.go. Each
// refutation/proof runs the full kernel composition (scale → sum → ring-
// normalize → cancel → close, plus forward negate→refute→peel) and lands the
// right conclusion + a hyp set among the inputs. Leaves are IntLemmaBundle
// placeholders, so soundness rides on the (future) bundle swap; the plumbing is
// real kernel work and checked here.
//
// The int terms here are built through the production builders (domain.go)
// rather than parsed from text.

// intVar builds an int-typed variable.
func intVar(name string) Term { return ext.Var(ext.TermName(name), dsl.IntType) }

func intCon(l, r Term, op relOp) LinConstraint {
	return LinConstraint{Lhs: l, Rhs: r, Op: op}
}

func intConstraintTerm(c LinConstraint) Term {
	if c.Hyp != nil {
		return c.Hyp
	}
	switch c.Op {
	case opLE:
		return intLeT(c.Lhs, c.Rhs)
	case opLT:
		return intLtT(c.Lhs, c.Rhs)
	default:
		return eqT(c.Lhs, c.Rhs)
	}
}

func checkIntRefute(t *testing.T, name string, cs []LinConstraint) {
	t.Helper()
	w, ok := IntLinRefuteProof(cs)
	if !ok {
		t.Fatalf("%s: expected an int refutation, got none", name)
	}
	if !w.Conclusion().Equals(prop.F) {
		t.Errorf("%s: conclusion = %v, want ⊥", name, w.Conclusion())
	}
	allowed := make([]Term, len(cs))
	for i, c := range cs {
		allowed[i] = intConstraintTerm(c)
	}
	hypsAmong(t, name, w, allowed)
}

func TestIntLinRefuteProof(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	xy := intPlusT(x, y)
	cases := []struct {
		name string
		cs   []LinConstraint
	}{
		{"x<x", []LinConstraint{intCon(x, x, opLT)}},
		{"x<y,y<x", []LinConstraint{intCon(x, y, opLT), intCon(y, x, opLT)}},
		{"&2<=x,x<=&1", []LinConstraint{intCon(intLit(2), x, opLE), intCon(x, intLit(1), opLE)}},
		{"x+y<=&1,&2<=x+y", []LinConstraint{
			intCon(xy, intLit(1), opLE), intCon(intLit(2), xy, opLE)}},
		{"cycle x<=y<=z<x", []LinConstraint{
			intCon(x, y, opLE), intCon(y, z, opLE), intCon(z, x, opLT)}},
		{"eq: x=y, y<x", []LinConstraint{intCon(x, y, opEQ), intCon(y, x, opLT)}},
	}
	for _, tc := range cases {
		checkIntRefute(t, tc.name, tc.cs)
	}
}

func checkIntProve(t *testing.T, name string, goal Term, hyps ...Term) {
	t.Helper()
	w, ok := IntLinProve(seqOf(hyps...), goal)
	if !ok {
		t.Fatalf("%s: expected a proof of the goal, got none", name)
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("%s: conclusion = %v, want %v", name, w.Conclusion(), goal)
	}
	hypsAmong(t, name, w, hyps)
}

func TestIntLinProve(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	// transitivity: x<y, y<z ⊢ x<z
	checkIntProve(t, "trans", intLtT(x, z), intLtT(x, y), intLtT(y, z))
	// weakening: x<y ⊢ x≤y
	checkIntProve(t, "lt⇒le", intLeT(x, y), intLtT(x, y))
	// antisymmetry (the `=` path): x≤y, y≤x ⊢ x=y
	checkIntProve(t, "antisym", eqT(x, y), intLeT(x, y), intLeT(y, x))
	// constant slack: &2≤x ⊢ &1≤x
	checkIntProve(t, "const", intLeT(intLit(1), x), intLeT(intLit(2), x))
	// `>` goal via the bridge: x<y ⊢ y>x
	checkIntProve(t, "gt-bridge", intGtT(y, x), intLtT(x, y))
}

func TestIntLinProve_Unprovable(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	// x<y does NOT entail y<x — the negation is ℚ-satisfiable, so ok=false.
	// (NB: ℤ-discreteness would still not make y<x follow; this is genuinely SAT.)
	if _, ok := IntLinProve(seqOf(intLtT(x, y)), intLtT(y, x)); ok {
		t.Errorf("y<x should not be provable from x<y")
	}
}

// Signed normalizer (subneg.go): TOTAL sub/neg peeled to the two-positive-
// sided `P + (−N)` form, placeholder-backed (the package init fabricator stands
// in for the unbound subneg leaves). Validates BOTH the returned linForms (the
// signed semantics) AND the proof's conclusion shape (the kernel composition is
// well-formed — a wrong leaf orientation would make an EqTrans panic).

func linFormEq(a, b linForm) bool { return sameLinForm(a, b) }

type signedEntry func(Term) (linForm, linForm, *prop.PropWrapper, bool)

func checkSigned(t *testing.T, dom *Domain, entry signedEntry, input Term, wantP, wantN linForm) {
	t.Helper()
	p, n, proof, ok := entry(input)
	if !ok {
		t.Fatalf("signedNorm(%v) returned ok=false", input)
	}
	// the returned linForms carry the intended signed semantics
	if !linFormEq(p, wantP) {
		t.Errorf("P = %+v, want %+v", p, wantP)
	}
	if !linFormEq(n, wantN) {
		t.Errorf("N = %+v, want %+v", n, wantN)
	}
	// the proof's conclusion is `⊢ input = buildTerm(P) + (−buildTerm(N))`
	l, r, eqok := ext.MatchesEQ(proof.Conclusion())
	if !eqok {
		t.Fatalf("conclusion is not an equality: %v", proof.Conclusion())
	}
	if !l.AlphaEquals(input) {
		t.Errorf("proof LHS = %v, want %v", l, input)
	}
	wantRHS := dom.plus(dom.buildTerm(p), dom.neg(dom.buildTerm(n)))
	if !r.AlphaEquals(wantRHS) {
		t.Errorf("proof RHS = %v, want %v", r, wantRHS)
	}
}

func mono1(c int64, a Term) linForm { return form(0, mono(c, a)) }

func TestSignedNorm_Int(t *testing.T) {
	x := core.Var("x", dsl.IntType)
	y := core.Var("y", dsl.IntType)
	zero := linForm{}

	// x − y  →  P={x}, N={y}
	checkSigned(t, intDomain, IntSignedNormalizeProof, intSubT(x, y), mono1(1, x), mono1(1, y))
	// −x  →  P=0, N={x}
	checkSigned(t, intDomain, IntSignedNormalizeProof, intNegT(x), zero, mono1(1, x))
	// −(−x)  →  P={x}, N=0  (double negation cancels)
	checkSigned(t, intDomain, IntSignedNormalizeProof, intNegT(intNegT(x)), mono1(1, x), zero)
	// (x + &2) − (y + &5)  →  P={x}+2, N={y}+5
	lhs := intSubT(intPlusT(x, intLit(2)), intPlusT(y, intLit(5)))
	checkSigned(t, intDomain, IntSignedNormalizeProof, lhs,
		form(2, mono(1, x)), form(5, mono(1, y)))
	// &3 · (x − y)  →  P={3·x}, N={3·y}  (scale distributes over the split)
	checkSigned(t, intDomain, IntSignedNormalizeProof, intStarT(intLit(3), intSubT(x, y)),
		mono1(3, x), mono1(3, y))
	// (x − y) · &3  →  same, via commute
	checkSigned(t, intDomain, IntSignedNormalizeProof, intStarT(intSubT(x, y), intLit(3)),
		mono1(3, x), mono1(3, y))
	// sub-free input still normalizes (P + −&0)
	checkSigned(t, intDomain, IntSignedNormalizeProof, intPlusT(x, y),
		form(0, mono(1, x), mono(1, y)), zero)
}

func TestSignedNorm_Real(t *testing.T) {
	x := core.Var("x", dsl.RealType)
	y := core.Var("y", dsl.RealType)
	zero := linForm{}

	checkSigned(t, realDomain, RealSignedNormalizeProof, realSubT(x, y), mono1(1, x), mono1(1, y))
	checkSigned(t, realDomain, RealSignedNormalizeProof, realNegT(x), zero, mono1(1, x))
	lhs := realSubT(realPlusT(x, realLit(2)), realPlusT(y, realLit(5)))
	checkSigned(t, realDomain, RealSignedNormalizeProof, lhs,
		form(2, mono(1, x)), form(5, mono(1, y)))
	checkSigned(t, realDomain, RealSignedNormalizeProof, realStarT(realLit(3), realSubT(x, y)),
		mono1(3, x), mono1(3, y))
}

// TestMoveAcross_Iff: moveAcrossCmp turns a sub/neg comparison atom into a
// positive two-sided iff (LHS preserved, RHS sub/neg-free).
func TestMoveAcross_Iff(t *testing.T) {
	x := core.Var("x", dsl.IntType)
	y := core.Var("y", dsl.IntType)
	atom := intLeT(intSubT(x, y), intLit(3)) // x − y ≤ &3
	w := intSubneg.moveAcrossCmp(atom)
	if w == nil {
		t.Fatal("moveAcrossCmp returned nil on a sub atom")
	}
	l, r, ok := ext.MatchesEQ(w.Conclusion()) // a bool iff
	if !ok {
		t.Fatalf("conclusion is not an iff: %v", w.Conclusion())
	}
	if !l.AlphaEquals(atom) {
		t.Errorf("iff LHS = %v, want the original atom", l)
	}
	ll, rr, isLe := intDomain.matchLe(r)
	if !isLe {
		t.Fatalf("iff RHS is not an int ≤ atom: %v", r)
	}
	if intSubneg.hasSubNeg(ll) || intSubneg.hasSubNeg(rr) {
		t.Errorf("iff RHS sides still carry sub/neg: %v", r)
	}
	// a positive atom is a no-op (no loop, no preemption)
	if intSubneg.moveAcrossCmp(r) != nil {
		t.Errorf("moveAcrossCmp on the positive RHS should be nil")
	}
}

// TestMoveAcross_ClosesGoals: the end-to-end decide path (IntArithDecide /
// RealArithDecide) closes universally-valid sub/neg goals — the move-across leaf
// feeds the positive decider, which collapses them to ⊤.
func TestMoveAcross_ClosesGoals(t *testing.T) {
	x := core.Var("x", dsl.IntType)
	y := core.Var("y", dsl.IntType)
	intGoals := []Term{
		intLeT(intSubT(x, y), intSubT(x, y)),                      // x−y ≤ x−y
		eqT(intSubT(intLit(5), intLit(2)), intLit(3)),             // &5−&2 = &3
		eqT(intSubT(intPlusT(x, intLit(3)), x), intLit(3)),        // (x+&3)−x = &3
		intLeT(intNegT(x), intNegT(x)),                            // −x ≤ −x
		intLtT(intSubT(x, y), intPlusT(intSubT(x, y), intLit(1))), // x−y < (x−y)+&1
		intGeT(intPlusT(intSubT(x, y), y), x),                     // (x−y)+y ≥ x
	}
	for _, g := range intGoals {
		w := IntArithDecide(g)
		if w == nil {
			t.Errorf("IntArithDecide(%v) = nil", g)
			continue
		}
		if !prop.Rhs(w).Equals(prop.T) {
			t.Errorf("IntArithDecide(%v) → %v, want ⊤", g, prop.Rhs(w))
		}
	}

	rx := core.Var("x", dsl.RealType)
	ry := core.Var("y", dsl.RealType)
	realGoals := []Term{
		realLeT(realSubT(rx, ry), realSubT(rx, ry)),              // x−y ≤ x−y
		eqT(realSubT(realPlusT(rx, realLit(3)), rx), realLit(3)), // (x+&3)−x = &3
		realLeT(realNegT(rx), realNegT(rx)),                      // −x ≤ −x
	}
	for _, g := range realGoals {
		w := RealArithDecide(g)
		if w == nil {
			t.Errorf("RealArithDecide(%v) = nil", g)
			continue
		}
		if !prop.Rhs(w).Equals(prop.T) {
			t.Errorf("RealArithDecide(%v) → %v, want ⊤", g, prop.Rhs(w))
		}
	}
}

// TestMoveAcross_HypSide: a comparison HYPOTHESIS carrying sub/neg now feeds
// linarith (positivized via the move-across), and the proof's hyps stay ⊆ the
// originals (checkIntProve/checkRealProve assert the IsStronger contract).
func TestMoveAcross_HypSide(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	// x−y ≤ &0 ⊢ x ≤ y
	checkIntProve(t, "sub-hyp-le", intLeT(x, y), intLeT(intSubT(x, y), intLit(0)))
	// a−b ≤ c ⊢ a ≤ c+b
	checkIntProve(t, "sub-hyp-radd", intLeT(a, intPlusT(c, b)), intLeT(intSubT(a, b), c))
	// x ≤ y−&1 ⊢ x < y
	checkIntProve(t, "sub-hyp-ladd", intLtT(x, y), intLeT(x, intSubT(y, intLit(1))))
	// x−y ≤ &0, y−z ≤ &0 ⊢ x ≤ z   (transitivity through two sub hyps)
	checkIntProve(t, "sub-hyp-trans", intLeT(x, z),
		intLeT(intSubT(x, y), intLit(0)), intLeT(intSubT(y, z), intLit(0)))
	// −x ≤ &0 ⊢ &0 ≤ x   (neg hyp)
	checkIntProve(t, "neg-hyp", intLeT(intLit(0), x), intLeT(intNegT(x), intLit(0)))
	// a−b > &0 ⊢ b < a   (>-hyp positivized via the bridge)
	checkIntProve(t, "gt-sub-hyp", intLtT(b, a), intGtT(intSubT(a, b), intLit(0)))

	// the same on ℝ (shared Domain.hypConstraints path; realDomain hook wired)
	rx := core.Var("x", dsl.RealType)
	ry := core.Var("y", dsl.RealType)
	checkRealProve(t, "real-sub-hyp", realLeT(rx, ry), realLeT(realSubT(rx, ry), realLit(0)))
}

// TestDiscreteness_Int: the strict-row strengthening (Discrete)
// closes the off-by-one / consecutive-integer class that pure ℚ-Farkas cannot,
// without over-proving (the dense-only conclusions still fail).
func TestDiscreteness_Int(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")

	// canonical: x < y ⊢ x + &1 ≤ y   (ℚ-FALSE: over ℚ, x<y ⇏ x+1≤y)
	checkIntProve(t, "lt⇒+1≤", intLeT(intPlusT(x, intLit(1)), y), intLtT(x, y))
	// chained gap: x < y, y < z ⊢ x + &2 ≤ z
	checkIntProve(t, "chain", intLeT(intPlusT(x, intLit(2)), z), intLtT(x, y), intLtT(y, z))
	// composes with the move-across: x − y < &1 ⊢ x ≤ y
	checkIntProve(t, "sub+discrete", intLeT(x, y), intLtT(intSubT(x, y), intLit(1)))

	// NOT provable even with discreteness (y could be x+1) — soundness guard.
	if _, ok := IntLinProve(seqOf(intLtT(x, y)), intLeT(intPlusT(x, intLit(2)), y)); ok {
		t.Errorf("x+&2 ≤ y must NOT follow from x < y")
	}
}

// TestSignedNorm_Nonlinear: a nonlinear-with-subtraction product (atom·(a−b)) is
// FOILed by the signed multivariate ring (mulSigned) — z·(x−y) normalizes
// to `z·x + (−(z·y))`.
func TestSignedNorm_Nonlinear(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	if _, _, _, ok := IntSignedNormalizeProof(intStarT(z, intSubT(x, y))); !ok {
		t.Errorf("z·(x−y) should now normalize (signed FOIL), got ok=false")
	}
	// end-to-end: the distributed identity z·(x−y) = z·x − z·y decides to ⊤.
	intDecidesTrue(t, "z·(x−y)=z·x−z·y",
		eqT(intStarT(z, intSubT(x, y)), intSubT(intStarT(z, x), intStarT(z, y))))
}

// int_max/int_min/int_sgn + raw COND case splits (int_split.go) and the
// hypothesis-driven splits ≠/∨/⇒. All placeholder-backed.

// checkIntDecideTrueH decides goal under hyps and asserts it collapses to ⊤.
func checkIntDecideTrueH(t *testing.T, name string, goal Term, hyps ...Term) {
	t.Helper()
	w := IntArithDecideWithHyps(hyps)(goal)
	if w == nil {
		t.Errorf("%s: IntArithDecideWithHyps(%v)(%v) = nil, want ⊤", name, hyps, goal)
		return
	}
	if !prop.Rhs(w).Equals(prop.T) {
		t.Errorf("%s: → %v, want ⊤", name, prop.Rhs(w))
	}
}

func TestIntMaxMin_ClosesGoals(t *testing.T) {
	a, b := intVar("a"), intVar("b")
	// a ≤ max(a,b), b ≤ max(a,b)
	checkIntDecideTrue(t, "a≤max", intLeT(a, intMaxT(a, b)))
	checkIntDecideTrue(t, "b≤max", intLeT(b, intMaxT(a, b)))
	// min(a,b) ≤ a, min(a,b) ≤ b
	checkIntDecideTrue(t, "min≤a", intLeT(intMinT(a, b), a))
	checkIntDecideTrue(t, "min≤b", intLeT(intMinT(a, b), b))
	// min(a,b) ≤ max(a,b) (both atoms split)
	checkIntDecideTrue(t, "min≤max", intLeT(intMinT(a, b), intMaxT(a, b)))
}

func TestIntSgn_ClosesGoals(t *testing.T) {
	x := intVar("x")
	sgn := intSgnT(x)
	// −&1 ≤ sgn x ≤ &1 (the three-way split, inner COND via the raw-COND kind)
	checkIntDecideTrue(t, "sgn≤1", intLeT(sgn, intLit(1)))
	checkIntDecideTrue(t, "−1≤sgn", intLeT(intNegT(intLit(1)), sgn))
}

func TestIntRawCond_ClosesGoals(t *testing.T) {
	x := intVar("x")
	// &0 ≤ COND(&0 ≤ x, x, &1): both arms nonneg.
	c := ext.Cond(intLeT(intLit(0), x), x, intLit(1))
	checkIntDecideTrue(t, "0≤cond", intLeT(intLit(0), c))
}

func TestIntHypSplit(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	// ≠ hyp: x ≠ y, x ≤ y ⊢ x < y  (trichotomy: the y<x branch contradicts x≤y).
	checkIntDecideTrueH(t, "neq-hyp", intLtT(x, y), not(eqT(x, y)), intLeT(x, y))
	// ∨ hyp: (x ≤ &0 ∨ &2 ≤ x) ⊢ x ≠ &1.
	checkIntDecideTrueH(t, "or-hyp", not(eqT(x, intLit(1))),
		or(intLeT(x, intLit(0)), intLeT(intLit(2), x)))
	// ⇒ hyp: (x ≤ &0 ⇒ &2 ≤ x) ⊢ &1 ≤ x  (¬p ⇒ x>0 ⇒ x≥1; q ⇒ x≥2 ⇒ x≥1).
	checkIntDecideTrueH(t, "imp-hyp", intLeT(intLit(1), x),
		imply(intLeT(x, intLit(0)), intLeT(intLit(2), x)))
}

// gcdStepP builds P(u,v) = ∃d x y. ((d = u*x + v*y) ∧ d|u) ∧ d|v — the Bézout
// body of a gcd-existence statement, opaque to the linear core.
func gcdStepP(u, v Term) Term {
	d, x, y := intVar("d"), intVar("x"), intVar("y")
	body := and(
		and(eqT(d, intPlusT(intStarT(u, x), intStarT(v, y))), intDividesT(d, u)),
		intDividesT(d, v))
	return ext.Exists(d, x, y)(ext.WrapTerm(body))
}

// gcdStepCases is the 5-way Euclidean descent-cases disjunction over free a, b:
// (a=0 ∨ b=0) ∨ |a−b|+|b| < |a|+|b| ∨ |a+b|+|b| < |a|+|b|
//
//	∨ |a|+|b−a| < |a|+|b| ∨ |a|+|b+a| < |a|+|b|.
func gcdStepCases(a, b Term) Term {
	absA, absB := intAbsT(a), intAbsT(b)
	m := intPlusT(absA, absB)
	return or(
		or(eqT(a, intLit(0)), eqT(b, intLit(0))),
		or(
			or(intLtT(intPlusT(intAbsT(intSubT(a, b)), absB), m),
				intLtT(intPlusT(intAbsT(intPlusT(a, b)), absB), m)),
			or(intLtT(intPlusT(absA, intAbsT(intSubT(b, a))), m),
				intLtT(intPlusT(absA, intAbsT(intPlusT(b, a))), m))))
}

// TestIntSplitCorePruning pins splitByCases' proof-core pruning (engine.go)
// on a gcd-existence step shape: deciding the (valid on its own)
// descent-cases disjunction with 10 certificate-IRRELEVANT ground
// implication hyps resident — 6 worker-lift implications over the opaque
// Bézout ∃-bodies plus 4 measure-guarded IH instances. Unpruned, every
// hyp/EM split doubles the tree whether or not any proof consumes its guard
// (≈2.5× per implication hyp; 7+ hyps never terminate, and the accumulating
// branch proofs exhaust memory). Pruned, a branch proof that does not carry
// the split guard in its hyp set is returned directly (weakening), so the
// irrelevant hyps cost a per-leaf linear walk and the decide terminates at
// roughly the goal's intrinsic abs-split cost. The companion "relevant-hyp"
// check guards the other direction: a hyp the certificate genuinely needs
// still gets its split.
func TestIntSplitCorePruning(t *testing.T) {
	a, b := intVar("a"), intVar("b")
	absA, absB := intAbsT(a), intAbsT(b)
	m := intPlusT(absA, absB)
	pAB := gcdStepP(a, b)
	hyps := []Term{
		imply(gcdStepP(a, intPlusT(b, a)), pAB),
		imply(gcdStepP(a, intSubT(b, a)), pAB),
		imply(gcdStepP(intPlusT(a, b), b), pAB),
		imply(gcdStepP(intSubT(a, b), b), pAB),
		imply(eqT(a, intLit(0)), pAB),
		imply(eqT(b, intLit(0)), pAB),
		imply(intLtT(intPlusT(absA, intAbsT(intPlusT(b, a))), m), gcdStepP(a, intPlusT(b, a))),
		imply(intLtT(intPlusT(absA, intAbsT(intSubT(b, a))), m), gcdStepP(a, intSubT(b, a))),
		imply(intLtT(intPlusT(intAbsT(intPlusT(a, b)), absB), m), gcdStepP(intPlusT(a, b), b)),
		imply(intLtT(intPlusT(intAbsT(intSubT(a, b)), absB), m), gcdStepP(intSubT(a, b), b)),
	}
	checkIntDecideTrueH(t, "gcd-step-irrelevant-hyps", gcdStepCases(a, b), hyps...)

	// Relevant-hyp control: {&0 ≤ |z| ⇒ &0 ≤ y} ⊢ (&0 ≤ y) ∨ (z = &0) — the
	// implication (and the abs split feeding its antecedent) is genuinely
	// needed, so the pruning must NOT skip its case analysis.
	y, z := intVar("y"), intVar("z")
	checkIntDecideTrueH(t, "gcd-step-relevant-hyp",
		or(intLeT(intLit(0), y), eqT(z, intLit(0))),
		imply(intLeT(intLit(0), intAbsT(z)), intLeT(intLit(0), y)))
}

// Integer case split (int_split.go): int_abs eliminated on excluded middle of
// its def guard `&0 ≤ x`, each branch pinned to x / −x and closed by the int
// forward prover (the −x branch through the signed normalizer). Placeholder-
// backed (the AbsBySign def + the int order leaves are fabricator stand-ins), so
// the kernel composition is what is exercised here.

// checkIntDecideTrue asserts IntArithDecide(g) collapses g to ⊤.
func checkIntDecideTrue(t *testing.T, name string, g Term) {
	t.Helper()
	w := IntArithDecide(g)
	if w == nil {
		t.Errorf("%s: IntArithDecide(%v) = nil, want ⊤", name, g)
		return
	}
	if !prop.Rhs(w).Equals(prop.T) {
		t.Errorf("%s: IntArithDecide(%v) → %v, want ⊤", name, g, prop.Rhs(w))
	}
	if !prop.Lhs(w).AlphaEquals(g) {
		t.Errorf("%s: decided LHS = %v, want %v", name, prop.Lhs(w), g)
	}
}

func TestIntAbs_ClosesGoals(t *testing.T) {
	x := intVar("x")
	abs := intAbsT(x)

	// |x| ≥ 0 : x≥0 branch |x|=x≥0; x<0 branch |x|=−x≥0.
	checkIntDecideTrue(t, "0≤|x|", intLeT(intLit(0), abs))
	// x ≤ |x| : x≥0 branch x≤x; x<0 branch x<0≤−x.
	checkIntDecideTrue(t, "x≤|x|", intLeT(x, abs))
	// −x ≤ |x| : x≥0 branch −x≤x (0≤2x); x<0 branch −x≤−x.
	checkIntDecideTrue(t, "−x≤|x|", intLeT(intNegT(x), abs))
	// &0 ≤ |x| + |x| : both atoms split; each nonneg.
	checkIntDecideTrue(t, "0≤|x|+|x|", intLeT(intLit(0), intPlusT(abs, abs)))
}

func TestIntAbs_DecidesFalse(t *testing.T) {
	x := intVar("x")
	abs := intAbsT(x)

	// |x| < &0 is false: ¬(|x|<0) ⇐ 0≤|x| (the split), so it decides ⊥.
	w := IntArithDecide(intLtT(abs, intLit(0)))
	if w == nil {
		t.Fatalf("IntArithDecide(|x|<&0) = nil, want ⊥")
	}
	if !prop.Rhs(w).Equals(prop.F) {
		t.Errorf("IntArithDecide(|x|<&0) → %v, want ⊥", prop.Rhs(w))
	}
}

// Formula-level int bool split (int_split.go) and int equality-hyp
// substitution into opaque atoms (int.go).

func TestIntArithBool_ClosesGoals(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	// trichotomy: (x<y) ∨ (x=y) ∨ (y<x)
	checkIntDecideTrue(t, "trichotomy", or(intLtT(x, y), or(eqT(x, y), intLtT(y, x))))
	// antisymmetry as iff: (x≤y ∧ y≤x) ⇔ (x=y)   (⇔ is `=` at bool)
	checkIntDecideTrue(t, "antisym-iff",
		eqT(prop.And(intLeT(x, y), intLeT(y, x)), eqT(x, y)))
	// contingent implication-in-disjunction: (x≤y ⇒ x≤z) ∨ (z<y)
	checkIntDecideTrue(t, "imp-in-or",
		or(imply(intLeT(x, y), intLeT(x, z)), intLtT(z, y)))
}

func TestIntEqHypSubst(t *testing.T) {
	x := intVar("x")
	// x = &3 ⊢ int_abs x = &3 : subst into the opaque int_abs atom, then it folds.
	checkIntDecideTrueH(t, "eqsubst-abs", eqT(intAbsT(x), intLit(3)), eqT(x, intLit(3)))
	// x = &5 ⊢ int_max x &3 = &5
	checkIntDecideTrueH(t, "eqsubst-max",
		eqT(intMaxT(x, intLit(3)), intLit(5)), eqT(x, intLit(5)))
}

// TestIntCoeffEqSubst: a coefficient-equality hyp `c·x = k` (c∣k) is SOLVED to
// `x = &(k/c)` (the SAT dual of the GCD-eq test, via discreteness) and then
// substituted into an opaque/nonlinear atom — the gap intEqHypSubst leaves.
func TestIntCoeffEqSubst(t *testing.T) {
	x := intVar("x")
	xx := intStarT(x, x)
	// 2x = 4 ⊢ x·x = 4  (solve x=2, fold the nonlinear product).
	checkIntDecideTrueH(t, "2x=4⊢x²=4", eqT(xx, intLit(4)), eqT(intStarT(intLit(2), x), intLit(4)))
	// 6x = 12 ⊢ x·x = 4
	checkIntDecideTrueH(t, "6x=12⊢x²=4", eqT(xx, intLit(4)), eqT(intStarT(intLit(6), x), intLit(12)))
	// 2x = 4 ⊢ |x| = 2  (solve, then abs)
	checkIntDecideTrueH(t, "2x=4⊢|x|=2", eqT(intAbsT(x), intLit(2)), eqT(intStarT(intLit(2), x), intLit(4)))
}

// TestIntRingFull: the full multivariate ℤ ring (IntRingProveFull) — the int twin
// of TestRingProveFull. Closes nonlinear polynomial equalities (commutativity,
// distribution, the (x+y)² expansion) that the linear IntRingProve cannot, and is
// reachable end-to-end through the `arith` decide leaf. Unequal polys decline.
func TestIntRingFull(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	two := intLit(2)
	mul, add := intStarT, intPlusT
	equal := []struct {
		name string
		l, r Term
	}{
		{"comm", mul(x, y), mul(y, x)},
		{"ldistrib", mul(x, add(y, z)), add(mul(x, y), mul(x, z))},
		{"rdistrib", mul(add(x, y), z), add(mul(x, z), mul(y, z))},
		// (x+y)·(x+y) = (x·x + 2·(x·y)) + y·y
		{"square", mul(add(x, y), add(x, y)),
			add(add(mul(x, x), mul(two, mul(x, y))), mul(y, y))},
	}
	for _, p := range equal {
		w, ok := IntRingProveFull(p.l, p.r)
		if !ok {
			t.Errorf("%s: IntRingProveFull(%v, %v) declined", p.name, p.l, p.r)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(p.l) || !prop.Rhs(w).AlphaEquals(p.r) {
			t.Errorf("%s: proof shape is %v = %v, want %v = %v", p.name, prop.Lhs(w), prop.Rhs(w), p.l, p.r)
		}
		// reachable end-to-end through the `arith` decide leaf (hyp-free).
		checkIntDecideTrue(t, p.name+"/decide", eqT(p.l, p.r))
	}
	// unequal polynomials must decline (the ⊥ side is linarith's job, not ring's).
	if _, ok := IntRingProveFull(mul(x, y), mul(x, z)); ok {
		t.Error("closed x·y = x·z")
	}
	if _, ok := IntRingProveFull(mul(add(x, y), add(x, y)), add(mul(x, x), mul(y, y))); ok {
		t.Error("closed (x+y)² = x²+y² (missing 2xy)")
	}
}

// TestLexicalArithPolicySurvivesBoolSplitRecursion pins the mixed-domain shape
// used by DivByOne / RemByOne. The nat bool leaf recurses through the shared
// collapse rewrite; that recursion must retain Int=false instead of falling
// back to the process-global legacy policy and simplifying the int atom.
func TestLexicalArithPolicySurvivesBoolSplitRecursion(t *testing.T) {
	SetIntLemmaBundle(&IntLemmaBundle{})
	t.Cleanup(func() { SetIntLemmaBundle(nil) })

	natTrue := lt(Numeral(0), Numeral(1))
	intTrue := intLtT(intLit(0), intLit(1))
	mixed := eqT(natTrue, intTrue)

	w := NewArithCtxWithPolicy([]Term{mixed}, ArithPolicy{Nat: true}, nil).DecideExcept(0, mixed)
	if w == nil {
		t.Fatal("nat-only policy did not simplify the nat side of mixed iff")
	}
	if got := prop.Rhs(w); !got.AlphaEquals(intTrue) {
		t.Fatalf("nat-only policy escaped during recursive collapse: got %v, want %v", got, intTrue)
	}
}

// TestIntOfNumCollapse: the int_of_num homomorphism collapse (int.go).
// `&n` with n a num VARIABLE is opaque to linarith/ring, but a tree of `&`-images
// collapses to `&(num expr)` via OfNumAdd/OfNumMul + the neg lemmas, and a
// nonnegative comparison drops to num. Closes the homomorphism `&n·&n = &(n·n)`
// and `&0 ≤ &n·&n` (the post-Image-split branch shape of `&0 ≤ x·x`).
func TestIntOfNumCollapse(t *testing.T) {
	m, n := numVar("m"), numVar("n")
	amp := intOfNumT // &·
	mul, add := intStarT, intPlusT
	neg := intNegT
	// equalities: both sides collapse to the same signed image.
	checkIntDecideTrue(t, "homo-mul", eqT(mul(amp(m), amp(n)), amp(star(m, n))))             // &m·&n = &(m·n)
	checkIntDecideTrue(t, "homo-add", eqT(add(amp(m), amp(n)), amp(plus(m, n))))             // &m+&n = &(m+n)
	checkIntDecideTrue(t, "square", eqT(mul(amp(n), amp(n)), amp(star(n, n))))               // &n·&n = &(n·n)
	checkIntDecideTrue(t, "neg-cancel", eqT(mul(neg(amp(n)), neg(amp(n))), amp(star(n, n)))) // (−&n)·(−&n) = &(n·n)
	checkIntDecideTrue(t, "neg-mul", eqT(mul(neg(amp(m)), amp(n)), neg(amp(star(m, n)))))    // (−&m)·&n = −&(m·n)
	// inequality: nonnegative product drops to the num `0 ≤ n·n` (default-nonneg).
	checkIntDecideTrue(t, "sq-nonneg", intLeT(intLit(0), mul(amp(n), amp(n)))) // &0 ≤ &n·&n
	checkIntDecideTrue(t, "le-homo", intLeT(amp(m), add(amp(m), amp(n))))      // &m ≤ &m+&n
	// negative-sided comparison currently declines (left for future work): a
	// direct intProveOfNum call returns false, not a wrong proof.
	if _, ok := intProveOfNum(intLeT(neg(amp(n)), amp(m))); ok {
		t.Error("intProveOfNum closed a negative-sided comparison (−&n ≤ &m) — not yet supported")
	}
}

// TestIntImageSquare: the Image sign split (int.go) closes the headline
// sign-dependent goal `&0 ≤ x·x` (SquareNonneg) — split x = ±&n via Image
// (∃-elimination), each branch `&0 ≤ (±&n)·(±&n)` flowing through the of_num collapse to
// the num `0 ≤ n·n`. The conclusion is the original goal (hyp-free).
func TestIntImageSquare(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	checkIntDecideTrue(t, "0≤x²", intLeT(intLit(0), intStarT(x, x)))                              // &0 ≤ x·x
	checkIntDecideTrue(t, "0≤(xy)²", intLeT(intLit(0), intStarT(intStarT(x, y), intStarT(x, y)))) // &0 ≤ (x·y)²
	// the split is hyp-free and lands the exact goal: drive intImageSplit directly.
	w, ok := intImageSplit(nil, intLeT(intLit(0), intStarT(x, x)))
	if !ok {
		t.Fatal("intImageSplit declined &0 ≤ x·x")
	}
	if !w.Conclusion().AlphaEquals(intLeT(intLit(0), intStarT(x, x))) {
		t.Errorf("conclusion = %v, want &0 ≤ x·x", w.Conclusion())
	}
}

// TestIntDivides: the int_divides handlers (intDividesGoal, intDividesSkolem). A GOAL closes by an
// ∃-witness (literal quotient / syntactic d·t); a contradictory divisibility HYP
// (`2∣1`, impossible) drives any goal via the gcd-equality test (2z=1, gcd 2∤1).
func TestIntDivides(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	two, six, one, three := intLit(2), intLit(6), intLit(1), intLit(3)

	// GOAL through the full `arith` decide: 2 ∣ 6 (witness &3), 2 ∣ 2·x (syntactic).
	checkIntDecideTrue(t, "2∣6", intDividesT(two, six))
	checkIntDecideTrue(t, "2∣2x", intDividesT(two, intStarT(two, x)))
	// 2 ∣ 3 has no integer witness → must NOT close.
	if w := IntArithDecide(intDividesT(two, three)); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Error("closed 2 ∣ 3 (false)")
	}
	// HYP through the full decide: `2∣1` is contradictory, so {2∣1} ⊢ x≤y closes by
	// ex falso (the skolemized `&1 = &2·z₀` is `2z₀ = 1`, gcd 2 ∤ 1, refuted).
	checkIntDecideTrueH(t, "2∤1⊢x≤y", intLeT(x, y), intDividesT(two, one))
	// conclusion exactness (the goal handler lands the divisibility verbatim).
	if w, ok := intDividesGoal(intDividesT(two, six)); !ok || !w.Conclusion().AlphaEquals(intDividesT(two, six)) {
		t.Errorf("2∣6 direct: ok=%v concl=%v", ok, w)
	}
	// PARITY: `2∣x ∧ 2∣(x+1)` is contradictory (consecutive integers can't both be
	// even). Skolemize both → `x=2z₀ ∧ x+1=2w₀`, cross-hyp eliminate x (int.go)
	// → `2z₀+1 = 2w₀` → gcd 2∤1 → ⊥, so it proves x≤y by ex falso.
	checkIntDecideTrueH(t, "2∣x∧2∣(x+1)⊢x≤y", intLeT(x, y),
		intDividesT(two, x), intDividesT(two, intPlusT(x, one)))
}

// TestIntDividesSkolem_PinUnused: div/abs/int_gcd goals with a residual divides
// hyp (`gcd ∣ abs(m·n) ⊢ abs(m·n) = gcd · int_div(abs(m·n), gcd)`).
// intDividesSkolem skolemizes the divides hyp to the pin `abs = gcd·ν0`, but the
// inner decide's int_div/int_rem enrichment closes the goal directly from the
// divides hyp without consuming the pin. A discharge fold that called chooseElim
// strictly on a pin-free branch proof would panic in DeriveTrans's HasHyp assert
// ("Should not happen."). chooseElim's pin-unused tolerance returns the v-free
// branch unchanged (sound: v is fresh so pin-free ⇒ v-free), and the goal
// closes cleanly. A branch proof still mentioning ν (a genuinely deformed pin)
// falls through to the strict path and stays loud.
func TestIntDividesSkolem_PinUnused(t *testing.T) {
	m, n := intVar("m"), intVar("n")
	x, y := intVar("x"), intVar("y")

	// int_gcd and int_lcm take a pair(int,int) argument — construct the const at
	// the concrete pair type. Not exposed by domain.go (the linarith surface
	// doesn't touch gcd/lcm terms), so wire it up locally.
	pairII := ext.MakeProdType(dsl.IntType, dsl.IntType)
	commaII := ext.Const(ext.CommaConstMeta,
		ext.MakeFun(dsl.IntType, ext.MakeFun(dsl.IntType, pairII)))
	gcdC := ext.Const(core.MakeConstMeta("int_gcd", ext.MakeFun(pairII, dsl.IntType)),
		ext.MakeFun(pairII, dsl.IntType))
	lcmC := ext.Const(core.MakeConstMeta("int_lcm", ext.MakeFun(pairII, dsl.IntType)),
		ext.MakeFun(pairII, dsl.IntType))

	pairMN := ext.Apply(commaII, m, n)
	gcd := ext.Apply(gcdC, pairMN)
	lcm := ext.Apply(lcmC, pairMN)
	abs := intAbsT(intStarT(m, n))
	divAbsGcd := intDivT(abs, gcd)

	// Faithful hyp/goal shapes from the fault report (the session proving int_div_rem.GcdTimesLcm).
	hyps := []Term{
		not(eqT(intStarT(m, n), intLit(0))),
		eqT(lcm, divAbsGcd),
		intDividesT(gcd, abs),
		and(and(and(
			eqT(gcd, intPlusT(intStarT(m, x), intStarT(n, y))),
			intDividesT(gcd, m)),
			intDividesT(gcd, n)),
			intLeT(intLit(0), gcd)),
	}
	goal := eqT(abs, intStarT(gcd, divAbsGcd))

	// Surgical: intDividesSkolem directly on the pre-simplified hyps ArithCtx.Decide
	// would feed it — this is the exact call the ENGINE-FAULT stack trace terminated
	// at. Verify no panic + the returned proof's contract (conclusion = goal,
	// hyps ⊆ inputs). Fast (~100ms); avoids the full deep+fixpoint decide's
	// sign-split / bounded-enum exploration that the public path adds around it.
	ctx := NewArithCtx(hyps)
	w, ok := intDividesSkolem(ctx.simplifiedHyps, goal)
	if !ok || w == nil {
		t.Fatalf("intDividesSkolem declined (ok=%v); expected a close via the int_div/int_rem enrichment", ok)
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("conclusion mismatch: got %v, want %v", w.Conclusion(), goal)
	}
	for h := range w.HypIter() {
		if !slices.ContainsFunc(ctx.simplifiedHyps, h.AlphaEquals) {
			t.Errorf("leaked hyp not among inputs: %v", h)
		}
	}
}

// TestIntElimEq: the cross-hyp equality elimination (int.go) on its own —
// two equalities sharing a variable combine so the gcd test sees the eliminated
// form. The Gaussian step the goal-only eq-subst cannot do.
func TestIntElimEq(t *testing.T) {
	x, y, a, b := intVar("x"), intVar("y"), intVar("a"), intVar("b")
	two := intLit(2)
	// {x=2a, x+1=2b} is ℤ-contradictory (eliminate x → 2b−2a=1, gcd 2∤1).
	checkIntDecideTrueH(t, "{x=2a,x+1=2b}⊢x≤y", intLeT(x, y),
		eqT(x, intStarT(two, a)), eqT(intPlusT(x, intLit(1)), intStarT(two, b)))
}

// TestIntElimEq_BranchWitnessWithoutCut: a goal of int_div_rem.DivLessIff's shape whose
// branch witness does not consume the Gaussian cut.
// intElimEqHyps hands the goal to the branch decider with the substituted copy
// hSub appended, but the branch's composed eq-subst leaves (intEqHypSubst /
// intCoeffEqSubst) can close the goal from the ORIGINAL hyps alone — here by
// substituting `a → &n0` into the goal and collapsing the of-num identity — so
// the witness never assumes hSub. An unconditional
// `hSubProof.DeriveTrans(iffTrueElim(w))` would trip DeriveTrans's strict
// hyp-membership assert there. Minimal trigger: an eliminable eq hyp, a second
// equality containing its variable (content irrelevant — it only opens the
// elimEq loop), and a goal closable only via goal-side eq-subst (which the
// atom-prover ladder lacks, so the ladder falls through to intElimEqHyps).
func TestIntElimEq_BranchWitnessWithoutCut(t *testing.T) {
	n0, n1, n2 := numVar("n0"), numVar("n1"), numVar("n2")
	a, b := intVar("a"), intVar("b")
	eqA := eqT(a, intOfNumT(n0))                                     // a = &n0 (the eliminable eq)
	otherEq := eqT(intPlusT(a, b), intOfNumT(n1))                    // a + b = &n1 (opens the elimEq loop)
	goal := eqT(intStarT(a, intOfNumT(n2)), intOfNumT(star(n0, n2))) // a·&n2 = &(n0·n2)

	// The exact call the engine's unified int decide leaf makes (the live panic
	// frame): it must DECIDE — the elimEq branch witness is sound whether or
	// not it consumed the cut.
	pf, ok := intProveDecAtomNoSignSplit(slices.Values([]Term{eqA, otherEq}), goal)
	if !ok || pf == nil {
		t.Fatalf("intProveDecAtomNoSignSplit({a=&n0, a+b=&n1}, a·&n2=&(n0·n2)) declined, want proved")
	}
	if !pf.Conclusion().AlphaEquals(goal) {
		t.Errorf("proved %v, want %v", pf.Conclusion(), goal)
	}

	// Public surface: the full decide collapses the goal to ⊤ under the hyps.
	checkIntDecideTrueH(t, "unused-cut", goal, eqA, otherEq)

	// The capability asymmetry that routes this shape through intElimEqHyps in
	// the first place: without the second equality the elimEq loop has no
	// candidate, and the atom ladder alone (no goal-side eq-subst) declines.
	if _, ok := intProveDecAtomNoSignSplit(slices.Values([]Term{eqA}), goal); ok {
		t.Logf("note: atom ladder now closes the shape without elimEq — this test no longer exercises the unused-cut path; refresh the trigger")
	}
}

// int_pow literal-exponent unfold (int.go) and two-sided bounded
// enumeration (int.go).

func TestIntPow_AutoSimp(t *testing.T) {
	x := intVar("x")
	// c ≤ 1 auto-folds inside the decider: int_pow x 0 → &1, int_pow x 1 → x.
	checkIntDecideTrue(t, "pow0", eqT(intPowT(x, Numeral(0)), intLit(1)))
	checkIntDecideTrue(t, "pow1", eqT(intPowT(x, Numeral(1)), x))
}

func TestIntPow_Expand(t *testing.T) {
	x := intVar("x")
	// Variable base: the unfold is a valid kernel equality with LHS = int_pow x 2
	// and a product-chain RHS.
	w := ExpandIntPowRewrite()(intPowT(x, Numeral(2)))
	if w == nil || !prop.Lhs(w).AlphaEquals(intPowT(x, Numeral(2))) {
		t.Fatalf("ExpandIntPowRewrite(int_pow x 2) = %v, want an int_pow x 2 = … equality", w)
	}
	// And `int_pow x 2 = x·x` CLOSES for a variable base via expand-then-decide: the
	// `&1`-fold + reflexivity, no nonlinear ring needed (only AC-reassociation of a
	// nonlinear product would need the multivariate ring int lacks).
	for _, c := range []struct {
		exp uint64
		rhs Term
	}{{2, intStarT(x, x)}, {3, intStarT(x, intStarT(x, x))}} {
		g := eqT(intPowT(x, Numeral(c.exp)), c.rhs)
		ew := ExpandIntPowRewrite()(g)
		if ew == nil {
			t.Fatalf("expand(int_pow x %d = …) = nil", c.exp)
		}
		dec := IntArithDecide(prop.Rhs(ew))
		if dec == nil || !prop.Rhs(dec).Equals(prop.T) {
			t.Errorf("int_pow x %d = (matching chain) did not decide ⊤ (got %v)", c.exp, dec)
		}
	}
	// Concrete base: expand-then-decide evaluates int_pow &3 2 to &9 and int_pow &2 3
	// to &8 — the literal product chain folds through the int numeral simps.
	for _, c := range []struct {
		base, exp, val uint64
	}{{3, 2, 9}, {2, 3, 8}, {5, 0, 1}} {
		g := eqT(intPowT(intLit(c.base), Numeral(c.exp)), intLit(c.val))
		ew := ExpandIntPowRewrite()(g) // ⊢ g = g'  (the int_pow atom unfolded)
		if ew == nil {
			t.Fatalf("expand(&%d pow %d) = nil", c.base, c.exp)
		}
		dec := IntArithDecide(prop.Rhs(ew)) // ⊢ g' = ⊤
		if dec == nil || !prop.Rhs(dec).Equals(prop.T) {
			t.Errorf("&%d pow %d = &%d did not evaluate (got %v)", c.base, c.exp, c.val, dec)
		}
	}
}

func TestIntBoundedEnum(t *testing.T) {
	x := intVar("x")
	xx := intStarT(x, x) // nonlinear, opaque to linarith
	// &0 ≤ x, x ≤ &2 ⊢ x·x ≤ &4  (enumerate x ∈ {0,1,2}: 0,1,4 all ≤ 4).
	checkIntDecideTrueH(t, "x²≤4", intLeT(xx, intLit(4)),
		intLeT(intLit(0), x), intLeT(x, intLit(2)))
	// &1 ≤ x, x ≤ &3 ⊢ &1 ≤ x·x  (enumerate 1,2,3: 1,4,9 all ≥ 1).
	checkIntDecideTrueH(t, "1≤x²", intLeT(intLit(1), xx),
		intLeT(intLit(1), x), intLeT(x, intLit(3)))
}

// Monotone scaling + sign-of-product (int.go): a nonlinear `c·a ⋈ c·b`
// or `&0 ≤ x·y` whose sign/order side conditions come from the hyps. The linear
// core atomizes the products; this handler applies LessEqMulLeft / LessThanMulLeft /
// LessEqMul with a symbolic multiplier. Placeholder-backed; the composition
// (the lemma application + commute) is real kernel work.
func TestIntMonotone_Scaling(t *testing.T) {
	a, b, c := intVar("a"), intVar("b"), intVar("c")
	aLeB := intLeT(a, b)
	zeroLeC := intLeT(intLit(0), c)

	// left factor: a≤b ∧ &0≤c ⊢ c·a ≤ c·b.
	intDecidesTrue(t, "a≤b,0≤c⊢ca≤cb", intLeT(intStarT(c, a), intStarT(c, b)), aLeB, zeroLeC)
	// right factor (via commute): a≤b ∧ &0≤c ⊢ a·c ≤ b·c.
	intDecidesTrue(t, "a≤b,0≤c⊢ac≤bc", intLeT(intStarT(a, c), intStarT(b, c)), aLeB, zeroLeC)

	// strict: a<b ∧ &0<c ⊢ c·a < c·b.
	intDecidesTrue(t, "a<b,0<c⊢ca<cb", intLtT(intStarT(c, a), intStarT(c, b)),
		intLtT(a, b), intLtT(intLit(0), c))

	// sanity: WITHOUT the `&0 ≤ c` hyp, `c·a ≤ c·b` must NOT decide ⊤ (it is not a
	// theorem — c could be negative).
	if w := IntArithDecideWithHyps([]Term{aLeB})(intLeT(intStarT(c, a), intStarT(c, b))); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("c·a≤c·b without &0≤c must NOT decide ⊤")
	}
}

func TestIntMonotone_ProductNonneg(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	// &0≤x ∧ &0≤y ⊢ &0 ≤ x·y  (LessEqMul; distinct vars, so NOT the Image
	// square case).
	intDecidesTrue(t, "0≤x,0≤y⊢0≤xy", intLeT(intLit(0), intStarT(x, y)),
		intLeT(intLit(0), x), intLeT(intLit(0), y))

	// sanity: WITHOUT the sign hyps, `&0 ≤ x·y` must NOT decide ⊤ (a bare product
	// of unconstrained ints is not nonneg).
	if w := IntArithDecideWithHyps(nil)(intLeT(intLit(0), intStarT(x, y))); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("&0≤x·y without sign hyps must NOT decide ⊤")
	}
}

// The sign-known product fragment beyond the both-nonneg LessEqMul case —
// strict products (MulPos), the both-negative and sign-mixed combinations (via the
// negation reduction in intProveSignedProduct), and the two-sided product
// bound (derived from monotone scaling + transitivity).
func TestIntMonotone_SignOfProduct(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	xy := intStarT(x, y)
	z := intLit(0)

	// strict, both positive: &0<x ∧ &0<y ⊢ &0 < x·y  (MulPos).
	intDecidesTrue(t, "0<x,0<y⊢0<xy", intLtT(z, xy), intLtT(z, x), intLtT(z, y))

	// both negative → nonneg: x≤&0 ∧ y≤&0 ⊢ &0 ≤ x·y  (reduces to LessEqMul on (−x,−y)).
	intDecidesTrue(t, "x≤0,y≤0⊢0≤xy", intLeT(z, xy), intLeT(x, z), intLeT(y, z))
	// both negative → strict: x<&0 ∧ y<&0 ⊢ &0 < x·y.
	intDecidesTrue(t, "x<0,y<0⊢0<xy", intLtT(z, xy), intLtT(x, z), intLtT(y, z))

	// sign-mixed → nonpositive: x≤&0 ∧ &0≤y ⊢ x·y ≤ &0  (negate x, flip).
	intDecidesTrue(t, "x≤0,0≤y⊢xy≤0", intLeT(xy, z), intLeT(x, z), intLeT(z, y))
	// sign-mixed (other side): &0≤x ∧ y≤&0 ⊢ x·y ≤ &0  (negate y, flip).
	intDecidesTrue(t, "0≤x,y≤0⊢xy≤0", intLeT(xy, z), intLeT(z, x), intLeT(y, z))
	// sign-mixed strict: x<&0 ∧ &0<y ⊢ x·y < &0.
	intDecidesTrue(t, "x<0,0<y⊢xy<0", intLtT(xy, z), intLtT(x, z), intLtT(z, y))

	// sanity: x≤&0 ∧ &0≤y ⊢ &0 ≤ x·y is FALSE (x=−1,y=1 ⇒ xy=−1); must NOT decide ⊤.
	if w := IntArithDecideWithHyps([]Term{intLeT(x, z), intLeT(z, y)})(intLeT(z, xy)); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("x≤0,0≤y⊢0≤xy must NOT decide ⊤ (counterexample x=−1,y=1)")
	}
}

func TestIntMonotone_TwoSided(t *testing.T) {
	a, b, c, d := intVar("a"), intVar("b"), intVar("c"), intVar("d")
	z := intLit(0)
	// &0≤a ∧ a≤b ∧ &0≤c ∧ c≤d ⊢ a·c ≤ b·d   (derived).
	intDecidesTrue(t, "0≤a,a≤b,0≤c,c≤d⊢ac≤bd", intLeT(intStarT(a, c), intStarT(b, d)),
		intLeT(z, a), intLeT(a, b), intLeT(z, c), intLeT(c, d))

	// sanity: WITHOUT the `&0≤a` / `&0≤c` lower bounds the handler must decline
	// (a=−2,b=1,c=−2,d=1 ⇒ ac=4 > bd=1). Checked at the handler (not the full
	// decider, which would fall through to the expensive nonlinear search before
	// also declining).
	if _, ok := intProveProductMul2([]Term{intLeT(a, b), intLeT(c, d)}, a, c, b, d); ok {
		t.Errorf("a≤b,c≤d⊢ac≤bd without lower bounds must NOT prove via intProveProductMul2")
	}
}

// B2: the integral-domain (MulEqZero — ℤ has no zero divisors) reasoning the
// Image sign split feeds — `x·y=&0 ⇒ x=&0∨y=&0` (and the square collapse
// `x·x=&0 ⊢ x=&0`), plus strict square positivity `x≠&0 ⊢ &0<x·x`.
func TestIntMulEqZero(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	z := intLit(0)
	xx, xy := intStarT(x, x), intStarT(x, y)

	// square collapse: x·x=&0 ⊢ x=&0 (the (p∨p)⇔p forward path).
	intDecidesTrue(t, "x·x=&0 ⊢ x=&0", eqT(x, z), eqT(xx, z))
	// distinct factors with one nonzero: x·y=&0, x≠&0 ⊢ y=&0 (the splittable hyp).
	intDecidesTrue(t, "x·y=&0,x≠&0 ⊢ y=&0", eqT(y, z), eqT(xy, z), not(eqT(x, z)))
	// the bare disjunction goal: x·y=&0 ⊢ x=&0 ∨ y=&0.
	intDecidesTrue(t, "x·y=&0 ⊢ x=&0∨y=&0", or(eqT(x, z), eqT(y, z)), eqT(xy, z))

	// strict square positivity: x≠&0 ⊢ &0 < x·x.
	intDecidesTrue(t, "x≠&0 ⊢ &0<x·x", intLtT(z, xx), not(eqT(x, z)))

	// sanity: WITHOUT `x≠&0`, `&0 < x·x` must NOT decide ⊤ (x=&0 ⇒ x·x=&0).
	if w := IntArithDecideWithHyps(nil)(intLtT(z, xx)); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("&0<x·x without x≠&0 must NOT decide ⊤")
	}
	// sanity: x·y=&0 ⊢ x=&0 must NOT decide ⊤ (y could be &0 with x≠&0).
	if w := IntArithDecideWithHyps([]Term{eqT(xy, z)})(eqT(x, z)); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("x·y=&0 ⊢ x=&0 must NOT decide ⊤ (counterexample x=1,y=0)")
	}
}

// Signed multivariate ring (subneg.go mulSigned): subtraction/negation in
// NONLINEAR position. The signed normalizer FOILs `(Px+−Nx)·(Py+−Ny)` into a
// canonical `P + (−N)` (positive full polynomials), so moveAcrossCmp positivizes a
// nonlinear-with-sub equality and the existing full ring closes it. Placeholder-
// backed; a misaligned FOIL EqTrans would panic at construction, so green = sound.

func TestIntSignedPoly(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	xx, yy, xy := intStarT(x, x), intStarT(y, y), intStarT(x, y)

	// (x−y)·(x−y) = x·x + y·y − &2·(x·y)   — the square of a difference.
	lhsSq := intStarT(intSubT(x, y), intSubT(x, y))
	rhsSq := intSubT(intPlusT(xx, yy), intStarT(intLit(2), xy))
	intDecidesTrue(t, "(x−y)² = x²+y²−2xy", eqT(lhsSq, rhsSq))
	// (int_pow form `(x−y)^2` composes too, but the c≥2 unfold is agent-driven —
	// `expand_exp` then `arith` — so it is not exercised by the always-on decider.)

	// difference of squares: (a−b)·(a+b) = a·a − b·b  (one side has an EMPTY N).
	a, b := intVar("a"), intVar("b")
	lhsDs := intStarT(intSubT(a, b), intPlusT(a, b))
	rhsDs := intSubT(intStarT(a, a), intStarT(b, b))
	intDecidesTrue(t, "(a−b)(a+b) = a²−b²", eqT(lhsDs, rhsDs))

	// (x+y)·(x−y) = x·x − y·y  (sub on the right factor).
	intDecidesTrue(t, "(x+y)(x−y) = x²−y²", eqT(intStarT(intPlusT(x, y), intSubT(x, y)), intSubT(xx, yy)))

	// negation in nonlinear position: (−x)·(−x) = x·x.
	intDecidesTrue(t, "(−x)(−x) = x²", eqT(intStarT(intNegT(x), intNegT(x)), xx))

	// sanity: a WRONG expansion must NOT decide ⊤ (missing the −2xy cross term).
	if w := IntArithDecideWithHyps(nil)(eqT(lhsSq, intPlusT(xx, yy))); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("(x−y)² = x²+y² (no cross term) must NOT decide ⊤")
	}
}

// IntOfRealThm tests — validate the lift's TRANSFORMATION logic with fabricated
// (core.TestThm) homomorphism bridges and a fabricated theorem over ℝ. No real
// proofs and no replay: the kernel makes any produced Thm sound by construction,
// so the only thing to check is that the output is the intended statement over ℤ
// (Conclusion().AlphaEquals) with no stray hypotheses. This is exactly how a
// future InstallIntBundle would validate IntOfRealThm against the real bundle.

// fakeThm wraps a statement as a (test-only) theorem — the bridge/real material.
func fakeThm(stmt Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(stmt)) }

// fullBridges builds the LINEAR-fragment bridge set in the stated orientation
// (defined-int-side = real-side), the shape IntOfRealThm GSYMs internally.
func fullBridges() *IntBridges {
	x, y := intVar("x"), intVar("y")
	n := numVar("n")
	rox, roy := realOfIntT(x), realOfIntT(y)
	return &IntBridges{
		// (x ⋈_int y) ⇔ (real_of_int x ⋈_real real_of_int y)
		Le: fakeThm(ext.ForAll(x, y)(eqT(intLeT(x, y), realLeT(rox, roy)))),
		Lt: fakeThm(ext.ForAll(x, y)(eqT(intLtT(x, y), realLtT(rox, roy)))),
		Eq: fakeThm(ext.ForAll(x, y)(eqT(eqT(x, y), eqT(rox, roy)))),
		// real_of_int(int_of_num n) = real_of_num n
		OfNum: fakeThm(ext.ForAll(n)(eqT(realOfIntT(intOfNumT(n)), realOfNumT(n)))),
		// real_of_int(x ⋆_int y) = real_of_int x ⋆_real real_of_int y
		Add: fakeThm(ext.ForAll(x, y)(eqT(realOfIntT(intPlusT(x, y)), realPlusT(rox, roy)))),
		Mul: fakeThm(ext.ForAll(x, y)(eqT(realOfIntT(intStarT(x, y)), realStarT(rox, roy)))),
	}
}

func checkIntOfReal(t *testing.T, name string, realThm *prop.PropWrapper, want Term) {
	t.Helper()
	got := IntOfRealThm(realThm, fullBridges())
	if got.NumHyps() != 0 {
		t.Errorf("%s: lifted theorem has %d stray hyp(s), want 0", name, got.NumHyps())
	}
	if !got.Conclusion().AlphaEquals(want) {
		t.Errorf("%s:\n  got  %s\n  want %s", name, ext.PrintTerm(got.Conclusion()), ext.PrintTerm(want))
	}
}

func TestIntOfRealThm(t *testing.T) {
	ra, rb, rc, rd := realVar("a"), realVar("b"), realVar("c"), realVar("d")
	rx, ry := realVar("x"), realVar("y")
	ia, ib, ic, id := intVar("a"), intVar("b"), intVar("c"), intVar("d")
	ix, iy := intVar("x"), intVar("y")

	cases := []struct {
		name string
		real Term // the statement over ℝ
		want Term // the expected statement over ℤ
	}{
		{
			// reflexivity of ≤: ∀x. x ≤ x   →   ∀x:int. int_le(x, x)
			"le_refl",
			ext.ForAll(rx)(realLeT(rx, rx)),
			ext.ForAll(ix)(intLeT(ix, ix)),
		},
		{
			// ℝ's MulSym: ∀x y. x·y = y·x   →   ∀x y:int. int_mul(x,y) = int_mul(y,x)
			"mul_sym",
			ext.ForAll(rx, ry)(eqT(realStarT(rx, ry), realStarT(ry, rx))),
			ext.ForAll(ix, iy)(eqT(intStarT(ix, iy), intStarT(iy, ix))),
		},
		{
			// ℝ's LessEqAdd2: ∀a b c d. a≤b ⇒ c≤d ⇒ a+c ≤ b+d
			//   →  ∀a b c d:int. int_le(a,b) ⇒ int_le(c,d) ⇒ int_le(a+c, b+d)
			"le_add2",
			ext.ForAll(ra, rb, rc, rd)(imply(realLeT(ra, rb),
				imply(realLeT(rc, rd), realLeT(realPlusT(ra, rc), realPlusT(rb, rd))))),
			ext.ForAll(ia, ib, ic, id)(imply(intLeT(ia, ib),
				imply(intLeT(ic, id), intLeT(intPlusT(ia, ic), intPlusT(ib, id))))),
		},
		{
			// literal + op + comparison: ∀x. x ≤ x + &1
			//   →  ∀x:int. int_le(x, int_add(x, int_of_num 1))
			"le_succ",
			ext.ForAll(rx)(realLeT(rx, realPlusT(rx, realLit(1)))),
			ext.ForAll(ix)(intLeT(ix, intPlusT(ix, intLit(1)))),
		},
		{
			// nested ops + literal: ∀x y. &2·x + y = y + &2·x   (exercises mul, add, of_num, eq)
			"ring_eq",
			ext.ForAll(rx, ry)(eqT(
				realPlusT(realStarT(realLit(2), rx), ry),
				realPlusT(ry, realStarT(realLit(2), rx)))),
			ext.ForAll(ix, iy)(eqT(
				intPlusT(intStarT(intLit(2), ix), iy),
				intPlusT(iy, intStarT(intLit(2), ix)))),
		},
	}
	for _, tc := range cases {
		checkIntOfReal(t, tc.name, fakeThm(tc.real), tc.want)
	}
}

// TestIntOfRealThm_Conjunction exercises the conjunction recursion: a top-level
// conjunction is lifted conjunct-by-conjunct and rejoined.
func TestIntOfRealThm_Conjunction(t *testing.T) {
	rx := realVar("x")
	ix := intVar("x")
	// (∀x. x ≤ x) ∧ (∀x. x·x = x·x)
	real := prop.And(
		ext.ForAll(rx)(realLeT(rx, rx)),
		ext.ForAll(rx)(eqT(realStarT(rx, rx), realStarT(rx, rx))))
	want := prop.And(
		ext.ForAll(ix)(intLeT(ix, ix)),
		ext.ForAll(ix)(eqT(intStarT(ix, ix), intStarT(ix, ix))))
	got := IntOfRealThm(fakeThm(real), fullBridges())
	if got.NumHyps() != 0 {
		t.Errorf("conjunction: %d stray hyp(s), want 0", got.NumHyps())
	}
	if !got.Conclusion().AlphaEquals(want) {
		t.Errorf("conjunction:\n  got  %v\n  want %v", got.Conclusion(), want)
	}
}

// TestIntOfRealThm_CondPushThrough — the piecewise-def lift (the real_max /
// real_min / real_sgn definition shapes). The bridge set collapses real
// OPERATORS and COMPARISONS over embedded ints, but COND is polymorphic (no
// bridge row exists for it), so a piecewise source would stall mid-lift with
// real_of_int residue on the COND branches — `real_of_int(int_sgn x) =
// COND(g, real_of_int(&1), …)` — and the bundle-leaf α-match downstream
// would reject it. condPushRealOfInt (int_lemmas.go) is the generic COND
// homomorphism completion: real_of_int pushes out through COND, then the
// enclosing Eq bridge fires in the same fixpoint, so the lift lands in the
// exact piecewise-int leaf shape (what intSgnDef / intMaxDef / intMinDef
// α-match).
func TestIntOfRealThm_CondPushThrough(t *testing.T) {
	rx, ry := realVar("x"), realVar("y")
	ix, iy := intVar("x"), intVar("y")
	br := fullBridges()
	// The algebraic-unary bridges the piecewise defs collapse through, in the
	// standard orientation (embedded-int-op on the LHS — Max /
	// Min / Sgn; Neg as InstallIntBundle installs it post-flip).
	rox, roy := realOfIntT(ix), realOfIntT(iy)
	br.Max = fakeThm(ext.ForAll(ix, iy)(eqT(realOfIntT(intMaxT(ix, iy)), realMaxT(rox, roy))))
	br.Min = fakeThm(ext.ForAll(ix, iy)(eqT(realOfIntT(intMinT(ix, iy)), realMinT(rox, roy))))
	br.Sgn = fakeThm(ext.ForAll(ix)(eqT(realOfIntT(intSgnT(ix)), realSgnT(rox))))
	br.Neg = fakeThm(ext.ForAll(ix)(eqT(realOfIntT(intNegT(ix)), realNegT(rox))))

	cases := []struct {
		name string
		real Term // the piecewise definition statement over ℝ
		want Term // the piecewise-int leaf shape
	}{
		{
			// real_max def: ∀x y. real_max(x,y) = COND(x ≤ y, y, x)
			"max_def",
			ext.ForAll(rx, ry)(eqT(realMaxT(rx, ry), ext.Cond(realLeT(rx, ry), ry, rx))),
			ext.ForAll(ix, iy)(eqT(intMaxT(ix, iy), ext.Cond(intLeT(ix, iy), iy, ix))),
		},
		{
			// real_min def: ∀x y. real_min(x,y) = COND(x ≤ y, x, y)
			"min_def",
			ext.ForAll(rx, ry)(eqT(realMinT(rx, ry), ext.Cond(realLeT(rx, ry), rx, ry))),
			ext.ForAll(ix, iy)(eqT(intMinT(ix, iy), ext.Cond(intLeT(ix, iy), ix, iy))),
		},
		{
			// real_sgn def (NESTED COND + literals + neg):
			// ∀x. real_sgn x = COND(&0 < x, &1, COND(x < &0, −&1, &0))
			"sgn_def",
			ext.ForAll(rx)(eqT(realSgnT(rx),
				ext.Cond(realLtT(realLit(0), rx), realLit(1),
					ext.Cond(realLtT(rx, realLit(0)), realNegT(realLit(1)), realLit(0))))),
			ext.ForAll(ix)(eqT(intSgnT(ix),
				ext.Cond(intLtT(intLit(0), ix), intLit(1),
					ext.Cond(intLtT(ix, intLit(0)), intNegT(intLit(1)), intLit(0))))),
		},
	}
	for _, tc := range cases {
		checkIntOfReal2(t, tc.name, br, fakeThm(tc.real), tc.want)
	}
}

// checkIntOfReal2 is checkIntOfReal with an explicit bridge set.
func checkIntOfReal2(t *testing.T, name string, br *IntBridges, realThm *prop.PropWrapper, want Term) {
	t.Helper()
	got := IntOfRealThm(realThm, br)
	if got.NumHyps() != 0 {
		t.Errorf("%s: lifted theorem has %d stray hyp(s), want 0", name, got.NumHyps())
	}
	if !got.Conclusion().AlphaEquals(want) {
		t.Errorf("%s:\n  got  %s\n  want %s", name, ext.PrintTerm(got.Conclusion()), ext.PrintTerm(want))
	}
}

// TestIntOfRealThm_MissingBridge: with a bridge absent the lift does not fully
// collapse — the residual real operator remains, visible in the output statement
// (so the caller's shape check fails loudly rather than producing a wrong cert).
func TestIntOfRealThm_MissingBridge(t *testing.T) {
	rx, ry := realVar("x"), realVar("y")
	ix, iy := intVar("x"), intVar("y")
	br := fullBridges()
	br.Add = nil // drop the + homomorphism
	got := IntOfRealThm(fakeThm(
		ext.ForAll(rx, ry)(realLeT(realPlusT(rx, ry), realPlusT(ry, rx)))), br)
	// le collapses, but + does not, so the int statement is NOT reached.
	wantFull := ext.ForAll(ix, iy)(intLeT(intPlusT(ix, iy), intPlusT(iy, ix)))
	if got.Conclusion().AlphaEquals(wantFull) {
		t.Errorf("missing Add bridge should NOT yield the fully-collapsed int statement")
	}
}

func TestIntNormalizeProofPlumbing(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	m := func(c int64, a Term) Term { return intMonoTerm(integerOf(c), a) } // `&c * a`
	exprs := []Term{
		intLit(5),
		x,
		intPlusT(x, y),
		intPlusT(y, x),
		intPlusT(intPlusT(x, y), z),
		intPlusT(x, intPlusT(y, z)),
		intPlusT(x, x),
		intPlusT(m(2, x), m(3, x)),
		m(3, x),
		intStarT(x, intLit(3)),
		intStarT(intLit(2), intPlusT(x, y)),
		intPlusT(intStarT(intLit(2), intPlusT(x, y)), intLit(7)),
		intStarT(intLit(2), intStarT(intLit(3), x)),
		intPlusT(intLit(5), intLit(7)),
		intPlusT(intPlusT(m(2, x), m(4, y)), m(4, x)),
		intPlusT(intPlusT(x, intLit(3)), intPlusT(y, intLit(4))),
		intStarT(intLit(0), intPlusT(x, y)), // scale by 0 → &0
		intPlusT(intPlusT(z, y), x),         // reverse order, exercises bubbling
	}
	for _, e := range exprs {
		checkIntNormalize(t, e)
	}
}

// TestIntNormalizeProofProducts: a product of atoms expands over the monomial
// basis on the proof side too (intRing.normalizeProof's product branch,
// mirrored on intDomain.polyMul) — checkIntNormalize pins the lockstep. The
// broader pins are in int_poly_basis_test.go.
func TestIntNormalizeProofProducts(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	for _, e := range []Term{
		intStarT(x, y), intStarT(y, x), intStarT(intStarT(x, y), z),
		intPlusT(intMonoTerm(integerOf(2), intStarT(x, y)), intMonoTerm(integerOf(3), intStarT(y, x))),
	} {
		checkIntNormalize(t, e)
	}
}

func TestIntRingProve(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	m := func(c int64, a Term) Term { return intMonoTerm(integerOf(c), a) }
	pairs := []struct{ l, r Term }{
		{intPlusT(intPlusT(x, y), z), intPlusT(x, intPlusT(y, z))},
		{intPlusT(x, y), intPlusT(y, x)},
		{intStarT(intLit(2), intPlusT(x, y)), intPlusT(m(2, x), m(2, y))},
		{intPlusT(intPlusT(x, intLit(3)), intPlusT(y, intLit(4))), intPlusT(intPlusT(x, y), intLit(7))},
		{intPlusT(m(3, x), m(2, x)), m(5, x)},
		{intPlusT(x, x), m(2, x)},
		{x, intPlusT(m(1, x), intLit(0))},
		{intStarT(intPlusT(x, y), intLit(3)), intPlusT(m(3, x), m(3, y))},
		{intStarT(x, y), intStarT(y, x)}, // a product reads over the monomial basis
	}
	for _, p := range pairs {
		w, ok := IntRingProve(p.l, p.r)
		if !ok {
			t.Errorf("IntRingProve(%v, %v) declined", p.l, p.r)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(p.l) || !prop.Rhs(w).AlphaEquals(p.r) {
			t.Errorf("IntRingProve(%v,%v): proof is %v = %v", p.l, p.r, prop.Lhs(w), prop.Rhs(w))
		}
	}
	declines := []struct{ l, r Term }{
		{intPlusT(x, y), intPlusT(x, z)},
		{m(2, x), m(3, x)},
		{intStarT(x, y), intStarT(x, z)},
	}
	for _, p := range declines {
		if _, ok := IntRingProve(p.l, p.r); ok {
			t.Errorf("IntRingProve(%v, %v) should decline", p.l, p.r)
		}
	}
}

// TestIntRingBundleWiring installs the nine ring fields in their normal-form
// orientation (mirroring the real wiring test): most ℤ ring lemmas are stated
// REVERSED relative to the engine shapes, and RightDistrib binds (a, m, b)
// with m the shared factor. prop.Assume markers prove each leaf bound its field
// — in particular pinning intRightDistrib's [a, c, b] instAll permutation.
func TestIntRingBundleWiring(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	ForAll := ext.ForAll
	stmts := map[string]Term{
		"AddSym":   ForAll(x, y)(eqT(intPlusT(x, y), intPlusT(y, x))),
		"AddAssoc": ForAll(x, y, z)(eqT(intPlusT(x, intPlusT(y, z)), intPlusT(intPlusT(x, y), z))),
		"MulSym":   ForAll(x, y)(eqT(intStarT(x, y), intStarT(y, x))),
		"MulAssoc": ForAll(x, y, z)(
			eqT(intStarT(x, intStarT(y, z)), intStarT(intStarT(x, y), z))),
		"AddRightIdentity": ForAll(y)(eqT(y, intPlusT(y, intLit(0)))),
		"MulLeftIdentity":  ForAll(x)(eqT(x, intStarT(intLit(1), x))),
		"MulLeftZero":      ForAll(x)(eqT(intLit(0), intStarT(intLit(0), x))),
		"LeftDistrib": ForAll(x, y, z)(
			eqT(intPlusT(intStarT(x, y), intStarT(x, z)), intStarT(x, intPlusT(y, z)))),
		// ∀a m b. a·m + b·m = (a+b)·m — m (the shared factor) is the MIDDLE binder
		"RightDistrib": ForAll(x, y, z)(
			eqT(intPlusT(intStarT(x, y), intStarT(z, y)), intStarT(intPlusT(x, z), y))),
	}
	SetIntLemmaBundle(&IntLemmaBundle{
		AddSym: prop.Assume(stmts["AddSym"]), AddAssoc: prop.Assume(stmts["AddAssoc"]),
		MulSym: prop.Assume(stmts["MulSym"]), MulAssoc: prop.Assume(stmts["MulAssoc"]),
		AddRightIdentity: prop.Assume(stmts["AddRightIdentity"]), MulLeftIdentity: prop.Assume(stmts["MulLeftIdentity"]),
		MulLeftZero:  prop.Assume(stmts["MulLeftZero"]),
		LeftDistrib:  prop.Assume(stmts["LeftDistrib"]),
		RightDistrib: prop.Assume(stmts["RightDistrib"]),
	})
	t.Cleanup(func() { SetIntLemmaBundle(nil) })

	a, b, c := intVar("a"), intVar("b"), intVar("c")
	cases := []struct {
		name   string
		run    func() *prop.PropWrapper
		want   Term
		marker Term
	}{
		{"commuteADD", func() *prop.PropWrapper { return intCommuteADD(a, b) },
			eqT(intPlusT(a, b), intPlusT(b, a)), stmts["AddSym"]},
		{"associateADD", func() *prop.PropWrapper { return intAssociateADD(a, b, c) },
			eqT(intPlusT(intPlusT(a, b), c), intPlusT(a, intPlusT(b, c))), stmts["AddAssoc"]},
		{"commuteMUL", func() *prop.PropWrapper { return intCommuteMUL(a, b) },
			eqT(intStarT(a, b), intStarT(b, a)), stmts["MulSym"]},
		{"associateMUL", func() *prop.PropWrapper { return intAssociateMUL(a, b, c) },
			eqT(intStarT(intStarT(a, b), c), intStarT(a, intStarT(b, c))), stmts["MulAssoc"]},
		{"oneMul", func() *prop.PropWrapper { return intOneMul(a) },
			eqT(intStarT(intLit(1), a), a), stmts["MulLeftIdentity"]},
		{"addZeroR", func() *prop.PropWrapper { return intAddZeroR(a) },
			eqT(intPlusT(a, intLit(0)), a), stmts["AddRightIdentity"]},
		{"zeroMul", func() *prop.PropWrapper { return intZeroMul(a) },
			eqT(intStarT(intLit(0), a), intLit(0)), stmts["MulLeftZero"]},
		{"distributeMUL", func() *prop.PropWrapper { return intDistributeMUL(a, b, c) },
			eqT(intStarT(a, intPlusT(b, c)), intPlusT(intStarT(a, b), intStarT(a, c))),
			stmts["LeftDistrib"]},
		{"rightDistrib", func() *prop.PropWrapper { return intRightDistrib(a, b, c) },
			eqT(intStarT(intPlusT(a, b), c), intPlusT(intStarT(a, c), intStarT(b, c))),
			stmts["RightDistrib"]},
	}
	for _, tc := range cases {
		w := tc.run()
		if !w.Conclusion().AlphaEquals(tc.want) {
			t.Errorf("%s: conclusion = %v, want %v", tc.name, w.Conclusion(), tc.want)
		}
		hypsAmong(t, tc.name, w, []Term{tc.marker})
	}
}

func TestIntSquareNonneg(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	z := intLit(0)
	// &0 ≤ x·x with no hyp.
	checkIntDecideTrueH(t, "0≤x·x (no hyp)", intLeT(z, intStarT(x, x)))
	// &0 ≤ x pow 2 composes (pow-sign PowTwoNonneg, the pow form of the same fact).
	checkIntDecideTrueH(t, "0≤x^2 (no hyp)", intLeT(z, intPowT(x, Numeral(2))))

	// sanity: `&0 ≤ x·y` (DISTINCT factors) — the square handler must
	// decline (it only fires on a literal square shape).
	if w, ok := intProveSquareNonneg(intLeT(z, intStarT(x, y))); ok || w != nil {
		t.Errorf("intProveSquareNonneg(&0≤x·y, distinct factors) must decline; got (%v, %v)", w, ok)
	}
}

// TestIntPowSign pins PowNonneg / PowPos / PowTwoNonneg — the sign-known
// fragment of pow (NOT full RCF).
func TestIntPowSign(t *testing.T) {
	x := intVar("x")
	z := intLit(0)
	n := numVar("n")

	// &0 ≤ x pow 2 with NO hyp (PowTwoNonneg — an even square is nonneg).
	checkIntDecideTrueH(t, "0≤x^2 (no hyp)", intLeT(z, intPowT(x, Numeral(2))))
	// &0 ≤ x ⊢ &0 ≤ x pow n  (symbolic exponent, PowNonneg).
	checkIntDecideTrueH(t, "0≤x⊢0≤x^n", intLeT(z, intPowT(x, n)), intLeT(z, x))
	// &0 ≤ x ⊢ &0 ≤ x pow 3  (literal exponent via PowNonneg).
	checkIntDecideTrueH(t, "0≤x⊢0≤x^3", intLeT(z, intPowT(x, Numeral(3))), intLeT(z, x))
	// &0 < x ⊢ &0 < x pow n  (PowPos).
	checkIntDecideTrueH(t, "0<x⊢0<x^n", intLtT(z, intPowT(x, n)), intLtT(z, x))

	// sanity: &0 ≤ x pow 3 with NO hyp must NOT decide ⊤ (x=−1 ⇒ x³=−1 < 0).
	if w := IntArithDecideWithHyps(nil)(intLeT(z, intPowT(x, Numeral(3)))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0≤x^3 without &0≤x must NOT decide ⊤ (counterexample x=−1)")
	}
	// sanity: &0 < x pow 2 with NO hyp must NOT decide ⊤ (x=&0 ⇒ x²=0).
	if w := IntArithDecideWithHyps(nil)(intLtT(z, intPowT(x, Numeral(2)))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0<x^2 without &0<x must NOT decide ⊤ (counterexample x=&0)")
	}
}

// TestIntSquareAbsInterchange pins SquareOfAbs (strip abs from a square) and
// NegEqZero (zero-detection through neg). Mirror of
// TestRealSquareAbsInterchange.
func TestIntSquareAbsInterchange(t *testing.T) {
	x := intVar("x")
	zero := intLit(0)
	two := Numeral(2)

	// int_abs(x) pow 2 = int_pow x 2  (SquareOfAbs) — strips abs from a square.
	checkIntDecideTrueH(t, "|x|^2=x^2", eqT(intPowT(intAbsT(x), two), intPowT(x, two)))
	// Composed: hyp `&0 ≤ x^2` closes goal `&0 ≤ |x|^2` (SquareOfAbs strips the abs).
	checkIntDecideTrueH(t, "0≤x^2 ⊢ 0≤|x|^2",
		intLeT(zero, intPowT(intAbsT(x), two)), intLeT(zero, intPowT(x, two)))

	// NegEqZero goal-side: (−x = &0) → (x = &0). Hyp `x = &0` closes goal
	// `−x = &0`.
	checkIntDecideTrueH(t, "x=0 ⊢ −x=0", eqT(intNegT(x), zero), eqT(x, zero))
}

// TestIntAbsLessEqIffPowTwoLessEq pins AbsLessEqIffPowTwoLessEq — `x² ≤ y²` simp-rewrites to
// `|x| ≤ |y|`. Closes when the abs-form is present as a hyp; composes with
// SquareOfAbs (strips abs from squared) so `|x|² ≤ |y|²` cascades through.
// Mirror of TestRealAbsLessEqIffPowTwoLessEq.
func TestIntAbsLessEqIffPowTwoLessEq(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	two := Numeral(2)
	// Hyp `|x| ≤ |y|` closes goal `x² ≤ y²` (simp rewrites goal toward abs).
	checkIntDecideTrueH(t, "|x|≤|y| ⊢ x²≤y²",
		intLeT(intPowT(x, two), intPowT(y, two)),
		intLeT(intAbsT(x), intAbsT(y)))
	// Cascade with SquareOfAbs: hyp `|x| ≤ |y|` closes goal `|x|² ≤ |y|²` (SquareOfAbs
	// strips both abs to `x² ≤ y²`, then AbsLessEqIffPowTwoLessEq rewrites back).
	checkIntDecideTrueH(t, "|x|≤|y| ⊢ |x|²≤|y|²",
		intLeT(intPowT(intAbsT(x), two), intPowT(intAbsT(y), two)),
		intLeT(intAbsT(x), intAbsT(y)))
}

// TestIntAbsTriangle pins AbsTriangle — binary + n-ary via iterated
// triangle, with a final linarith transit. Mirror of TestRealAbsTriangle.
func TestIntAbsTriangle(t *testing.T) {
	x, y, z := intVar("x"), intVar("y"), intVar("z")
	// Binary: |x + y| ≤ |x| + |y|  (the lemma applied directly; rhs == absSum).
	checkIntDecideTrueH(t, "|x+y|≤|x|+|y|",
		intLeT(intAbsT(intPlusT(x, y)), intPlusT(intAbsT(x), intAbsT(y))))
	// Ternary (right-associated): |x + (y + z)| ≤ |x| + (|y| + |z|).
	checkIntDecideTrueH(t, "|x+(y+z)|≤|x|+(|y|+|z|)",
		intLeT(intAbsT(intPlusT(x, intPlusT(y, z))),
			intPlusT(intAbsT(x), intPlusT(intAbsT(y), intAbsT(z)))))
	// Binary with linarith tail: hyps `|x| ≤ a` and `|y| ≤ b` close goal
	// `|x+y| ≤ a + b` (triangle + linarith transit).
	a, b := intVar("a"), intVar("b")
	checkIntDecideTrueH(t, "|x|≤a ∧ |y|≤b ⊢ |x+y|≤a+b",
		intLeT(intAbsT(intPlusT(x, y)), intPlusT(a, b)),
		intLeT(intAbsT(x), a), intLeT(intAbsT(y), b))
}

// TestIntDividesIffRemZero pins DividesIffRemZero — the simp `int_rem(m,n) = &0 → divides(n,m)`.
// Bridges rem subsystem to divides subsystem; the bridged goal closes through
// the existing intDividesGoal path (∃-witness intro).
func TestIntDividesIffRemZero(t *testing.T) {
	x := intVar("x")
	two, six := intLit(2), intLit(6)

	// Goal `int_rem(&6, &2) = &0` — DivModSimp's literal evaluator beats us to it
	// (int_rem(&6,&2)=&0 via DivModUnique, then &0=&0 reflexively). Pin it as a
	// regression — the new simp must NOT break the literal path.
	checkIntDecideTrueH(t, "int_rem(&6,&2)=&0", eqT(intRemT(six, two), intLit(0)))

	// Goal `int_rem(&2·x, &2) = &0` — symbolic dividend, the bridge kicks in:
	//   simp rewrites goal to `int_divides(&2, &2·x)`,
	//   intDividesGoal finds the witness `x` (since &2·x = &2 · x),
	//   producing ⊢ int_divides(&2, &2·x).
	checkIntDecideTrueH(t, "int_rem(&2·x,&2)=&0", eqT(intRemT(intStarT(two, x), two), intLit(0)))

	// Hyp side: a hyp `int_rem(m,&3)=&0` (after hyp pre-simp) becomes
	// `int_divides(&3, m)`, then intDividesSkolem releases the linear equation
	// `m = &3 · z` that closes a `divides(&3, m)` goal via the existing path.
	m := intVar("m")
	three := intLit(3)
	checkIntDecideTrueH(t, "int_rem(m,&3)=&0 ⊢ int_divides(&3,m)",
		intDividesT(three, m),
		eqT(intRemT(m, three), intLit(0)))
}

// TestIntDivisorBoundedByDividend pins DivisorBoundedByDividend — `d ∣ e ∧ e ≠ &0 ⊢ |d| ≤ |e|`. Closes
// the contradictory `int_divides(literal, literal)` class the gcd-rank-1 test
// can't reach (each row's coeff gcd = 1).
func TestIntDivisorBoundedByDividend(t *testing.T) {
	five, three := intLit(5), intLit(3)
	x, y := intVar("x"), intVar("y")

	// `int_divides(&5, &3) ⊢ ⊥` — &3 ≠ &0 trivially, the injected |&5| ≤ |&3|
	// after int_abs's literal split becomes &5 ≤ &3, refuted by linarith. The
	// goal here is any unprovable atom; the hyp is contradictory so anything
	// closes.
	checkIntDecideTrueH(t, "int_divides(&5,&3),&0<x ⊢ x<x",
		intLeT(x, y), intDividesT(five, three))

	// `int_divides(d, e) ∧ e ≠ &0 ⊢ |d| ≤ |e|` directly — the size bound is the
	// goal, the bridge produces it as the injected fact.
	d, e := intVar("d"), intVar("e")
	checkIntDecideTrueH(t, "d∣e ∧ e≠0 ⊢ |d|≤|e|",
		intLeT(intAbsT(d), intAbsT(e)),
		intDividesT(d, e), not(eqT(e, intLit(0))))
}

// TestIntQuotientExactOfDivides pins QuotientExactOfDivides — under `q ∣ m`, the exact-division
// identity `int_div(m,q)·q = m` becomes a hyp, so linarith can substitute int_div(m,q)
// away.
func TestIntQuotientExactOfDivides(t *testing.T) {
	m, q := intVar("m"), intVar("q")

	// `q ∣ m ⊢ int_div(m,q)·q = m` — the bridge's direct claim.
	checkIntDecideTrueH(t, "q∣m ⊢ int_div(m,q)·q=m",
		eqT(intStarT(intDivT(m, q), q), m),
		intDividesT(q, m))

	// Subtraction form `q∣m ⊢ m − int_div(m,q)·q = &0` — equivalent to the eq form
	// via move-across. moveAcrossCmp's signedNorm canonicalizes the residual
	// product to multivariate-sorted order (`q · int_div(m,q)`), which alpha-misses
	// intProveQuotientExact's raw injected fact `int_div(m,q)·q = m` — unbridged, this falls
	// to intImageSplit and hangs. Closed by intHypEchoEq's ring-bridge
	// fallback (int.go): when alpha checks miss, IntRingProveFull bridges each
	// goal side to a hyp eq side, so the commute `q·int_div(m,q) = int_div(m,q)·q`
	// closes the gap and the goal reaches the hyp through EqTrans/EqSym.
	checkIntDecideTrueH(t, "q∣m ⊢ m − int_div(m,q)·q = &0",
		eqT(intSubT(m, intStarT(intDivT(m, q), q)), intLit(0)),
		intDividesT(q, m))
}

// TestIntOfNumDivMod pins OfNumDiv / OfNumRem as the of_num bridge
// for the int_div/int_rem literal evaluator. Same coverage as DivModUnique for
// fully-literal operands; this test just verifies the bridge path is wired
// without breaking the existing evaluator.
func TestIntOfNumDivMod(t *testing.T) {
	// Both fully literal — the intLitVal path beats the OfNum bridge to it
	// (DivModUnique), so the OfNum bridge is exercised only on the leaf
	// shape level. Pin the leaf builders return the expected bound shape:
	a, b := Numeral(7), Numeral(2)
	la, lb := intOfNumT(a), intOfNumT(b)

	// intOfNumDiv: ⊢ int_div(&7, &2) = &(nat_div(7, 2))
	w := intOfNumDiv(a, b)
	wantConcl := eqT(intDivT(la, lb), intOfNumT(divT(a, b)))
	if !w.Conclusion().AlphaEquals(wantConcl) {
		t.Errorf("intOfNumDiv shape: got %v, want %v", w.Conclusion(), wantConcl)
	}

	// intOfNumRem: ⊢ int_rem(&7, &2) = &(nat_mod(7, 2))
	w2 := intOfNumRem(a, b)
	wantConcl2 := eqT(intRemT(la, lb), intOfNumT(modT(a, b)))
	if !w2.Conclusion().AlphaEquals(wantConcl2) {
		t.Errorf("intOfNumRem shape: got %v, want %v", w2.Conclusion(), wantConcl2)
	}

	// End-to-end: `int_div(&6, &2) = &3` still closes (the literal evaluator path
	// is now duplicated by the of_num bridge — both fold to the same answer).
	checkIntDecideTrueH(t, "int_div(&6,&2)=&3",
		eqT(intDivT(intLit(6), intLit(2)), intLit(3)))
	checkIntDecideTrueH(t, "int_rem(&7,&2)=&1",
		eqT(intRemT(intLit(7), intLit(2)), intLit(1)))
}

// Sanity: a divisibility hyp that does NOT pair with a derivable e ≠ &0 must
// not inject the bound (e=&0 makes |d| ≤ |e| equivalent to |d| ≤ &0, which
// might wrongly close a downstream goal).
func TestIntDivisorBoundedByDividend_NoNonZero(t *testing.T) {
	d, e := intVar("d"), intVar("e")
	// `int_divides(d, e)` alone — no `e ≠ &0` discharge — must NOT decide
	// `|d| ≤ |e|` (the case e=&0 makes the lemma vacuous).
	if w := IntArithDecideWithHyps([]Term{intDividesT(d, e)})(intLeT(intAbsT(d), intAbsT(e))); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("d∣e WITHOUT e≠0 must NOT decide |d|≤|e| ⊤")
	}
}

// TestIntDivMulAddSimp pins DivMulAdd / RemMulAdd — the auto simp
// in intDivModFold that strips a `n·p` summand from a int_div/int_rem dividend when n
// is a literal nonzero.
func TestIntDivMulAddSimp(t *testing.T) {
	m, p := intVar("m"), intVar("p")
	two := intLit(2)

	// `int_div(m + &2·p, &2) = int_div(m, &2) + p` — exact bound shape, literal &2.
	// After the simp, the goal collapses through the rest of the decider.
	checkIntDecideTrueH(t, "int_div(m+&2·p,&2) = int_div(m,&2)+p",
		eqT(intDivT(intPlusT(m, intStarT(two, p)), two),
			intPlusT(intDivT(m, two), p)))

	// `int_rem(m + &2·p, &2) = int_rem(m, &2)` — same shape for rem.
	checkIntDecideTrueH(t, "int_rem(m+&2·p,&2) = int_rem(m,&2)",
		eqT(intRemT(intPlusT(m, intStarT(two, p)), two), intRemT(m, two)))

	// Sanity: a symbolic divisor (no literal nonzero) — the simp must decline
	// (it can't discharge `~(n=&0)`). The atom stays as `int_div(m + n·p, n)`, and
	// nothing in the linear core closes the catch-all goal.
	n := intVar("n")
	g := eqT(intDivT(intPlusT(m, intStarT(n, p)), n), intPlusT(intDivT(m, n), p))
	if w := IntArithDecideWithHyps(nil)(g); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("int_div(m+n·p,n) = int_div(m,n)+p with symbolic n must NOT decide ⊤ (need ~(n=&0) hyp)")
	}
}

// TestIntDivisionAlgorithm pins the agent-invoked DivisionAlgorithm helper — verifies
// the leaf builder constructs the full bundled identity in the expected shape.
// NOT exercised through IntArithDecideWithHyps because the helper is not
// auto-wired (per README "deferred — needs guarded/agent-invoked form").
func TestIntDivisionAlgorithm(t *testing.T) {
	m, n := intVar("m"), intVar("n")
	w := IntDivisionAlgorithm(m, n)
	// Want: ~(n = &0) ⇒ (m = int_div(m,n)·n + int_rem(m,n) ∧ &0 ≤ int_rem(m,n) ∧ int_rem(m,n) < int_abs n)
	div := intDivT(m, n)
	rem := intRemT(m, n)
	eqId := eqT(m, intPlusT(intStarT(div, n), rem))
	remNonneg := intLeT(intLit(0), rem)
	remLtAbs := intLtT(rem, intAbsT(n))
	want := imply(not(eqT(n, intLit(0))),
		prop.And(eqId, prop.And(remNonneg, remLtAbs)))
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("IntDivisionAlgorithm shape:\n got  %v\n want %v", w.Conclusion(), want)
	}
}

// TestIntOfNumPow pins OfNumPow — the int_pow base/exp `&_` bridge to
// `&(nat_pow(m, n))`. The wired simp clause folds the head; what becomes of the
// inner `nat_pow(m, n)` is the num simp step's business, and the test does not
// depend on it.
func TestIntOfNumPow(t *testing.T) {
	a, b := Numeral(3), Numeral(2)
	la := intOfNumT(a)

	// Leaf builder shape.
	w := intOfNumPow(a, b)
	wantConcl := eqT(intPowT(la, b), intOfNumT(expT(a, b)))
	if !w.Conclusion().AlphaEquals(wantConcl) {
		t.Errorf("intOfNumPow shape: got %v, want %v", w.Conclusion(), wantConcl)
	}

	// End-to-end: the simp rewrites `int_pow(&3, 2)` to `&(nat_pow(3, 2))`, so
	// the goal `int_pow(&3, 2) = &(nat_pow(3, 2))` decides ⊤ (both sides
	// normalize through the same bridge, whether or not the inner power then
	// folds).
	checkIntDecideTrueH(t, "int_pow(&3, 2) = &(nat_pow(3, 2))",
		eqT(intPowT(la, b), intOfNumT(expT(a, b))))
}

// TestIntForallExistsNonneg pins the higher-order quantifier
// bridges. They are not auto-wired (quantifier handling lives above omega's
// atom-level decider); the test just verifies leaf shape.
func TestIntForallExistsNonneg(t *testing.T) {
	// A concrete int → bool predicate P: λx. &0 ≤ x.
	x := core.Var(core.TermName("x"), dsl.IntType)
	P := core.Abs(x, intLeT(intLit(0), x))

	// IntForallNonneg(P): (∀x:int. &0 ≤ x ⇒ P x) ⇔ (∀n:num. P (int_of_num n))
	w := IntForallNonneg(P)
	bx := core.Var(core.TermName("x"), dsl.IntType)
	bn := core.Var(core.TermName("n"), dsl.NumType)
	wantLhs := ext.ForAll(bx)(imply(intLeT(intLit(0), bx), ext.Apply(P, bx)))
	wantRhs := ext.ForAll(bn)(ext.Apply(P, intOfNumT(bn)))
	want := eqT(wantLhs, wantRhs)
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("IntForallNonneg shape:\n got  %v\n want %v", w.Conclusion(), want)
	}

	// IntExistsNonneg(P): (∃x:int. &0 ≤ x ∧ P x) ⇔ (∃n:num. P (int_of_num n))
	w2 := IntExistsNonneg(P)
	wantLhs2 := prop.Exists(bx)(prop.And(intLeT(intLit(0), bx), ext.Apply(P, bx)))
	wantRhs2 := prop.Exists(bn)(ext.Apply(P, intOfNumT(bn)))
	want2 := eqT(wantLhs2, wantRhs2)
	if !w2.Conclusion().AlphaEquals(want2) {
		t.Errorf("IntExistsNonneg shape:\n got  %v\n want %v", w2.Conclusion(), want2)
	}
}

func TestIntAbsLaws(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	n := numVar("n")
	ax, ay := intAbsT(x), intAbsT(y)

	// |x·y| = |x|·|y|  (AbsMul) — both orientations.
	checkIntDecideTrueH(t, "|x·y|=|x|·|y|", eqT(intAbsT(intStarT(x, y)), intStarT(ax, ay)))
	checkIntDecideTrueH(t, "|x|·|y|=|x·y|", eqT(intStarT(ax, ay), intAbsT(intStarT(x, y))))

	// |−x| = |x|  (AbsEven).
	checkIntDecideTrueH(t, "|−x|=|x|", eqT(intAbsT(intNegT(x)), ax))

	// ||x|| = |x|  (AbsIdempotent).
	checkIntDecideTrueH(t, "||x||=|x|", eqT(intAbsT(ax), ax))

	// |&n| = &n  (OfNumAbs, n a num variable).
	checkIntDecideTrueH(t, "|&n|=&n", eqT(intAbsT(intOfNumT(n)), intOfNumT(n)))

	// Composed: |−(x·y)| = |x|·|y| (neg then mul folds compose).
	checkIntDecideTrueH(t, "|−(x·y)|=|x|·|y|",
		eqT(intAbsT(intNegT(intStarT(x, y))), intStarT(ax, ay)))

	// sanity: |x+y| = |x|+|y| is NOT a law (the triangle inequality is ≤,
	// not =); the fold has no `+` clause, and the split cannot close the
	// mixed-sign branch.
	if w := IntArithDecideWithHyps(nil)(eqT(intAbsT(intPlusT(x, y)), intPlusT(ax, ay))); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("|x+y|=|x|+|y| must NOT decide ⊤ (it is not a theorem)")
	}
}

func TestIntSgnLaws(t *testing.T) {
	x, y := intVar("x"), intVar("y")
	sx, sy := intSgnT(x), intSgnT(y)

	// int_sgn(x·y) = int_sgn x · int_sgn y  (SgnMul).
	checkIntDecideTrueH(t, "sgn(x·y)=sgn x·sgn y",
		eqT(intSgnT(intStarT(x, y)), intStarT(sx, sy)))

	// int_sgn(−x) = −(int_sgn x)  (SgnOdd).
	checkIntDecideTrueH(t, "sgn(−x)=−sgn x", eqT(intSgnT(intNegT(x)), intNegT(sx)))

	// Composed: sgn(−(x·y)) = −(sgn x · sgn y)  (SgnOdd then SgnMul). Closes
	// thanks to the no-sign-split restricted decider used by imageBranchImp:
	// the nonlinear `sgn x · sgn y` product does not drive unbounded image-
	// split recursion.
	checkIntDecideTrueH(t, "sgn(−(x·y))=−(sgn x·sgn y)",
		eqT(intSgnT(intNegT(intStarT(x, y))), intNegT(intStarT(sx, sy))))
}

func TestIntArithSelectUniqueHypDoesNotBoolSplitForever(t *testing.T) {
	goal := dsl.MustParseProp(
		"∀P:(int → bool).∀x:int.∃y:int.((x = (εx0:int.P(x0))) ∨ (¬P(y) ⇔ (x = y)))," +
			"∀x:int.∃y:int.((x = (εx0:int.(λa:int.∀b:int.((b = (a * b)) ∧ (b = (b * a))))(x0))) ∨ " +
			"(¬(λa:int.∀b:int.((b = (a * b)) ∧ (b = (b * a))))(y) ⇔ (x = y)))," +
			"∀x:int.(x = (x * int_of_num(1)))," +
			"∀x:int.(x = (int_of_num(1) * x))," +
			"∃y:int.((int_of_num(1) = (εx0:int.(λa:int.∀b:int.((b = (a * b)) ∧ (b = (b * a))))(x0))) ∨ " +
			"(¬(λa:int.∀b:int.((b = (a * b)) ∧ (b = (b * a))))(y) ⇔ (int_of_num(1) = y)))" +
			" ⊢ int_of_num(1) = (εx:int.∀y:int.((y = (x * y)) ∧ (y = (y * x))))")
	hyps := slices.Collect(goal.HypIter())
	if len(hyps) != 5 {
		t.Fatalf("parsed %d hyps, want 5", len(hyps))
	}

	SetIntLemmaBundle(&IntLemmaBundle{})
	t.Cleanup(func() { SetIntLemmaBundle(nil) })

	const deadline = time.Second
	done := make(chan struct{})
	go func() {
		ctx := NewArithCtx(hyps)
		_ = ctx.DecideExcept(1, hyps[1])
		close(done)
	}()

	select {
	case <-done:
	case <-time.After(deadline):
		t.Fatalf("ArithCtx.DecideExcept on a unique-choice-style int hyp did not return within %s", deadline)
	}
}

// TestIntFirstSplittable_BinderFree pins the binder-free candidate walk
// behind the int tautology splits: an int_abs under an enclosing ∀ is no
// candidate; the same shape free is (intComparisonAtomsOf already was).
func TestIntFirstSplittable_BinderFree(t *testing.T) {
	SetIntLemmaBundle(&IntLemmaBundle{})
	t.Cleanup(func() { SetIntLemmaBundle(nil) })
	x, a, b := intVar("x"), intVar("a"), intVar("b")
	bound := ext.ForAll(x)(intLeT(intLit(0), intAbsT(x))) // ∀x. &0 ≤ |x|
	if sa, ok := intFirstSplittable([]Term{bound}, intLeT(a, b), nil); ok {
		t.Errorf("|x| under ∀x offered as a split candidate: %v", sa.atom)
	}
	if sa, ok := intFirstSplittable([]Term{bound}, intLeT(a, intAbsT(a)), nil); !ok || !sa.atom.AlphaEquals(intAbsT(a)) {
		t.Errorf("free |a| not the split candidate: ok=%v atom=%v", ok, sa.atom)
	}
}
