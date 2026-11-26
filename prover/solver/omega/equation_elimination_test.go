package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// TestIntRefuteProof_EliminatesEquations: systems whose contradiction is the
// rounding of a row an equation's substitution leaves. Each has a rational
// solution (q = 1/2 in the first), and no single input row rounds, so
// neither the per-row cut nor Fourier–Motzkin on the equation's two `≤`
// rows refutes it.
func TestIntRefuteProof_EliminatesEquations(t *testing.T) {
	installTestBundle(t)
	for _, tc := range []struct {
		name string
		cs   []LinConstraint
	}{
		{"n = 2q, 0 < n, n < 2", []LinConstraint{
			con(tn("n"), tn("2 * q"), opEQ), con(tn("0"), tn("n"), opLT), con(tn("n"), tn("2"), opLT)}},
		{"the quotient on the left", []LinConstraint{
			con(tn("2 * q"), tn("n"), opEQ), con(tn("0"), tn("n"), opLT), con(tn("n"), tn("2"), opLT)}},
		{"n = 2q + 1, 1 < n, n < 3", []LinConstraint{
			con(tn("n"), tn("2 * q + 1"), opEQ), con(tn("1"), tn("n"), opLT), con(tn("n"), tn("3"), opLT)}},
		{"the remainder a variable two inequalities pin", []LinConstraint{
			con(tn("n"), tn("2 * q + r"), opEQ), con(tn("r"), tn("2"), opLT), con(tn("0"), tn("r"), opLT),
			con(tn("1"), tn("n"), opLT), con(tn("n"), tn("3"), opLT)}},
		{"the remainder pinned by an equation", []LinConstraint{
			con(tn("n"), tn("2 * q + r"), opEQ), con(tn("r"), tn("1"), opEQ),
			con(tn("1"), tn("n"), opLT), con(tn("n"), tn("3"), opLT)}},
		{"two equations and no bound", []LinConstraint{
			con(tn("n"), tn("2 * q"), opEQ), con(tn("n"), tn("2 * p + 1"), opEQ)}},
		{"two equations, the second shifted", []LinConstraint{
			con(tn("n"), tn("2 * q"), opEQ), con(tn("n + 1"), tn("2 * p"), opEQ)}},
		{"an equation only two inequalities state", []LinConstraint{
			con(tn("2 * q"), tn("n"), opLE), con(tn("n"), tn("2 * q"), opLE),
			con(tn("1"), tn("n"), opLE), con(tn("n"), tn("1"), opLE)}},
		{"two odd numbers one apart", []LinConstraint{
			con(tn("m"), tn("2 * a + 1"), opEQ), con(tn("n"), tn("2 * b + 1"), opEQ),
			con(tn("m"), tn("n"), opLT), con(tn("n"), tn("m + 2"), opLT)}},
		{"a residue mod 3", []LinConstraint{
			con(tn("n"), tn("3 * q + 2"), opEQ), con(tn("2"), tn("n"), opLT), con(tn("n"), tn("5"), opLT)}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if unsat, ok := IntUnsat(tc.cs); !ok || !unsat {
				t.Fatalf("IntUnsat = (%v, %v), want unsatisfiable", unsat, ok)
			}
			w, ok := IntRefuteProof(tc.cs)
			if !ok {
				t.Fatal("expected an integer refutation, got none")
			}
			if !w.Conclusion().Equals(prop.F) {
				t.Errorf("conclusion = %v, want ⊥", w.Conclusion())
			}
			hypsAmong(t, tc.name, w, constraintTerms(tc.cs))
		})
	}
	for _, tc := range []struct {
		name string
		cs   []LinConstraint
	}{
		// n = 2, q = 1.
		{"n = 2q, 0 < n, n < 3", []LinConstraint{
			con(tn("n"), tn("2 * q"), opEQ), con(tn("0"), tn("n"), opLT), con(tn("n"), tn("3"), opLT)}},
		// n = 3, q = 1.
		{"n = 2q + 1, 1 < n, n < 4", []LinConstraint{
			con(tn("n"), tn("2 * q + 1"), opEQ), con(tn("1"), tn("n"), opLT), con(tn("n"), tn("4"), opLT)}},
		// n = 4, q = 2, p = 1.
		{"n = 2q and n = 4p", []LinConstraint{
			con(tn("n"), tn("2 * q"), opEQ), con(tn("n"), tn("4 * p"), opEQ), con(tn("0"), tn("n"), opLT)}},
		// m = 1, n = 3.
		{"two odd numbers two apart", []LinConstraint{
			con(tn("m"), tn("2 * a + 1"), opEQ), con(tn("n"), tn("2 * b + 1"), opEQ),
			con(tn("m"), tn("n"), opLT), con(tn("n"), tn("m + 3"), opLT)}},
	} {
		t.Run("satisfiable: "+tc.name, func(t *testing.T) {
			if unsat, ok := IntUnsat(tc.cs); ok && unsat {
				t.Error("IntUnsat calls a satisfiable system unsatisfiable")
			}
			if _, ok := IntRefuteProof(tc.cs); ok {
				t.Error("IntRefuteProof refutes a satisfiable system")
			}
		})
	}
}

// TestEliminateEquations_RowsAndCertificate: the elimination's own
// arithmetic on `n = 2q + r`, `1 ≤ r ≤ 1`, `2 ≤ n ≤ 2`. Solving for n and
// then for r leaves `1 ≤ 2q`, `2q ≤ 1` and `0 ≤ 2q + 1`, which round to
// `1 ≤ q`, `q ≤ 0` and `0 ≤ q`; the last two are the equation `q = 0`, and
// substituting it leaves the one row `1 ≤ 0`. Three rows were rounded, each
// a node beside the input rows, and the certificate of `1 ≤ 0` over the
// nodes replays to ⊥.
func TestEliminateEquations_RowsAndCertificate(t *testing.T) {
	installTestBundle(t)
	p, built := buildIntProv([]LinConstraint{
		con(tn("n"), tn("2 * q + r"), opEQ),
		con(tn("1"), tn("r"), opLE), con(tn("r"), tn("1"), opLE),
		con(tn("2"), tn("n"), opLE), con(tn("n"), tn("2"), opLE),
	})
	if !built {
		t.Fatal("buildIntProv declined a linear system")
	}
	fm, prs := finalize(p.tbl, p.fm, p.prs)
	e, eliminated := eliminateEquations(p.tbl, fm, prs, natEliminationLeaves)
	if !eliminated {
		t.Fatal("no equation eliminated")
	}
	if len(e.rows) != 1 || !vectorOf(e.rows[0].coeffs).isZero() || !e.rows[0].konst.isOne() {
		t.Fatalf("rows after elimination: %d, want the one row 1 ≤ 0", len(e.rows))
	}
	if got := len(e.nodes) - len(prs); got != 3 {
		t.Errorf("%d rounded rows, want 3 (1 ≤ q, q ≤ 0, 0 ≤ q)", got)
	}
	lambda, refuted := refute(p.tbl.n(), e.system())
	if !refuted {
		t.Fatal("the row 1 ≤ 0 is not read as the refutation")
	}
	certificate := e.certificate(lambda)
	for j := range prs {
		if certificate[j].sign() < 0 {
			t.Errorf("input row %d has the negative multiplier %s", j, certificate[j])
		}
	}
	w, ok := replay(e.nodes, certificate)
	if !ok || !w.Conclusion().Equals(prop.F) {
		t.Fatalf("the certificate over the nodes does not replay to ⊥ (ok=%v)", ok)
	}
}

// TestEliminateEquations_NoUnitAtomDeclines: an equation none of whose
// atoms has coefficient ±1 is not solved, and the caller keeps its rows.
func TestEliminateEquations_NoUnitAtomDeclines(t *testing.T) {
	installTestBundle(t)
	p, built := buildIntProv([]LinConstraint{
		con(tn("2 * a"), tn("3 * b"), opEQ), con(tn("a"), tn("7"), opLT),
	})
	if !built {
		t.Fatal("buildIntProv declined a linear system")
	}
	fm, prs := finalize(p.tbl, p.fm, p.prs)
	if _, eliminated := eliminateEquations(p.tbl, fm, prs, natEliminationLeaves); eliminated {
		t.Error("2a = 3b eliminated, and neither atom has coefficient ±1")
	}
}

// TestIntLinRefuteProof_EliminatesEquations: the same step over ℤ, where a
// rounding is proved by discreteness and no row says an atom is
// non-negative.
func TestIntLinRefuteProof_EliminatesEquations(t *testing.T) {
	n, q, p := intVar("n"), intVar("q"), intVar("p")
	two := intLit(2)
	twoQ, twoP := intStarT(two, q), intStarT(two, p)
	for _, tc := range []struct {
		name string
		cs   []LinConstraint
	}{
		{"n = 2q + 1, 1 < n, n < 3", []LinConstraint{
			intCon(n, intPlusT(twoQ, intLit(1)), opEQ), intCon(intLit(1), n, opLT), intCon(n, intLit(3), opLT)}},
		{"n = 2q, 0 < n, n < 2", []LinConstraint{
			intCon(n, twoQ, opEQ), intCon(intLit(0), n, opLT), intCon(n, two, opLT)}},
		{"two equations and no bound", []LinConstraint{
			intCon(n, twoQ, opEQ), intCon(n, intPlusT(twoP, intLit(1)), opEQ)}},
		{"an equation only two inequalities state", []LinConstraint{
			intCon(twoQ, n, opLE), intCon(n, twoQ, opLE), intCon(intLit(1), n, opLE), intCon(n, intLit(1), opLE)}},
	} {
		checkIntRefute(t, tc.name, tc.cs)
	}
	// n = 2, q = 1.
	if _, ok := IntLinRefuteProof([]LinConstraint{
		intCon(n, twoQ, opEQ), intCon(intLit(0), n, opLT), intCon(n, intLit(3), opLT)}); ok {
		t.Error("n = 2q, 0 < n, n < 3 must not be refutable (n = 2)")
	}
	// n = −1, q = −1: no row bounds an integer atom below.
	if _, ok := IntLinRefuteProof([]LinConstraint{
		intCon(n, intPlusT(twoQ, intLit(1)), opEQ), intCon(n, intLit(1), opLT)}); ok {
		t.Error("n = 2q + 1, n < 1 must not be refutable over ℤ (n = −1)")
	}
}

// TestDivModFacts_BothConjunctsForEitherAtom: a `nat_mod(m, n)` atom and a
// `nat_div(m, n)` atom each bring Division's bound and its identity, and
// the two atoms together bring them once.
func TestDivModFacts_BothConjunctsForEitherAtom(t *testing.T) {
	installDivModSplitBundle(t)
	n := numVar("n")
	two := Numeral(2)
	bound := lt(modT(n, two), two)
	identity := eqT(n, plus(star(divT(n, two), two), modT(n, two)))
	count := func(facts []*prop.PropWrapper, want Term) int {
		k := 0
		for _, f := range facts {
			if f.Conclusion().AlphaEquals(want) {
				k++
			}
		}
		return k
	}
	for _, tc := range []struct {
		name  string
		atoms []Term
	}{
		{"the remainder", []Term{modT(n, two)}},
		{"the quotient", []Term{divT(n, two)}},
		{"both", []Term{modT(n, two), divT(n, two)}},
	} {
		facts := divModFacts(tc.atoms, nil)
		if got := count(facts, bound); got != 1 {
			t.Errorf("%s: the bound nat_mod(n, 2) < 2 is injected %d times, want once", tc.name, got)
		}
		if got := count(facts, identity); got != 1 {
			t.Errorf("%s: the identity n = nat_div(n, 2) * 2 + nat_mod(n, 2) is injected %d times, want once", tc.name, got)
		}
	}
}

// TestProveDecAtom_ReadsTheDivisionIdentity: decisions that need the
// remainder's bound, the identity and a rounding together — a bound that
// parity and an inequality give, and a bound of the quotient.
func TestProveDecAtom_ReadsTheDivisionIdentity(t *testing.T) {
	installDivModSplitBundle(t)
	n := numVar("n")
	zero, one, two, three := natZero, Numeral(1), Numeral(2), Numeral(3)
	rem2 := modT(n, two)
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"an odd number above 1 is at least 3", []Term{not(eqT(zero, rem2)), lt(one, n)}, le(three, n)},
		{"an even number above 0 is at least 2", []Term{eqT(zero, rem2), lt(zero, n)}, le(two, n)},
		{"the remainder stated as 1", []Term{eqT(rem2, one), lt(one, n)}, le(three, n)},
		{"a residue mod 3", []Term{eqT(modT(n, three), two), lt(two, n)}, le(Numeral(5), n)},
		{"the quotient of a number from 3 up", []Term{le(three, n)}, le(one, divT(n, two))},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			w, ok := proveDecAtom(slices.Values(r.hyps), r.goal)
			if !ok {
				t.Fatalf("not decided: the goal %s", ext.PrintTerm(r.goal))
			}
			if !w.Conclusion().AlphaEquals(r.goal) {
				t.Errorf("conclusion %s, want %s", ext.PrintTerm(w.Conclusion()), ext.PrintTerm(r.goal))
			}
			for _, h := range w.Hyps() {
				if !slices.ContainsFunc(r.hyps, h.AlphaEquals) {
					t.Errorf("the proof carries %s, which is no hypothesis of the row", ext.PrintTerm(h))
				}
			}
		})
	}
	// False at n = 3 and at n = 2.
	if _, ok := proveDecAtom(slices.Values([]Term{not(eqT(zero, rem2)), lt(one, n)}), le(Numeral(4), n)); ok {
		t.Error("0 ≠ nat_mod(n, 2), 1 < n ⊢ 4 ≤ n decided, and it is false at n = 3")
	}
	if _, ok := proveDecAtom(slices.Values([]Term{eqT(zero, rem2), lt(zero, n)}), le(three, n)); ok {
		t.Error("0 = nat_mod(n, 2), 0 < n ⊢ 3 ≤ n decided, and it is false at n = 2")
	}
}

// TestProveDecAtom_MemoizedPerQuestion: a question asked again inside a step
// is answered with the proof the first asking built, a decline is
// remembered too, and the step's release drops both.
func TestProveDecAtom_MemoizedPerQuestion(t *testing.T) {
	installDivModSplitBundle(t)
	t.Cleanup(ReleaseStepMemos)
	ReleaseStepMemos()
	n := numVar("n")
	hyps := []Term{eqT(natZero, modT(n, Numeral(2))), lt(natZero, n)}
	first, ok := proveDecAtom(slices.Values(hyps), le(Numeral(2), n))
	if !ok {
		t.Fatal("0 = nat_mod(n, 2), 0 < n ⊢ 2 ≤ n not decided")
	}
	again, ok := proveDecAtom(slices.Values(hyps), le(Numeral(2), n))
	if !ok || again != first {
		t.Error("the question asked again is not answered with the first proof")
	}
	// The same hypotheses in another order are another question.
	swapped := []Term{hyps[1], hyps[0]}
	if other, ok := proveDecAtom(slices.Values(swapped), le(Numeral(2), n)); !ok || other == first {
		t.Error("another order of the hypotheses is answered from the first question's entry")
	}
	if _, ok := proveDecAtom(slices.Values(hyps), le(Numeral(3), n)); ok {
		t.Fatal("2 ≤ n strengthened to 3 ≤ n decided, and it is false at n = 2")
	}
	key := linQuestionKey(hyps, le(Numeral(3), n))
	if e, hit := natDecMemo.lookup(key, hyps, le(Numeral(3), n)); !hit || e.proof != nil {
		t.Error("the decline is not remembered as a decline")
	}
	ReleaseStepMemos()
	if _, hit := natDecMemo.lookup(key, hyps, le(Numeral(3), n)); hit {
		t.Error("the step's release left the decline in the memo")
	}
	fresh, ok := proveDecAtom(slices.Values(hyps), le(Numeral(2), n))
	if !ok || fresh == first {
		t.Error("the step's release left the proof in the memo")
	}
}

func constraintTerms(cs []LinConstraint) []Term {
	out := make([]Term, len(cs))
	for i, c := range cs {
		out[i] = constraintTerm(c)
	}
	return out
}
