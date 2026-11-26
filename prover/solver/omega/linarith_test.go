package omega

import (
	"iter"
	"slices"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext/prop"
)

// Validates the extraction + Farkas-search decision core: every refutation FM finds must be (a) a
// valid non-negative Farkas certificate (Σλ·row = 0·x + k, infeasible k) and
// (b) genuinely unsatisfiable over ℕ (brute force). SAT systems must not refute.

func con(l, r Term, op relOp) LinConstraint { return LinConstraint{Lhs: l, Rhs: r, Op: op} }

func TestFMRefuteCertificateFreeFailure(t *testing.T) {
	rows := []row{
		{coeffs: vector(1)},
		{coeffs: vector(-1)},
	}
	if lambda, ok := fmRefute(1, rows); ok || lambda.len() != 0 {
		t.Fatalf("satisfiable system refuted: lambda=%v ok=%v", lambda.entries(), ok)
	}
	if combined := combineRows(rows[0], rows[1], integerOne, integerOne); combined.lambda.len() != 0 {
		t.Fatalf("certificate-free combination materialized lambda %v", combined.lambda.entries())
	}
	for i, r := range rows {
		if r.lambda.len() != 0 {
			t.Fatalf("decision pass mutated input row %d lambda to %v", i, r.lambda.entries())
		}
	}
}

func TestRefuteDeterministicCertificateReplay(t *testing.T) {
	rows := []row{
		{coeffs: vector(1)},
		{coeffs: vector(-1), konst: integerOf(1)},
	}
	lambda, ok := refute(1, rows)
	if !ok || !checkCert(rows, lambda) {
		t.Fatalf("two-pass refute returned invalid certificate %v (ok=%v)", lambda, ok)
	}
	replayed, replayOK := fmRefute(1, seedCertificateRows(rows))
	if !replayOK || !slices.EqualFunc(lambda, replayed.entries(), _Integer.equal) {
		t.Fatalf("certificate replay = %v, %v; want %v, true", replayed.entries(), replayOK, lambda)
	}
}

// TestDedupRows_ASubsetOfPrunedRowsIsPruned is what fmRefute rests on when it
// skips the pruning after an elimination that combined nothing: the rows
// left are a subset, in order, of rows pruned already, and pruning them
// again returns them as they stand.
func TestDedupRows_ASubsetOfPrunedRowsIsPruned(t *testing.T) {
	pruned := dedupRows([]row{
		{coeffs: vector(1, 0, 2)},
		{coeffs: vector(2, 0, 4), konst: integerOf(3)}, // the first row's direction, stronger
		{coeffs: vector(0, 1, -1), strict: true},
		{coeffs: vector(-1, 0, 0), konst: integerOf(1)},
		{coeffs: vector(0, 0, 1)},
		{coeffs: vector(0, -3, 3)}, // the opposite direction of the third: its own
	})
	if len(pruned) != 5 {
		t.Fatalf("pruned to %d rows; want one per direction, five", len(pruned))
	}
	same := func(a, b []row) bool {
		return slices.EqualFunc(a, b, func(x, y row) bool {
			return slices.EqualFunc(x.coeffs.entries(), y.coeffs.entries(), _Integer.equal) &&
				x.konst.equal(y.konst) && x.strict == y.strict
		})
	}
	for mask := range 1 << len(pruned) {
		var subset []row
		for i, r := range pruned {
			if mask&(1<<i) != 0 {
				subset = append(subset, r)
			}
		}
		if again := dedupRows(subset); !same(again, subset) {
			t.Fatalf("subset %05b of pruned rows changed under a second pruning", mask)
		}
	}
}

func TestFMRefuteDedupsInputsBeforeElimination(t *testing.T) {
	rows := []row{
		{coeffs: vector(1)},                      // weaker: x ≤ 0
		{coeffs: vector(1), konst: integerOf(2)}, // stronger: x + 2 ≤ 0
		{coeffs: vector(-1), konst: integerOf(1)},
	}
	lambda, ok := refute(1, rows)
	if !ok || !checkCert(rows, lambda) {
		t.Fatalf("input-dedup refute returned invalid certificate %v (ok=%v)", lambda, ok)
	}
	want := integers(0, 1, 1)
	if !slices.EqualFunc(lambda, want, _Integer.equal) {
		t.Fatalf("certificate = %v; want %v (later stronger row retained)", lambda, want)
	}
}

func TestProvRowBuildsProofOnDemand(t *testing.T) {
	zero := Numeral(0)
	want := prop.Assume(le(zero, zero))
	builds := 0
	pr := lazyProvRow(zero, zero, false, func() *prop.PropWrapper {
		builds++
		return want
	})
	if builds != 0 {
		t.Fatalf("lazyProvRow invoked builder during construction")
	}
	got, ok := pr.proof()
	if !ok || got != want || builds != 1 {
		t.Fatalf("proof() = (%p, %v), builds=%d; want (%p, true), builds=1", got, ok, builds, want)
	}
}

func TestReduceForKeyCanonicalDirection(t *testing.T) {
	key, konst := reduceForKey(vector(6, -9, 0), integerOf(12))
	scaledKey, scaledKonst := reduceForKey(vector(2, -3, 0), integerOf(4))
	if key != scaledKey || konst.cmp(scaledKonst) != 0 {
		t.Fatalf("positive scalar multiples got different canonical forms")
	}

	for name, coeffs := range map[string]_Vector{
		"opposite direction":  vector(-2, 3, 0),
		"different component": vector(2, -3, 1),
		"different length":    vector(2, -3),
	} {
		other, _ := reduceForKey(coeffs, integerOf(4))
		if key == other {
			t.Errorf("%s collided with canonical direction key", name)
		}
	}
}

// checkCert verifies lambda is a sound Farkas refutation of rows.
func checkCert(rows []row, lambda []_Integer) bool {
	if len(rows) == 0 {
		return false
	}
	n := rows[0].coeffs.len()
	combo := make([]_Integer, n)
	var k _Integer
	strict := false
	for j, r := range rows {
		if lambda[j].sign() < 0 {
			return false
		}
		for i := 0; i < n; i++ {
			combo[i] = combo[i].add(lambda[j].mul(r.coeffs.at(i)))
		}
		k = k.add(lambda[j].mul(r.konst))
		if lambda[j].sign() > 0 && r.strict {
			strict = true
		}
	}
	if !vectorOf(combo).isZero() {
		return false
	}
	if strict {
		return k.sign() >= 0
	}
	return k.sign() > 0
}

func holds(c LinConstraint, env func(Term) uint64) bool {
	l, _ := evalExpr(c.Lhs, env)
	r, _ := evalExpr(c.Rhs, env)
	switch c.Op {
	case opLE:
		return l <= r
	case opLT:
		return l < r
	default:
		return l == r
	}
}

func satisfiable(cs []LinConstraint, a, b, c Term, B uint64) bool {
	for va := uint64(0); va <= B; va++ {
		for vb := uint64(0); vb <= B; vb++ {
			for vc := uint64(0); vc <= B; vc++ {
				env := envOf(a, b, c, va, vb, vc)
				ok := true
				for _, con := range cs {
					if !holds(con, env) {
						ok = false
						break
					}
				}
				if ok {
					return true
				}
			}
		}
	}
	return false
}

func TestLinRefuteUnsat(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")

	unsat := [][]LinConstraint{
		{con(tn("a"), tn("a"), opLT)},                                                               // a < a
		{con(tn("a + 1"), tn("a"), opLE)},                                                           // a+1 ≤ a
		{con(tn("a"), tn("b"), opLE), con(tn("b"), tn("a"), opLT)},                                  // a≤b, b<a
		{con(tn("a"), tn("b"), opLE), con(tn("b"), tn("c"), opLE), con(tn("c"), tn("a"), opLT)},     // cycle
		{con(tn("2 * a"), tn("b"), opLE), con(tn("b"), tn("a"), opLE), con(tn("1"), tn("a"), opLE)}, // 2a≤b≤a, a≥1
		{con(tn("a + b"), tn("2"), opLE), con(tn("2"), tn("a"), opLE), con(tn("1"), tn("b"), opLE)}, // a+b≤2, a≥2, b≥1
	}
	for i, cs := range unsat {
		rows, lambda, ok := LinRefute(cs)
		if !ok {
			t.Errorf("case %d: expected refutation, got none", i)
			continue
		}
		if !checkCert(rows, lambda) {
			t.Errorf("case %d: invalid Farkas certificate %v", i, lambda)
		}
		if satisfiable(cs, a, b, c, 8) {
			t.Errorf("case %d: refuted but brute-force SAT", i)
		}
	}
}

func TestLinRefuteSat(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")

	sat := [][]LinConstraint{
		{},
		{con(tn("a"), tn("b"), opLE)},
		{con(tn("a"), tn("b"), opLE), con(tn("b"), tn("c"), opLE)},
		{con(tn("a"), tn("b"), opLT), con(tn("b"), tn("c"), opLT)},
		{con(tn("a"), tn("b + 1"), opLE)},
		{con(tn("a + b"), tn("10"), opLE), con(tn("1"), tn("a"), opLE)},
	}
	for i, cs := range sat {
		if _, _, ok := LinRefute(cs); ok {
			t.Errorf("case %d: refuted a satisfiable system", i)
		}
		if !satisfiable(cs, a, b, c, 8) {
			t.Errorf("case %d: test bug — claimed SAT but brute-force UNSAT", i)
		}
	}
}

func TestLinRefuteNonlinearDeclined(t *testing.T) {
	if _, _, ok := LinRefute([]LinConstraint{con(tn("a * b"), tn("a"), opLE)}); ok {
		t.Error("refuted a nonlinear constraint set")
	}
}

// `>` / `≥` HYPOTHESES. A `>`/`≥` hyp is canonicalized to the swapped `<`/`≤`
// for the linear machinery, but its ORIGINAL term must remain the carried
// hypothesis (LinConstraint.Hyp + canonAssume's gt/geBridge), so the refutation
// stays a subset of the goal's hyps. checkProve/checkProveWith assert exactly
// that (a stray rebuilt `<`/`≤` hyp would fail the subset check), so these tests
// pin the invariant, not just the ok verdict. We do NOT lean on any upstream
// `>`/`≥`→`<`/`≤` normalization — omega handles it itself.

func TestForwardProversGtHyps(t *testing.T) {
	// ℚ-valid from `>`/`≥` hyps (LinProve suffices).
	checkProve(t, "a>b ⊢ b<a", []Term{tb("a > b")}, tb("b < a"), true)
	checkProve(t, "a>=b ⊢ b<=a", []Term{tb("a >= b")}, tb("b <= a"), true)
	checkProve(t, "a>b,b>c ⊢ a>c", []Term{tb("a > b"), tb("b > c")}, tb("a > c"), true)
	checkProve(t, "a>=b,b>=c ⊢ a>=c", []Term{tb("a >= b"), tb("b >= c")}, tb("a >= c"), true)
	checkProve(t, "a>b ⊢ a>=b", []Term{tb("a > b")}, tb("a >= b"), true)

	// mixed `>` hyp with a `<` goal that still needs the hyp.
	checkProve(t, "a>b+1 ⊢ b<a", []Term{tb("a > b + 1")}, tb("b < a"), true)

	// not derivable: a>b does not give b>a.
	checkProve(t, "a>b ⊬ b>a", []Term{tb("a > b")}, tb("b > a"), false)
}

func TestForwardProversGtHypsInteger(t *testing.T) {
	installTestBundle(t) // integer cut leaves (TestThm stand-ins)
	// Integer-only from a `>` hyp: a>b ⟺ b+1≤a over ℤ; ℚ-Farkas can't bridge it
	// (b < a < b+1 is ℚ-SAT). OmegaProve closes it; LinProve must not.
	checkProveWith(t, "OmegaProve a>b ⊢ b+1<=a", OmegaProve,
		[]Term{tb("a > b")}, tb("b + 1 <= a"), true)
	if _, ok := LinProve(numSeq(tb("a > b")), tb("b + 1 <= a")); ok {
		t.Error("guard: LinProve should NOT prove a>b ⊢ b+1<=a (needs integrality)")
	}

	// `≥` hyp combined with suc in the goal, exercising both new paths at once:
	// a≥suc b ⟝ b+1≤a, and b < b+1 ≤ a ⟹ b<a (ℚ-valid; OmegaProve subsumes it).
	checkProveWith(t, "OmegaProve a>=suc b ⊢ b<a", OmegaProve,
		[]Term{tb("a >= suc(b)")}, tb("b < a"), true)
}

// TestProbe_OmegaBoolIffHyp is the regression guard for the panic harvested
// during a session proving left cancellation of a product equation (inspect → enumerateStructuralFacts
// → arith tactic → omega).
//
// Root cause: parseHypConstraint uses ext.MatchesEQ, which fires on a boolean
// `⇔` (core.Eq at bool type). Its sides were then handed to isLinear → linOf,
// whose fallback `return linAtom(t), true` accepted ANY term as an opaque atom
// regardless of type. So a boolean ⇔-hypothesis like `(a=b) ⇔ (c=d)` was admitted
// as a numeric linear constraint with bool-typed Lhs/Rhs. During refutation,
// toTerm rebuilt the monomial as `star(Numeral(coeff), atom)` = Apply(natStar,
// Numeral, boolTerm); natStar expects a num 2nd operand, so the Assert in
// core.Apply (applied_term.go) failed: panic "Should not happen."
//
// This is exactly the hyp shape present in that proof's suc/suc leaf
// (the IH iff `((suc m * n) = (suc m * suc p)) ⇔ (n = suc p)`), which is why
// `inspect` on that goal panicked and left the session un-inspectable.
//
// linOf guards its fallback atom branch on the domain's element-type guard
// (isElem), and linConstraint
// additionally requires both sides be num terms. A bool `⇔` hyp is therefore
// dropped (not treated as a linear constraint), so omega never builds
// `coeff * boolTerm`.
//
// Expected post-fix: OmegaProve/LinProve must return a verdict WITHOUT panicking.
// The goal `a=b` does not follow from a single bool `⇔` hyp (the constraint is
// dropped), so both decline cleanly (ok=false).
func TestProbe_OmegaBoolIffHyp(t *testing.T) {
	// (a=b) ⇔ (c=d): a boolean hypothesis whose sides are num-equalities.
	boolIffHyp := tb("(a = b) <=> (c = d)")
	goal := tb("a = b") // a linear num equality goal → triggers the `=` refute path

	// This must return a clean verdict, not panic inside toTerm.
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("PANIC reproduced (bug NOT fixed): %v", r)
		}
	}()

	if _, ok := OmegaProve(slices.Values([]Term{boolIffHyp}), goal); ok {
		t.Errorf("OmegaProve: goal a=b should not follow from a bool ⇔ hyp (got ok=true)")
	}
	if _, ok := LinProve(slices.Values([]Term{boolIffHyp}), goal); ok {
		t.Errorf("LinProve: goal a=b should not follow from a bool ⇔ hyp (got ok=true)")
	}
}

type proveFunc = func(iter.Seq[Term], Term) (*prop.PropWrapper, bool)

// LinProve tests: the forward `{hyps} ⊢ goal` path. We check (a) the ok verdict
// matches whether the goal is genuinely linear-valid given the hyps, and (b) on
// success the produced proof actually concludes `goal` with hyps drawn only from
// the inputs (so a tactic could close the goal with it via IsStronger). Leaves
// are placeholders; the kernel COMPOSITION (negate → refute → NegHyp → duality)
// is real and any misalignment panics here.

// checkProve drives LinProve and validates the result against the contract.
func checkProve(t *testing.T, name string, hyps []Term, goal Term, wantOK bool) {
	t.Helper()
	checkProveWith(t, "LinProve "+name, LinProve, hyps, goal, wantOK)
}

// checkProveWith validates an arbitrary prover (LinProve or OmegaProve): the ok
// verdict matches, and on success the proof concludes goal with hyps drawn only
// from the inputs (so a tactic could close the goal via IsStronger).
func checkProveWith(t *testing.T, name string, prove proveFunc, hyps []Term, goal Term, wantOK bool) {
	t.Helper()
	w, ok := prove(slices.Values(hyps), goal)
	if ok != wantOK {
		t.Errorf("%s: ok = %v, want %v", name, ok, wantOK)
		return
	}
	if !ok {
		return
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("%s: conclusion = %v, want %v", name, w.Conclusion(), goal)
	}
	for i := 0; i < w.NumHyps(); i++ {
		h := w.Hyp(i)
		found := false
		for _, hy := range hyps {
			if h.AlphaEquals(hy) {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("%s: stray hypothesis %v not among the input hyps", name, h)
		}
	}
}

func TestLinProveValid(t *testing.T) {
	cases := []struct {
		name string
		hyps []string
		goal string
	}{
		// provable from no hypotheses (pure arithmetic facts)
		{"a < a+1", nil, "a < a + 1"},
		{"a <= a", nil, "a <= a"},
		{"a <= a+1", nil, "a <= a + 1"},
		{"0 <= a", nil, "0 <= a"},
		{"a != a+1", nil, "~(a = a + 1)"},
		{"a+1 > a", nil, "a + 1 > a"},
		{"a+1 >= a", nil, "a + 1 >= a"},
		{"1 <= 2", nil, "1 <= 2"},
		// provable from hypotheses
		{"trans <=", []string{"a <= b", "b <= c"}, "a <= c"},
		{"trans <", []string{"a < b", "b < c"}, "a < c"},
		{"<= from <", []string{"a < b"}, "a <= b"},
		{"assumption <=", []string{"a <= b"}, "a <= b"},
		{"antisym =", []string{"a <= b", "b <= a"}, "a = b"},
	}
	for _, tc := range cases {
		var hyps []Term
		for _, h := range tc.hyps {
			hyps = append(hyps, tb(h))
		}
		checkProve(t, tc.name, hyps, tb(tc.goal), true)
	}
}

func TestLinProveUnprovable(t *testing.T) {
	cases := []struct {
		name string
		hyps []string
		goal string
	}{
		{"a<b no hyps", nil, "a < b"},
		{"a<=b no hyps", nil, "a <= b"},
		{"b<=a from a<=b", []string{"a <= b"}, "b <= a"},
		{"a<b from a<=b", []string{"a <= b"}, "a < b"},
		{"b<a from a<b", []string{"a < b"}, "b < a"},
		{"a=b from a<=b", []string{"a <= b"}, "a = b"},
	}
	for _, tc := range cases {
		var hyps []Term
		for _, h := range tc.hyps {
			hyps = append(hyps, tb(h))
		}
		checkProve(t, tc.name, hyps, tb(tc.goal), false)
	}
}

func TestLinProveNonArithDeclined(t *testing.T) {
	// A bare term (not a comparison) is not a linear goal.
	checkProve(t, "bare var", nil, tn("a"), false)
	// Under the monomial basis a nonlinear product is a canonical (nonnegative)
	// monomial atom, so a comparison linear IN that atom proves: `a·b < a·b + 1`
	// is `X < X + 1`. (A product the goal cannot relate, e.g. `a·b < 1`, still
	// declines — no bound on the unknown.)
	checkProve(t, "monomial product X<X+1", nil, tb("a * b < a * b + 1"), true)
	checkProve(t, "unbounded product", nil, tb("a * b < 1"), false)
	// Non-arith hyps are ignored, not fatal: the goal still proves from the
	// arith hyp alone.
	checkProve(t, "ignore junk hyp", []Term{tn("p"), tb("a <= b"), tb("b <= a")}, tb("a = b"), true)
}

// TestLinProveNonCanonicalNumeralDeclined pins the panic fix for goals carrying
// a well-formed but NON-canonical BIT-tower (the shape an NumeralEq clause
// instantiated at n := _0 produces: `_0 = bit0 _0`). Before the asLiteral
// canonicality gate (domain.go literalValue), LinProve's `=` route refuted the
// ≤ direction trivially and the certificate replay panicked in core.EqTrans
// ("Should not happen.") because normalizeProof returned Refl(bit0 _0) against
// the canonical toTerm _0. Post-fix the literal declines, so LinProve returns
// a clean not-proved — no panic. (The goal is true — both sides denote 0 — but
// deciding it belongs to the refuter's NumeralEq route, not linarith.)
func TestLinProveNonCanonicalNumeralDeclined(t *testing.T) {
	goal := eqT(natZero, bit0(natZero)) // `_0 = bit0 _0`
	w, ok := LinProve(slices.Values([]Term{}), goal)
	if ok {
		t.Errorf("LinProve proved %v; expected a clean decline (w=%v)", goal, w)
	}
}

// TestOmegaProve covers the integer core: OmegaProve must (a) prove everything
// LinProve proves, and (b) additionally prove goals that need integrality —
// while still declining genuinely invalid goals.
func TestOmegaProve(t *testing.T) {
	installTestBundle(t) // integer cut / divmod / divisibility leaves (TestThm stand-ins)
	omega := func(name string, hyps []Term, goal Term, wantOK bool) {
		t.Helper()
		checkProveWith(t, "OmegaProve "+name, OmegaProve, hyps, goal, wantOK)
	}

	// integer-specific: ℚ-Farkas cannot prove these, the rounding cut / GCD can.
	//   b<a+1 ⟺ b≤a over ℤ  (the canonical integrality example)
	omega("b<a+1 ⊢ b<=a", []Term{tb("b < a + 1")}, tb("b <= a"), true)
	//   ¬(2a=1): negate to 2a=1, GCD test gcd(2)∤1 refutes.
	omega("2a != 1", nil, tb("~(2 * a = 1)"), true)
	//   2a<=1 ⟹ a=0 over ℤ (a≤0 from the cut, a≥0 from nonnegativity).
	omega("2a<=1 ⊢ a=0", []Term{tb("2 * a <= 1")}, tb("a = 0"), true)

	// LinProve fails on b<a+1 ⊢ b<=a (rational gap) — OmegaProve is the upgrade.
	if _, ok := LinProve(numSeq(tb("b < a + 1")), tb("b <= a")); ok {
		t.Error("guard: LinProve should NOT prove b<a+1 ⊢ b<=a (it needs integrality)")
	}

	// everything LinProve proves, OmegaProve proves too.
	omega("trans <=", []Term{tb("a <= b"), tb("b <= c")}, tb("a <= c"), true)
	omega("a<a+1", nil, tb("a < a + 1"), true)
	omega("antisym =", []Term{tb("a <= b"), tb("b <= a")}, tb("a = b"), true)

	// still declines genuinely invalid / non-arith goals.
	omega("a<=b no hyps", nil, tb("a <= b"), false)
	omega("2a=1 unsat goal", nil, tb("2 * a = 1"), false)
	omega("bare var", nil, tn("a"), false)
}

// numSeq is a tiny helper to pass term hyps as an iter.Seq in guard checks.
func numSeq(hyps ...Term) iter.Seq[Term] { return slices.Values(hyps) }

func TestComparisonSidesLinear(t *testing.T) {
	linear := []Term{
		tb("a < b + 1"), tb("a <= b"), tb("a = b"), tb("~(a = b)"),
		tb("a + 1 > b"), tb("a >= 0"),
	}
	for _, g := range linear {
		if !ComparisonSidesLinear(g) {
			t.Errorf("expected linear: %v", g)
		}
	}

	nonlinear := []Term{
		tb("a * b < 1"), tb("a * b = a"), tb("a <= a * b"),
	}
	for _, g := range nonlinear {
		if ComparisonSidesLinear(g) {
			t.Errorf("expected nonlinear: %v", g)
		}
	}

	// not a comparison at all
	if ComparisonSidesLinear(tn("a")) {
		t.Error("a bare term is not a comparison")
	}
}

// Certificate-replay tests: every refutation must produce a real `{hyps} ⊢ ⊥` whose
// hypotheses are all among the input constraint terms. Running replay exercises
// the full kernel composition (scale → sum → ring-normalize → cancel → norm_num); any
// mis-aligned EqMP/DeriveTrans/congruence panics. Leaves are placeholders, so
// soundness rides on the leaf swap, but the plumbing is real and checked here.

func constraintTerm(c LinConstraint) Term {
	if c.Hyp != nil { // a >/≥ origin carries its original term as the hypothesis
		return c.Hyp
	}
	switch c.Op {
	case opLE:
		return le(c.Lhs, c.Rhs)
	case opLT:
		return lt(c.Lhs, c.Rhs)
	default:
		return eqT(c.Lhs, c.Rhs)
	}
}

func checkRefuteProof(t *testing.T, name string, cs []LinConstraint) {
	t.Helper()
	w, ok := LinRefuteProof(cs)
	if !ok {
		t.Fatalf("%s: expected a refutation proof, got none", name)
	}
	if !w.Conclusion().Equals(prop.F) {
		t.Errorf("%s: conclusion = %v, want ⊥", name, w.Conclusion())
	}
	// every hypothesis must be one of the input constraint terms
	allowed := make([]Term, len(cs))
	for i, c := range cs {
		allowed[i] = constraintTerm(c)
	}
	for i := 0; i < w.NumHyps(); i++ {
		h := w.Hyp(i)
		found := false
		for _, a := range allowed {
			if h.AlphaEquals(a) {
				found = true
				break
			}
		}
		if !found {
			t.Errorf("%s: stray hypothesis %v not among input constraints", name, h)
		}
	}
}

func TestLinRefuteProof(t *testing.T) {
	cases := []struct {
		name string
		cs   []LinConstraint
	}{
		{"a<a", []LinConstraint{con(tn("a"), tn("a"), opLT)}},
		{"a+1<=a", []LinConstraint{con(tn("a + 1"), tn("a"), opLE)}},
		{"a<=b,b<a", []LinConstraint{con(tn("a"), tn("b"), opLE), con(tn("b"), tn("a"), opLT)}},
		{"cycle", []LinConstraint{con(tn("a"), tn("b"), opLE), con(tn("b"), tn("c"), opLE), con(tn("c"), tn("a"), opLT)}},
		{"2a<=b<=a,a>=1", []LinConstraint{
			con(tn("2 * a"), tn("b"), opLE), con(tn("b"), tn("a"), opLE), con(tn("1"), tn("a"), opLE)}},
		{"a+b<=2,a>=2,b>=1", []LinConstraint{
			con(tn("a + b"), tn("2"), opLE), con(tn("2"), tn("a"), opLE), con(tn("1"), tn("b"), opLE)}},
		{"eq: a=b, b+1<=a", []LinConstraint{con(tn("a"), tn("b"), opEQ), con(tn("b + 1"), tn("a"), opLE)}},
	}
	for _, tc := range cases {
		checkRefuteProof(t, tc.name, tc.cs)
	}
}

// ── int decide termination: bool split × ∃-binders × nonlinear products ──────
//
// Termination guard for the omega int decide. IntArithDecideWithHyps would
// never return on a goal with a boolean head (∧/∨/⇒/⇔) whose int comparison
// atoms sit under ∃/∀ binders next to a nonlinear bare-var product (`d·x`),
// were a case-split branch to run the full decider: intArithBoolLeaf EM-splits
// on binder-crossing atoms (collected across abs bodies by a raw walk), a
// branch re-enters the FULL intProveDecAtom, intImageSplit mints a fresh
// ν-var, and imageBranchImp's sub-decider re-fires the bool leaf with `done`
// reset to nil — the fresh ν-vars / α-renamed binders defeat every
// identity-keyed guard while the hyps grow monotonically. It is closed by
// (a) excluding intArithBoolLeaf and the sign split from the case-split
// branch sub-decider (intArithCollapseRewriteNoSignSplit) and (b) skipping
// binder-crossing atoms in the bool-split candidate collection
// (intComparisonAtomsOf via collectBinderFreeSubterms).
//
// Every case must RETURN within the watchdog; the verdict is free (a partial
// rewrite or nil — these shapes carry quantifiers the decider cannot decide,
// so no ⊤/⊥ outcome is pinned). The bisection controls return with neither
// exclusion in place and are kept as controls.
func TestIntDecideBoolSplitBinderCrossingTerminates(t *testing.T) {
	n, d, x := intVar("n"), intVar("d"), intVar("x")
	x1, x2 := intVar("x1"), intVar("x2")
	existsNeg := prop.Exists(x)(eqT(intNegT(n), intStarT(d, x))) // ∃x. -n = d·x
	existsNonneg := prop.Exists(x)(eqT(n, intStarT(d, x)))       // ∃x.  n = d·x
	// The Skolemized-clausal sibling body (prop_10e4e417539ea8a0 normalized):
	// ¬(x = -(d·x1)) ∨ (x = d·x2): two equalities sharing x under a bool
	// split, with a nonlinear product on each.
	siblingBody := or(
		not(eqT(x, intNegT(intStarT(d, x1)))),
		eqT(x, intStarT(d, x2)))

	cases := []struct {
		name string
		goal Term
	}{
		// The original hang shape (engine key prop_1adddf324b607876):
		// (∃x. -n = d·x) ⇔ (∃x. n = d·x).
		{"ExistsIff", eqT(existsNeg, existsNonneg)},
		// Bisection controls: each ∃-side alone, and the bare atom.
		{"ExistsNegSide", existsNeg},
		{"ExistsPosSide", existsNonneg},
		{"SingleAtomAllFree", eqT(intNegT(n), intStarT(d, x))},
		// The sibling clause, bare and under its ∀∀∀∃ prefix.
		{"SiblingClauseBody", siblingBody},
		{"SiblingClausePrenex", prop.ForAll(x)(prop.ForAll(d)(
			prop.ForAll(x1)(prop.Exists(x2)(siblingBody))))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			done := make(chan *prop.PropWrapper, 1)
			start := time.Now()
			go func() { done <- IntArithDecideWithHyps(nil)(tc.goal) }()
			select {
			case w := <-done:
				t.Logf("decide returned in %v (rewrote=%v)", time.Since(start), w != nil)
			case <-time.After(60 * time.Second):
				t.Fatalf("IntArithDecideWithHyps did not return within 60s — the int-decide non-termination regressed")
			}
		})
	}
}
