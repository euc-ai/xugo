package omega

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// With a bundle installed, the bit-recursion leaves must route through conjunct
// projection (nat_norm.go) out of the named Numeral* theorems and still
// conclude exactly the placeholder statement — and the consumers (norm_num)
// must keep working through them, with no ring↔norm_num cycle. We build each
// Numeral* as a TestThm conjunction of the placeholder leaf statements (the
// leaves fall back to placeholders while no bundle is installed).

// testArithDecisionThms holds the three comparison-decision theorems
// (NumeralLessThan / NumeralLessEq / NumeralEq) built as TestThm conjunctions of the per-bit
// placeholder leaf statements, for populating a test bundle.
type testArithDecisionThms struct{ lt, le, eq *prop.PropWrapper }

// testArithCmp assembles NumeralLessThan / NumeralLessEq / NumeralEq from the per-bit
// placeholder leaves (generalized over fresh vars, ∀-quantified), so a
// test bundle can exercise the projection machinery (projectMatch) end-to-end.
func testArithCmp() testArithDecisionThms {
	m, n := numVar("m"), numVar("n")
	ForAll := ext.ForAll
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }

	numeralLessThan := andFold(
		ltZeroZero().Conclusion(),
		ForAll(n)(ltZeroB0(n).Conclusion()),
		ForAll(n)(ltZeroB1(n).Conclusion()),
		ForAll(m)(ltB0Zero(m).Conclusion()),
		ForAll(m)(ltB1Zero(m).Conclusion()),
		ForAll(m, n)(ltB0B0(m, n).Conclusion()),
		ForAll(m, n)(ltB0B1(m, n).Conclusion()),
		ForAll(m, n)(ltB1B0(m, n).Conclusion()),
		ForAll(m, n)(ltB1B1(m, n).Conclusion()),
	)
	numeralLessEq := andFold(
		ForAll(n)(leZeroAny(n).Conclusion()),
		ForAll(m)(leB0Zero(m).Conclusion()),
		ForAll(m)(leB1Zero(m).Conclusion()),
		ForAll(m, n)(leB0B0(m, n).Conclusion()),
		ForAll(m, n)(leB0B1(m, n).Conclusion()),
		ForAll(m, n)(leB1B0(m, n).Conclusion()),
		ForAll(m, n)(leB1B1(m, n).Conclusion()),
	)
	numeralEq := andFold(
		eqZeroZero().Conclusion(),
		ForAll(n)(eqZeroB0(n).Conclusion()),
		ForAll(n)(eqZeroB1(n).Conclusion()),
		ForAll(m)(eqB0Zero(m).Conclusion()),
		ForAll(m)(eqB1Zero(m).Conclusion()),
		ForAll(m, n)(eqB0B0(m, n).Conclusion()),
		ForAll(m, n)(eqB0B1(m, n).Conclusion()),
		ForAll(m, n)(eqB1B0(m, n).Conclusion()),
		ForAll(m, n)(eqB1B1(m, n).Conclusion()),
	)
	return testArithDecisionThms{lt: mk(numeralLessThan), le: mk(numeralLessEq), eq: mk(numeralEq)}
}

func installTestBundle(t *testing.T) {
	t.Helper()
	m, n := numVar("m"), numVar("n")
	ForAll := ext.ForAll
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	ac := testArithCmp()

	numeralAdd := mk(andFold(
		ForAll(m, n)(addB0B0(m, n).Conclusion()),
		ForAll(m, n)(addB0B1(m, n).Conclusion()),
		ForAll(m, n)(addB1B0(m, n).Conclusion()),
		ForAll(m, n)(addB1B1(m, n).Conclusion()),
	))
	numeralSuc := mk(andFold(
		sucBitsZero().Conclusion(),
		ForAll(m)(sucB0(m).Conclusion()),
		ForAll(m)(sucB1(m).Conclusion()),
	))
	numeralMul := mk(andFold(
		ForAll(m, n)(mulB0(m, n).Conclusion()),
		ForAll(m, n)(mulB1(m, n).Conclusion()),
	))

	// DivModUniq: ∀m n q r. (m = q·n + r ∧ r < n) ⇒ (nat_div(m, n) = q ∧ nat_mod(m, n) = r).
	dm, dn, dq, dr := numVar("dm"), numVar("dn"), numVar("dq"), numVar("dr")
	divModUniq := mk(ForAll(dm, dn, dq, dr)(
		imply(prop.And(eqT(dm, plus(star(dq, dn), dr)), lt(dr, dn)),
			prop.And(eqT(divT(dm, dn), dq), eqT(modT(dm, dn), dr)))))

	// ModEqZero: ∀m n. (∃q. m = q·n) ⇔ (0 = nat_mod(m, n)). Bound var "q" matches
	// dvd's dividesWitness so the notDivides composition lands structurally.
	em, en, eq := numVar("em"), numVar("en"), numVar("q")
	modEqZero := mk(ForAll(em, en)(
		eqT(prop.Exists(eq)(eqT(em, star(eq, en))), eqT(Numeral(0), modT(em, en)))))

	// LessEqRightDivEq (raw-disjunction / normalized clause form, the shape roundedCut's
	// instAll([Lr,D,g]) + rdivDischargeZero consume): ∀a b c.
	// ((a ≤ nat_div(b, c)) ⇔ (c·a ≤ b)) ∨ (c = 0).
	ra, rb, rc := numVar("ra"), numVar("rb"), numVar("rc")
	lessEqRightDivEq := mk(ForAll(ra, rb, rc)(
		or(eqT(le(ra, divT(rb, rc)), le(star(rc, ra), rb)), eqT(rc, Numeral(0)))))

	// SucLessEqIffLessThan: ∀m n. (m < n) ⇔ (suc m ≤ n) — the strict→non-strict bridge the
	// `<` rows feed the rounding cut through.
	lm, ln := numVar("lm"), numVar("ln")
	sucLessEqIffLessThan := mk(ForAll(lm, ln)(eqT(lt(lm, ln), le(sucT(lm), ln))))

	SetNatLemmaBundle(&NatLemmaBundle{
		NumeralAdd: numeralAdd, NumeralSuc: numeralSuc, NumeralMul: numeralMul,
		NumeralLessThan: ac.lt, NumeralLessEq: ac.le, NumeralEq: ac.eq,
		DivModUniq: divModUniq, ModEqZero: modEqZero,
		LessEqRightDivEq: lessEqRightDivEq, SucLessEqIffLessThan: sucLessEqIffLessThan,
	})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
}

func eqConcl(t *testing.T, name string, w *prop.PropWrapper, want Term) {
	t.Helper()
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("%s: got\n  %v\nwant\n  %v", name, w.Conclusion(), want)
	}
}

func TestBundleWiring(t *testing.T) {
	installTestBundle(t)
	a, b := numVar("a"), numVar("b")

	// Arithmetic leaves route through NumeralAdd/NumeralSuc/NumeralMul projection.
	eqConcl(t, "addB0B0", addB0B0(a, b), tb("bit0(a) + bit0(b) = bit0(a + b)"))
	eqConcl(t, "addB1B1", addB1B1(a, b), tb("bit1(a) + bit1(b) = bit0(suc(a + b))"))
	eqConcl(t, "sucB1", sucB1(a), tb("suc(bit1(a)) = bit0(suc(a))"))
	eqConcl(t, "mulB1", mulB1(a, b), tb("bit1(a) * b = bit0(a * b) + b"))

	// Comparison leaves route through NumeralLessThan/NumeralLessEq/NumeralEq projection.
	eqConcl(t, "ltB0B0", ltB0B0(a, b), tb("(bit0(a) < bit0(b)) <=> (a < b)"))
	eqConcl(t, "ltB0B1", ltB0B1(a, b), tb("(bit0(a) < bit1(b)) <=> (a <= b)"))
	eqConcl(t, "leB1B0", leB1B0(a, b), tb("(bit1(a) <= bit0(b)) <=> (a < b)"))
	eqConcl(t, "eqB0B1", eqB0B1(a, b), tb("(bit0(a) = bit1(b)) <=> ⊥"))
	eqConcl(t, "leZeroAny", leZeroAny(a), tb("0 <= a <=> ⊤"))
}

// TestBundleConsumers checks the full chain (consumer → leaf → projection) still
// computes correct numeral verdicts with the bundle on — and that there is no
// ring↔norm_num recursion (RingProveFull folds coefficients via norm_num, whose
// leaves now project rather than call ring).
func TestBundleConsumers(t *testing.T) {
	installTestBundle(t)

	add, ok := NormNatAdd(Numeral(2), Numeral(3))
	if !ok || !prop.Rhs(add).AlphaEquals(Numeral(5)) {
		t.Errorf("NormNatAdd(2,3): ok=%v rhs=%v, want 5", ok, prop.Rhs(add))
	}
	mul, ok := NormNatMul(Numeral(2), Numeral(3))
	if !ok || !prop.Rhs(mul).AlphaEquals(Numeral(6)) {
		t.Errorf("NormNatMul(2,3): ok=%v rhs=%v, want 6", ok, prop.Rhs(mul))
	}
	ltTrue, ok := NormNatLt(Numeral(2), Numeral(3))
	if !ok || !prop.Rhs(ltTrue).Equals(prop.T) {
		t.Errorf("NormNatLt(2,3): ok=%v rhs=%v, want T", ok, prop.Rhs(ltTrue))
	}
	ltFalse, ok := NormNatLt(Numeral(3), Numeral(2))
	if !ok || !prop.Rhs(ltFalse).Equals(prop.F) {
		t.Errorf("NormNatLt(3,2): ok=%v rhs=%v, want F", ok, prop.Rhs(ltFalse))
	}
	eqTrue, ok := NormNatEq(Numeral(4), Numeral(4))
	if !ok || !prop.Rhs(eqTrue).Equals(prop.T) {
		t.Errorf("NormNatEq(4,4): ok=%v rhs=%v, want T", ok, prop.Rhs(eqTrue))
	}

	// RingProveFull (which folds coefficients through norm_num) must terminate.
	a := numVar("a")
	if _, ok := RingProveFull(plus(a, a), star(Numeral(2), a)); !ok {
		t.Error("RingProveFull(a+a, 2*a) failed with bundle on")
	}
}

// TestBundleMacroWiring installs the macro library theorems (built from the
// placeholder leaves, ∀-generalized) and checks the ring-AC / duality / order
// leaves route through the bundle to the same statements.
func TestBundleMacroWiring(t *testing.T) {
	p, q, r, s := numVar("p"), numVar("q"), numVar("r"), numVar("s")
	ForAll := ext.ForAll
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	SetNatLemmaBundle(&NatLemmaBundle{
		AddSym:          mk(ForAll(p, q)(commuteADD(p, q).Conclusion())),
		AddAssoc:        mk(ForAll(p, q, r)(associateADD(p, q, r).Conclusion())),
		MulSym:          mk(ForAll(p, q)(commuteMUL(p, q).Conclusion())),
		NotLessThan:     mk(ForAll(p, q)(notLT(p, q).Conclusion())),
		NotLessEq:       mk(ForAll(p, q)(notLE(p, q).Conclusion())),
		LessEqAntisym:   mk(ForAll(p, q)(lessEqAntisym(p, q).Conclusion())),
		LessEqOfEq:      mk(ForAll(p, q)(lessEqOfEq(p, q).Conclusion())),
		ZeroLessEq:      mk(ForAll(p)(zeroLe(p).Conclusion())),
		LessEqAdd2:      mk(ForAll(p, q, r, s)(addLe2(p, q, r, s).Conclusion())),
		LessEqAddCancel: mk(ForAll(p, q, r)(addLcancelLe(p, q, r).Conclusion())),
	})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	a, b, c, d := numVar("a"), numVar("b"), numVar("c"), numVar("d")
	eqConcl(t, "commuteADD", commuteADD(a, b), tb("a + b = b + a"))
	eqConcl(t, "associateADD", associateADD(a, b, c), tb("(a + b) + c = a + (b + c)"))
	eqConcl(t, "notLT", notLT(a, b), tb("~(a < b) <=> b <= a"))
	eqConcl(t, "lessEqAntisym", lessEqAntisym(a, b), tb("a <= b => b <= a => a = b"))
	eqConcl(t, "lessEqOfEq", lessEqOfEq(a, b), tb("a = b => a <= b"))
	eqConcl(t, "zeroLe", zeroLe(a), tb("0 <= a"))
	eqConcl(t, "addLe2", addLe2(a, b, c, d), tb("a <= b => c <= d => a + c <= b + d"))
	eqConcl(t, "addLcancelLe", addLcancelLe(a, b, c), tb("(a + b <= a + c) <=> (b <= c)"))
}

// TestBundleDividesIntroReal checks dividesIntro is a REAL ∃-introduction with no
// bundle field of its own: it concludes the nat-native `(b = a·k) ⇒ ∃q. b = q·a`
// (MulSym bridge + InstExists), not a `divides` const. Runs with no
// bundle installed — dividesIntro derives regardless (the only named dependency,
// MulSym, falls back to its placeholder here but the composition is real).
func TestBundleDividesIntroReal(t *testing.T) {
	a, b, k := numVar("a"), numVar("b"), numVar("k")
	eqConcl(t, "dividesIntro", dividesIntro(a, b, k), imply(eqT(b, star(a, k)), dvd(a, b)))
}

// TestNotDividesReal checks that with ModEqZero and DivModUniq
// (DivModUniq) supplied, notDivides derives a REAL `⊢ ¬∃q. n = q·d` for a genuine
// non-divisor (ok=true, no `divides`/real route) via ModEqZero + the
// proof-producing nat_mod evaluator (nat_mod(n, d) = r ≠ 0 ⟹ RHS ⊥ ⟹ ¬∃).
func TestNotDividesReal(t *testing.T) {
	installTestBundle(t) // supplies ModEqZero + DivModUniq + the witness arith leaves
	d, n := Numeral(3), Numeral(7)
	w, ok := notDivides(d, n)
	if !ok {
		t.Fatal("notDivides declined despite ModEqZero + DivModUniq present")
	}
	if !w.Conclusion().AlphaEquals(prop.Not(dvd(d, n))) {
		t.Errorf("notDivides(3,7): concl %v, want ¬∃q. 7 = q·3", w.Conclusion())
	}
	if w.NumHyps() != 0 {
		t.Errorf("notDivides(3,7): %d stray hyps, want 0", w.NumHyps())
	}
}

// installTestFabricator installs the bundle-nil placeholder fabricator for
// omega's own algorithm unit tests, which exercise the kernel composition
// without the real corpus bundle. This is the SOLE core.TestThm reference for
// this package outside explicit per-test bundle fabrication (bundle_test.go);
// production never compiles it, so core.TestThm stays out of the production
// build (bundle.go).
func installTestFabricator() {
	SetPlaceholderFabricator(func(concl Term) *prop.PropWrapper {
		return prop.WrapProp(core.TestThm(concl))
	})
}

func init() { installTestFabricator() }

// withoutFabricator removes the placeholder fabricator for the duration of a
// test that wants PRODUCTION behavior — a bundle-nil leaf must panic, not fall
// back to a stand-in — and reinstalls it on cleanup. Use it to assert that an
// installed bundle binds a leaf's real theorem (a degrade then panics, failing
// the test loudly) — the way a test opts into production no-degrade behavior
// inside this fabricator-installed package.
func withoutFabricator(t *testing.T) {
	t.Helper()
	SetPlaceholderFabricator(nil)
	t.Cleanup(installTestFabricator)
}

// TestPromiseBackedBundleForcedOnUse is the weak-B-lazy end-to-end check on the
// omega side: a LemmaBundle field is backed by a core.ThmPromise (statement
// now, certificate deferred) instead of a TestThm. omega consumes it
// (commuteADD routes through AddSym), producing a promise-backed wrapper that
// does NOT run the builder. The force happens only at the arith-tactic boundary
// — exactly the core.AsThm(w).Force call that arith_tactics.closeByOmega now makes —
// at which point the lemma builds exactly once, on use, and the result carries
// the correct instantiated conclusion.
//
// The builder here stands in for a corpus entry's Build (the real-entry half
// is covered by library/serve's bundle binding tests; the import graph —
// library → prover → tactic → omega — forbids pulling an entry's Build into a
// package omega test, so the two halves are validated separately).
func TestPromiseBackedBundleForcedOnUse(t *testing.T) {
	p, q := numVar("p"), numVar("q")
	// The exact general statement omega expects for AddSym: ∀p q. p+q = q+p.
	addSymTerm := ext.ForAll(p, q)(commuteADD(p, q).Conclusion())
	addSymStmt := core.MakeProp(addSymTerm)

	built := 0
	promise := core.Promise(addSymStmt, func(f core.Forcer) core.ThmCert {
		built++
		return core.TestThm(addSymTerm) // stands in for AddSym's proof
	})

	SetNatLemmaBundle(&NatLemmaBundle{AddSym: prop.WrapProp(promise)})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	// omega instantiates the promise-backed lemma at a,b. This must stay lazy.
	a, b := numVar("a"), numVar("b")
	w := commuteADD(a, b)
	if w.Proved() {
		t.Fatal("omega leaf is already proved — promise was forced before the boundary")
	}
	if built != 0 {
		t.Fatalf("builder ran %d times during omega derivation (want 0 — must stay lazy)", built)
	}

	// The arith-tactic boundary: closeByOmega's core.AsThm(w).Force. Forcing the
	// derived promise builds exactly the bundle lemma it used, on demand.
	thm := core.Force(context.Background(), core.AsThm(w))
	if want := core.Eq(plus(a, b), plus(b, a)); !thm.Conclusion().AlphaEquals(want) {
		t.Fatalf("forced thm concl = %v, want %v", thm.Conclusion(), want)
	}
	if built != 1 {
		t.Fatalf("builder ran %d times (want exactly 1, on first use)", built)
	}
	// The bundle's root promise is now realized — a second consumer is a cache hit.
	if !promise.Proved() {
		t.Fatal("bundle root promise not realized after force")
	}
}

// DeriveLessEqOfEqSwapped must produce ⊢ ∀a b.(a=b)⇒(b≤a) from a (here TestThm-backed)
// LessEqOfEq, and the result must bind omega's lessEqOfEqSwapped leaf.
func TestDeriveLessEqOfEqSwapped(t *testing.T) {
	m, n := numVar("m"), numVar("n")
	a, b := numVar("a"), numVar("b")
	ForAll := ext.ForAll

	lessEqOfEq := prop.WrapProp(core.TestThm(
		ForAll(m, n)(imply(eqT(m, n), le(m, n)))))

	got := DeriveLessEqOfEqSwapped(lessEqOfEq)
	want := ForAll(a, b)(imply(eqT(a, b), le(b, a)))
	if !got.Conclusion().AlphaEquals(want) {
		t.Fatalf("DeriveLessEqOfEqSwapped:\n  got  %v\n  want %v", got.Conclusion(), want)
	}

	SetNatLemmaBundle(&NatLemmaBundle{LessEqOfEqSwapped: got})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
	leaf := lessEqOfEqSwapped(a, b)
	if wantLeaf := imply(eqT(a, b), le(b, a)); !leaf.Conclusion().AlphaEquals(wantLeaf) {
		t.Errorf("lessEqOfEqSwapped leaf did not bind:\n  got  %v\n  want %v", leaf.Conclusion(), wantLeaf)
	}
}

func and(a, b Term) Term  { return ext.Apply(prop.AND, a, b) }
func iffT(a, b Term) Term { return eqT(a, b) } // ⇔ is `=` at bool

// CurryIffConj: corpus X⇔(A∧B) → A⇒B⇒X; must bind the lessEqAntisym leaf.
func TestCurryIffConj(t *testing.T) {
	m, n := numVar("m"), numVar("n")
	a, b := numVar("a"), numVar("b")
	ForAll := ext.ForAll

	norm := prop.WrapProp(core.TestThm(
		ForAll(m, n)(iffT(eqT(m, n), and(le(m, n), le(n, m))))))

	got := CurryIffConj(norm)
	want := ForAll(m, n)(imply(le(m, n), imply(le(n, m), eqT(m, n))))
	if !got.Conclusion().AlphaEquals(want) {
		t.Fatalf("CurryIffConj:\n  got  %v\n  want %v", got.Conclusion(), want)
	}
	SetNatLemmaBundle(&NatLemmaBundle{LessEqAntisym: got})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
	if leaf := lessEqAntisym(a, b); !leaf.Conclusion().AlphaEquals(
		imply(le(a, b), imply(le(b, a), eqT(a, b)))) {
		t.Errorf("lessEqAntisym leaf did not bind: %v", leaf.Conclusion())
	}
}

// MulCancelToScale: corpus (m*n≤m*p)⇔((n≤p)∨(m=0)) → (n≤p)⇒(m*n≤m*p); binds leScale.
func TestMulCancelToScale(t *testing.T) {
	m, n, p := numVar("m"), numVar("n"), numVar("p")
	a, b := numVar("a"), numVar("b")
	ForAll := ext.ForAll

	norm := prop.WrapProp(core.TestThm(
		ForAll(m, n, p)(iffT(le(star(m, n), star(m, p)), or(le(n, p), eqT(m, natZero))))))

	got := MulCancelToScale(norm)
	want := ForAll(m, n, p)(imply(le(n, p), le(star(m, n), star(m, p))))
	if !got.Conclusion().AlphaEquals(want) {
		t.Fatalf("MulCancelToScale:\n  got  %v\n  want %v", got.Conclusion(), want)
	}
	SetNatLemmaBundle(&NatLemmaBundle{LessEqMulMono: got})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
	c := uint64(2)
	if leaf := leScale(integerOfUint(c), a, b); !leaf.Conclusion().AlphaEquals(
		imply(le(a, b), le(star(Numeral(c), a), star(Numeral(c), b)))) {
		t.Errorf("leScale leaf did not bind: %v", leaf.Conclusion())
	}
}

// TestLtScaleDischarge: ltScale reads the 2-premise LessThanMulMono field
// (CurryIffConj of the cancel-iff) and discharges `c≠0` numerically, leaving
// (a<b)⇒(c·a<c·b). Run with the placeholder fabricator cleared (production
// behavior) — if the discharge fell back to a placeholder (field mis-shaped or
// NormNatNe failed), it panics at the seam. The eq
// comparison leaves (for NormNatNe(2,0)) are supplied via a minimal synthetic
// NumeralEq (the `(k=0)⇔(0=bit0 k)` clause + the `0≠bit1 n` bare fact).
func TestLtScaleDischarge(t *testing.T) {
	m, n, p := numVar("m"), numVar("n"), numVar("p")
	a, b := numVar("a"), numVar("b")
	k, nn := numVar("k"), numVar("nn")
	ForAll := ext.ForAll
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }

	ltMultNorm := mk(ForAll(m, n, p)(iffT(
		lt(star(m, n), star(m, p)), and(not(eqT(m, natZero)), lt(n, p)))))
	numeralEq := mk(andFold(
		ForAll(k)(iffT(eqT(k, natZero), eqT(natZero, bit0(k)))), // (k=0)⇔(0=bit0 k)
		ForAll(nn)(not(eqT(natZero, bit1(nn)))),                 // 0≠bit1 n
	))

	SetNatLemmaBundle(&NatLemmaBundle{
		LessThanMulMono: CurryIffConj(ltMultNorm),
		NumeralEq:       numeralEq,
	})
	withoutFabricator(t) // production behavior: a degrade panics, proving ltScale bound the field
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	got := ltScale(integerOf(2), a, b) // no fabricator: panics on degrade
	want := imply(lt(a, b), lt(star(Numeral(2), a), star(Numeral(2), b)))
	if !got.Conclusion().AlphaEquals(want) {
		t.Fatalf("ltScale:\n  got  %v\n  want %v", got.Conclusion(), want)
	}
}
