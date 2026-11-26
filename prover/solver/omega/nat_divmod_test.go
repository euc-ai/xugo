package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// These tests are the bundle-fabricated guard for the nat_div/nat_mod layer.
// Real-bundle end-to-end coverage lives in library/serve
// (TestInstallNatBundleBindingDivMod); this file pins the normal-form
// statement shapes the leaves project from + the discharge logic, so
// a shape drift surfaces here at unit speed without needing the corpus build.
//
// Shapes pinned (the EXACT normal forms):
//
//	DivLessEq   : ∀m n. nat_div(m,n) ≤ m
//	ModLessEq   : ∀m n. nat_mod(m,n) ≤ m
//	ModRefl : ∀n. 0 = nat_mod(n,n)
//	DivZero : ∀n. 0 = nat_div(n,0)
//	ModZero : ∀n. n = nat_mod(n,0)
//	ModLessThan   : ∀m n. ¬(m<n) ∨ (m = nat_mod(m,n))   (clause form; leaf wants
//	                                            (m<n) ⇒ (m = nat_mod(m,n)) via
//	                                            PromiseForGeneral)
//	DivRefl : ∀n. (n=0) ∨ (1 = nat_div(n,n))
//	Division : ∀n m. (n=0) ∨ (nat_mod(m,n)<n ∧ m = nat_div(m,n)·n + nat_mod(m,n))
//	DivModUniq: already pinned by the int-cut layer
func installDivModTestBundle(t *testing.T) func() {
	t.Helper()
	m, n := numVar("m"), numVar("n")
	mk := func(c core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }

	prev := natLemmaBundle
	b := &NatLemmaBundle{}
	if prev != nil { // preserve already-installed fields (DivModUniq etc.)
		*b = *prev
	}
	// Unconditional bounds.
	b.DivLessEq = mk(ext.ForAll(m, n)(le(divT(m, n), m)))
	b.ModLessEq = mk(ext.ForAll(m, n)(le(modT(m, n), m)))
	b.ModRefl = mk(ext.ForAll(n)(eqT(natZero, modT(n, n))))
	b.DivZero = mk(ext.ForAll(m)(eqT(natZero, divT(m, natZero))))
	b.ModZero = mk(ext.ForAll(m)(eqT(m, modT(m, natZero))))
	// Clausal ModLessThan — leaf wants the implication.
	b.ModLessThan = mk(ext.ForAll(m, n)(imply(lt(m, n), eqT(m, modT(m, n)))))
	// Disjunction-form DivRefl.
	b.DivRefl = mk(ext.ForAll(n)(or(eqT(n, natZero), eqT(Numeral(1), divT(n, n)))))
	// Division binder order (n, m): n=0 ∨ (nat_mod<n ∧ identity).
	b.Division = mk(ext.ForAll(n, m)(or(
		eqT(n, natZero),
		and(lt(modT(m, n), n),
			eqT(m, plus(star(divT(m, n), n), modT(m, n)))))))
	// PosIffNonzero shape: ∀n. (n ≠ 0) ⇔ (0 < n). Powers proveDivModSplitOnZero.
	b.PosIffNonzero = mk(ext.ForAll(n)(eqT(not(eqT(n, natZero)), lt(natZero, n))))

	SetNatLemmaBundle(b)
	return func() { SetNatLemmaBundle(prev) }
}

// TestDivModUnconditional: ModLessEq / DivLessEq / ModRefl leaves produce the expected
// proof shapes. These never degrade to a placeholder regardless of side conditions.
func TestDivModUnconditional(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")

	if got, want := modLessEq(m, n).Conclusion(), le(modT(m, n), m); !got.AlphaEquals(want) {
		t.Errorf("modLessEq: got %v, want %v", got, want)
	}
	if got, want := divLessEq(m, n).Conclusion(), le(divT(m, n), m); !got.AlphaEquals(want) {
		t.Errorf("divLessEq: got %v, want %v", got, want)
	}
	if got, want := modRefl(n).Conclusion(), eqT(modT(n, n), natZero); !got.AlphaEquals(want) {
		t.Errorf("modRefl: got %v, want %v", got, want)
	}
	if got, want := divZero(m).Conclusion(), eqT(divT(m, natZero), natZero); !got.AlphaEquals(want) {
		t.Errorf("divZero: got %v, want %v", got, want)
	}
	if got, want := modZero(m).Conclusion(), eqT(modT(m, natZero), m); !got.AlphaEquals(want) {
		t.Errorf("modZero: got %v, want %v", got, want)
	}
}

// TestProveLinDivMod_PhaseOne: the unconditional ModLessEq/DivLessEq injection closes
// goals that pure linarith can't because the nat_div/nat_mod atom would be unconstrained.
func TestProveLinDivMod_PhaseOne(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")

	// nat_mod(m,n) ≤ m: pure linarith declines (nat_mod is opaque); enrichment closes it.
	if _, ok := proveLinDivMod(nil, le(modT(m, n), m)); !ok {
		t.Error("nat_mod(m,n) ≤ m not closed by phase-1 enrichment")
	}
	if _, ok := proveLinDivMod(nil, le(divT(m, n), m)); !ok {
		t.Error("nat_div(m,n) ≤ m not closed by phase-1 enrichment")
	}
	// Compositional: m + nat_mod(a,b) ≤ m + a.
	a, b := numVar("a"), numVar("b")
	if _, ok := proveLinDivMod(nil, le(plus(m, modT(a, b)), plus(m, a))); !ok {
		t.Error("m + nat_mod(a,b) ≤ m + a not closed")
	}
}

// TestProveLinDivMod_Conditional: ModLessThan discharges `m<n` from a hyp; Division
// discharges `n≠0` for literal n; DivRefl similarly.
func TestProveLinDivMod_Conditional(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")

	// ModLessThan path: `m<n ⊢ nat_mod(m,n) = m`.
	hyps := []core.Term{lt(m, n)}
	if _, ok := proveLinDivMod(hyps, eqT(modT(m, n), m)); !ok {
		t.Error("ModLessThan-enriched goal not closed: m<n ⊢ nat_mod(m,n) = m")
	}

	// Division (literal nonzero divisor): `nat_mod(m, 5) < 5`.
	if _, ok := proveLinDivMod(nil, lt(modT(m, Numeral(5)), Numeral(5))); !ok {
		t.Error("Division-enriched: nat_mod(m,5) < 5 not closed")
	}

	// DivRefl (symbolic n with 0<n in hyps): nat_div(n,n) = 1.
	hyps2 := []core.Term{lt(natZero, n)}
	if _, ok := proveLinDivMod(hyps2, eqT(divT(n, n), Numeral(1))); !ok {
		t.Error("DivRefl-enriched: 0<n ⊢ nat_div(n,n) = 1 not closed")
	}
}

// TestDivEqZeroFact: with `m<n` in hyps AND `n≠0` discharged (symbolic via 0<n),
// divEqZeroFact produces ⊢ nat_div(m,n) = 0 from DivEqZero's iff direction.
func TestDivEqZeroFact(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")
	// The bound NORMAL-FORM shape: ∀m n. ((m<n) ⇔ (0 = nat_div(m,n))) ∨ (n=0). The iff is on
	// the LEFT (opposite of Division/DivRefl which have (n=0) on the left).
	// divEqZeroFact normalizes via CommuteOR. An earlier test bundle had the
	// disjuncts swapped — that masked a real shape-orientation bug, surfaced
	// by the engine-side TestApplyStep_Arith_ClosesCompoundNumGoals/DivEqZero
	// failing while this unit kept passing. Pin the normal-form shape here so a
	// regression fires in unit tests too.
	natLemmaBundle.DivEqZero = prop.WrapProp(core.TestThm(
		ext.ForAll(m, n)(or(eqT(lt(m, n), eqT(natZero, divT(m, n))), eqT(n, natZero)))))

	hyps := []core.Term{lt(m, n), lt(natZero, n)} // m<n and 0<n
	w := divEqZeroFact(m, n, hyps)
	if w == nil {
		t.Fatal("divEqZeroFact returned nil with both side conditions in hyps")
	}
	if want := eqT(divT(m, n), natZero); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("divEqZeroFact: got %v, want %v", w.Conclusion(), want)
	}
	// Missing m<n → declines (NB: over num, m<n alone WOULD suffice because
	// nonnegativity gives 0<n for free, so the only way to lose discharge is to
	// drop m<n entirely).
	if got := divEqZeroFact(m, n, []core.Term{lt(natZero, n)}); got != nil {
		t.Errorf("divEqZeroFact should decline without m<n, got %v", got.Conclusion())
	}
}

// TestDivCommonFactor: literal nonzero c factors out of nat_div(c·a, c·b); a
// non-literal or zero c declines, as does a mismatched factor.
func TestDivCommonFactor(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n, p := numVar("m"), numVar("n"), numVar("p")
	// Normal-form shape: ∀m n p. (m=0) ∨ (nat_div(n,p) = nat_div(m·n, m·p)).
	natLemmaBundle.DivMult2 = prop.WrapProp(core.TestThm(
		ext.ForAll(m, n, p)(or(eqT(m, natZero), eqT(divT(n, p), divT(star(m, n), star(m, p)))))))

	a, b := numVar("a"), numVar("b")
	two := Numeral(2)

	// nat_div(2·a, 2·b) → nat_div(a, b)
	w := divCommonFactor(star(two, a), star(two, b))
	if w == nil {
		t.Fatal("divCommonFactor returned nil for nat_div(2·a, 2·b)")
	}
	if want := eqT(divT(star(two, a), star(two, b)), divT(a, b)); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("divCommonFactor:\n got  %v\n want %v", w.Conclusion(), want)
	}

	// Mismatched factor: nat_div(2·a, 3·b) declines.
	three := Numeral(3)
	if got := divCommonFactor(star(two, a), star(three, b)); got != nil {
		t.Errorf("divCommonFactor should decline on mismatched factor, got %v", got.Conclusion())
	}
	// Non-literal factor: nat_div(c·a, c·b) declines (no hyps to discharge c≠0).
	c := numVar("c")
	if got := divCommonFactor(star(c, a), star(c, b)); got != nil {
		t.Errorf("divCommonFactor should decline on non-literal factor, got %v", got.Conclusion())
	}
	// Zero factor: nat_div(0·a, 0·b) declines.
	if got := divCommonFactor(star(natZero, a), star(natZero, b)); got != nil {
		t.Errorf("divCommonFactor should decline on zero factor, got %v", got.Conclusion())
	}
}

// TestProveNeqZeroHypRoute: proveNeqZero accepts `¬(n=0)` directly from hyps,
// in either `¬(n=0)` or `¬(0=n)` orientation. Without this, the conditional
// nat_div/nat_mod enricher couldn't fire on goals where the user supplied n≠0 as a hyp.
func TestProveNeqZeroHypRoute(t *testing.T) {
	defer installDivModTestBundle(t)()
	n := numVar("n")
	// hyp ¬(n = 0): direct route.
	if w := proveNeqZero(n, []Term{not(eqT(n, natZero))}); w == nil {
		t.Error("proveNeqZero declined with ¬(n=0) hyp")
	} else if want := not(eqT(n, natZero)); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("got %v, want %v", w.Conclusion(), want)
	}
	// hyp ¬(0 = n): symmetric route via CommuteEQ.
	if w := proveNeqZero(n, []Term{not(eqT(natZero, n))}); w == nil {
		t.Error("proveNeqZero declined with ¬(0=n) hyp")
	} else if want := not(eqT(n, natZero)); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("got %v, want %v", w.Conclusion(), want)
	}
}

// TestNZeroFactsForDivisor: per-atom equation derivation under the n=0 assume.
// nat_mod(m, n) atom → ⊢ {n=0} ⊢ nat_mod(m, n) = m via ModZero + cong on n.
// nat_div(m, n) atom → ⊢ {n=0} ⊢ nat_div(m, n) = 0 via DivZero + cong on n.
func TestNZeroFactsForDivisor(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")
	// ModZero and DivZero need real shapes pinned. Normal forms: ∀n. n = nat_mod(n, 0)
	// and ∀n. 0 = nat_div(n, 0).
	mk := func(c core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	x := numVar("x")
	natLemmaBundle.ModZero = mk(ext.ForAll(x)(eqT(x, modT(x, natZero))))
	natLemmaBundle.DivZero = mk(ext.ForAll(x)(eqT(natZero, divT(x, natZero))))

	hyps := []Term{}
	goal := plus(modT(m, n), divT(m, n))
	facts := nZeroFactsForDivisor(n, hyps, goal)
	if len(facts) != 2 {
		t.Fatalf("expected 2 facts (one nat_mod, one nat_div), got %d: %v", len(facts), facts)
	}
	// One fact should be nat_mod(m, n) = m; the other nat_div(m, n) = 0.
	wantMod := eqT(modT(m, n), m)
	wantDiv := eqT(divT(m, n), natZero)
	foundMod, foundDiv := false, false
	for _, f := range facts {
		if f.Conclusion().AlphaEquals(wantMod) {
			foundMod = true
		}
		if f.Conclusion().AlphaEquals(wantDiv) {
			foundDiv = true
		}
	}
	if !foundMod {
		t.Errorf("missing nat_mod(m, n) = m fact")
	}
	if !foundDiv {
		t.Errorf("missing nat_div(m, n) = 0 fact")
	}
}

// TestFirstUnsplitDivisor: skips literals, already-split, and divisors with
// `0<n` or `¬(n=0)` info in hyps; PICKS up `n=0` (the split's n=0 branch
// handles that case via injection — the conditional enricher can't).
func TestFirstUnsplitDivisor(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n, p := numVar("m"), numVar("n"), numVar("p")

	// Literal divisor — skipped (conditional enricher handles literal-nonzero via NormNatEq).
	if _, ok := firstUnsplitDivisor(nil, modT(m, Numeral(5)), nil); ok {
		t.Error("should skip literal divisor")
	}
	// In done — skipped.
	if _, ok := firstUnsplitDivisor(nil, modT(m, n), []Term{n}); ok {
		t.Error("should skip divisor in done")
	}
	// 0<n in hyps — skipped (existing enricher fires).
	if _, ok := firstUnsplitDivisor([]Term{lt(natZero, n)}, modT(m, n), nil); ok {
		t.Error("should skip when 0<n in hyps")
	}
	// ¬(n=0) in hyps — skipped (existing enricher fires after proveNeqZero fix).
	if _, ok := firstUnsplitDivisor([]Term{not(eqT(n, natZero))}, modT(m, n), nil); ok {
		t.Error("should skip when ¬(n=0) in hyps")
	}
	// n=0 in hyps — NOT skipped (conditional enricher can't handle, split's n=0 branch can).
	if got, ok := firstUnsplitDivisor([]Term{eqT(n, natZero)}, modT(m, n), nil); !ok || !got.AlphaEquals(n) {
		t.Error("should NOT skip when n=0 in hyps (split needed)")
	}
	// Symbolic divisor, no info — picked up.
	if got, ok := firstUnsplitDivisor(nil, modT(m, p), nil); !ok || !got.AlphaEquals(p) {
		t.Error("should pick symbolic divisor with no info")
	}
}

// TestProveDivModSplitOnZero_NEq0InHyps: with ¬(n=0) in hyps, the conditional
// enricher fires directly (no split needed) — proveNeqZero's new hyp route +
// hypsAlreadyDecideN skip make `n ≠ 0 ⊢ nat_mod(m, n) < n` close via Division's
// bound alone.
func TestProveDivModSplitOnZero_NEq0InHyps(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")
	hyps := []Term{not(eqT(n, natZero))}
	goal := lt(modT(m, n), n)
	// proveLinDivMod alone (no split) should close this now via proveNeqZero's
	// direct hyp route.
	if _, ok := proveLinDivMod(hyps, goal); !ok {
		t.Error("proveLinDivMod declined `n ≠ 0 ⊢ nat_mod(m, n) < n` — proveNeqZero hyp route should fire")
	}
}

// TestProveDivModSplitOnZero_BareSymbolicDeclines: a goal that's FALSE at n=0
// must decline overall — the split fires but the n=0 branch can't close
// (`m < 0` over num is false), so the whole split returns nil. Guards against
// an unsound future change.
func TestProveDivModSplitOnZero_BareSymbolicDeclines(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")
	if _, ok := proveDivModSplitOnZero(nil, lt(modT(m, n), n), nil); ok {
		t.Error("split unexpectedly succeeded on a goal false at n=0")
	}
}

// TestCollectDivModAtoms: walker picks up both nat_div and nat_mod, dedups α-equal.
func TestCollectDivModAtoms(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")
	terms := []Term{plus(divT(a, b), divT(a, b)), modT(c, b)} // a/b twice + c%b
	got := collectDivModAtoms(terms)
	if len(got) != 2 {
		t.Fatalf("got %d, want 2: %v", len(got), got)
	}
	// quick contains check
	if !slices.ContainsFunc(got, divT(a, b).AlphaEquals) ||
		!slices.ContainsFunc(got, modT(c, b).AlphaEquals) {
		t.Errorf("missing atom: %v", got)
	}
}

// Integer Euclidean int_div/int_rem (nat_divmod.go): the bounded-atom enrichment injects
// DivisionIdentity's identity + the [0,n) bounds (RemNonneg / RemBelowDivisor), so
// for a literal/positive divisor linarith + ℤ-discreteness pins the values with
// no separate literal evaluator. Plus the divisor-0/1 simp folds. All leaves are
// IntLemmaBundle placeholders; the composition here is real kernel work, sound
// once serve.InstallIntBundle binds the Div* / Rem* family.

// intDecideRhs runs the full int decider on `goal` under `hyps` and returns the
// rewritten RHS (⊤ when fully decided true, ⊥ when decided false).
func intDecideRhs(t *testing.T, name string, goal Term, hyps ...Term) Term {
	t.Helper()
	w := IntArithDecideWithHyps(hyps)(goal)
	if w == nil {
		t.Fatalf("%s: IntArithDecide = nil", name)
	}
	return prop.Rhs(w)
}

func intDecidesTrue(t *testing.T, name string, goal Term, hyps ...Term) {
	t.Helper()
	if r := intDecideRhs(t, name, goal, hyps...); !r.Equals(prop.T) {
		t.Errorf("%s: decided %v, want ⊤", name, r)
	}
}

func TestIntDivRem_LiteralEval(t *testing.T) {
	// int_div(&7,&2)=&3 and int_rem(&7,&2)=&1 fall out of `7 = 2·d + r ∧ 0 ≤ r < 2` —
	// the enrichment + ℤ-discreteness, no separate literal evaluator.
	intDecidesTrue(t, "int_div(7,2)=3", eqT(intDivT(intLit(7), intLit(2)), intLit(3)))
	intDecidesTrue(t, "int_rem(7,2)=1", eqT(intRemT(intLit(7), intLit(2)), intLit(1)))
	// exact division: int_div(&6,&3)=&2, int_rem(&6,&3)=&0.
	intDecidesTrue(t, "int_div(6,3)=2", eqT(intDivT(intLit(6), intLit(3)), intLit(2)))
	intDecidesTrue(t, "int_rem(6,3)=0", eqT(intRemT(intLit(6), intLit(3)), intLit(0)))

	// sanity: a WRONG quotient/remainder decides ⊥ (the negation closes — for
	// int_rem(&7,&2)≠&0 even via the gcd test: 2·d = 7 has gcd 2 ∤ 7).
	if r := intDecideRhs(t, "int_div(7,2)=4", eqT(intDivT(intLit(7), intLit(2)), intLit(4))); !r.Equals(prop.F) {
		t.Errorf("int_div(7,2)=4: decided %v, want ⊥", r)
	}
}

func TestIntDivRem_Bounds(t *testing.T) {
	m := intVar("m")
	three := intLit(3)
	// symbolic dividend, literal positive divisor: the [0,n) bounds.
	intDecidesTrue(t, "0≤int_rem(m,3)", intLeT(intLit(0), intRemT(m, three)))
	intDecidesTrue(t, "int_rem(m,3)<3", intLtT(intRemT(m, three), three))
	// the unconditional division identity m = int_div(m,3)·3 + int_rem(m,3).
	id := eqT(m, intPlusT(intStarT(intDivT(m, three), three), intRemT(m, three)))
	intDecidesTrue(t, "m=int_div(m,3)·3+int_rem(m,3)", id)
}

func TestIntDivRem_SymbolicDivisor(t *testing.T) {
	m, n := intVar("m"), intVar("n")
	zeroLtN := intLtT(intLit(0), n) // &0 < n in hyps
	// With `&0 < n` the bounds fire for a symbolic divisor too.
	intDecidesTrue(t, "0<n⊢0≤int_rem(m,n)", intLeT(intLit(0), intRemT(m, n)), zeroLtN)
	intDecidesTrue(t, "0<n⊢int_rem(m,n)<n", intLtT(intRemT(m, n), n), zeroLtN)
}

// B3: the general division bounds for a NEGATIVE / unknown-sign divisor, where
// RemBelowDivisor's `rem < n` is false. The nonneg + `rem < int_abs(n)` bounds fire from
// `n ≠ &0` (incl. derived from `n < &0`); the int_abs upper bound composes with the
// int_abs case split to pin `rem < −n` for a negative divisor.
func TestIntDivRem_NegativeDivisor(t *testing.T) {
	m, n := intVar("m"), intVar("n")
	z := intLit(0)
	rem := intRemT(m, n)
	nNeq0 := not(eqT(n, z))
	// n ≠ &0 ⊢ the general bounds.
	intDecidesTrue(t, "n≠0⊢0≤int_rem(m,n)", intLeT(z, rem), nNeq0)
	intDecidesTrue(t, "n≠0⊢int_rem(m,n)<|n|", intLtT(rem, intAbsT(n)), nNeq0)
	// n < &0 ⊢ the bounds (n≠0 derived from n<0), incl. the int_abs composition.
	nLt0 := intLtT(n, z)
	intDecidesTrue(t, "n<0⊢0≤int_rem(m,n)", intLeT(z, rem), nLt0)
	intDecidesTrue(t, "n<0⊢int_rem(m,n)<−n", intLtT(rem, intNegT(n)), nLt0)

	// sanity: WITHOUT `n≠&0`, `int_rem(m,n) < int_abs(n)` must NOT decide ⊤ (n=&0 ⇒
	// rem=m, int_abs(&0)=&0, and m<&0 is not forced).
	if w := IntArithDecideWithHyps(nil)(intLtT(rem, intAbsT(n))); w != nil && prop.Rhs(w).Equals(prop.T) {
		t.Errorf("int_rem(m,n)<int_abs(n) without n≠0 must NOT decide ⊤")
	}
}

func TestIntDivRem_Folds(t *testing.T) {
	m := intVar("m")
	// divisor-0 / divisor-1 simp folds.
	intDecidesTrue(t, "int_div(m,0)=0", eqT(intDivT(m, intLit(0)), intLit(0)))
	intDecidesTrue(t, "int_rem(m,0)=m", eqT(intRemT(m, intLit(0)), m))
	intDecidesTrue(t, "int_div(m,1)=m", eqT(intDivT(m, intLit(1)), m))
	intDecidesTrue(t, "int_rem(m,1)=0", eqT(intRemT(m, intLit(1)), intLit(0)))
}

// nat_div/nat_mod distribution leaves (nat_divmod.go) + the DivMulLessEq enrichment fact
// (nat_divmod.go). TestThm-fabricated bundles pin the EXACT normal-form
// statement shapes the leaves project/orient from; the kernel composition is
// real. The strict end-to-end coverage against the real corpus bundle is
// library/serve's TestInstallNatBundleBindingDivModDist.

// TestDivMulLessEq: the floor LOWER bound leaf, normal-form shape ∀n m. (n·nat_div(m,n)) ≤ m.
func TestDivMulLessEq(t *testing.T) {
	defer installDivModTestBundle(t)()
	m, n := numVar("m"), numVar("n")
	natLemmaBundle.DivMulLessEq = prop.WrapProp(core.TestThm(
		ext.ForAll(n, m)(le(star(n, divT(m, n)), m))))

	if w := divMulLessEq(m, n); w == nil {
		t.Fatal("divMulLessEq returned nil")
	} else if want := le(star(n, divT(m, n)), m); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("divMulLessEq:\n got  %v\n want %v", w.Conclusion(), want)
	}
}

// TestDivMultAddSimp: the conditional affine-nat_div simp, normal-form 4-clause shape
// `(v=0) ∨ eq`. Covers both summand positions and both factor orders; declines on
// a non-multiple, a symbolic (undischargeable) divisor, and a non-sum dividend.
func TestDivMultAddSimp(t *testing.T) {
	defer installDivModTestBundle(t)()
	n, a, b := numVar("n"), numVar("a"), numVar("b")
	l, e, f := numVar("l"), numVar("e"), numVar("f")
	k, d, c := numVar("k"), numVar("d"), numVar("c")
	// DivMultAdd normal-form shape (binders n a b lʹ e f kʹ d c):
	//   C0: (n=0) ∨ (a + nat_div(b,n)   = nat_div(a·n + b, n))
	//   C1: (l=0) ∨ (e + nat_div(f,l)   = nat_div(l·e + f, l))
	//   C2: (k=0) ∨ (nat_div(d,k) + c   = nat_div(d + k·c, k))
	//   C3: (k=0) ∨ (nat_div(d,k) + c   = nat_div(d + c·k, k))
	natLemmaBundle.DivMultAdd = prop.WrapProp(core.TestThm(
		ext.ForAll(n, a, b, l, e, f, k, d, c)(and(and(and(
			or(eqT(n, natZero), eqT(plus(a, divT(b, n)), divT(plus(star(a, n), b), n))),
			or(eqT(l, natZero), eqT(plus(e, divT(f, l)), divT(plus(star(l, e), f), l)))),
			or(eqT(k, natZero), eqT(plus(divT(d, k), c), divT(plus(d, star(k, c)), k)))),
			or(eqT(k, natZero), eqT(plus(divT(d, k), c), divT(plus(d, star(c, k)), k)))))))

	x, y := numVar("x"), numVar("y")
	two := Numeral(2)
	check := func(label string, num, want Term) {
		t.Helper()
		w := divMultAdd(num, two)
		if w == nil {
			t.Fatalf("%s: divMultAdd returned nil", label)
		}
		if !w.Conclusion().AlphaEquals(want) {
			t.Errorf("%s:\n got  %v\n want %v", label, w.Conclusion(), want)
		}
	}
	// FIRST summand a multiple, divisor LEFT factor: nat_div(2·x + y, 2) → x + nat_div(y,2).
	num0 := plus(star(two, x), y)
	check("nat_div(2·x+y,2)", num0, eqT(divT(num0, two), plus(x, divT(y, two))))
	// FIRST summand a multiple, divisor RIGHT factor: nat_div(x·2 + y, 2) → x + nat_div(y,2).
	num1 := plus(star(x, two), y)
	check("nat_div(x·2+y,2)", num1, eqT(divT(num1, two), plus(x, divT(y, two))))
	// SECOND summand a multiple: nat_div(y + 2·x, 2) → nat_div(y,2) + x.
	num2 := plus(y, star(two, x))
	check("nat_div(y+2·x,2)", num2, eqT(divT(num2, two), plus(divT(y, two), x)))

	// Neither summand a multiple of the divisor: nil.
	if got := divMultAdd(plus(x, y), two); got != nil {
		t.Errorf("divMultAdd(x+y, 2) should be nil, got %v", got.Conclusion())
	}
	// Symbolic divisor: n≠0 cannot discharge in the simp path (no hyps) → nil.
	if got := divMultAdd(plus(star(n, x), y), n); got != nil {
		t.Errorf("divMultAdd with symbolic divisor should be nil, got %v", got.Conclusion())
	}
	// Not a sum: nil (the c·n shape with no remainder is modMultZero's nat_mod-side job).
	if got := divMultAdd(star(two, x), two); got != nil {
		t.Errorf("divMultAdd(2·x, 2) should be nil (not a sum), got %v", got.Conclusion())
	}
}

// TestDivMultAddFact: the symbolic-divisor ENRICHMENT companion to divMultAdd.
// With n≠0 available from hyps, it returns the affine-nat_div equality as a
// hyp-carrying fact (not a rewrite) — nat_div(n·x+y, n) = x + nat_div(y,n) — for
// divModFacts to inject. Declines when n≠0 cannot be discharged.
func TestDivMultAddFact(t *testing.T) {
	defer installDivModTestBundle(t)()
	n, a, b := numVar("n"), numVar("a"), numVar("b")
	l, e, f := numVar("l"), numVar("e"), numVar("f")
	k, d, c := numVar("k"), numVar("d"), numVar("c")
	// Same DivMultAdd 4-clause normal-form shape as TestDivMultAddSimp.
	natLemmaBundle.DivMultAdd = prop.WrapProp(core.TestThm(
		ext.ForAll(n, a, b, l, e, f, k, d, c)(and(and(and(
			or(eqT(n, natZero), eqT(plus(a, divT(b, n)), divT(plus(star(a, n), b), n))),
			or(eqT(l, natZero), eqT(plus(e, divT(f, l)), divT(plus(star(l, e), f), l)))),
			or(eqT(k, natZero), eqT(plus(divT(d, k), c), divT(plus(d, star(k, c)), k)))),
			or(eqT(k, natZero), eqT(plus(divT(d, k), c), divT(plus(d, star(c, k)), k)))))))

	x, y := numVar("x"), numVar("y")
	num := plus(star(n, x), y) // n·x + y, a symbolic-divisor affine dividend
	want := eqT(divT(num, n), plus(x, divT(y, n)))

	// (a) ¬(n=0) hyp — proveNeqZero's direct hyp route.
	w := divMultAddFact(num, n, []Term{not(eqT(n, natZero))})
	if w == nil {
		t.Fatal("divMultAddFact returned nil with ¬(n=0) hyp")
	}
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("divMultAddFact concl:\n got  %v\n want %v", w.Conclusion(), want)
	}
	// The fact carries only the discharging hyp (a subset of the goal's hyps), so
	// enrichAndCut can cut it back cleanly.
	if !w.HasHyp(not(eqT(n, natZero))) {
		t.Errorf("divMultAddFact should carry the ¬(n=0) hyp; got %v", w.Hyps())
	}

	// (b) 0<n hyp — proveNeqZero's symbolic linarith route.
	if w2 := divMultAddFact(num, n, []Term{lt(natZero, n)}); w2 == nil {
		t.Error("divMultAddFact should discharge n≠0 from a 0<n hyp")
	} else if !w2.Conclusion().AlphaEquals(want) {
		t.Errorf("divMultAddFact (0<n route) concl:\n got  %v\n want %v", w2.Conclusion(), want)
	}

	// (c) No hyps ⇒ symbolic n≠0 cannot discharge ⇒ nil.
	if got := divMultAddFact(num, n, nil); got != nil {
		t.Errorf("divMultAddFact with no hyps should be nil, got %v", got.Conclusion())
	}
	// (d) Dividend not an affine multiple of n ⇒ nil even with n≠0 available.
	if got := divMultAddFact(plus(x, y), n, []Term{not(eqT(n, natZero))}); got != nil {
		t.Errorf("divMultAddFact(x+y, n) should be nil, got %v", got.Conclusion())
	}
}

// TestModAddModSimp: ModAddMod wired in the COMBINE (term-shrinking) direction,
// auto-oriented by eqLeaf from the bound DISTRIBUTE statement.
func TestModAddModSimp(t *testing.T) {
	defer installDivModTestBundle(t)()
	a, b, n := numVar("a"), numVar("b"), numVar("n")
	// Bound DISTRIBUTE orientation: ∀a b n. nat_mod(a+b,n) = nat_mod(nat_mod(a,n)+nat_mod(b,n),n).
	natLemmaBundle.ModAddMod = prop.WrapProp(core.TestThm(
		ext.ForAll(a, b, n)(eqT(modT(plus(a, b), n), modT(plus(modT(a, n), modT(b, n)), n)))))

	// COMBINE: nat_mod(nat_mod(a,n)+nat_mod(b,n), n) → nat_mod(a+b, n).
	dividend := plus(modT(a, n), modT(b, n))
	if w := modAddMod(dividend, n); w == nil {
		t.Fatal("modAddMod returned nil")
	} else if want := eqT(modT(dividend, n), modT(plus(a, b), n)); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("modAddMod:\n got  %v\n want %v", w.Conclusion(), want)
	}
	// Mismatched inner divisors: nil.
	if got := modAddMod(plus(modT(a, n), modT(b, numVar("p"))), n); got != nil {
		t.Errorf("modAddMod with mismatched divisor should be nil, got %v", got.Conclusion())
	}
	// A summand that is not a nat_mod: nil.
	if got := modAddMod(plus(a, modT(b, n)), n); got != nil {
		t.Errorf("modAddMod with non-nat_mod summand should be nil, got %v", got.Conclusion())
	}
}

// nat_div/nat_mod enrichment for a multiple and a nested residue: multiple-is-zero (via ModEqZero)
// and idempotence (via ModModRefl). TestThm-fabricated bundles pin the normal-form
// shapes the leaves project from; the kernel composition is real.

func installEnrichBundle(t *testing.T) {
	t.Helper()
	a, b, m, n := numVar("a"), numVar("b"), numVar("m"), numVar("n")
	mk := func(c core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	SetNatLemmaBundle(&NatLemmaBundle{
		MulSym: mk(ext.ForAll(a, b)(eqT(star(a, b), star(b, a)))),
		// ModEqZero: ∀m n. (∃q. m = q·n) ⇔ (0 = nat_mod(m,n)).  dvd(n,m) = ∃q. m = q·n.
		ModEqZero: mk(ext.ForAll(m, n)(eqT(dvd(n, m), eqT(natZero, modT(m, n))))),
		// ModModRefl: ∀m n. nat_mod(m,n) = nat_mod(nat_mod(m,n), n).
		ModModRefl: mk(ext.ForAll(m, n)(eqT(modT(m, n), modT(modT(m, n), n)))),
	})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
}

func TestModMultZero(t *testing.T) {
	installEnrichBundle(t)
	k, n := numVar("k"), numVar("n")

	// nat_mod(k*n, n) = 0 (divisor is the RIGHT factor).
	if w := modMultZero(star(k, n), n); w == nil {
		t.Error("modMultZero(k*n, n) = nil")
	} else if want := eqT(modT(star(k, n), n), natZero); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("modMultZero(k*n,n): got %v, want %v", w.Conclusion(), want)
	}
	// nat_mod(n*k, n) = 0 (divisor is the LEFT factor — needs the MulSym bridge).
	if w := modMultZero(star(n, k), n); w == nil {
		t.Error("modMultZero(n*k, n) = nil")
	} else if want := eqT(modT(star(n, k), n), natZero); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("modMultZero(n*k,n): got %v, want %v", w.Conclusion(), want)
	}
	// Not a multiple of the divisor: nil.
	if modMultZero(star(k, k), n) != nil {
		t.Error("modMultZero(k*k, n) should be nil (n not a factor)")
	}
	if modMultZero(plus(k, n), n) != nil {
		t.Error("modMultZero(k+n, n) should be nil (not a product)")
	}
}

func TestModIdemp(t *testing.T) {
	installEnrichBundle(t)
	p, n := numVar("p"), numVar("n")

	// dividend nat_mod(p,n) with the same divisor n ⇒ idempotence.
	if w := modIdemp(modT(p, n), n); w == nil {
		t.Error("modIdemp(nat_mod(p,n), n) = nil")
	} else if want := eqT(modT(modT(p, n), n), modT(p, n)); !w.Conclusion().AlphaEquals(want) {
		t.Errorf("modIdemp: got %v, want %v", w.Conclusion(), want)
	}
	// Different divisor: nil.
	if modIdemp(modT(p, numVar("d")), n) != nil {
		t.Error("modIdemp with a different inner divisor should be nil")
	}
	// Non-nat_mod dividend: nil.
	if modIdemp(plus(p, n), n) != nil {
		t.Error("modIdemp on a non-nat_mod dividend should be nil")
	}
}

// The modMultAdd / divDivNest simp leaves: affine-nat_mod reduction (ModMultAdd)
// and nested-nat_div flattening (DivDiv), both unconditional. TestThm-fabricated bundles
// pin the normal-form shapes; end-to-end against the real corpus bundle is in
// library/serve (TestInstallNatBundleBindingDivModPhase3).
func installPhase3Bundle(t *testing.T) {
	t.Helper()
	m, n, p := numVar("m"), numVar("n"), numVar("p")
	s, nn, mm := numVar("s"), numVar("nn"), numVar("mm")
	r, l, k := numVar("r"), numVar("l"), numVar("k")
	mk := func(c core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	SetNatLemmaBundle(&NatLemmaBundle{
		// ModMultAdd: the normal form's 4-clause conjunction — multiple as first or
		// second summand, divisor as left or right factor (clauseLeaf projects the
		// matching conjunct).
		ModMultAdd: mk(ext.ForAll(p, n, m, s, nn, mm, r, l, k)(and(and(and(
			eqT(modT(p, n), modT(plus(star(m, n), p), n)),      // nat_mod(p,n)=nat_mod(m·n+p,n)
			eqT(modT(s, nn), modT(plus(star(nn, mm), s), nn))), // nat_mod(s,nn)=nat_mod(nn·mm+s,nn)
			eqT(modT(r, l), modT(plus(r, star(l, k)), l))), // nat_mod(r,l)=nat_mod(r+l·k,l)
			eqT(modT(r, l), modT(plus(r, star(k, l)), l))))), // nat_mod(r,l)=nat_mod(r+k·l,l)
		// DivDiv: ∀m n p. m nat_div (n·p) = (nat_div(m, n)) nat_div p (single equation).
		DivDiv: mk(ext.ForAll(m, n, p)(eqT(divT(m, star(n, p)), divT(divT(m, n), p)))),
	})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
}

func TestModMultAddSimp(t *testing.T) {
	installPhase3Bundle(t)
	k, n, r := numVar("k"), numVar("n"), numVar("r")

	// nat_mod(k·n + r, n) → nat_mod(r, n)  (multiple is first summand, divisor RIGHT factor).
	x := plus(star(k, n), r)
	if w := modMultAdd(x, n); w == nil || !w.Conclusion().AlphaEquals(eqT(modT(x, n), modT(r, n))) {
		t.Errorf("modMultAdd(k·n+r, n) = %v", w)
	}
	// nat_mod(n·k + r, n) → nat_mod(r, n)  (divisor LEFT factor — a distinct conjunct).
	x2 := plus(star(n, k), r)
	if w := modMultAdd(x2, n); w == nil || !w.Conclusion().AlphaEquals(eqT(modT(x2, n), modT(r, n))) {
		t.Errorf("modMultAdd(n·k+r, n) = %v", w)
	}
	// First summand not a multiple of n: nil.
	if modMultAdd(plus(star(k, k), r), n) != nil {
		t.Error("modMultAdd(k·k+r, n) should be nil (n not a factor of the first summand)")
	}
	// Not a sum: nil.
	if modMultAdd(star(k, n), n) != nil {
		t.Error("modMultAdd(k·n, n) should be nil (not a sum — modMultZero's job)")
	}
}

func TestDivDivNestSimp(t *testing.T) {
	installPhase3Bundle(t)
	a, b, c := numVar("a"), numVar("b"), numVar("c")

	// nat_div(nat_div(a,b), c) → nat_div(a, b·c).
	if w := divDivNest(divT(a, b), c); w == nil ||
		!w.Conclusion().AlphaEquals(eqT(divT(divT(a, b), c), divT(a, star(b, c)))) {
		t.Errorf("divDivNest(nat_div(a,b), c) = %v", w)
	}
	// Dividend not itself a nat_div: nil.
	if divDivNest(a, c) != nil {
		t.Error("divDivNest(a, c) should be nil (dividend not a nested nat_div)")
	}
}

// End-to-end: the enrichment closes goals the existing nat_div/nat_mod injection cannot
// (both need a nonlinear `q·n = 0` step linarith can't see).
func TestProveLinDivModEnrich(t *testing.T) {
	installEnrichBundle(t)
	k, n, p := numVar("k"), numVar("n"), numVar("p")

	if _, ok := proveLinDivMod(nil, eqT(modT(star(k, n), n), natZero)); !ok {
		t.Error("nat_mod(k*n, n) = 0 not closed by the multiple-is-zero enrichment")
	}
	if _, ok := proveLinDivMod(nil, eqT(modT(modT(p, n), n), modT(p, n))); !ok {
		t.Error("nat_mod(nat_mod(p,n),n) = nat_mod(p,n) not closed by the idempotence enrichment")
	}
}
