package omega

import (
	"fmt"
	"iter"
	"regexp"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Real-domain test helpers: build real terms from text via ext/dsl, mirroring
// this file's num helpers. Real literals are written `&n`, real
// variables are any non-reserved identifier (real-scoped below). Every case
// doubles as a round-trip check of the dsl real support (overloaded +,*,<,…
// dispatched to the real instance + the `&` coercion prefix).

// realScope assigns RealType to every non-reserved identifier in s.
func realScope(s string) map[string]core.HolType {
	ctx := map[string]core.HolType{}
	for _, id := range tIdentRE.FindAllString(s, -1) {
		if !tReservedConst[id] && id != "real_of_num" {
			ctx[id] = dsl.RealType
		}
	}
	return ctx
}

func rParse(s string, expected core.HolType) Term {
	r := dsl.ParseTermTextInScope(s, realScope(s), &dsl.ParseScope{}, expected)
	if len(r.Errors) > 0 {
		panic(fmt.Sprintf("dsl parse %q: %v", s, r.Errors))
	}
	return r.Term
}

// rr parses s as a real-typed term (e.g. "&2 * x + &3").
func rr(s string) Term { return rParse(s, dsl.RealType) }

// rb parses s as a bool-typed term — a real comparison (e.g. "x < &2").
func rb(s string) Term { return rParse(s, core.TypeBool()) }

func TestRealDomain_LinOf(t *testing.T) {
	cases := []struct {
		text  string
		konst int64
		monos []monomialL // expected, by atom text — checked structurally below
	}{
		{"&5", 5, nil},
		{"x", 0, []monomialL{mono(1, rr("x"))}},
		{"&2 * x + &3", 3, []monomialL{mono(2, rr("x"))}},
		{"x * &2 + &3", 3, []monomialL{mono(2, rr("x"))}}, // const on the right
		{"x + y", 0, []monomialL{mono(1, rr("x")), mono(1, rr("y"))}},
		{"&2 * x + &4 * y + &1", 1, []monomialL{mono(2, rr("x")), mono(4, rr("y"))}},
	}
	for _, c := range cases {
		lf, ok := realDomain.linOf(rr(c.text))
		if !ok {
			t.Errorf("linOf(%q): ok=false, want true", c.text)
			continue
		}
		if !lf.konst.equal(integerOf(c.konst)) {
			t.Errorf("linOf(%q): konst=%v, want %d", c.text, lf.konst, c.konst)
		}
		if len(lf.monos) != len(c.monos) {
			t.Errorf("linOf(%q): %d monos, want %d", c.text, len(lf.monos), len(c.monos))
			continue
		}
		for _, want := range c.monos {
			found := false
			for _, got := range lf.monos {
				if got.atom.AlphaEquals(want.atom) {
					found = true
					if !got.coeff.equal(want.coeff) {
						t.Errorf("linOf(%q): atom %v coeff=%v, want %v",
							c.text, want.atom, got.coeff, want.coeff)
					}
				}
			}
			if !found {
				t.Errorf("linOf(%q): missing atom %v", c.text, want.atom)
			}
		}
	}
}

func TestRealDomain_LinOf_Nonlinear(t *testing.T) {
	// A product of two non-constant real subforms reads over the monomial
	// basis (Domain.polyMul, wired to realRing's): ONE monomial whose atom is
	// the canonical product, so `x * y` and `y * x` are the same unknown.
	lf, ok := realDomain.linOf(rr("x * y"))
	if !ok || !lf.konst.isZero() || len(lf.monos) != 1 || !lf.monos[0].coeff.isOne() {
		t.Fatalf("linOf(x * y) = %+v ok=%v; want one unit monomial", lf, ok)
	}
	if lf2, _ := realDomain.linOf(rr("y * x")); !lf2.monos[0].atom.AlphaEquals(lf.monos[0].atom) {
		t.Errorf("x * y and y * x read as different atoms: %v vs %v", lf.monos[0].atom, lf2.monos[0].atom)
	}
}

func TestRealDomain_BuildTerm_RoundTrip(t *testing.T) {
	// buildTerm emits the canonical real form: explicit coeff per monomial,
	// trailing constant. For an already-canonical input it round-trips exactly.
	for _, s := range []string{"&2 * x + &3", "&2 * x + &4 * y + &1"} {
		lf, ok := realDomain.linOf(rr(s))
		if !ok {
			t.Fatalf("linOf(%q) failed", s)
		}
		got := realDomain.buildTerm(lf)
		if !got.AlphaEquals(rr(s)) {
			t.Errorf("buildTerm∘linOf(%q) = %v, want the canonical input term", s, got)
		}
	}
}

// TestRealDomain_NoSuc confirms the real domain carries no suc folding: there is
// no suc on ℝ, so matchSuc is nil and linOf never invents a +1.
func TestRealDomain_NoSuc(t *testing.T) {
	if realDomain.matchSuc != nil {
		t.Errorf("realDomain.matchSuc should be nil (ℝ has no successor)")
	}
}

// ── Hyp-side constraint extraction over ℝ ────────────────────────────────────

func TestRealDomain_ParseHypConstraint(t *testing.T) {
	cases := []struct {
		text    string
		lhs     string // expected canonical Lhs / Rhs text (real-parsed)
		rhs     string
		op      relOp
		origHyp bool // true ⇒ Hyp carries the original (>,≥) term
	}{
		{"x < y", "x", "y", opLT, false},
		{"x <= y", "x", "y", opLE, false},
		{"x = y", "x", "y", opEQ, false},
		{"&2 * x <= &3", "&2 * x", "&3", opLE, false},
		// `>` / `≥` canonicalize to swapped `<` / `≤`, original term kept in Hyp.
		{"x > y", "y", "x", opLT, true},
		{"x >= y", "y", "x", opLE, true},
	}
	for _, c := range cases {
		got, ok := realDomain.parseHypConstraint(rb(c.text))
		if !ok {
			t.Errorf("parseHypConstraint(%q): ok=false, want true", c.text)
			continue
		}
		if !got.Lhs.AlphaEquals(rr(c.lhs)) || !got.Rhs.AlphaEquals(rr(c.rhs)) {
			t.Errorf("parseHypConstraint(%q): got %v %v, want %q %q",
				c.text, got.Lhs, got.Rhs, c.lhs, c.rhs)
		}
		if got.Op != c.op {
			t.Errorf("parseHypConstraint(%q): Op=%v, want %v", c.text, got.Op, c.op)
		}
		if c.origHyp {
			if got.Hyp == nil || !got.Hyp.AlphaEquals(rb(c.text)) {
				t.Errorf("parseHypConstraint(%q): Hyp should carry the original term", c.text)
			}
		} else if got.Hyp != nil {
			t.Errorf("parseHypConstraint(%q): Hyp should be nil for %q", c.text, c.text)
		}
	}
}

func TestRealDomain_ParseHypConstraint_Drops(t *testing.T) {
	// A product comparison is a linear constraint over the monomial basis
	// (kept); a non-comparison hyp is dropped (ok=false).
	if _, ok := realDomain.parseHypConstraint(rb("x * y <= &1")); !ok {
		t.Errorf("`x * y <= &1` should be read over the monomial basis, not dropped")
	}
	if _, ok := realDomain.parseHypConstraint(rb("x < &2 ⇒ y < &3")); ok {
		t.Errorf("a non-comparison (implication) hyp should be dropped")
	}
}

func TestRealDomain_HypConstraints_FiltersAndKeeps(t *testing.T) {
	// A mixed hyp set: two real linear comparisons + one product comparison
	// (read over the monomial basis) + one implication (dropped).
	hyps := seqOf(rb("x <= y"), rb("x * y < &1"), rb("&2 * y < &5"), rb("x < &2 ⇒ y < &3"))
	cs := realDomain.hypConstraints(hyps)
	if len(cs) != 3 {
		t.Fatalf("hypConstraints kept %d, want 3 (the implication dropped, the product kept)", len(cs))
	}
}

// seqOf adapts terms into an iter.Seq for the hypConstraints API.
func seqOf(ts ...Term) iter.Seq[Term] {
	return func(yield func(Term) bool) {
		for _, t := range ts {
			if !yield(t) {
				return
			}
		}
	}
}

// andFold builds a right-nested ∧-conjunction of the given terms, used by the
// bundle/derive/bare-fact tests to assemble TestThm Numeral* conjunctions from
// the per-bit placeholder leaves.
func andFold(ts ...Term) Term {
	out := ts[len(ts)-1]
	for i := len(ts) - 2; i >= 0; i-- {
		out = ext.Apply(prop.AND, ts[i], out)
	}
	return out
}

// Test-construction helpers that build omega terms from text via ext/dsl rather
// than the native plus/star/eqT/… constructors. Two payoffs: the test bodies
// read as the math they assert ("a + b * c = …"), and every case doubles as a
// round-trip check of the dsl parser against the same consts omega builds with.
//
// Numerals are safe: dsl lowers a bare literal to a bit-tree
// (ext/dsl/build.go `*astNumLit` → ext.MakeNumeral), identical to omega's Numeral(n) — so
// "2 + 3" parses to the exact bare term omega expects. (Only a numeral bound
// to a runtime loop variable must stay native Numeral(v); a literal string can't
// hold a dynamic value.)

var tIdentRE = regexp.MustCompile(`[A-Za-z_][A-Za-z0-9_]*`)

// tReservedConst are the identifiers in omega term text that are CONSTS, not num
// variables; everything else lexes as a num-typed free var (numScope below).
var tReservedConst = map[string]bool{
	"bit0": true, "bit1": true, "_0": true, "suc": true,
	"nat_div": true, "nat_mod": true, "divides": true, "T": true, "F": true,
}

// numScope assigns NumType to every non-const identifier in s, so the helpers
// need no per-call type-declaration boilerplate regardless of the var names used.
func numScope(s string) map[string]core.HolType {
	ctx := map[string]core.HolType{}
	for _, id := range tIdentRE.FindAllString(s, -1) {
		if !tReservedConst[id] {
			ctx[id] = dsl.NumType
		}
	}
	return ctx
}

// tParseConsts registers omega's `divides`/`nat_div`/`nat_mod` so the parser resolves
// them as the same consts omega builds with (they are not among the dsl's
// well-known nat encoders). The five literal encoders + the arith infixes are
// already well-known, so only these three need a scope entry.
var tParseConsts = map[string]core.ConstTerm{
	"divides": NatDividesMeta.Term(),
	"nat_div": dsl.NatDivMeta.Term(),
	"nat_mod": dsl.NatModMeta.Term(),
}

func tParse(s string, expected core.HolType) Term {
	r := dsl.ParseTermTextInScope(s, numScope(s),
		&dsl.ParseScope{Consts: tParseConsts}, expected)
	if len(r.Errors) > 0 {
		panic(fmt.Sprintf("dsl parse %q: %v", s, r.Errors))
	}
	return r.Term
}

// tn parses s as a num-typed term (e.g. "a + b * 2", "bit0(a)", "suc(n)", "nat_div(a, b)").
func tn(s string) Term { return tParse(s, dsl.NumType) }

// tb parses s as a bool-typed term — equality / comparison / ⇒ / ⇔ / ¬ /
// `divides` / ⊤ / ⊥ (e.g. "a < b", "a <= b => b <= a => a = b", "divides(d, n)").
func tb(s string) Term { return tParse(s, core.TypeBool()) }

// suc is folded into the linear form as `suc x = x + 1` (successor →
// coefficient), in both the untrusted model (linOf) and the proof
// mirror (normalizeProof). These tests pin (1) the canonical form,
// (2) the proof plumbing closes, and (3) the forward provers now see through suc
// — the load-bearing case being the ℕ identity `b < suc a ⟺ b ≤ a`, which needs
// the integer core once suc is recognized.

func TestSucNormalizesToPlusOne(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	n := func(k uint64) Term { return Numeral(k) }

	// canonical forms: suc contributes +1 to the constant, recursively.
	forms := []struct {
		e    Term
		want linForm
	}{
		{sucT(a), form(1, mono(1, a))},
		{sucT(sucT(a)), form(2, mono(1, a))},
		{sucT(plus(a, b)), form(1, mono(1, a), mono(1, b))},
		{plus(sucT(a), sucT(b)), form(2, mono(1, a), mono(1, b))},
		{sucT(n(4)), form(5)},
	}
	for _, f := range forms {
		got, ok := linOf(f.e)
		if !ok {
			t.Errorf("linOf declined %v", f.e)
			continue
		}
		if evalLinNeq(got, f.want) {
			t.Errorf("linOf(%v) = %+v, want %+v", f.e, got, f.want)
		}
		// proof mirror agrees and closes.
		checkNormalize(t, f.e)
	}
}

func TestSucRingProve(t *testing.T) {
	pairs := []struct{ l, r Term }{
		{tn("suc(a)"), tn("a + 1")},
		{tn("suc(suc(a))"), tn("a + 2")},
		{tn("suc(a) + 3"), tn("a + 4")},
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

// The full multivariate ring (RingProveFull, used by the engine `ring` move)
// must also see through suc — including in a nonlinear context.
func TestSucRingProveFull(t *testing.T) {
	pairs := []struct{ l, r Term }{
		{tn("suc(a)"), tn("a + 1")},
		{tn("suc(a) * b"), tn("a * b + b")},                // (a+1)·b = a·b + b
		{tn("suc(a) * suc(a)"), tn("a * a + (2 * a + 1)")}, // (a+1)² = a²+2a+1
	}
	for _, p := range pairs {
		w, ok := RingProveFull(p.l, p.r)
		if !ok {
			t.Errorf("RingProveFull failed to close %v = %v", p.l, p.r)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(p.l) || !prop.Rhs(w).AlphaEquals(p.r) {
			t.Errorf("RingProveFull(%v,%v): proof is %v = %v", p.l, p.r, prop.Lhs(w), prop.Rhs(w))
		}
	}
}

func TestSucForwardProvers(t *testing.T) {
	installTestBundle(t) // the b<suc a ⊢ b<=a upgrade needs the integer cut leaves
	// ℚ-valid suc goals: LinProve already suffices once suc is seen through.
	checkProve(t, "a < suc a", nil, tb("a < suc(a)"), true)
	checkProve(t, "a <= suc a", nil, tb("a <= suc(a)"), true)
	checkProve(t, "suc a != a", nil, tb("~(suc(a) = a)"), true)

	// The integer identity b < suc a ⟺ b ≤ a: ℚ-Farkas cannot bridge it (a < b <
	// a+1 is ℚ-SAT), so it is the OmegaProve upgrade — and only reachable now that
	// suc normalizes to a+1.
	checkProveWith(t, "OmegaProve b<suc a ⊢ b<=a", OmegaProve,
		[]Term{tb("b < suc(a)")}, tb("b <= a"), true)
	if _, ok := LinProve(numSeq(tb("b < suc(a)")), tb("b <= a")); ok {
		t.Error("guard: LinProve should NOT prove b<suc a ⊢ b<=a (needs integrality)")
	}

	// Before the fix suc a was an opaque atom distinct from a, so this declined;
	// now b ≤ suc a follows from b ≤ a.
	checkProve(t, "b<=a ⊢ b<=suc a", []Term{tb("b <= a")}, tb("b <= suc(a)"), true)
}

// TestGtGeBridge guards the `>` / `≥` definitional bridges against the binder-order
// regression (a `[x,y]`-vs-`[y,x]` instantiation bug that panicked every `≥`/`>`
// goal under a production bundle). It installs the GT/GE defs in their
// real normal-form shape — `∀a b. (a<b) ⇔ (b>a)` / `∀a b. (a≤b) ⇔ (b≥a)`, the
// strict/large relation on the swapped second binder — and clears the placeholder
// fabricator, so a wrong instantiation order degrades + panics rather than silently
// fabricating the wanted shape (which is exactly how the bug hid with the
// fabricator installed). The bridges must orient to the `x>y ⇔ y<x` / `x≥y ⇔ y≤x` shape their
// callers (proveWith / decideCmp) consume.
func TestGtGeBridge(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	gtDef := mk(ext.ForAll(a, b)(eqT(lt(a, b), gt(b, a)))) // ∀a b. (a<b) ⇔ (b>a)
	geDef := mk(ext.ForAll(a, b)(eqT(le(a, b), ge(b, a)))) // ∀a b. (a≤b) ⇔ (b≥a)

	SetNatLemmaBundle(&NatLemmaBundle{GtDef: gtDef, GeDef: geDef})
	withoutFabricator(t) // production behavior: a degrade panics, proving the bridge bound the field
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	x, y := numVar("x"), numVar("y")
	if got, want := gtBridge(x, y).Conclusion(), eqT(gt(x, y), lt(y, x)); !got.AlphaEquals(want) {
		t.Errorf("gtBridge(x,y): got %v, want %v", got, want)
	}
	if got, want := geBridge(x, y).Conclusion(), eqT(ge(x, y), le(y, x)); !got.AlphaEquals(want) {
		t.Errorf("geBridge(x,y): got %v, want %v", got, want)
	}
}

// numVar builds a num-typed free variable; shared across the omega test suite.
func numVar(name string) prop.Term { return ext.Var(ext.TermName(name), dsl.NumType) }

// The matchers recognize the arith shapes.
func TestMatchers(t *testing.T) {
	a, b := numVar("a"), numVar("b")

	if l, r, ok := MatchesPlus(tn("a + b")); !ok || !l.AlphaEquals(a) || !r.AlphaEquals(b) {
		t.Errorf("MatchesPlus(a+b) = (%v,%v,%v)", l, r, ok)
	}
	if _, _, ok := MatchesPlus(tn("a * b")); ok {
		t.Error("MatchesPlus matched a*b")
	}
	if x, ok := MatchesSuc(tn("suc(a)")); !ok || !x.AlphaEquals(a) {
		t.Errorf("MatchesSuc(suc a) = (%v,%v)", x, ok)
	}
	if _, ok := MatchesSuc(tn("a")); ok {
		t.Error("MatchesSuc matched a bare var")
	}
}

// ℤ ring-normalizer tests — the intRing instantiation of the domain-generic
// machinery (ring.go), the twin of real_test.go. Leaves are
// placeholders (no int bundle installed), but the kernel enforces every
// EqTrans/congruence in the composition, and we pin Lhs = t, Rhs =
// buildTerm(linOf(t)) + model lockstep. TestIntRingBundleWiring then pins each
// ring leaf's bound orientation/binder order with marker hypotheses.

func checkIntNormalize(t *testing.T, e Term) {
	t.Helper()
	lf, w, ok := intRing.normalizeProof(e)
	if !ok {
		t.Fatalf("intNormalizeProof declined %v", e)
	}
	if !prop.Lhs(w).AlphaEquals(e) {
		t.Errorf("Lhs = %v, want %v", prop.Lhs(w), e)
	}
	if !prop.Rhs(w).AlphaEquals(intDomain.buildTerm(lf)) {
		t.Errorf("Rhs = %v, want toTerm %v", prop.Rhs(w), intDomain.buildTerm(lf))
	}
	if ref, _ := intDomain.linOf(e); evalLinNeq(lf, ref) {
		t.Errorf("intNormalizeProof form disagrees with linOf for %v", e)
	}
}

// ── Negated comparison hypotheses ────────────────────────────────────────────
//
// A negated comparison carries exactly the same information as its positive
// spelling — `¬(a<b)` IS `b≤a` (NotLessThan) — but nothing downstream of
// hypConstraints is negation-aware: linOf reads positive atoms only. Before the
// unnegateHyp hook the parser simply dropped these, so a goal decided or not
// depending on how its hypothesis happened to be written.

func TestHypConstraints_UnnegatesComparisons(t *testing.T) {
	cases := []struct {
		text string // the NEGATED hyp
		lhs  string // the positive constraint it must become
		rhs  string
		op   relOp
	}{
		// ¬(a<b) ⇔ b≤a
		{"¬(x < y)", "y", "x", opLE},
		// ¬(a≤b) ⇔ b<a
		{"¬(x <= y)", "y", "x", opLT},
		// The compound shape the words val channel produces.
		{"¬(x + y < z)", "z", "x + y", opLE},
	}
	for _, c := range cases {
		cs := natDomain.hypConstraints(seqOf(tb(c.text)))
		if len(cs) != 1 {
			t.Errorf("hypConstraints(%q): got %d constraints, want 1", c.text, len(cs))
			continue
		}
		got := cs[0]
		if !got.Lhs.AlphaEquals(tn(c.lhs)) || !got.Rhs.AlphaEquals(tn(c.rhs)) {
			t.Errorf("hypConstraints(%q): got %v %v, want %q %q",
				c.text, got.Lhs, got.Rhs, c.lhs, c.rhs)
		}
		if got.Op != c.op {
			t.Errorf("hypConstraints(%q): Op=%v, want %v", c.text, got.Op, c.op)
		}
		// The un-negation carries `{h} ⊢ positive`, so the refutation's
		// hypotheses stay within the goal's (the IsStronger contract). A bare
		// Assume of the rebuilt positive term would silently widen them.
		if got.HypProof == nil {
			t.Errorf("hypConstraints(%q): no HypProof — the original hyp is not carried", c.text)
			continue
		}
		if !got.HypProof.HasHyp(tb(c.text)) {
			t.Errorf("hypConstraints(%q): HypProof does not depend on the ORIGINAL hyp; hyps=%v",
				c.text, got.HypProof.Hyps())
		}
		if got.Hyp != nil {
			t.Errorf("hypConstraints(%q): Hyp must be nil (the proof is carried in HypProof)", c.text)
		}
	}
}

// TestHypConstraints_NegatedEqualityStillDropped pins the deliberate carve-out:
// `¬(a=b)` is a DISJUNCTION, not a comparison. Turning it into one linear row
// would be unsound; it belongs to the case-split engine (hypSplittable), which
// already ingests it.
func TestHypConstraints_NegatedEqualityStillDropped(t *testing.T) {
	if cs := natDomain.hypConstraints(seqOf(tb("¬(x = y)"))); len(cs) != 0 {
		t.Errorf("¬(x = y) must not become a linear constraint; got %d", len(cs))
	}
}

// TestUnnegate_DomainsWired checks all three domains got the hook — the
// vocabulary is per-domain, so a missing wire would leave that domain with the
// original spelling-dependent behavior.
func TestUnnegate_DomainsWired(t *testing.T) {
	for _, d := range []*Domain{natDomain, realDomain, intDomain} {
		if d.unnegateHyp == nil {
			t.Errorf("domain %q has no unnegateHyp hook", d.name)
		}
	}
	// And it actually fires on the real domain's own vocabulary.
	cs := realDomain.hypConstraints(seqOf(rb("¬(x < y)")))
	if len(cs) != 1 {
		t.Fatalf("real: ¬(x < y) produced %d constraints, want 1", len(cs))
	}
	if !cs[0].Lhs.AlphaEquals(rr("y")) || !cs[0].Rhs.AlphaEquals(rr("x")) || cs[0].Op != opLE {
		t.Errorf("real: ¬(x < y) became %v %v (op %v), want y ≤ x",
			cs[0].Lhs, cs[0].Rhs, cs[0].Op)
	}
}

// TestLinProve_NegatedHypSpellingAgnostic is the end-to-end claim: the same
// fact decides the same way however it is spelled. This is the gap the words
// val channel surfaced — `m ≤ a+b ⊢ …` closed while `¬(a+b < m) ⊢ …` declined.
//
// LinProve (ℚ-Farkas) rather than OmegaProve: the integer layer's leaves are
// placeholder-by-design and DECLINE in this package, so OmegaProve decides
// nothing here — measured, not assumed.
func TestLinProve_NegatedHypSpellingAgnostic(t *testing.T) {
	goal := tb("y <= x + 1")
	positive, ok := LinProve(seqOf(tb("y <= x")), goal)
	if !ok {
		t.Fatal("baseline: the positive spelling should decide")
	}
	negated, ok := LinProve(seqOf(tb("¬(x < y)")), goal)
	if !ok {
		t.Fatal("the negated spelling of the same fact must decide too")
	}
	if !negated.Conclusion().AlphaEquals(positive.Conclusion()) {
		t.Errorf("the two spellings proved different conclusions:\n %v\n %v",
			negated.Conclusion(), positive.Conclusion())
	}
	// The certificate must depend on the hypothesis AS WRITTEN.
	if !negated.HasHyp(tb("¬(x < y)")) {
		t.Errorf("certificate does not carry the original negated hyp; hyps=%v", negated.Hyps())
	}
}

// TestHypConstraintsMemo pins the extraction memo's contract
// (Domain.hypConstraintsOf): the same hypothesis term extracts once and the
// carried proof is shared; the key is the exact term, so an α-variant with
// a binder inside a conjunct misses (its proof names the term it was built
// from); a bundle swap drops the entries.
func TestHypConstraintsMemo(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	first := realDomain.hypConstraintsOf(rb("a - b ≤ c")) // a sub hyp: the carried proof is the move-across iff
	second := realDomain.hypConstraintsOf(rb("a - b ≤ c"))
	if len(first) != 1 || len(second) != 1 || first[0].HypProof == nil || first[0].HypProof != second[0].HypProof {
		t.Fatalf("second extraction of the same hyp not served from the memo: %v / %v", first, second)
	}
	conj := func(v Term) Term { return and(rb("a ≤ c"), ext.ForAll(v)(realLeT(v, v))) }
	cx, cy := conj(realVar("x")), conj(realVar("y"))
	ex, ey := realDomain.hypConstraintsOf(cx), realDomain.hypConstraintsOf(cy)
	if len(ex) != 1 || len(ey) != 1 || ex[0].HypProof == ey[0].HypProof {
		t.Fatalf("an α-variant hyp must miss the memo: %v / %v", ex, ey)
	}
	if !ex[0].HypProof.Hyp(0).Equals(cx) || !ey[0].HypProof.Hyp(0).Equals(cy) {
		t.Errorf("a conjunct's carried proof must name its own hyp: %v / %v", ex[0].HypProof, ey[0].HypProof)
	}
	SetRealLemmaBundle(&RealLemmaBundle{})
	if again := realDomain.hypConstraintsOf(rb("a - b ≤ c")); again[0].HypProof == first[0].HypProof {
		t.Fatalf("a bundle swap must drop the memo")
	}
}
