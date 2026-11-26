package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

func TestArithDecide_B1Identities(t *testing.T) {
	cases := []struct {
		name, in, want string
	}{
		{"a+0 → a", "a + 0", "a"},
		{"0+a → a", "0 + a", "a"},
		{"a*0 → 0", "a * 0", "0"},
		{"0*a → 0", "0 * a", "0"},
		{"a*1 → a", "a * 1", "a"},
		{"1*a → a", "1 * a", "a"},
		// nested / fixpoint
		{"(a+0)+0 → a", "(a + 0) + 0", "a"},
		{"a*1+0 → a", "a * 1 + 0", "a"},
		{"(a*1)*(b+0) → a*b", "(a * 1) * (b + 0)", "a * b"},
		// numeral folding
		{"2+3 → 5", "2 + 3", "5"},
		{"2*3 → 6", "2 * 3", "6"},
		{"a + (2+3) → a + 5", "a + (2 + 3)", "a + 5"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			in := tn(tc.in)
			w := ArithDecide(in)
			if w == nil {
				t.Fatalf("ArithDecide(%q) = nil, want a rewrite", tc.in)
			}
			if !prop.Lhs(w).AlphaEquals(in) {
				t.Errorf("Lhs = %v, want %v", prop.Lhs(w), in)
			}
			if want := tn(tc.want); !prop.Rhs(w).AlphaEquals(want) {
				t.Errorf("Rhs = %v, want %v", prop.Rhs(w), want)
			}
		})
	}
}

// An already-reduced term (no 0/1 identity, no two adjacent numerals, no
// decidable atom) yields no rewrite, and crucially the rewrite does NOT
// collect or expand (a+b stays a+b; that is RingProveFull's job).
func TestArithDecide_DeclinesAndNeverGrows(t *testing.T) {
	for _, s := range []string{"a", "a + b", "a * b", "a + b * c", "(a + b) * c"} {
		if w := ArithDecide(tn(s)); w != nil {
			t.Errorf("ArithDecide(%q) = %v, want nil (no conservative simplification)", s, prop.Rhs(w))
		}
	}
}

// ── Comparison decision ─────────────────────────────────────────────────────

func TestArithDecideValidToTrue(t *testing.T) {
	for _, s := range []string{"a < a + 1", "a + 1 > a", "a <= a", "a <= a + 1", "a + 1 >= a", "0 <= a"} {
		t.Run(s, func(t *testing.T) {
			in := tb(s)
			w := ArithDecide(in)
			if w == nil {
				t.Fatalf("ArithDecide(%q) = nil, want ⊤", s)
			}
			if !prop.Lhs(w).AlphaEquals(in) {
				t.Errorf("Lhs = %v, want %v", prop.Lhs(w), in)
			}
			if !prop.Rhs(w).AlphaEquals(prop.T) {
				t.Errorf("Rhs = %v, want ⊤", prop.Rhs(w))
			}
		})
	}
}

func TestArithDecideFalseToBottom(t *testing.T) {
	for _, s := range []string{"a < a", "a + 1 <= a", "a < a"} {
		t.Run(s, func(t *testing.T) {
			w := ArithDecide(tb(s))
			if w == nil {
				t.Fatalf("ArithDecide(%q) = nil, want ⊥", s)
			}
			if !prop.Rhs(w).AlphaEquals(prop.F) {
				t.Errorf("Rhs = %v, want ⊥", prop.Rhs(w))
			}
		})
	}
}

// A buried comparison atom (here under ¬) is decided in place. The unified
// deep+fixpoint rewrite decides `a<a+1→⊤` and BoolRewrite immediately
// collapses `¬⊤→⊥` in the same pass — exactly the cascade the user's
// `Cond(a=a,0,1)` example pushed on.
func TestArithDecideBuriedAtom(t *testing.T) {
	in := tb("~(a < a + 1)")
	w := ArithDecide(in)
	if w == nil {
		t.Fatal("ArithDecide(~(a<a+1)) = nil, want decided + ¬-collapsed")
	}
	if !prop.Lhs(w).AlphaEquals(in) {
		t.Errorf("Lhs = %v, want %v", prop.Lhs(w), in)
	}
	// Inner atom decides ⊤; BoolRewrite folds ¬⊤ → ⊥ in the same fixpoint pass.
	if !prop.Rhs(w).AlphaEquals(prop.F) {
		t.Errorf("Rhs = %v, want ⊥", prop.Rhs(w))
	}
}

// ArithDecide declines on a comparison that is neither universally valid nor
// universally false (it is hyp-free — `a<b` follows from no context).
func TestArithDecideDeclinesContingent(t *testing.T) {
	for _, s := range []string{"a < b", "a <= b", "a = b"} {
		if w := ArithDecide(tb(s)); w != nil {
			t.Errorf("ArithDecide(%q) = %v, want nil (contingent, hyp-free)", s, prop.Rhs(w))
		}
	}
}

// Per-atom soundness must not let a contingent atom's failed prove attempt
// poison the sound decisions of its siblings: `(a<a+1) ∧ (a<b)` must still
// collapse the valid `a<a+1` to ⊤ even though `a<b` is contingent (a failed
// OmegaProve attempt on it can bump the global unsound counter). Guarding the
// whole DeepRewrite once would wrongly decline the entire term here.
// BoolRewrite then folds `⊤ ∧ (a<b) → a<b` in the same fixpoint pass.
func TestArithDecideNoCrossAtomPoisoning(t *testing.T) {
	in := tb("(a < a + 1) /\\ (a < b)")
	w := ArithDecide(in)
	if w == nil {
		t.Fatal("ArithDecide declined a term whose decidable conjunct should collapse")
	}
	if want := tb("a < b"); !prop.Rhs(w).AlphaEquals(want) {
		t.Errorf("Rhs = %v, want (a<b) — decidable conjunct → ⊤, BoolRewrite folds ⊤∧X→X", prop.Rhs(w))
	}
}

// Ring fold for the equality fragment: a NONLINEAR universally-true equality
// (`a*b = b*a`, `(a+b)*c = a*c + b*c`) is decided to ⊤, subsuming what the old
// separate `arith` closer did via RingProveFull. The same ArithDecide rewrite
// handles both linear comparisons and nonlinear semiring equalities now.
func TestArithDecideRingFoldedIn(t *testing.T) {
	for _, s := range []string{"a * b = b * a", "(a + b) * c = a * c + b * c"} {
		t.Run(s, func(t *testing.T) {
			in := tb(s)
			w := ArithDecide(in)
			if w == nil {
				t.Fatalf("ArithDecide(%q) = nil, want ⊤ via ring", s)
			}
			if !prop.Lhs(w).AlphaEquals(in) {
				t.Errorf("Lhs = %v, want %v", prop.Lhs(w), in)
			}
			if !prop.Rhs(w).AlphaEquals(prop.T) {
				t.Errorf("Rhs = %v, want ⊤", prop.Rhs(w))
			}
		})
	}
}

// Hyp-aware decision: a comparison that is contingent on its own but follows
// from a hypothesis decides under ArithDecideWithHyps, and the resulting
// equality carries that hypothesis. The hyp-free entry still declines it.
func TestArithDecideHypAware(t *testing.T) {
	atom := tb("a < b + 1") // contingent alone; follows from a ≤ b
	if w := ArithDecide(atom); w != nil {
		t.Fatalf("hyp-free ArithDecide(a<b+1) = %v, want nil (contingent)", prop.Rhs(w))
	}
	w := ArithDecideWithHyps([]Term{tb("a <= b")})(atom)
	if w == nil {
		t.Fatal("ArithDecideWithHyps([a≤b])(a<b+1) = nil, want ⊤")
	}
	if !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("Rhs = %v, want ⊤", prop.Rhs(w))
	}
	if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(tb("a <= b")) {
		t.Errorf("decided equality must carry the used hyp a≤b, got %d hyps", w.NumHyps())
	}
}

// The cascade-across-rules regression. `a + Cond(a=a, 0, 1)`:
//
//   - none of the leaves fire at the top level.
//   - recurse into Cond: arithDecideLeaf decides `a=a → ⊤`. Wrapper substituted into Cond.
//   - trivialCondRewrite collapses `Cond(⊤, 0, 1) → 0` (next pass of the same
//     fixpoint).
//   - arithSimpStep reduces `a + 0 → a`.
//
// Each step lives in BasicRewritesWith's underlying DeepRewrite — one call
// drives the whole cascade to fixpoint via RewriteConclRhsRecur. A linear
// chain (simp once, decide once, trivial once) would have left `a + 0` on the
// floor; this is exactly what motivated rebuilding the composite as ONE
// deep+fixpoint rewrite.
func TestArithDecide_CondCascade(t *testing.T) {
	a := tn("a")
	// a + Cond(a=a, 0, 1) — built manually because the test DSL doesn't carry COND.
	condInIfTrue := ext.Cond(eqT(a, a), Numeral(0), Numeral(1)).Core()
	in1 := plus(a, condInIfTrue)
	w := ArithDecide(in1)
	if w == nil {
		t.Fatal("ArithDecide(a + Cond(a=a, 0, 1)) = nil, want `a` via the arith→cond→arith cascade")
	}
	if !prop.Rhs(w).AlphaEquals(a) {
		t.Errorf("Rhs = %v, want `a` (a + Cond(⊤,0,1) → a + 0 → a)", prop.Rhs(w))
	}

	// a + Cond(a=a+1, 0, 1) — false branch picks 1; arithSimpStep leaves `a+1` alone.
	one := Numeral(1)
	condFalse := ext.Cond(eqT(a, plus(a, one)), Numeral(0), one).Core()
	in2 := plus(a, condFalse)
	w2 := ArithDecide(in2)
	if w2 == nil {
		t.Fatal("ArithDecide(a + Cond(a=a+1, 0, 1)) = nil, want `a + 1`")
	}
	if want := plus(a, one); !prop.Rhs(w2).AlphaEquals(want) {
		t.Errorf("Rhs = %v, want `a + 1`", prop.Rhs(w2))
	}
}

// Hyp-aware decision reaching UNDER a binder: the hyp-carrying equality for the
// free-var atom `a<b+1` lifts under the ∃c binder (c is NOT free in a≤b → no
// rename needed), and the bound-var atom `c<c+1` decides on its own. Both go
// to ⊤; BoolRewrite folds `⊤ ∧ ⊤ → ⊤`; QuantifierRewrite folds the trivial
// `∃c. ⊤ → ⊤` — all in the same fixpoint pass. The a≤b hyp is preserved on
// the wrapper through the lift.
func TestArithDecideHypUnderBinder(t *testing.T) {
	in := tb("∃ c:num. ((a < b + 1) /\\ (c < c + 1))")
	w := ArithDecideWithHyps([]Term{tb("a <= b")})(in)
	if w == nil {
		t.Fatal("ArithDecideWithHyps under a binder = nil")
	}
	if !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("Rhs = %v, want ⊤ (cascade: decide + ⊤∧⊤→⊤ + ∃x.⊤→⊤)", prop.Rhs(w))
	}
	if w.NumHyps() != 1 {
		t.Errorf("expected the a≤b hyp carried through the binder, got %d hyps", w.NumHyps())
	}
}

// arithIffLeaf gating (engine.go). End-to-end closure of `(a<b) ⇔ (suc a ≤ b)`
// is validated against the real corpus bundle (library/serve's
// TestInstallNatBundleBindingIffCompare). Here we pin the shape gate: only a
// bool iff of two DISTINCT comparison atoms is a candidate, and a candidate
// whose directions do not hold is declined.
func TestArithIffLeafGating(t *testing.T) {
	SetNatLemmaBundle(nil)
	t.Cleanup(func() { SetNatLemmaBundle(nil) })
	leaf := arithIffLeaf(nil)
	a, b := numVar("a"), numVar("b")

	// num equality `a = b` — not a comparison-iff (operands aren't comparisons).
	if leaf(eqT(a, b)) != nil {
		t.Error("arithIffLeaf fired on a num equality")
	}
	// reflexive comparison-iff `P ⇔ P` — BoolRewrite's (l=l)→⊤ handles it.
	if leaf(eqT(lt(a, b), lt(a, b))) != nil {
		t.Error("arithIffLeaf fired on a reflexive iff")
	}
	// a non-comparison subterm — declines.
	if leaf(lt(a, b)) != nil {
		t.Error("arithIffLeaf fired on a bare comparison (not an iff)")
	}
	// A contingent comparison-iff is a candidate; one direction of
	// `(a < b) ⇔ (a ≤ b)` fails at a = b, so it declines rather than panic.
	if leaf(eqT(lt(a, b), le(a, b))) != nil {
		t.Error("arithIffLeaf fired on (a < b) ⇔ (a ≤ b), false at a = b")
	}
}

// installFactTestBundle pins the factorial recursion in its stated shape:
//
//	factorial : (factorial 0 = 1) ∧ (∀n. factorial(suc n) = suc n · factorial n)
//
// A unit guard against shape drift (the clause shapes the leaves project) that
// doesn't need the corpus build. End-to-end `factorial(c) → c!` (which also needs the
// full NormNatMul / sucBits backing) is validated against the real installed bundle
// in library/serve (TestInstallNatBundleBindingFact).
func installFactTestBundle(t *testing.T) func() {
	t.Helper()
	n := numVar("n")
	mk := func(c core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	prev := natLemmaBundle
	b := &NatLemmaBundle{}
	if prev != nil {
		*b = *prev
	}
	b.Factorial = mk(and(
		eqT(factT(natZero), Numeral(1)),
		ext.ForAll(n)(eqT(factT(sucT(n)), star(sucT(n), factT(n))))))
	SetNatLemmaBundle(b)
	return func() { SetNatLemmaBundle(prev) }
}

func TestFactClauseLeaves(t *testing.T) {
	defer installFactTestBundle(t)()
	n := numVar("n")

	// clause 1: factorial(0) = 1
	if w := factBase(); w == nil || !w.Conclusion().AlphaEquals(eqT(factT(natZero), Numeral(1))) {
		t.Errorf("factBase() = %v, want factorial(0) = 1", w)
	}
	// clause 2: factorial(suc n) = suc n · factorial n
	want := eqT(factT(sucT(n)), star(sucT(n), factT(n)))
	if w := factRecursion2(n); w == nil || !w.Conclusion().AlphaEquals(want) {
		t.Errorf("factRecursion2(n) = %v, want %v", w, want)
	}
}

func TestFactSimpGating(t *testing.T) {
	// Unbundled: even a literal factorial declines (no Factorial field).
	SetNatLemmaBundle(nil)
	if w := factSimp(factT(Numeral(4))); w != nil {
		t.Error("factSimp fired with no bundle installed")
	}
	defer installFactTestBundle(t)()
	// Symbolic argument: opaque, declines.
	if w := factSimp(factT(numVar("n"))); w != nil {
		t.Error("factSimp fired on a symbolic factorial argument")
	}
	// A non-factorial term: declines.
	if w := factSimp(star(Numeral(2), Numeral(3))); w != nil {
		t.Error("factSimp matched a non-factorial term")
	}
	// Over the cap: declines (factEvalMax = 10).
	if w := factSimp(factT(Numeral(factEvalMax + 1))); w != nil {
		t.Error("factSimp fired past factEvalMax")
	}
}

// Implication-hypothesis split (nat_sub.go hypSplittable, the `p ⇒ q` branch). The
// linear core drops an implication hyp; the case split turns it into `¬p ∨ q`
// and proves the goal in each branch. Placeholder leaves — we validate the
// kernel COMPOSITION (proveDecAtom concludes the goal with hyps ⊆ inputs).

func TestImplHypSplit(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	// {a<b ⇒ b<a} ⊢ b≤a : either ¬(a<b) i.e. b≤a, or b<a ⟹ b≤a. Valid only via
	// the implication split (linarith alone drops the hyp and cannot close it).
	hyps := []Term{imply(lt(a, b), lt(b, a))}
	goal := le(b, a)

	w, ok := proveDecAtom(slices.Values(hyps), goal)
	if !ok {
		t.Fatal("proveDecAtom did not close {a<b ⇒ b<a} ⊢ b≤a via the implication split")
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("conclusion = %v, want %v", w.Conclusion(), goal)
	}
	for i := 0; i < w.NumHyps(); i++ {
		if !slices.ContainsFunc(hyps, w.Hyp(i).AlphaEquals) {
			t.Errorf("stray hypothesis %v not among inputs", w.Hyp(i))
		}
	}

	// Sanity: linarith ALONE (dropping the implication) cannot prove b≤a.
	if _, ok := proveLinThenInt(slices.Values(hyps), goal); ok {
		t.Error("proveLinThenInt unexpectedly closed the goal without the split")
	}
}

// A non-comparison antecedent still splits soundly: the ¬p branch has no
// linear-usable bridge, so the goal must hold from q alone (or ¬p irrelevant).
func TestImplHypSplitNonCompAntecedent(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")
	// {P ⇒ a≤b, P} would be trivial; instead use q that forces the goal in the
	// q branch and ¬p (here ¬(c<c), vacuous) closing the other.
	hyps := []Term{imply(lt(c, c), lt(a, b)), lt(c, c)} // c<c is unsatisfiable ⇒ a<b
	goal := lt(a, b)
	if _, ok := proveDecAtom(slices.Values(hyps), goal); !ok {
		t.Fatal("proveDecAtom did not close {c<c ⇒ a<b, c<c} ⊢ a<b")
	}
}

// Real deep-rewrite tests — the ℝ twin of this file's nat deep-rewrite tests.
// Leaves are placeholders
// (no real bundle installed), so these pin the PLUMBING: the kernel enforces
// every EqTrans/congruence in the composition, and the deep+fixpoint cascade
// across the standard basic rewrites + the two real arith leaves lands the
// right reduced term. (Soundness rides on the bundle swap — the corpus binding
// suite, with no placeholder fabricator — as elsewhere in the real layer.)

// TestArithDecideUnifiedDispatch is the merge headline: ONE ArithDecide pass
// dispatches per atom by operand type — a nat atom to the nat leaves, a real
// atom to the real leaves — collapsing a goal that mixes both. The real half is
// gated on a real bundle being present; with none, a real atom is left
// untouched (the rewrite is byte-for-byte the nat-only one).
func TestArithDecideUnifiedDispatch(t *testing.T) {
	// Gate ON: a non-nil real bundle (empty → real leaves run on placeholders,
	// enough to pin the dispatch plumbing). Strict stays off by default.
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })

	natAtom := tb("2 + 3 = 5")     // nat numeral eq → nat leaves
	realAtom := rb("&2 + &3 = &5") // real numeral eq (of_num bridge) → real leaves
	in := prop.And(natAtom, realAtom)
	w := ArithDecide(in)
	if w == nil {
		t.Fatal("ArithDecide(nat ∧ real) = nil, want ⊤ via per-atom dispatch")
	}
	if !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("Rhs = %v, want ⊤ (both atoms decided in one pass)", prop.Rhs(w))
	}

	// Gate OFF: no real bundle ⇒ real leaves absent ⇒ a real atom does not reduce.
	SetRealLemmaBundle(nil)
	if w := ArithDecide(rb("&2 + &3 = &5")); w != nil {
		t.Errorf("gate off: ArithDecide(real) = %v, want nil (real leaves absent)", prop.Rhs(w))
	}
}

// checkRealBoolGoal is the ℝ mirror of this file's checkBoolGoal: it drives
// realProveBoolGoal directly and checks the conclusion + hyp-subset contract.
// A real bundle is installed by the caller so the in-branch collapse
// (arithCollapseRewrite) dispatches real atoms.
func checkRealBoolGoal(t *testing.T, name string, hyps []Term, goal Term, wantOK bool) {
	t.Helper()
	w, ok := realProveBoolGoal(hyps, goal, nil)
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
		if !slices.ContainsFunc(hyps, w.Hyp(i).AlphaEquals) {
			t.Errorf("%s: stray hypothesis %v not among inputs", name, w.Hyp(i))
		}
	}
}

// Conjunction-hypothesis flattening: a hyp `p ∧ q` (which parseHypConstraint
// alone drops — it ingests only top-level comparison atoms) is split into its
// comparison conjuncts, each carrying the projection `{p∧q} ⊢ conjunct` as its
// provenance. checkProveWith additionally asserts every hyp of the produced
// proof is among the INPUT hyps, so a PASS confirms the refutation carries the
// whole `∧` hyp — not a stray bare conjunct — preserving the IsStronger contract.
func TestConjHypFlatten(t *testing.T) {
	installTestBundle(t) // OmegaProve's `<` rows use the integer cut leaves (TestThm stand-ins)
	for _, prove := range []struct {
		name string
		fn   proveFunc
	}{{"LinProve", LinProve}, {"OmegaProve", OmegaProve}} {
		ck := func(n string, hyps []Term, goal Term, want bool) {
			checkProveWith(t, prove.name+" "+n, prove.fn, hyps, goal, want)
		}
		// basic two-conjunct transitivity
		ck("a<b ∧ b<c ⊢ a<c", []Term{tb("(a < b) /\\ (b < c)")}, tb("a < c"), true)
		// nested + equality conjunct
		ck("a<=b ∧ (b=c ∧ c<=d) ⊢ a<=d",
			[]Term{tb("(a <= b) /\\ ((b = c) /\\ (c <= d))")}, tb("a <= d"), true)
		// a `>` conjunct (the canonical form is swapped, provenance is the ∧ hyp)
		ck("a>b ∧ b>c ⊢ a>c", []Term{tb("(a > b) /\\ (b > c)")}, tb("a > c"), true)
		// a non-comparison junk conjunct (⊤) is ignored, the comparison ones fire
		ck("(a<=b ∧ T) ∧ b<=a ⊢ a=b",
			[]Term{tb("((a <= b) /\\ T) /\\ (b <= a)")}, tb("a = b"), true)
		// genuinely underdetermined: flattening must not over-prove
		ck("a<b ∧ c<d ⊬ b<c", []Term{tb("(a < b) /\\ (c < d)")}, tb("b < c"), false)
	}
}

// The bound NumeralLessThan/NumeralLessEq/NumeralEq carry their terminal cases as BARE facts
// (¬(0<0), 0<bit1 l, 0≠bit1 n) rather than the (P⇔⊤)/(P⇔⊥) form the synthetic
// theorems of the bit-comparison tests use — so that test does NOT exercise
// projectBareFact. Here we build the three decision theorems with the bare-fact
// conjuncts in the bound orientation (the two `=` ones flipped, so the
// CommuteEQ swap in projectBareFact fires) and check every comparison leaf still
// projects to the same ⊢ targetLHS ⇔ reduced the placeholder would produce.
func TestArithCmpBareFactExtraction(t *testing.T) {
	m, n := numVar("m"), numVar("n")
	a, b := numVar("a"), numVar("b")
	ForAll := ext.ForAll
	mk := func(c Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }

	// bareify turns a leaf's (lhs ⇔ ⊤/⊥) placeholder conclusion into the bare
	// fact (lhs / ¬lhs) the bound statement carries; a reducing iff passes through.
	bareify := func(w *prop.PropWrapper) Term {
		l, r, ok := prop.MatchesEQ(w.Conclusion())
		if !ok {
			return w.Conclusion()
		}
		switch {
		case r.AlphaEquals(prop.T):
			return l
		case r.AlphaEquals(prop.F):
			return not(l)
		default:
			return w.Conclusion()
		}
	}

	// Construct with no bundle installed → leaves return their placeholder iffs.
	numeralLessThan := mk(andFold(
		bareify(ltZeroZero()),               // ¬(0<0)
		ForAll(m)(bareify(ltB0Zero(m))),     // ¬(bit0 m<0)
		ForAll(n)(bareify(ltB1Zero(n))),     // ¬(bit1 n<0)
		ForAll(n)(bareify(ltZeroB1(n))),     // 0<bit1 n
		ForAll(n)(ltZeroB0(n).Conclusion()), // reducing iffs (leaf orientation)
		ForAll(m, n)(ltB0B0(m, n).Conclusion()),
		ForAll(m, n)(ltB0B1(m, n).Conclusion()),
		ForAll(m, n)(ltB1B0(m, n).Conclusion()),
		ForAll(m, n)(ltB1B1(m, n).Conclusion()),
	))
	numeralLessEq := mk(andFold(
		ForAll(n)(bareify(leZeroAny(n))), // 0≤n
		ForAll(m)(bareify(leB1Zero(m))),  // ¬(bit1 m≤0)
		ForAll(m)(leB0Zero(m).Conclusion()),
		ForAll(m, n)(leB0B0(m, n).Conclusion()),
		ForAll(m, n)(leB0B1(m, n).Conclusion()),
		ForAll(m, n)(leB1B0(m, n).Conclusion()),
		ForAll(m, n)(leB1B1(m, n).Conclusion()),
	))
	// `=` bare facts in the bound orientation (0=bit1, bit0=bit1); eqB1Zero /
	// eqB1B0 ask the flipped form and must route through the CommuteEQ swap.
	numeralEq := mk(andFold(
		ForAll(n)(not(eqT(natZero, bit1(n)))),    // 0 ≠ bit1 n
		ForAll(m, n)(not(eqT(bit0(m), bit1(n)))), // bit0 m ≠ bit1 n
		bareify(eqZeroZero()),                    // 0=0
		ForAll(n)(eqZeroB0(n).Conclusion()),
		ForAll(m)(eqB0Zero(m).Conclusion()),
		ForAll(m, n)(eqB0B0(m, n).Conclusion()),
		ForAll(m, n)(eqB1B1(m, n).Conclusion()),
	))

	cases := []struct {
		name string
		leaf func() *prop.PropWrapper
	}{
		{"ltZeroZero", ltZeroZero},
		{"ltZeroB0", func() *prop.PropWrapper { return ltZeroB0(a) }},
		{"ltZeroB1", func() *prop.PropWrapper { return ltZeroB1(a) }},
		{"ltB0Zero", func() *prop.PropWrapper { return ltB0Zero(a) }},
		{"ltB1Zero", func() *prop.PropWrapper { return ltB1Zero(a) }},
		{"ltB0B0", func() *prop.PropWrapper { return ltB0B0(a, b) }},
		{"ltB0B1", func() *prop.PropWrapper { return ltB0B1(a, b) }},
		{"ltB1B0", func() *prop.PropWrapper { return ltB1B0(a, b) }},
		{"ltB1B1", func() *prop.PropWrapper { return ltB1B1(a, b) }},
		{"leZeroAny", func() *prop.PropWrapper { return leZeroAny(a) }},
		{"leB0Zero", func() *prop.PropWrapper { return leB0Zero(a) }},
		{"leB1Zero", func() *prop.PropWrapper { return leB1Zero(a) }},
		{"leB0B0", func() *prop.PropWrapper { return leB0B0(a, b) }},
		{"leB0B1", func() *prop.PropWrapper { return leB0B1(a, b) }},
		{"leB1B0", func() *prop.PropWrapper { return leB1B0(a, b) }},
		{"leB1B1", func() *prop.PropWrapper { return leB1B1(a, b) }},
		{"eqZeroZero", eqZeroZero},
		{"eqZeroB0", func() *prop.PropWrapper { return eqZeroB0(a) }},
		{"eqZeroB1", func() *prop.PropWrapper { return eqZeroB1(a) }},
		{"eqB0Zero", func() *prop.PropWrapper { return eqB0Zero(a) }},
		{"eqB1Zero", func() *prop.PropWrapper { return eqB1Zero(a) }},
		{"eqB0B0", func() *prop.PropWrapper { return eqB0B0(a, b) }},
		{"eqB0B1", func() *prop.PropWrapper { return eqB0B1(a, b) }},
		{"eqB1B0", func() *prop.PropWrapper { return eqB1B0(a, b) }},
		{"eqB1B1", func() *prop.PropWrapper { return eqB1B1(a, b) }},
	}

	// want = the placeholder conclusion (no bundle); got = the projected one.
	want := make([]Term, len(cases))
	for i, tc := range cases {
		want[i] = tc.leaf().Conclusion()
	}

	SetNatLemmaBundle(&NatLemmaBundle{NumeralLessThan: numeralLessThan, NumeralLessEq: numeralLessEq, NumeralEq: numeralEq})
	t.Cleanup(func() { SetNatLemmaBundle(nil) })

	for i, tc := range cases {
		got := tc.leaf().Conclusion()
		if !got.AlphaEquals(want[i]) {
			t.Errorf("%s: projected\n  %v\nwant\n  %v", tc.name, got, want[i])
		}
	}
}

// End-to-end: a var=var hyp lets two opaque atoms over the equal variables merge,
// so the equality goal collapses to ⊤ in the unified rewrite — the payoff the
// var=literal-only version could not reach.
func TestEqHypSubstMergesOpaqueAtoms(t *testing.T) {
	a, n, m := numVar("a"), numVar("n"), numVar("m")
	goal := eqT(modT(a, n), modT(a, m)) // nat_mod(a,n) = nat_mod(a,m)
	w := ArithDecideWithHyps([]Term{eqT(n, m)})(goal)
	if w == nil {
		t.Fatal("ArithDecideWithHyps({n=m}) did not rewrite nat_mod(a,n)=nat_mod(a,m)")
	}
	if !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("want goal reduced to ⊤ under n=m, got %v", w.Conclusion())
	}
}

// Goal-side disjunction closer (nat.go). Like the rest of the omega unit
// suite the leaves are PLACEHOLDERS: we validate the kernel COMPOSITION
// (proveDisj concludes exactly `g0∨g1` with hyps drawn only from the inputs,
// so a tactic could close the goal via IsStronger), not soundness — that is
// covered end-to-end against the real corpus bundle in library/serve.

// checkDisj drives proveDisj and validates the result shape.
func checkDisj(t *testing.T, name string, hyps []Term, g0, g1 Term, wantOK bool) {
	t.Helper()
	w, ok := proveDisj(proveLinThenInt, hyps, g0, g1)
	if ok != wantOK {
		t.Errorf("%s: ok = %v, want %v", name, ok, wantOK)
		return
	}
	if !ok {
		return
	}
	want := or(g0, g1)
	if !w.Conclusion().AlphaEquals(want) {
		t.Errorf("%s: conclusion = %v, want %v", name, w.Conclusion(), want)
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
			t.Errorf("%s: stray hypothesis %v not among inputs", name, h)
		}
	}
}

func TestProveDisjTotality(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	// Totality / trichotomy: neither disjunct holds universally, the disjunction does.
	checkDisj(t, "a≤b ∨ b≤a", nil, le(a, b), le(b, a), true) // LessEqTotal shape
	checkDisj(t, "a<b ∨ b≤a", nil, lt(a, b), le(b, a), true) // pivot on a<b
	checkDisj(t, "a≤b ∨ b<a", nil, le(a, b), lt(b, a), true) // pivot on a≤b
	// Direct: a disjunct follows from the hyps.
	checkDisj(t, "{a<b} ⊢ a≤b ∨ b<a", []Term{lt(a, b)}, le(a, b), lt(b, a), true)
	checkDisj(t, "{a<b} ⊢ b<a ∨ a≤b", []Term{lt(a, b)}, lt(b, a), le(a, b), true)
	// Not valid: a<b ∨ a=b is not a tautology and no hyp forces it.
	checkDisj(t, "a<b ∨ a=b (invalid)", nil, lt(a, b), eqT(a, b), false)
}

// The unified deep rewrite reduces a pure-linear totality disjunction GOAL to ⊤
// (the totality proof is pure ℚ-Farkas, so it survives the per-atom soundness
// guard even with placeholder named-lemma leaves).
func TestArithDecideDisjGoal(t *testing.T) {
	a, b := numVar("a"), numVar("b")
	goal := or(le(a, b), le(b, a))
	w := ArithDecide(goal)
	if w == nil {
		t.Fatal("ArithDecide(a≤b ∨ b≤a) = nil; want reduction to ⊤")
	}
	if !prop.Lhs(w).AlphaEquals(goal) || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("ArithDecide totality: got %v, want (a≤b∨b≤a) ⇔ ⊤", w.Conclusion())
	}
}

// ── Formula-level decider (nat.go) — arbitrary boolean over comparisons ──

// checkBoolGoal drives proveBoolGoal and validates the COMPOSITION: it concludes
// exactly `goal` with hyps drawn only from the inputs (so a tactic could close
// the goal via IsStronger). Same placeholder-leaf / shape-only contract as
// checkDisj — soundness is the corpus binding suite's job.
func checkBoolGoal(t *testing.T, name string, hyps []Term, goal Term, wantOK bool) {
	t.Helper()
	w, ok := proveBoolGoal(hyps, goal, nil)
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
		if !slicesContainsAlpha(hyps, w.Hyp(i)) {
			t.Errorf("%s: stray hypothesis %v not among inputs", name, w.Hyp(i))
		}
	}
}

func slicesContainsAlpha(hs []Term, h Term) bool {
	for _, x := range hs {
		if x.AlphaEquals(h) {
			return true
		}
	}
	return false
}

// proveBoolGoal closes a boolean combination of comparison atoms that the atom
// decider and binary-disj leaf cannot crack — by case-splitting on the atoms and
// collapsing each branch. These are exactly the shapes nat.go (binary) and
// arithDecideLeaf (single atom) leave open.
func TestProveBoolGoal(t *testing.T) {
	a, b, c, d := numVar("a"), numVar("b"), numVar("c"), numVar("d")

	// ⇒ nested inside ∨ (valid via transitivity): (a≤b ⇒ a≤c) ∨ (c<b).
	checkBoolGoal(t, "(a≤b⇒a≤c) ∨ (c<b)", nil,
		or(imply(le(a, b), le(a, c)), lt(c, b)), true)
	// 3-way (nested) trichotomy: (a<b) ∨ ((a=b) ∨ (b<a)).
	checkBoolGoal(t, "(a<b) ∨ (a=b) ∨ (b<a)", nil,
		or(lt(a, b), or(eqT(a, b), lt(b, a))), true)
	// ⇒ with a conjunctive antecedent and an additive conclusion.
	checkBoolGoal(t, "(a≤b ∧ c≤d) ⇒ a+c≤b+d", nil,
		imply(prop.And(le(a, b), le(c, d)), le(plus(a, c), plus(b, d))), true)
	// ⇒ to a disjunctive consequent: (a≤b) ⇒ ((a<b) ∨ (a=b)).
	checkBoolGoal(t, "(a≤b) ⇒ ((a<b) ∨ (a=b))", nil,
		imply(le(a, b), or(lt(a, b), eqT(a, b))), true)
	// Hyp-driven: {a≤b, b≤c} ⊢ (a≤c) ∨ (c<a) — the left disjunct follows.
	checkBoolGoal(t, "{a≤b,b≤c} ⊢ (a≤c) ∨ (c<a)", []Term{le(a, b), le(b, c)},
		or(le(a, c), lt(c, a)), true)
	// `⇔` between COMPOUND boolean combinations (arithIffLeaf only does single-
	// comparison iffs): antisymmetry `(a≤b ∧ b≤a) ⇔ (a=b)`, and a `⇔` to a ∨.
	checkBoolGoal(t, "(a≤b ∧ b≤a) ⇔ (a=b)", nil,
		eqT(prop.And(le(a, b), le(b, a)), eqT(a, b)), true)
	checkBoolGoal(t, "(a≤b) ⇔ ((a<b) ∨ (a=b))", nil,
		eqT(le(a, b), or(lt(a, b), eqT(a, b))), true)

	// NOT valid — a feasible countermodel exists, so the split runs out of
	// productive branches and declines (never falsely closes).
	checkBoolGoal(t, "(a<b) ∨ (a=b)  [invalid]", nil, or(lt(a, b), eqT(a, b)), false)
	checkBoolGoal(t, "(a≤b) ⇒ (b<a)  [invalid]", nil, imply(le(a, b), lt(b, a)), false)
	checkBoolGoal(t, "(a≤b) ⇔ (a=b)  [invalid]", nil, eqT(le(a, b), eqT(a, b)), false)
}

// End-to-end through the deep rewrite: a contingent boolean over comparisons
// that no single atom decides reduces to ⊤ via arithBoolLeaf, while an invalid
// one is left untouched (no false ⊤).
func TestArithDecideBoolGoal(t *testing.T) {
	a, b, c := numVar("a"), numVar("b"), numVar("c")

	valid := or(imply(le(a, b), le(a, c)), lt(c, b)) // (a≤b⇒a≤c) ∨ (c<b)
	w := ArithDecide(valid)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("ArithDecide((a≤b⇒a≤c)∨(c<b)) = %v; want reduction to ⊤", w)
	}
	if !prop.Lhs(w).AlphaEquals(valid) {
		t.Errorf("ArithDecide bool goal: Lhs = %v, want %v", prop.Lhs(w), valid)
	}

	// Invalid: must NOT decide to ⊤ (declining / leaving it is the sound result).
	invalid := or(lt(a, b), eqT(a, b)) // (a<b) ∨ (a=b)
	if w := ArithDecide(invalid); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("ArithDecide((a<b)∨(a=b)) falsely reduced an invalid goal to ⊤")
	}

	// `⇔` between compound boolean combinations (the arithBoolLeaf `⇔` head):
	// antisymmetry `(a≤b ∧ b≤a) ⇔ (a=b)` reduces to ⊤; a num `=` is untouched
	// here (it is a comparison atom for arithDecideLeaf, not an iff).
	antisym := eqT(prop.And(le(a, b), le(b, a)), eqT(a, b))
	if w := ArithDecide(antisym); w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("ArithDecide((a≤b∧b≤a)⇔(a=b)) = %v; want reduction to ⊤", w)
	}
}

// TestSplitCandidates_BinderFree pins the binder-free candidate walks behind
// the num case splits (collectSplitCandidates / comparisonAtomsOf): a monus
// or comparison atom under an enclosing ∀ is no candidate; the same shape
// free is.
func TestSplitCandidates_BinderFree(t *testing.T) {
	x, a, b := numVar("x"), numVar("a"), numVar("b")
	bound := ext.ForAll(x)(le(minus(x, a), x)) // ∀x. x − a ≤ x
	if got := collectSplitCandidates([]Term{bound, le(a, b)}); len(got) != 0 {
		t.Errorf("x − a under ∀x collected: %v", got)
	}
	if got := collectSplitCandidates([]Term{bound, le(minus(a, b), a)}); len(got) != 1 || !got[0].AlphaEquals(minus(a, b)) {
		t.Errorf("free a − b not the candidate: %v", got)
	}
	if got := comparisonAtomsOf(and(bound, le(a, b))); len(got) != 1 || !got[0].AlphaEquals(le(a, b)) {
		t.Errorf("comparison atoms under ∀x collected: %v", got)
	}
}
