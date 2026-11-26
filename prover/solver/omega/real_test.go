package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

func TestRealArithDecide_Identities(t *testing.T) {
	cases := []struct {
		name, in, want string
	}{
		{"x+&0 → x", "x + &0", "x"},
		{"&0+x → x", "&0 + x", "x"},
		{"x*&0 → &0", "x * &0", "&0"},
		{"&0*x → &0", "&0 * x", "&0"},
		{"x*&1 → x", "x * &1", "x"},
		{"&1*x → x", "&1 * x", "x"},
		// nested / fixpoint
		{"(x+&0)+&0 → x", "(x + &0) + &0", "x"},
		{"x*&1+&0 → x", "x * &1 + &0", "x"},
		{"(x*&1)*(y+&0) → x*y", "(x * &1) * (y + &0)", "x * y"},
		// numeral folding through the of_num bridge
		{"&2+&3 → &5", "&2 + &3", "&5"},
		{"&2*&3 → &6", "&2 * &3", "&6"},
		{"x + (&2+&3) → x + &5", "x + (&2 + &3)", "x + &5"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			in := rr(tc.in)
			w := RealArithDecide(in)
			if w == nil {
				t.Fatalf("RealArithDecide(%q) = nil, want a rewrite", tc.in)
			}
			if !prop.Lhs(w).AlphaEquals(in) {
				t.Errorf("Lhs = %v, want %v", prop.Lhs(w), in)
			}
			if want := rr(tc.want); !prop.Rhs(w).AlphaEquals(want) {
				t.Errorf("Rhs = %v, want %v", prop.Rhs(w), want)
			}
		})
	}
}

// An already-reduced term yields no rewrite, and the rewrite does NOT collect
// or expand (x+y stays x+y — that is RealRingProve's job, not the simp leaf's).
func TestRealArithDecide_DeclinesAndNeverGrows(t *testing.T) {
	for _, s := range []string{"x", "x + y", "x * y", "&5", "x + &5"} {
		if w := RealArithDecide(rr(s)); w != nil {
			t.Errorf("RealArithDecide(%q) = %v, want nil (no conservative simplification)", s, prop.Rhs(w))
		}
	}
}

func TestRealArithDecideValidToTrue(t *testing.T) {
	for _, s := range []string{"&2 < &3", "&3 <= &3", "&4 > &1", "&2 >= &2", "&4 = &4"} {
		t.Run(s, func(t *testing.T) {
			in := rb(s)
			w := RealArithDecide(in)
			if w == nil {
				t.Fatalf("RealArithDecide(%q) = nil, want ⊤", s)
			}
			if !prop.Rhs(w).AlphaEquals(prop.T) {
				t.Errorf("Rhs = %v, want ⊤", prop.Rhs(w))
			}
		})
	}
}

func TestRealArithDecideFalseToBottom(t *testing.T) {
	for _, s := range []string{"&3 < &2", "&3 < &3", "&4 <= &1", "&3 = &4", "&1 > &2"} {
		t.Run(s, func(t *testing.T) {
			w := RealArithDecide(rb(s))
			if w == nil {
				t.Fatalf("RealArithDecide(%q) = nil, want ⊥", s)
			}
			if !prop.Rhs(w).AlphaEquals(prop.F) {
				t.Errorf("Rhs = %v, want ⊥", prop.Rhs(w))
			}
		})
	}
}

// A buried comparison atom (under ¬) is decided in place; BoolRewrite collapses
// ¬⊤ → ⊥ in the same fixpoint pass.
func TestRealArithDecideBuriedAtom(t *testing.T) {
	in := rb("~(x < x + &1)") // x < x+&1 is universally true ⇒ ¬ collapses to ⊥
	w := RealArithDecide(in)
	if w == nil {
		t.Fatal("RealArithDecide(~(x<x+&1)) = nil, want decided + ¬-collapsed")
	}
	if !prop.Rhs(w).AlphaEquals(prop.F) {
		t.Errorf("Rhs = %v, want ⊥", prop.Rhs(w))
	}
}

// Hyp-free decline of a contingent atom; the hyp-aware entry decides it and the
// resulting equality carries the used hyp.
func TestRealArithDecideHypAware(t *testing.T) {
	atom := rb("x < y + &1") // contingent alone; follows from x ≤ y
	if w := RealArithDecide(atom); w != nil {
		t.Fatalf("hyp-free RealArithDecide(x<y+&1) = %v, want nil (contingent)", prop.Rhs(w))
	}
	hyp := rb("x <= y")
	w := RealArithDecideWithHyps([]Term{hyp})(atom)
	if w == nil {
		t.Fatal("RealArithDecideWithHyps([x≤y])(x<y+&1) = nil, want ⊤")
	}
	if !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("Rhs = %v, want ⊤", prop.Rhs(w))
	}
	if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(hyp) {
		t.Errorf("decided equality must carry the used hyp x≤y, got %d hyps", w.NumHyps())
	}
}

// Ring equalities fold to ⊤ in place via RealRingProve — the same decider the
// closer uses, reached buried inside the deep rewrite.
func TestRealArithDecideRingFoldedIn(t *testing.T) {
	for _, s := range []string{"x + y = y + x", "&2 * (x + y) = &2 * x + &2 * y", "x + x = &2 * x"} {
		t.Run(s, func(t *testing.T) {
			in := rb(s)
			w := RealArithDecide(in)
			if w == nil {
				t.Fatalf("RealArithDecide(%q) = nil, want ⊤ via ring", s)
			}
			if !prop.Rhs(w).AlphaEquals(prop.T) {
				t.Errorf("Rhs = %v, want ⊤", prop.Rhs(w))
			}
		})
	}
}

// The cascade-across-rules headline (the ℝ twin of TestArithDecide_CondCascade):
// x + Cond(x=x, &0, &1) → x. None of the leaves fire at the top; recurse into
// Cond, decide x=x→⊤ (RealRingProve), trivialCondRewrite collapses
// Cond(⊤,&0,&1)→&0, then the identity leaf reduces x+&0→x — all in one
// deep+fixpoint pass.
func TestRealArithDecide_CondCascade(t *testing.T) {
	x := rr("x")
	z, o := realLit(0), realLit(1)
	// x + Cond(x=x, &0, &1) — built manually because the test DSL doesn't carry COND.
	condTrue := ext.Cond(eqT(x, x), z, o).Core()
	in1 := realPlusT(x, condTrue)
	w := RealArithDecide(in1)
	if w == nil {
		t.Fatal("RealArithDecide(x + Cond(x=x, &0, &1)) = nil, want `x`")
	}
	if !prop.Rhs(w).AlphaEquals(x) {
		t.Errorf("Rhs = %v, want `x`", prop.Rhs(w))
	}

	// x + Cond(x=x+&1, &0, &1) — false branch picks &1; identity leaves x+&1 alone.
	condFalse := ext.Cond(eqT(x, realPlusT(x, o)), z, o).Core()
	in2 := realPlusT(x, condFalse)
	w2 := RealArithDecide(in2)
	if w2 == nil {
		t.Fatal("RealArithDecide(x + Cond(x=x+&1, &0, &1)) = nil, want `x + &1`")
	}
	if want := realPlusT(x, o); !prop.Rhs(w2).AlphaEquals(want) {
		t.Errorf("Rhs = %v, want `x + &1`", prop.Rhs(w2))
	}
}

// TestRealProveBoolGoal mirrors TestProveBoolGoal (nat_test.go) case-for-case
// over ℝ: the real twin closes the same shapes and declines the same
// invalid ones.
func TestRealProveBoolGoal(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	x, y, z, d := realVar("x"), realVar("y"), realVar("z"), realVar("d")
	le, lt, plus := realLeT, realLtT, realPlusT

	checkRealBoolGoal(t, "(x≤y⇒x≤z) ∨ (z<y)", nil,
		or(imply(le(x, y), le(x, z)), lt(z, y)), true)
	checkRealBoolGoal(t, "(x<y) ∨ (x=y) ∨ (y<x)", nil,
		or(lt(x, y), or(eqT(x, y), lt(y, x))), true)
	checkRealBoolGoal(t, "(x≤y ∧ z≤d) ⇒ x+z≤y+d", nil,
		imply(prop.And(le(x, y), le(z, d)), le(plus(x, z), plus(y, d))), true)
	checkRealBoolGoal(t, "(x≤y) ⇒ ((x<y) ∨ (x=y))", nil,
		imply(le(x, y), or(lt(x, y), eqT(x, y))), true)
	checkRealBoolGoal(t, "{x≤y,y≤z} ⊢ (x≤z) ∨ (z<x)", []Term{le(x, y), le(y, z)},
		or(le(x, z), lt(z, x)), true)
	checkRealBoolGoal(t, "(x≤y ∧ y≤x) ⇔ (x=y)", nil,
		eqT(prop.And(le(x, y), le(y, x)), eqT(x, y)), true)
	checkRealBoolGoal(t, "(x≤y) ⇔ ((x<y) ∨ (x=y))", nil,
		eqT(le(x, y), or(lt(x, y), eqT(x, y))), true)

	// NOT valid — the split runs out of productive branches and declines.
	checkRealBoolGoal(t, "(x<y) ∨ (x=y)  [invalid]", nil, or(lt(x, y), eqT(x, y)), false)
	checkRealBoolGoal(t, "(x≤y) ⇒ (y<x)  [invalid]", nil, imply(le(x, y), lt(y, x)), false)
	checkRealBoolGoal(t, "(x≤y) ⇔ (x=y)  [invalid]", nil, eqT(le(x, y), eqT(x, y)), false)
}

// Real formula-level bool-split tests — the ℝ twin of nat_test.go's
// TestArithDecideBoolGoal. The real bool leaf is GATED on a real bundle being
// installed, so each test flips the gate with an (empty) real bundle; the leaves
// then run on placeholders, pinning the split/ByCases/collapse PLUMBING (a goal
// no single atom decides reduces to ⊤ via case analysis; an invalid one is left
// untouched). Soundness rides on the bundle swap, as elsewhere in the real layer.

func TestRealArithDecideBoolGoal(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{}) // flip the real gate (placeholder leaves)
	t.Cleanup(func() { SetRealLemmaBundle(nil) })

	x, y, z := realVar("x"), realVar("y"), realVar("z")

	// Valid, no atom decides alone: (x≤y ⇒ x≤z) ∨ (z<y).
	valid := or(imply(realLeT(x, y), realLeT(x, z)), realLtT(z, y))
	w := ArithDecide(valid)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("ArithDecide((x≤y⇒x≤z)∨(z<y)) = %v; want reduction to ⊤", w)
	}
	if !prop.Lhs(w).AlphaEquals(valid) {
		t.Errorf("real bool goal: Lhs = %v, want %v", prop.Lhs(w), valid)
	}

	// Real trichotomy (nested): (x<y) ∨ ((x=y) ∨ (y<x)) → ⊤.
	trich := or(realLtT(x, y), or(eqT(x, y), realLtT(y, x)))
	if w := ArithDecide(trich); w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("ArithDecide(real trichotomy) = %v; want ⊤", w)
	}

	// Invalid: (x<y) ∨ (x=y) must NOT decide to ⊤.
	invalid := or(realLtT(x, y), eqT(x, y))
	if w := ArithDecide(invalid); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("ArithDecide((x<y)∨(x=y)) falsely reduced an invalid goal to ⊤")
	}

	// `⇔` between compound boolean combinations: real antisymmetry
	// (x≤y ∧ y≤x) ⇔ (x=y) → ⊤ (the realArithBoolLeaf `⇔` head).
	antisym := eqT(prop.And(realLeT(x, y), realLeT(y, x)), eqT(x, y))
	if w := ArithDecide(antisym); w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("ArithDecide((x≤y∧y≤x)⇔(x=y)) = %v; want ⊤", w)
	}
}

// Gate off: with no real bundle, a contingent real boolean is left untouched
// (the real bool leaf is absent from the leaf set).
func TestRealArithBoolGoalGatedOff(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	valid := or(imply(realLeT(x, y), realLeT(x, z)), realLtT(z, y))
	if w := ArithDecide(valid); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("gate off: ArithDecide(real bool goal) reduced to ⊤; want untouched")
	}
}

func TestRealNormNumEval(t *testing.T) {
	runRealNormNumCases(t)
}

func TestRealNormNumDeclines(t *testing.T) {
	// A real VARIABLE side (not real_of_num-applied) declines.
	if _, ok := realNormNatAdd(rr("x"), rr("&4")); ok {
		t.Error("realNormNatAdd(x, &4): ok=true, want decline")
	}
	if _, ok := realNormNatLt(rr("&4"), rr("x")); ok {
		t.Error("realNormNatLt(&4, x): ok=true, want decline")
	}
	// `&x` with a num-VARIABLE argument is real_of_num-shaped but not a literal:
	// the num evaluator gates it out (no bit-tree), still a decline.
	coercedVar := realOfNumT(numVar("k"))
	if _, ok := realNormNatMul(coercedVar, rr("&4")); ok {
		t.Error("realNormNatMul(&k, &4): ok=true, want decline")
	}
}

// TestRealBundleOfNumWiring installs the OfNum* fields in their normal-form
// orientation (`&(m+n) = &m + &n` and `(m<n) ⇔ (&m<&n)`, i.e. the reverse of
// the bridge direction) and re-runs the evaluator cases: macroEq
// must instantiate and auto-flip each bridge. The fields are built with
// prop.Assume rather than TestThm, so the ∀-statement rides along as a marker
// hypothesis — its presence on the result PROVES the leaf bound the bundle field
// instead of silently degrading to a placeholder (which a conclusion-only check
// cannot distinguish).
func TestRealBundleOfNumWiring(t *testing.T) {
	m, n := numVar("m"), numVar("n")
	ForAll := ext.ForAll
	ofNumAdd := ForAll(m, n)(eqT(realOfNumT(plus(m, n)), realPlusT(realOfNumT(m), realOfNumT(n))))
	ofNumMul := ForAll(m, n)(eqT(realOfNumT(star(m, n)), realStarT(realOfNumT(m), realOfNumT(n))))
	ofNumLessThan := ForAll(m, n)(eqT(lt(m, n), realLtT(realOfNumT(m), realOfNumT(n))))
	ofNumLessEq := ForAll(m, n)(eqT(le(m, n), realLeT(realOfNumT(m), realOfNumT(n))))
	ofNumEq := ForAll(m, n)(eqT(eqT(m, n), eqT(realOfNumT(m), realOfNumT(n))))
	SetRealLemmaBundle(&RealLemmaBundle{
		OfNumAdd:      prop.Assume(ofNumAdd),
		OfNumMul:      prop.Assume(ofNumMul),
		OfNumLessThan: prop.Assume(ofNumLessThan),
		OfNumLessEq:   prop.Assume(ofNumLessEq),
		OfNumEq:       prop.Assume(ofNumEq),
	})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })

	// Same conclusions as placeholder mode…
	runRealNormNumCases(t)

	// …and each result carries exactly its bridge's marker hypothesis.
	markers := []struct {
		name   string
		run    func() (*prop.PropWrapper, bool)
		marker Term
	}{
		{"add", func() (*prop.PropWrapper, bool) { return realNormNatAdd(rr("&3"), rr("&4")) }, ofNumAdd},
		{"mul", func() (*prop.PropWrapper, bool) { return realNormNatMul(rr("&3"), rr("&4")) }, ofNumMul},
		{"lt", func() (*prop.PropWrapper, bool) { return realNormNatLt(rr("&3"), rr("&4")) }, ofNumLessThan},
		{"le", func() (*prop.PropWrapper, bool) { return realNormNatLe(rr("&3"), rr("&3")) }, ofNumLessEq},
		{"eq", func() (*prop.PropWrapper, bool) { return realNormNatEq(rr("&3"), rr("&4")) }, ofNumEq},
	}
	for _, c := range markers {
		w, ok := c.run()
		if !ok {
			t.Fatalf("%s: ok=false under bundle", c.name)
		}
		if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(c.marker) {
			t.Errorf("%s: bundle field not bound (no marker hyp) — leaf degraded to placeholder", c.name)
		}
	}
}

// Scale-leaf tests — the scaling lemma's side condition: realLeScale /
// realLtScale must instantiate the bundle's curried LessEqMulLeft / LessThanMulLeft
// at the concrete multiplier and discharge the `&0 ⋈ &c` side condition through
// the norm_num bridge — not absorb it into a placeholder.

// realVar builds a real-typed variable (the rr scope helper types identifiers
// real already; this is for native construction next to numVar).
func realVar(name string) Term { return ext.Var(ext.TermName(name), rr("x").Type()) }

func TestRealScalePlaceholder(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	wantLe := imply(realLeT(x, y), realLeT(realMonoTerm(integerOf(3), x), realMonoTerm(integerOf(3), y)))
	if w := realLeScale(integerOf(3), x, y); !w.Conclusion().AlphaEquals(wantLe) {
		t.Errorf("realLeScale(3,x,y): got %v want %v", w.Conclusion(), wantLe)
	}
	wantLt := imply(realLtT(x, y), realLtT(realMonoTerm(integerOf(2), x), realMonoTerm(integerOf(2), y)))
	if w := realLtScale(integerOf(2), x, y); !w.Conclusion().AlphaEquals(wantLt) {
		t.Errorf("realLtScale(2,x,y): got %v want %v", w.Conclusion(), wantLt)
	}
}

// TestRealScaleBundleWiring: the bundle fields hold the curried forms (binder
// order [c, a, b]); built with prop.Assume so the ∀-statement rides along as a
// marker hypothesis proving the leaf BOUND the field (the side-condition
// discharge itself runs on the placeholder-backed norm_num bridge here — its
// TestThm carries no hyps, so the marker is the only hypothesis).
func TestRealScaleBundleWiring(t *testing.T) {
	c, a, b := realVar("c"), realVar("a"), realVar("b")
	ForAll := ext.ForAll
	leLmul := ForAll(c, a, b)(imply(realLeT(realLit(0), c),
		imply(realLeT(a, b), realLeT(realStarT(c, a), realStarT(c, b)))))
	ltLmul := ForAll(c, a, b)(imply(realLtT(realLit(0), c),
		imply(realLtT(a, b), realLtT(realStarT(c, a), realStarT(c, b)))))
	SetRealLemmaBundle(&RealLemmaBundle{
		LessEqMulLeft:   prop.Assume(leLmul),
		LessThanMulLeft: prop.Assume(ltLmul),
	})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })

	x, y := realVar("x"), realVar("y")
	cases := []struct {
		name   string
		run    func() *prop.PropWrapper
		want   Term
		marker Term
	}{
		{"leScale", func() *prop.PropWrapper { return realLeScale(integerOf(3), x, y) },
			imply(realLeT(x, y), realLeT(realMonoTerm(integerOf(3), x), realMonoTerm(integerOf(3), y))), leLmul},
		{"ltScale", func() *prop.PropWrapper { return realLtScale(integerOf(2), x, y) },
			imply(realLtT(x, y), realLtT(realMonoTerm(integerOf(2), x), realMonoTerm(integerOf(2), y))), ltLmul},
	}
	for _, tc := range cases {
		w := tc.run()
		if !w.Conclusion().AlphaEquals(tc.want) {
			t.Errorf("%s: got %v want %v", tc.name, w.Conclusion(), tc.want)
		}
		if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(tc.marker) {
			t.Errorf("%s: bundle field not bound (no marker hyp) — leaf degraded to placeholder", tc.name)
		}
	}
}

// TestRealLinProveScaled: an end-to-end forward proof whose Farkas certificate
// carries a multiplier ≥ 2, forcing the replay through the scale leaf (the
// existing TestRealLinProve cases all have λ=1 rows). Placeholder mode — the
// composition (instantiate → side-discharge → sum → cancel → close) is what is
// pinned here.
func TestRealLinProveScaled(t *testing.T) {
	checkRealProve(t, "scaled", rb("&2 * x <= &2 * y"), rb("x <= y"))
}

// Real case-split engine (real_ops.go) — the ℝ twin of the int case split
// (int_test.go's TestIntAbs/MaxMin/Sgn/RawCond/HypSplit). real_abs / real_max /
// real_min / real_sgn / raw COND eliminated on excluded middle of their guard, and
// the ≠/∨/⇒/product-zero hypothesis splits. Placeholder-backed (the ℝ defs +
// order leaves are fabricator stand-ins, incl. the LessThanTrichotomy the ≠ split
// rides), so the kernel composition is what is exercised here.

// realDecidesTrue decides goal under hyps and asserts it collapses to ⊤.
func realDecidesTrue(t *testing.T, name string, goal Term, hyps ...Term) {
	t.Helper()
	w := RealArithDecideWithHyps(hyps)(goal)
	if w == nil {
		t.Errorf("%s: RealArithDecideWithHyps(%v)(%v) = nil, want ⊤", name, hyps, goal)
		return
	}
	if !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("%s: → %v, want ⊤", name, prop.Rhs(w))
	}
}

func TestRealAbs_ClosesGoals(t *testing.T) {
	x := realVar("x")
	abs := realAbsT(x)
	// |x| ≥ 0 : x≥0 branch |x|=x≥0; x<0 branch |x|=−x≥0.
	realDecidesTrue(t, "0≤|x|", realLeT(realLit(0), abs))
	// x ≤ |x| : x≥0 branch x≤x; x<0 branch x<0≤−x.
	realDecidesTrue(t, "x≤|x|", realLeT(x, abs))
	// −x ≤ |x| : x≥0 branch −x≤0≤x; x<0 branch −x≤−x.
	realDecidesTrue(t, "−x≤|x|", realLeT(realNegT(x), abs))
}

func TestRealMaxMin_ClosesGoals(t *testing.T) {
	a, b := realVar("a"), realVar("b")
	realDecidesTrue(t, "a≤max", realLeT(a, realMaxT(a, b)))
	realDecidesTrue(t, "b≤max", realLeT(b, realMaxT(a, b)))
	realDecidesTrue(t, "min≤a", realLeT(realMinT(a, b), a))
	realDecidesTrue(t, "min≤b", realLeT(realMinT(a, b), b))
	// both atoms split in one decision.
	realDecidesTrue(t, "min≤max", realLeT(realMinT(a, b), realMaxT(a, b)))
}

func TestRealSgn_ClosesGoals(t *testing.T) {
	x := realVar("x")
	sgn := realSgnT(x)
	// −&1 ≤ sgn x ≤ &1 (the three-way split, inner COND via the raw-COND kind).
	realDecidesTrue(t, "sgn≤1", realLeT(sgn, realLit(1)))
	realDecidesTrue(t, "−1≤sgn", realLeT(realNegT(realLit(1)), sgn))
}

func TestRealRawCond_ClosesGoals(t *testing.T) {
	x := realVar("x")
	// &0 ≤ COND(&0 ≤ x, x, &1): both arms nonneg.
	c := ext.Cond(realLeT(realLit(0), x), x, realLit(1))
	realDecidesTrue(t, "0≤cond", realLeT(realLit(0), c))
}

func TestRealHypSplit(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	// ≠ hyp: x ≠ y, x ≤ y ⊢ x < y  (trichotomy: the y<x branch contradicts x≤y).
	realDecidesTrue(t, "neq-hyp", realLtT(x, y), not(eqT(x, y)), realLeT(x, y))
	// ∨ hyp: (x ≤ &0 ∨ &2 ≤ x) ⊢ x ≠ &1.
	realDecidesTrue(t, "or-hyp", not(eqT(x, realLit(1))),
		or(realLeT(x, realLit(0)), realLeT(realLit(2), x)))
	// ⇒ hyp: (x ≤ &1 ⇒ &2 ≤ x) ⊢ &1 < x  (¬p ⇒ x>1; q ⇒ x≥2 ⇒ x>1).
	realDecidesTrue(t, "imp-hyp", realLtT(realLit(1), x),
		imply(realLeT(x, realLit(1)), realLeT(realLit(2), x)))
}

func TestRealMulEqZeroHypSplit(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	z := realLit(0)
	xy := realStarT(x, y)
	// distinct factors with one nonzero: x·y=&0, x≠&0 ⊢ y=&0 (the splittable hyp).
	realDecidesTrue(t, "x·y=0,x≠0⊢y=0", eqT(y, z), eqT(xy, z), not(eqT(x, z)))
}

// TestRealMulEqZeroBoolGoal: the bare disjunction goal `x·y=&0 ⊢ x=&0 ∨ y=&0` — a
// boolean combination over comparison atoms, so it goes through the bool-split
// (realArithBoolLeaf) composed with the product-zero hyp split. The bool-split is
// wired into the UNIFIED ArithDecideWithHyps gated on a real bundle, so (like
// TestRealArithDecideBoolGoal) it installs a placeholder bundle to flip the gate.
func TestRealMulEqZeroBoolGoal(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{}) // flip the real gate (placeholder leaves)
	t.Cleanup(func() { SetRealLemmaBundle(nil) })

	x, y := realVar("x"), realVar("y")
	z := realLit(0)
	goal := or(eqT(x, z), eqT(y, z))
	w := ArithDecideWithHyps([]Term{eqT(realStarT(x, y), z)})(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("ArithDecideWithHyps([x·y=0])(x=0∨y=0) = %v, want ⊤", w)
	}
}

// Monotone scaling / sign-of-product / integral domain over ℝ (real_ops.go) —
// the ℝ twin of TestIntMonotone_* / TestIntMulEqZero. The linear core atomizes the
// products; these handlers apply LessEqMulLeft / LessThanMulLeft / LessEqMul /
// MulPos / MulEqZero / LessEqTrans with a symbolic multiplier.
// Placeholder-backed (MulPos / NegNonnegativeIffNonpositive/NegPositiveIffNegative / LessThanTrichotomy are fabricator
// stand-ins); the composition (the lemma application + commute + flip) is real
// kernel work, so green = the plumbing is sound.

func TestRealMonotone_Scaling(t *testing.T) {
	a, b, c := realVar("a"), realVar("b"), realVar("c")
	aLeB := realLeT(a, b)
	zeroLeC := realLeT(realLit(0), c)

	// left factor: a≤b ∧ &0≤c ⊢ c·a ≤ c·b.
	realDecidesTrue(t, "a≤b,0≤c⊢ca≤cb", realLeT(realStarT(c, a), realStarT(c, b)), aLeB, zeroLeC)
	// right factor (via commute): a≤b ∧ &0≤c ⊢ a·c ≤ b·c.
	realDecidesTrue(t, "a≤b,0≤c⊢ac≤bc", realLeT(realStarT(a, c), realStarT(b, c)), aLeB, zeroLeC)
	// strict: a<b ∧ &0<c ⊢ c·a < c·b.
	realDecidesTrue(t, "a<b,0<c⊢ca<cb", realLtT(realStarT(c, a), realStarT(c, b)),
		realLtT(a, b), realLtT(realLit(0), c))

	// sanity: WITHOUT `&0 ≤ c`, `c·a ≤ c·b` must NOT decide ⊤ (c could be negative).
	if w := RealArithDecideWithHyps([]Term{aLeB})(realLeT(realStarT(c, a), realStarT(c, b))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("c·a≤c·b without &0≤c must NOT decide ⊤")
	}
}

func TestRealMonotone_ProductNonneg(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	// &0≤x ∧ &0≤y ⊢ &0 ≤ x·y  (LessEqMul).
	realDecidesTrue(t, "0≤x,0≤y⊢0≤xy", realLeT(realLit(0), realStarT(x, y)),
		realLeT(realLit(0), x), realLeT(realLit(0), y))

	// sanity: WITHOUT the sign hyps, `&0 ≤ x·y` must NOT decide ⊤.
	if w := RealArithDecideWithHyps(nil)(realLeT(realLit(0), realStarT(x, y))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0≤x·y without sign hyps must NOT decide ⊤")
	}
}

func TestRealMonotone_SignOfProduct(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	xy := realStarT(x, y)
	z := realLit(0)

	// strict, both positive: &0<x ∧ &0<y ⊢ &0 < x·y  (MulPos).
	realDecidesTrue(t, "0<x,0<y⊢0<xy", realLtT(z, xy), realLtT(z, x), realLtT(z, y))
	// both negative → nonneg: x≤&0 ∧ y≤&0 ⊢ &0 ≤ x·y  (reduces to LessEqMul on (−x,−y)).
	realDecidesTrue(t, "x≤0,y≤0⊢0≤xy", realLeT(z, xy), realLeT(x, z), realLeT(y, z))
	// both negative → strict: x<&0 ∧ y<&0 ⊢ &0 < x·y.
	realDecidesTrue(t, "x<0,y<0⊢0<xy", realLtT(z, xy), realLtT(x, z), realLtT(y, z))
	// sign-mixed → nonpositive: x≤&0 ∧ &0≤y ⊢ x·y ≤ &0  (negate x, flip).
	realDecidesTrue(t, "x≤0,0≤y⊢xy≤0", realLeT(xy, z), realLeT(x, z), realLeT(z, y))
	// sign-mixed (other side): &0≤x ∧ y≤&0 ⊢ x·y ≤ &0  (negate y, flip).
	realDecidesTrue(t, "0≤x,y≤0⊢xy≤0", realLeT(xy, z), realLeT(z, x), realLeT(y, z))
	// sign-mixed strict: x<&0 ∧ &0<y ⊢ x·y < &0.
	realDecidesTrue(t, "x<0,0<y⊢xy<0", realLtT(xy, z), realLtT(x, z), realLtT(z, y))

	// sanity: x≤&0 ∧ &0≤y ⊢ &0 ≤ x·y is FALSE (x=−1,y=1 ⇒ xy=−1); must NOT decide ⊤.
	if w := RealArithDecideWithHyps([]Term{realLeT(x, z), realLeT(z, y)})(realLeT(z, xy)); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("x≤0,0≤y⊢0≤xy must NOT decide ⊤ (counterexample x=−1,y=1)")
	}
}

func TestRealMonotone_TwoSided(t *testing.T) {
	a, b, c, d := realVar("a"), realVar("b"), realVar("c"), realVar("d")
	z := realLit(0)
	// &0≤a ∧ a≤b ∧ &0≤c ∧ c≤d ⊢ a·c ≤ b·d  (derived via LessEqTrans).
	realDecidesTrue(t, "0≤a,a≤b,0≤c,c≤d⊢ac≤bd", realLeT(realStarT(a, c), realStarT(b, d)),
		realLeT(z, a), realLeT(a, b), realLeT(z, c), realLeT(c, d))

	// sanity: WITHOUT the lower bounds the handler must decline (a=−2,b=1,c=−2,d=1 ⇒
	// ac=4 > bd=1). Checked at the handler (the full decider would fall through).
	if _, ok := realProveProductMul2([]Term{realLeT(a, b), realLeT(c, d)}, a, c, b, d); ok {
		t.Errorf("a≤b,c≤d⊢ac≤bd without lower bounds must NOT prove via realProveProductMul2")
	}
}

func TestRealMulEqZero(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	z := realLit(0)
	xx, xy := realStarT(x, x), realStarT(x, y)

	// square collapse: x·x=&0 ⊢ x=&0 (the (p∨p)⇔p forward path).
	realDecidesTrue(t, "x·x=&0 ⊢ x=&0", eqT(x, z), eqT(xx, z))
	// distinct factors with one nonzero: x·y=&0, x≠&0 ⊢ y=&0 (the splittable hyp).
	// (The bare disjunction goal `x·y=&0 ⊢ x=&0 ∨ y=&0` is a bool-combination over
	// atoms — it needs the bool-split + a real bundle gate; see TestRealMulEqZeroBoolGoal.)
	realDecidesTrue(t, "x·y=&0,x≠&0 ⊢ y=&0", eqT(y, z), eqT(xy, z), not(eqT(x, z)))

	// strict square positivity: x≠&0 ⊢ &0 < x·x.
	realDecidesTrue(t, "x≠&0 ⊢ &0<x·x", realLtT(z, xx), not(eqT(x, z)))

	// sanity: WITHOUT `x≠&0`, `&0 < x·x` must NOT decide ⊤ (x=&0 ⇒ x·x=&0).
	if w := RealArithDecideWithHyps(nil)(realLtT(z, xx)); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0<x·x without x≠&0 must NOT decide ⊤")
	}
}

// No-hyp square nonnegativity (real_ops.go realProveSquareNonneg) — the ℝ twin
// of `int`'s Image square split, but a SINGLE lemma (SquareNonneg; ℝ needs no
// sign split). Placeholder-backed. realProveMonotone (needing factor-sign hyps)
// declines, so this is what closes `&0 ≤ x·x` with no hypothesis.
func TestRealSquareNonneg(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	z := realLit(0)
	// &0 ≤ x·x with no hyp.
	realDecidesTrue(t, "0≤x·x (no hyp)", realLeT(z, realStarT(x, x)))
	// &0 ≤ x pow 2 composes (pow-sign PowTwoNonneg, the pow form of the same fact).
	realDecidesTrue(t, "0≤x^2 (no hyp)", realLeT(z, realPowT(x, Numeral(2))))

	// sanity: `&0 ≤ x·y` (DISTINCT factors) is not a square and must NOT decide ⊤.
	if w := RealArithDecideWithHyps(nil)(realLeT(z, realStarT(x, y))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0≤x·y (distinct factors) must NOT decide ⊤")
	}
}

// Field layer (real_ops.go) — inverse cancellation + denominator clearing.
// Placeholder-backed (the field suite's leaves are fabricator stand-ins), so the
// composition (the iff modus-ponens + sign discharge + recurse) is what is
// exercised. ℝ-only — no int twin.

func TestRealField_Folds(t *testing.T) {
	x := realVar("x")
	// x/&1 → x (DivOne), inv &1 → &1 (InvOne) — hyp-free simp folds.
	realDecidesTrue(t, "x/&1=x", eqT(realDivT(x, realLit(1)), x))
	realDecidesTrue(t, "inv &1=&1", eqT(realInvT(realLit(1)), realLit(1)))
}

func TestRealField_Cancel(t *testing.T) {
	x := realVar("x")
	xNeq0 := not(eqT(x, realLit(0)))
	// inverse cancellation under x ≠ &0.
	realDecidesTrue(t, "x≠0⊢x·inv x=&1", eqT(realStarT(x, realInvT(x)), realLit(1)), xNeq0)
	realDecidesTrue(t, "x≠0⊢inv x·x=&1", eqT(realStarT(realInvT(x), x), realLit(1)), xNeq0)
	realDecidesTrue(t, "x≠0⊢x/x=&1", eqT(realDivT(x, x), realLit(1)), xNeq0)
	// the sign route to x ≠ &0: &0 < x ⊢ x·inv x = &1.
	realDecidesTrue(t, "0<x⊢x·inv x=&1", eqT(realStarT(x, realInvT(x)), realLit(1)), realLtT(realLit(0), x))

	// sanity: WITHOUT x ≠ &0, `x·inv x = &1` must NOT decide ⊤ (false at x=&0).
	if w := RealArithDecideWithHyps(nil)(eqT(realStarT(x, realInvT(x)), realLit(1))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("x·inv x = &1 without x≠&0 must NOT decide ⊤")
	}
}

func TestRealField_ClearLiteralDivisor(t *testing.T) {
	// Positive literal divisor: the sign 0<&2 is automatic (of_num bridge), and the
	// cleared atom evaluates through the real numeral simps.
	realDecidesTrue(t, "&6/&2=&3", eqT(realDivT(realLit(6), realLit(2)), realLit(3)))
	realDecidesTrue(t, "&4≤&8/&2", realLeT(realLit(4), realDivT(realLit(8), realLit(2))))
	realDecidesTrue(t, "&8/&2<&5", realLtT(realDivT(realLit(8), realLit(2)), realLit(5)))
}

func TestRealField_ClearPositiveDivisor(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	pos := realLtT(realLit(0), z)
	// right-division `x ≤ y/z` clears to `x·z ≤ y` (a hyp); 0<z from a hyp.
	realDecidesTrue(t, "0<z,x·z≤y⊢x≤y/z", realLeT(x, realDivT(y, z)), pos, realLeT(realStarT(x, z), y))
	realDecidesTrue(t, "0<z,x·z<y⊢x<y/z", realLtT(x, realDivT(y, z)), pos, realLtT(realStarT(x, z), y))
	realDecidesTrue(t, "0<z,y=x·z⊢x=y/z", eqT(x, realDivT(y, z)), pos, eqT(y, realStarT(x, z)))
	// left-division `x/z ≤ y` clears to `x ≤ y·z`.
	realDecidesTrue(t, "0<z,x≤y·z⊢x/z≤y", realLeT(realDivT(x, z), y), pos, realLeT(x, realStarT(y, z)))
}

func TestRealField_ClearNegativeDivisor(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	neg := realLtT(z, realLit(0))
	// right-division `x ≤ y/z` with z<&0 clears (FLIPPED) to `y ≤ x·z`.
	realDecidesTrue(t, "z<0,y≤x·z⊢x≤y/z", realLeT(x, realDivT(y, z)), neg, realLeT(y, realStarT(x, z)))
	// equality does NOT flip: z<&0, y=x·z ⊢ x=y/z.
	realDecidesTrue(t, "z<0,y=x·z⊢x=y/z", eqT(x, realDivT(y, z)), neg, eqT(y, realStarT(x, z)))
}

func TestRealField_ClearUnknownSign(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	zNeq0 := not(eqT(z, realLit(0)))
	// Equality is valid for either sign of z (no flip), so the unknown-sign split
	// (z<&0 ∨ &0<z, from z≠&0) closes both branches: z≠&0, y=x·z ⊢ x=y/z.
	realDecidesTrue(t, "z≠0,y=x·z⊢x=y/z", eqT(x, realDivT(y, z)), zNeq0, eqT(y, realStarT(x, z)))
}

// real_pow literal-exponent unfold (realPowUnfold) — the real twin of TestIntPow_*.
// Placeholder-backed (PowZero / PowSuc are fabricator stand-ins); the composition (the recursion unfold +
// suc congruence) is real kernel work.

func TestRealPow_AutoSimp(t *testing.T) {
	x := realVar("x")
	// c ≤ 1 auto-folds inside the decider: real_pow x 0 → &1, real_pow x 1 → x.
	realDecidesTrue(t, "pow0", eqT(realPowT(x, Numeral(0)), realLit(1)))
	realDecidesTrue(t, "pow1", eqT(realPowT(x, Numeral(1)), x))
}

func TestRealPow_Expand(t *testing.T) {
	x := realVar("x")
	// Variable base: the unfold is a valid kernel equality with LHS = real_pow x 2.
	w := ExpandRealPowRewrite()(realPowT(x, Numeral(2)))
	if w == nil || !prop.Lhs(w).AlphaEquals(realPowT(x, Numeral(2))) {
		t.Fatalf("ExpandRealPowRewrite(real_pow x 2) = %v, want a real_pow x 2 = … equality", w)
	}
	// `real_pow x c = <matching product chain>` CLOSES for a variable base via
	// expand-then-decide: the `&1`-fold + reflexivity (the chain RHS is exactly the
	// unfold's shape, so no nonlinear ring is needed).
	for _, c := range []struct {
		exp uint64
		rhs Term
	}{{2, realStarT(x, realStarT(x, realLit(1)))}, {3, realStarT(x, realStarT(x, realStarT(x, realLit(1))))}} {
		g := eqT(realPowT(x, Numeral(c.exp)), c.rhs)
		ew := ExpandRealPowRewrite()(g)
		if ew == nil {
			t.Fatalf("expand(real_pow x %d = …) = nil", c.exp)
		}
		dec := RealArithDecide(prop.Rhs(ew))
		if dec == nil || !prop.Rhs(dec).AlphaEquals(prop.T) {
			t.Errorf("real_pow x %d = (matching chain) did not decide ⊤ (got %v)", c.exp, dec)
		}
	}
	// Concrete base: expand-then-decide evaluates real_pow &3 2 to &9, real_pow &2 3
	// to &8 — the literal product chain folds through the real numeral simps.
	for _, c := range []struct {
		base, exp, val uint64
	}{{3, 2, 9}, {2, 3, 8}, {5, 0, 1}} {
		g := eqT(realPowT(realLit(c.base), Numeral(c.exp)), realLit(c.val))
		ew := ExpandRealPowRewrite()(g) // ⊢ g = g'  (the real_pow atom unfolded)
		if ew == nil {
			t.Fatalf("expand(&%d pow %d) = nil", c.base, c.exp)
		}
		dec := RealArithDecide(prop.Rhs(ew))
		if dec == nil || !prop.Rhs(dec).AlphaEquals(prop.T) {
			t.Errorf("&%d pow %d = &%d did not decide ⊤ (got %v)", c.base, c.exp, c.val, dec)
		}
	}
}

// real_pow sign (realProvePowSign) — the sign-known fragment.
// Placeholder-backed (PowTwoNonneg / PowNonneg / PowPos are fabricator stand-ins).
func TestRealPowSign(t *testing.T) {
	x := realVar("x")
	z := realLit(0)
	n := numVar("n")

	// &0 ≤ x pow 2 with NO hyp (PowTwoNonneg — an even square is nonneg).
	realDecidesTrue(t, "0≤x^2 (no hyp)", realLeT(z, realPowT(x, Numeral(2))))
	// &0 ≤ x ⊢ &0 ≤ x pow n  (symbolic exponent, PowNonneg).
	realDecidesTrue(t, "0≤x⊢0≤x^n", realLeT(z, realPowT(x, n)), realLeT(z, x))
	// &0 ≤ x ⊢ &0 ≤ x pow 3  (literal exponent via PowNonneg).
	realDecidesTrue(t, "0≤x⊢0≤x^3", realLeT(z, realPowT(x, Numeral(3))), realLeT(z, x))
	// &0 < x ⊢ &0 < x pow n  (PowPos).
	realDecidesTrue(t, "0<x⊢0<x^n", realLtT(z, realPowT(x, n)), realLtT(z, x))

	// sanity: &0 ≤ x pow 3 with NO hyp must NOT decide ⊤ (x=−1 ⇒ x³=−1 < 0).
	if w := RealArithDecideWithHyps(nil)(realLeT(z, realPowT(x, Numeral(3)))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0≤x^3 without &0≤x must NOT decide ⊤ (counterexample x=−1)")
	}
	// sanity: &0 < x pow 2 with NO hyp must NOT decide ⊤ (x=&0 ⇒ x²=0, not >0).
	if w := RealArithDecideWithHyps(nil)(realLtT(z, realPowT(x, Numeral(2)))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0<x^2 without &0<x must NOT decide ⊤ (counterexample x=&0)")
	}
}

// realProveAbsNonneg (real_ops.go) — closes `&0 ≤ |t|` directly via AbsNonneg,
// the single-lemma alternative to the abs case split. Also powers the
// sign-of-product side-condition discharge so `&0 ≤ |x|·|y|` (after the
// realAbsSgnSimp fold of `|x·y|`) reaches the LessEqMul clause without a
// 4-way case split.
func TestRealAbsNonneg_Direct(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	z := realLit(0)
	// Bare |t| for various t: variable, compound, literal, negated, abs-of-abs.
	realDecidesTrue(t, "0≤|x|", realLeT(z, realAbsT(x)))
	realDecidesTrue(t, "0≤|x+y|", realLeT(z, realAbsT(realPlusT(x, y))))
	realDecidesTrue(t, "0≤|-x|", realLeT(z, realAbsT(realNegT(x))))
	realDecidesTrue(t, "0≤||x||", realLeT(z, realAbsT(realAbsT(x))))
	// Compound abs of a product/quotient: AbsNonneg does NOT need the operand to
	// be a variable — any t works (the abs simp may fold first; either path closes).
	realDecidesTrue(t, "0≤|x·y|", realLeT(z, realAbsT(realStarT(x, y))))
	// Sign-of-product side-cond payoff: `&0 ≤ |x|·|y|` (the result of realAbsSgnSimp
	// folding `|x·y|`). Without the abs-aware discharge this would force the case
	// split (the realProveSignedProduct side conditions `&0 ≤ |x|` and `&0 ≤ |y|`
	// are opaque to linarith). With it, LessEqMul closes directly.
	realDecidesTrue(t, "0≤|x|·|y|", realLeT(z, realStarT(realAbsT(x), realAbsT(y))))
}

// realPowSimp's OfNumPow bridge: `real_pow(&m, n) → &(nat_pow(m, n))` when the base
// is `&_`, gated on the bundle field OfNumPow being non-nil. For LITERAL m, n
// the chain composes with my new NormNatExp (auto-fired in expSimp) into a
// single num literal, then the real_of_num bridge folds the equality to ⊤
// without the agent calling ExpandRealPowRewrite. Bundle field built via
// prop.Assume so the test exercises the bound path (vs the no-op gated path).
func TestRealPowOfNumPow_Literal(t *testing.T) {
	// Install the nat_pow bundle (NormNatExp needs expUnfold's bundle deps).
	defer installExpTestBundle(t, true)()
	// Install a stand-in OfNumPow + the OfNum* bridges (the
	// runRealNormNumCases pattern). prop.Assume keeps the ∀-stmt as a marker hyp so the test still
	// pins SOMETHING about wiring; only the kernel composition is exercised.
	m, n := numVar("m"), numVar("n")
	ForAll := ext.ForAll
	ofNumAdd := ForAll(m, n)(eqT(realOfNumT(plus(m, n)), realPlusT(realOfNumT(m), realOfNumT(n))))
	ofNumMul := ForAll(m, n)(eqT(realOfNumT(star(m, n)), realStarT(realOfNumT(m), realOfNumT(n))))
	ofNumEq := ForAll(m, n)(eqT(eqT(m, n), eqT(realOfNumT(m), realOfNumT(n))))
	ofNumPow := ForAll(m, n)(eqT(realPowT(realOfNumT(m), n), realOfNumT(expT(m, n))))
	SetRealLemmaBundle(&RealLemmaBundle{
		OfNumAdd: prop.Assume(ofNumAdd),
		OfNumMul: prop.Assume(ofNumMul),
		OfNumEq:  prop.Assume(ofNumEq),
		OfNumPow: prop.Assume(ofNumPow),
	})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })

	// `real_pow(&3, 4) = &81` — end-to-end auto: realPowSimp(OfNumPow) folds
	// `real_pow(&3, 4) → &(nat_pow(3, 4))`, expSimp(NormNatExp) folds `nat_pow(3, 4) → 81`
	// (under the nat_pow bundle), realNormNatEq closes `&81 = &81`.
	for _, c := range []struct {
		base, exp, want uint64
	}{
		{3, 4, 81}, {2, 5, 32}, {5, 3, 125}, {7, 0, 1}, {0, 5, 0},
	} {
		goal := eqT(realPowT(realLit(c.base), Numeral(c.exp)), realLit(c.want))
		w := ArithDecide(goal)
		if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
			t.Errorf("ArithDecide(real_pow &%d %d = &%d) = %v; want ⊤", c.base, c.exp, c.want, w)
		}
	}
}

// realPowSimp's OfNumPow bridge GATED OFF: with no OfNumPow field in the
// bundle, the realPowSimp clause is a no-op and the agent-driven
// ExpandRealPowRewrite path stays in effect — no production panic from a
// fabricator-free build. This pins the gate.
func TestRealPowOfNumPow_GatedOff(t *testing.T) {
	defer installExpTestBundle(t, true)()
	// Real bundle with NO OfNumPow field.
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	// realPowSimp must return nil for `real_pow(&3, 4)` (literal c ≥ 2 with
	// the OfNumPow gate off — no auto fold).
	if w := realPowSimp(realPowT(realLit(3), Numeral(4))); w != nil {
		t.Errorf("realPowSimp(real_pow &3 4) under gated-off OfNumPow = %v; want nil (no-op)", w)
	}
}

// realEvenPowNonneg (real_ops.go) — closes `&0 ≤ x pow &(2k)` for literal even
// 2k ≥ 4 via the perfect-square split: PowAdd at (x, k, k) rewrites
// `x^k · x^k = x^(2k)`, then SquareNonneg closes. The literal-2 case is taken
// upstream by PowTwoNonneg.
func TestRealEvenPowNonneg(t *testing.T) {
	x := realVar("x")
	z := realLit(0)
	// Literal even exponents — all close with NO hypothesis.
	realDecidesTrue(t, "0≤x^4", realLeT(z, realPowT(x, Numeral(4))))
	realDecidesTrue(t, "0≤x^6", realLeT(z, realPowT(x, Numeral(6))))
	realDecidesTrue(t, "0≤x^8", realLeT(z, realPowT(x, Numeral(8))))

	// sanity: odd literal exponents must NOT decide ⊤ without `&0 ≤ x`
	// (counter-ex x = −1 ⇒ x^odd = −1 < 0). pow 1 special-cases via expSimp; check 3.
	if w := RealArithDecideWithHyps(nil)(realLeT(z, realPowT(x, Numeral(3)))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0≤x^3 with no hyp must NOT decide ⊤ (counterexample x=−1)")
	}
	if w := RealArithDecideWithHyps(nil)(realLeT(z, realPowT(x, Numeral(5)))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0≤x^5 with no hyp must NOT decide ⊤ (counterexample x=−1)")
	}
}

// realSymbolicEvenPowNonneg (real_ops.go) — closes `nat_even n ⊢ &0 ≤ x pow n` for
// SYMBOLIC n. Recipe: EvenIffDouble skolemizes `nat_even n` to `n = 2·m₀`, PowPow
// reshapes `x pow n` to `(x pow 2) pow m₀`, PowTwoNonneg + PowNonneg closes, and
// the body hyp bridges back.
func TestRealSymbolicEvenPowNonneg(t *testing.T) {
	x := realVar("x")
	z := realLit(0)
	n := numVar("n")

	// Headline: nat_even n ⊢ &0 ≤ x pow n.
	realDecidesTrue(t, "nat_even n⊢0≤x^n", realLeT(z, realPowT(x, n)), evenT(n))

	// sanity: without a nat_even hyp the decider must NOT close `&0 ≤ x pow n` (x=−1,
	// n=3 is a counterexample). The PowNonneg path would need `&0 ≤ x`, also absent.
	if w := RealArithDecideWithHyps(nil)(realLeT(z, realPowT(x, n))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&0≤x^n without nat_even n must NOT decide ⊤ (x=−1, n=3 counterexample)")
	}
	// sanity: nat_odd n alone must NOT close it (x=−1, n=3 still counterexample). The
	// MatchesEven matcher rejects nat_odd, so the symbolic handler declines.
	if w := RealArithDecideWithHyps([]Term{oddT(n)})(realLeT(z, realPowT(x, n))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("nat_odd n ⊢ &0≤x^n must NOT decide ⊤ (x=−1, n=3 counterexample)")
	}
}

// abs / sgn algebraic laws (real_ops.go) — the homomorphism / identity folds. The
// fold fires in realArithSimpStep, so `|x·y| = |x|·|y|` closes as reflexivity after
// both sides normalize. Placeholder-backed (every Abs* / Sgn* is a fabricator stand-in);
// the composition (the fold's congruence + the post-fold ring/refl) is real kernel
// work, so green = the plumbing is sound.

func TestRealAbsLaws(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	n := numVar("n")
	ax, ay := realAbsT(x), realAbsT(y)

	// abs(x·y) = abs x · abs y  (AbsMul) — the headline; both orientations.
	realDecidesTrue(t, "|x·y|=|x|·|y|", eqT(realAbsT(realStarT(x, y)), realStarT(ax, ay)))
	realDecidesTrue(t, "|x|·|y|=|x·y|", eqT(realStarT(ax, ay), realAbsT(realStarT(x, y))))
	// abs(−x) = abs x  (AbsEven).
	realDecidesTrue(t, "|−x|=|x|", eqT(realAbsT(realNegT(x)), ax))
	// abs(abs x) = abs x  (AbsIdempotent).
	realDecidesTrue(t, "||x||=|x|", eqT(realAbsT(ax), ax))
	// abs(x/y) = abs x / abs y  (AbsDiv).
	realDecidesTrue(t, "|x/y|=|x|/|y|", eqT(realAbsT(realDivT(x, y)), realDivT(ax, ay)))
	// abs(inv x) = inv(abs x)  (AbsInv).
	realDecidesTrue(t, "|inv x|=inv|x|", eqT(realAbsT(realInvT(x)), realInvT(ax)))
	// abs(x pow 2) = abs x pow 2  (AbsPow).
	realDecidesTrue(t, "|x^2|=|x|^2", eqT(realAbsT(realPowT(x, Numeral(2))), realPowT(ax, Numeral(2))))
	// abs(&n) = &n  (AbsOfNum, n a num variable).
	realDecidesTrue(t, "|&n|=&n", eqT(realAbsT(realOfNumT(n)), realOfNumT(n)))
	// Composed: abs(−(x·y)) = abs x · abs y  (neg then mul folds compose).
	realDecidesTrue(t, "|−(x·y)|=|x|·|y|", eqT(realAbsT(realNegT(realStarT(x, y))), realStarT(ax, ay)))

	// sanity: |x+y| = |x|+|y| is NOT a law (the triangle inequality is ≤, not =);
	// there is no abs-of-SUM fold, and the split cannot close the mixed-sign branch.
	if w := RealArithDecideWithHyps(nil)(eqT(realAbsT(realPlusT(x, y)), realPlusT(ax, ay))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("|x+y|=|x|+|y| must NOT decide ⊤ (it is not a theorem)")
	}
}

func TestRealSgnLaws(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	sx, sy := realSgnT(x), realSgnT(y)

	// real_sgn(x·y) = real_sgn x · real_sgn y  (SgnMul).
	realDecidesTrue(t, "sgn(x·y)=sgn x·sgn y", eqT(realSgnT(realStarT(x, y)), realStarT(sx, sy)))
	// real_sgn(−x) = −(real_sgn x)  (SgnOdd).
	realDecidesTrue(t, "sgn(−x)=−sgn x", eqT(realSgnT(realNegT(x)), realNegT(sx)))
	// real_sgn(inv x) = real_sgn x  (SgnPreservedByInv).
	realDecidesTrue(t, "sgn(inv x)=sgn x", eqT(realSgnT(realInvT(x)), sx))
}

func TestRealInvLaws(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	ix, iy := realInvT(x), realInvT(y)

	// inv(x·y) = inv x · inv y  (InvMul).
	realDecidesTrue(t, "inv(x·y)=inv x·inv y", eqT(realInvT(realStarT(x, y)), realStarT(ix, iy)))
	realDecidesTrue(t, "inv x·inv y=inv(x·y)", eqT(realStarT(ix, iy), realInvT(realStarT(x, y))))
	// inv(inv x) = x  (InvInv).
	realDecidesTrue(t, "inv(inv x)=x", eqT(realInvT(ix), x))
	// inv(−x) = −(inv x)  (InvNeg).
	realDecidesTrue(t, "inv(−x)=−inv x", eqT(realInvT(realNegT(x)), realNegT(ix)))
	// inv(x/y) = y/x  (InvDiv).
	realDecidesTrue(t, "inv(x/y)=y/x", eqT(realInvT(realDivT(x, y)), realDivT(y, x)))
	// inv(x pow n) = inv x pow n  (InvPow; n a num variable — the symbolic
	// case expand_exp cannot reach, the inv twin of AbsPow).
	n := numVar("n")
	realDecidesTrue(t, "inv(x pow n)=inv x pow n",
		eqT(realInvT(realPowT(x, n)), realPowT(realInvT(x), n)))
	// Composed: inv(inv(x·y)) = x·y (InvInv then unwrap; the fixpoint converges).
	realDecidesTrue(t, "inv(inv(x·y))=x·y", eqT(realInvT(realInvT(realStarT(x, y))), realStarT(x, y)))
	// Composed: inv(−(x·y)) = −(inv x · inv y)  (InvNeg then InvMul).
	realDecidesTrue(t, "inv(−(x·y))=−(inv x·inv y)",
		eqT(realInvT(realNegT(realStarT(x, y))), realNegT(realStarT(ix, iy))))

	// sanity: inv(x+y) = inv x + inv y is NOT a law (no homomorphism over `+`); the
	// fold has no `+` clause, so this must NOT decide ⊤.
	if w := RealArithDecideWithHyps(nil)(eqT(realInvT(realPlusT(x, y)), realPlusT(ix, iy))); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("inv(x+y)=inv x+inv y must NOT decide ⊤ (no such law)")
	}
}

// inv sign monotonicity (InvPos / InvNonneg / InvEqZero)
// — the dual to NegNonnegativeIffNonpositive/NegPositiveIffNegative. Sign is PRESERVED through inv, so the comparison atom
// rewrites straight to the same comparison on `x`. Closing through atom rewrites,
// the goal becomes literally a hyp or a tautology after rewriting.
func TestRealInvSignMono(t *testing.T) {
	x := realVar("x")
	zero := realLit(0)
	// Goal-side (the simp visits the goal atom and rewrites it):
	// (&0 < inv x) ⇔ (&0 < x): hyp `&0 < x` closes goal `&0 < inv x`.
	realDecidesTrue(t, "0<x ⊢ 0<inv x", realLtT(zero, realInvT(x)), realLtT(zero, x))
	// (&0 ≤ inv x) ⇔ (&0 ≤ x): hyp `&0 ≤ x` closes goal `&0 ≤ inv x`.
	realDecidesTrue(t, "0≤x ⊢ 0≤inv x", realLeT(zero, realInvT(x)), realLeT(zero, x))
	// (inv x = &0) ⇔ (x = &0): hyp `x = &0` closes goal `inv x = &0`.
	realDecidesTrue(t, "x=0 ⊢ inv x=0", eqT(realInvT(x), zero), eqT(x, zero))
}

// TestRealInvSignMono_HypSide pins the SYMMETRIC hyp-side direction of the inv
// sign monotonicity iffs. UNBLOCKED by d9350352 (the hyp pre-simp pass in
// RealArithDecideWithHyps): each hyp now flows through the same simp stack as
// the goal (modulo the goal-only realSquarePosSimp carve-out), so an inv-rooted
// hyp atom gets its iff applied before the decide leaf reads it.
func TestRealInvSignMono_HypSide(t *testing.T) {
	x := realVar("x")
	zero := realLit(0)
	// hyp `&0 < inv x` closes goal `&0 < x` (InvPos applied to the hyp atom).
	realDecidesTrue(t, "0<inv x ⊢ 0<x", realLtT(zero, x), realLtT(zero, realInvT(x)))
	// hyp `&0 ≤ inv x` closes goal `&0 ≤ x`.
	realDecidesTrue(t, "0≤inv x ⊢ 0≤x", realLeT(zero, x), realLeT(zero, realInvT(x)))
	// hyp `inv x = &0` closes goal `x = &0` (the failing case from the design).
	realDecidesTrue(t, "inv x=0 ⊢ x=0", eqT(x, zero), eqT(realInvT(x), zero))
}

// pow distribution laws (MulPowDistrib / DivPow / PowPow / OnePow).
func TestRealPowLaws(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	n, m := numVar("n"), numVar("m")
	// (x·y) pow n = x pow n · y pow n  (MulPowDistrib).
	realDecidesTrue(t, "(x·y)^n=x^n·y^n",
		eqT(realPowT(realStarT(x, y), n), realStarT(realPowT(x, n), realPowT(y, n))))
	// (x/y) pow n = x pow n / y pow n  (DivPow).
	realDecidesTrue(t, "(x/y)^n=x^n/y^n",
		eqT(realPowT(realDivT(x, y), n), realDivT(realPowT(x, n), realPowT(y, n))))
	// (x pow m) pow n = x pow (m·n)  (PowPow) — m·n is num multiplication.
	realDecidesTrue(t, "(x^m)^n=x^(m·n)",
		eqT(realPowT(realPowT(x, m), n), realPowT(x, star(m, n))))
	// &1 pow n = &1  (OnePow).
	realDecidesTrue(t, "&1^n=&1", eqT(realPowT(realLit(1), n), realLit(1)))
	// Composed: inv((x·y) pow n) = inv x pow n · inv y pow n  (InvPow + MulPowDistrib + InvMul).
	realDecidesTrue(t, "inv((x·y)^n)=inv x^n·inv y^n",
		eqT(realInvT(realPowT(realStarT(x, y), n)),
			realStarT(realPowT(realInvT(x), n), realPowT(realInvT(y), n))))
}

// sgn laws at zero, quotients and powers (SgnOfZero / SgnDiv / SgnPow).
func TestRealSgnExtras(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	n := numVar("n")
	// sgn &0 = &0  (SgnOfZero, literal fold).
	realDecidesTrue(t, "sgn 0=0", eqT(realSgnT(realLit(0)), realLit(0)))
	// sgn(x/y) = sgn x / sgn y  (SgnDiv).
	realDecidesTrue(t, "sgn(x/y)=sgn x/sgn y",
		eqT(realSgnT(realDivT(x, y)), realDivT(realSgnT(x), realSgnT(y))))
	// sgn(x pow n) = sgn x pow n  (SgnPow).
	realDecidesTrue(t, "sgn(x^n)=sgn x^n",
		eqT(realSgnT(realPowT(x, n)), realPowT(realSgnT(x), n)))
}

// AbsLessEqIffPowTwoLessEq — `x² ≤ y²` simp-rewrites to `|x| ≤ |y|`. Closes
// when the abs-form is present as a hyp; composes with SquareOfAbs (strips abs
// from squared) so `|x|² ≤ |y|²` cascades through.
func TestRealAbsLessEqIffPowTwoLessEq(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	two := Numeral(2)
	// Hyp `|x| ≤ |y|` closes goal `x² ≤ y²` (simp rewrites goal toward abs).
	realDecidesTrue(t, "|x|≤|y| ⊢ x²≤y²",
		realLeT(realPowT(x, two), realPowT(y, two)),
		realLeT(realAbsT(x), realAbsT(y)))
	// Cascade with SquareOfAbs: hyp `|x| ≤ |y|` closes goal `|x|² ≤ |y|²`
	// (SquareOfAbs strips both abs to `x² ≤ y²`, then AbsLessEqIffPowTwoLessEq rewrites back).
	realDecidesTrue(t, "|x|≤|y| ⊢ |x|²≤|y|²",
		realLeT(realPowT(realAbsT(x), two), realPowT(realAbsT(y), two)),
		realLeT(realAbsT(x), realAbsT(y)))
}

// pow base/exponent monotonicity (PowMonoBase / PowMonoBaseStrict / PowMonoExp).
func TestRealPowMonotonicity(t *testing.T) {
	x, y := realVar("x"), realVar("y")
	m, n := numVar("m"), numVar("n")
	zero := realLit(0)
	one := realLit(1)
	// PowMonoBase: &0 ≤ x ∧ x ≤ y ⊢ xⁿ ≤ yⁿ.
	realDecidesTrue(t, "0≤x ∧ x≤y ⊢ xⁿ≤yⁿ",
		realLeT(realPowT(x, n), realPowT(y, n)),
		realLeT(zero, x), realLeT(x, y))
	// PowMonoBaseStrict: ~(n=0) ∧ &0 ≤ x ∧ x < y ⊢ xⁿ < yⁿ.
	realDecidesTrue(t, "n≠0 ∧ 0≤x ∧ x<y ⊢ xⁿ<yⁿ",
		realLtT(realPowT(x, n), realPowT(y, n)),
		prop.Not(eqT(n, Numeral(0))), realLeT(zero, x), realLtT(x, y))
	// PowMonoExp: &1 ≤ x ∧ m ≤ n ⊢ xᵐ ≤ xⁿ.
	realDecidesTrue(t, "1≤x ∧ m≤n ⊢ xᵐ≤xⁿ",
		realLeT(realPowT(x, m), realPowT(x, n)),
		realLeT(one, x), le(m, n))
}

// AbsTriangle — binary + n-ary via iterated triangle.
func TestRealAbsTriangle(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	// Binary: |x + y| ≤ |x| + |y|  (the lemma applied directly; rhs == absSum).
	realDecidesTrue(t, "|x+y|≤|x|+|y|",
		realLeT(realAbsT(realPlusT(x, y)), realPlusT(realAbsT(x), realAbsT(y))))
	// Ternary (right-associated): |x + (y + z)| ≤ |x| + (|y| + |z|).
	realDecidesTrue(t, "|x+(y+z)|≤|x|+(|y|+|z|)",
		realLeT(realAbsT(realPlusT(x, realPlusT(y, z))),
			realPlusT(realAbsT(x), realPlusT(realAbsT(y), realAbsT(z)))))
	// Binary with linarith tail: hyps `|x| ≤ a` and `|y| ≤ b` close goal
	// `|x+y| ≤ a + b` (triangle + linarith transit).
	a, b := realVar("a"), realVar("b")
	realDecidesTrue(t, "|x|≤a ∧ |y|≤b ⊢ |x+y|≤a+b",
		realLeT(realAbsT(realPlusT(x, y)), realPlusT(a, b)),
		realLeT(realAbsT(x), a), realLeT(realAbsT(y), b))
}

// square ↔ abs interchange (SquareOfAbs / SquarePos / NegEqZero).
func TestRealSquareAbsInterchange(t *testing.T) {
	x := realVar("x")
	zero := realLit(0)
	two := Numeral(2)
	// abs(x) pow 2 = x pow 2  (SquareOfAbs) — strips abs from a square.
	realDecidesTrue(t, "|x|^2=x^2", eqT(realPowT(realAbsT(x), two), realPowT(x, two)))
	// Composed: hyp `&0 ≤ x^2` closes goal `&0 ≤ |x|^2` (SquareOfAbs strips the abs).
	realDecidesTrue(t, "0≤x^2 ⊢ 0≤|x|^2",
		realLeT(zero, realPowT(realAbsT(x), two)), realLeT(zero, realPowT(x, two)))

	// SquarePos goal-side: ~(x = &0) → &0 < x·x. Hyp `&0 < x·x` closes
	// goal `~(x = &0)`.
	realDecidesTrue(t, "0<x·x ⊢ x≠0",
		prop.Not(eqT(x, zero)), realLtT(zero, realStarT(x, x)))

	// NegEqZero goal-side: (−x = &0) → (x = &0). Hyp `x = &0` closes goal
	// `−x = &0`.
	realDecidesTrue(t, "x=0 ⊢ −x=0", eqT(realNegT(x), zero), eqT(x, zero))
}

// real_of_num homomorphism collapse (real_ops.go) — the ℝ twin of TestIntOfNumCollapse.
// `&n` (n a num VARIABLE) is opaque to linarith (real vars carry no default bound)
// and the ring atomizes it, so neither sees `&n·&n = &(n·n)` nor `&0 ≤ &n`. The
// collapse runs the OfNum* homomorphism as proof rewrites and drops the
// nonneg-image comparisons to the num prover. OfNum*/Neg* are bound, so this is
// real kernel work (no placeholder leaf).

func TestRealOfNum(t *testing.T) {
	n, m := numVar("n"), numVar("m")
	on, om := realOfNumT(n), realOfNumT(m)

	// `=` collapse: both sides reduce to the same signed num image.
	realDecidesTrue(t, "&n·&n = &(n·n)", eqT(realStarT(on, on), realOfNumT(star(n, n))))
	realDecidesTrue(t, "&n·&m = &(n·m)", eqT(realStarT(on, om), realOfNumT(star(n, m))))
	realDecidesTrue(t, "&n+&m = &(n+m)", eqT(realPlusT(on, om), realOfNumT(plus(n, m))))

	// `≤` drop to the num goal (num default-nonneg).
	realDecidesTrue(t, "&0 ≤ &n", realLeT(realLit(0), on))
	realDecidesTrue(t, "&0 ≤ &n·&n", realLeT(realLit(0), realStarT(on, on)))
	realDecidesTrue(t, "&0 ≤ &n + &m", realLeT(realLit(0), realPlusT(on, om)))

	// sanity: `&n = &m` (distinct vars) is NOT valid — must NOT decide ⊤ (the images
	// `&n`, `&m` differ, so the collapse correctly declines).
	if w := RealArithDecideWithHyps(nil)(eqT(on, om)); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&n = &m must NOT decide ⊤ (distinct vars)")
	}
	// sanity: `&n ≤ &m` (distinct vars) is NOT valid — must NOT decide ⊤.
	if w := RealArithDecideWithHyps(nil)(realLeT(on, om)); w != nil && prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("&n ≤ &m must NOT decide ⊤ (distinct vars)")
	}
}

// The hyp pre-simp pass (engine.go preSimpHyps + bridgeBackHyps) folds each hyp
// through the goal-side's hyp-FREE leaves before feeding it to the decider, so
// abs/sgn / pow / numeral / identity folds on hyps benefit linarith's shallow
// parseHypConstraint (which would otherwise atomize the unfolded form as a
// distinct opaque atom from the folded goal). The cases below exercise the
// hyp-side fold producing a result the OLD per-call rewrite (concl only) would
// have left for a later tactic step.

// Real abs algebraic-law fold on a HYPOTHESIS: `|a + &0| ≤ &5 ⊢ |a| ≤ &5` —
// the identity-fold `a + &0 → a` inside abs reaches the hyp via pre-simp, after
// which the linarith hyp-echo closes the (now-α-equal) goal. Without pre-simp
// the hyp atomizes as `[|a+&0|]` and the goal as `[|a|]`, two distinct atoms
// linarith cannot relate (the abs-of-compound fold lives in the simp leaf, not
// in linOf).
func TestRealArithDecide_HypAbsFold(t *testing.T) {
	a := realVar("a")
	five := realLit(5)
	hypUnfolded := realLeT(realAbsT(realPlusT(a, realLit(0))), five) // |a + &0| ≤ &5
	goal := realLeT(realAbsT(a), five)                               // |a| ≤ &5
	w := RealArithDecideWithHyps([]Term{hypUnfolded})(goal)
	if w == nil {
		t.Fatal("RealArithDecideWithHyps([|a+&0|≤&5])(|a|≤&5) = nil, want ⊤ via hyp pre-simp")
	}
	if !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Errorf("Rhs = %v, want ⊤", prop.Rhs(w))
	}
	// IsStronger: result hyps ⊆ original hyps (the bridge cuts h' back to h).
	if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(hypUnfolded) {
		t.Errorf("result must carry the ORIGINAL unfolded hyp; got %d hyps, hyp[0]=%v",
			w.NumHyps(), w.Hyp(0))
	}
}

// Real numeral fold on a HYPOTHESIS: `x ≤ &2 + &3 ⊢ x ≤ &5`. The norm_num
// numeral fold `&2 + &3 → &5` fires in the hyp via pre-simp.
func TestRealArithDecide_HypNumeralFold(t *testing.T) {
	x := realVar("x")
	hyp := realLeT(x, realPlusT(realLit(2), realLit(3))) // x ≤ &2 + &3
	goal := realLeT(x, realLit(5))                       // x ≤ &5
	w := RealArithDecideWithHyps([]Term{hyp})(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("RealArithDecideWithHyps([x≤&2+&3])(x≤&5) = %v, want ⊤", w)
	}
}

// Real sgn algebraic-law fold on a HYPOTHESIS: `real_sgn(−x) = c ⊢ −real_sgn(x) = c`.
// SgnOdd folds the hyp's `real_sgn(−x) → −real_sgn(x)` via pre-simp; the
// goal already matches.
func TestRealArithDecide_HypSgnFold(t *testing.T) {
	x := realVar("x")
	c := realVar("c")
	sx := realSgnT(x)
	hyp := eqT(realSgnT(realNegT(x)), c) // real_sgn(−x) = c
	goal := eqT(realNegT(sx), c)         // −real_sgn(x) = c
	w := RealArithDecideWithHyps([]Term{hyp})(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("RealArithDecideWithHyps([sgn(−x)=c])(−sgn(x)=c) = %v, want ⊤", w)
	}
}

// Int pow fold on a HYPOTHESIS: `x pow &1 ≤ &5 ⊢ x ≤ &5`. intPowSimp's
// strictly-shrinking `m pow 1 → m` fold fires in the hyp via pre-simp.
// linOf treats `int_pow(x, &1)` as an opaque atom distinct from the bare `x`
// in the goal, so without hyp pre-simp linarith cannot relate them.
func TestIntArithDecide_HypPowFold(t *testing.T) {
	x := intVar("x")
	hyp := intLeT(intPowT(x, Numeral(1)), intLit(5)) // x pow &1 ≤ &5
	goal := intLeT(x, intLit(5))                     // x ≤ &5
	w := IntArithDecideWithHyps([]Term{hyp})(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("IntArithDecideWithHyps([x^1≤&5])(x≤&5) = %v, want ⊤", w)
	}
	if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(hyp) {
		t.Errorf("result must carry the ORIGINAL hyp; got %d hyps, hyp[0]=%v",
			w.NumHyps(), w.Hyp(0))
	}
}

// Int image-split termination guard: when pre-simp ran the move-across leaf on
// a hyp like `x = −&n0` it positivized to `x + &n0 = &0`, which broke
// pinnedByHyp (int.go:776) — the Image split's recursion guard — and recursed
// forever. The fix dropped intMoveAcrossLeaf from int pre-simp. This test pins
// the regression: `&0 ≤ x·x` (the canonical Image split goal) must close
// without overflowing.
func TestIntArithDecide_ImageSplitTerminates(t *testing.T) {
	x := intVar("x")
	goal := intLeT(intLit(0), intStarT(x, x)) // &0 ≤ x·x
	w := IntArithDecideWithHyps(nil)(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		t.Fatalf("IntArithDecideWithHyps(nil)(&0≤x·x) = %v, want ⊤", w)
	}
}

// ℝ ring-normalizer tests — the realRing instantiation of the domain-generic
// machinery (ring.go). Mirrors ring_test.go: leaves are placeholders
// (no real bundle installed), but the kernel enforces every EqTrans/congruence
// in the composition lines up, and we pin Lhs = t, Rhs = buildTerm(linOf(t)),
// plus model lockstep. TestRealRingBundleWiring then pins each ring leaf's
// bound orientation/binder order with marker hypotheses.

func checkRealNormalize(t *testing.T, e Term) {
	t.Helper()
	lf, w, ok := realRing.normalizeProof(e)
	if !ok {
		t.Fatalf("realNormalizeProof declined %v", e)
	}
	if !prop.Lhs(w).AlphaEquals(e) {
		t.Errorf("Lhs = %v, want %v", prop.Lhs(w), e)
	}
	if !prop.Rhs(w).AlphaEquals(realDomain.buildTerm(lf)) {
		t.Errorf("Rhs = %v, want toTerm %v", prop.Rhs(w), realDomain.buildTerm(lf))
	}
	// cross-check the form matches the untrusted model (lockstep invariant)
	if ref, _ := realDomain.linOf(e); evalLinNeq(lf, ref) {
		t.Errorf("realNormalizeProof form disagrees with linOf for %v", e)
	}
}

func TestRealNormalizeProofPlumbing(t *testing.T) {
	exprs := []Term{
		rr("&5"),
		rr("x"),
		rr("x + y"),
		rr("y + x"),
		rr("(x + y) + z"),
		rr("x + (y + z)"),
		rr("x + x"),
		rr("&2 * x + &3 * x"),
		rr("&3 * x"),
		rr("x * &3"),
		rr("&2 * (x + y)"),
		rr("&2 * (x + y) + &7"),
		rr("&2 * (&3 * x)"),
		rr("&5 + &7"),
		rr("(&2 * x + &3 * y) + &4 * x"),
		rr("(x + &3) + (y + &4)"),
		rr("&0 * (x + y)"), // scale by 0 → &0
		rr("(z + y) + x"),  // reverse order, exercises bubbling
	}
	for _, e := range exprs {
		checkRealNormalize(t, e)
	}
}

// TestRealNormalizeProofProducts: a product of atoms expands over the
// monomial basis on the proof side too (realRing.normalizeProof's product
// branch, mirrored on realDomain.polyMul) — checkRealNormalize pins the
// lockstep with the model. The broader pins are in real_poly_basis_test.go.
func TestRealNormalizeProofProducts(t *testing.T) {
	for _, s := range []string{"x * y", "y * x", "(x * y) * z", "&2 * (x * y) + &3 * (y * x)"} {
		checkRealNormalize(t, rr(s))
	}
}

func TestRealRingProve(t *testing.T) {
	pairs := []struct{ l, r Term }{
		{rr("(x + y) + z"), rr("x + (y + z)")},
		{rr("x + y"), rr("y + x")},
		{rr("&2 * (x + y)"), rr("&2 * x + &2 * y")},
		{rr("(x + &3) + (y + &4)"), rr("(x + y) + &7")},
		{rr("&3 * x + &2 * x"), rr("&5 * x")},
		{rr("x + x"), rr("&2 * x")},
		{rr("x"), rr("&1 * x + &0")},
		{rr("(x + y) * &3"), rr("&3 * x + &3 * y")},
		{rr("x * y"), rr("y * x")}, // a product reads over the monomial basis
	}
	for _, p := range pairs {
		w, ok := RealRingProve(p.l, p.r)
		if !ok {
			t.Errorf("RealRingProve(%v, %v) declined", p.l, p.r)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(p.l) || !prop.Rhs(w).AlphaEquals(p.r) {
			t.Errorf("RealRingProve(%v,%v): proof is %v = %v", p.l, p.r, prop.Lhs(w), prop.Rhs(w))
		}
	}
	declines := []struct{ l, r Term }{
		{rr("x + y"), rr("x + z")},
		{rr("&2 * x"), rr("&3 * x")},
		{rr("x * y"), rr("x * z")},
	}
	for _, p := range declines {
		if _, ok := RealRingProve(p.l, p.r); ok {
			t.Errorf("RealRingProve(%v, %v) should decline", p.l, p.r)
		}
	}
}

// TestRealRingFull: the full multivariate ℝ ring (RealRingProveFull) — closes the
// nonlinear products RealRingProve defers (x*y = y*x, distribution, the (x+y)²
// expansion) by monomial atomization. Unequal polys decline.
func TestRealRingFull(t *testing.T) {
	equal := []struct{ l, r Term }{
		{rr("x * y"), rr("y * x")},
		{rr("x * (y + z)"), rr("x * y + x * z")},
		{rr("(x + y) * (x + y)"), rr("(x * x + &2 * (x * y)) + y * y")},
	}
	for _, p := range equal {
		w, ok := RealRingProveFull(p.l, p.r)
		if !ok {
			t.Errorf("RealRingProveFull(%v, %v) declined", p.l, p.r)
			continue
		}
		if !prop.Lhs(w).AlphaEquals(p.l) || !prop.Rhs(w).AlphaEquals(p.r) {
			t.Errorf("RealRingProveFull(%v,%v): proof is %v = %v", p.l, p.r, prop.Lhs(w), prop.Rhs(w))
		}
	}
	if _, ok := RealRingProveFull(rr("(x + y) * (x + y)"), rr("x * x + y * y")); ok {
		t.Error("closed (x+y)² = x²+y² (missing 2xy)")
	}
}

// TestRealRingBundleWiring installs the nine ring fields in their normal-form
// orientation (most are REVERSED relative to the engine shapes, and
// RightDistrib binds (a, m, b) with m the shared factor). prop.Assume markers prove each leaf bound its field — in particular
// pinning realRightDistrib's [a, c, b] instAll permutation against a real
// binder-order regression.
func TestRealRingBundleWiring(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	ForAll := ext.ForAll
	stmts := map[string]Term{
		// ∀x y. x+y = y+x  /  ∀x y z. x+(y+z) = (x+y)+z
		"AddSym":   ForAll(x, y)(eqT(realPlusT(x, y), realPlusT(y, x))),
		"AddAssoc": ForAll(x, y, z)(eqT(realPlusT(x, realPlusT(y, z)), realPlusT(realPlusT(x, y), z))),
		"MulSym":   ForAll(x, y)(eqT(realStarT(x, y), realStarT(y, x))),
		"MulAssoc": ForAll(x, y, z)(
			eqT(realStarT(x, realStarT(y, z)), realStarT(realStarT(x, y), z))),
		// ∀y. y = y+&0  /  ∀x. x = &1·x  /  ∀x. &0 = &0·x
		"AddRightId":  ForAll(y)(eqT(y, realPlusT(y, realLit(0)))),
		"MulLeftId":   ForAll(x)(eqT(x, realStarT(realLit(1), x))),
		"MulLeftZero": ForAll(x)(eqT(realLit(0), realStarT(realLit(0), x))),
		// ∀x y z. x·y + x·z = x·(y+z)
		"LeftDistrib": ForAll(x, y, z)(
			eqT(realPlusT(realStarT(x, y), realStarT(x, z)), realStarT(x, realPlusT(y, z)))),
		// ∀a m b. a·m + b·m = (a+b)·m — m (the shared factor) is the MIDDLE binder
		"RightDistrib": ForAll(x, y, z)(
			eqT(realPlusT(realStarT(x, y), realStarT(z, y)), realStarT(realPlusT(x, z), y))),
	}
	SetRealLemmaBundle(&RealLemmaBundle{
		AddSym: prop.Assume(stmts["AddSym"]), AddAssoc: prop.Assume(stmts["AddAssoc"]),
		MulSym: prop.Assume(stmts["MulSym"]), MulAssoc: prop.Assume(stmts["MulAssoc"]),
		AddRightId: prop.Assume(stmts["AddRightId"]), MulLeftId: prop.Assume(stmts["MulLeftId"]),
		MulLeftZero:  prop.Assume(stmts["MulLeftZero"]),
		LeftDistrib:  prop.Assume(stmts["LeftDistrib"]),
		RightDistrib: prop.Assume(stmts["RightDistrib"]),
	})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })

	a, b, c := realVar("a"), realVar("b"), realVar("c")
	cases := []struct {
		name   string
		run    func() *prop.PropWrapper
		want   Term
		marker Term
	}{
		{"commuteADD", func() *prop.PropWrapper { return realCommuteADD(a, b) },
			eqT(realPlusT(a, b), realPlusT(b, a)), stmts["AddSym"]},
		{"associateADD", func() *prop.PropWrapper { return realAssociateADD(a, b, c) },
			eqT(realPlusT(realPlusT(a, b), c), realPlusT(a, realPlusT(b, c))), stmts["AddAssoc"]},
		{"commuteMUL", func() *prop.PropWrapper { return realCommuteMUL(a, b) },
			eqT(realStarT(a, b), realStarT(b, a)), stmts["MulSym"]},
		{"associateMUL", func() *prop.PropWrapper { return realAssociateMUL(a, b, c) },
			eqT(realStarT(realStarT(a, b), c), realStarT(a, realStarT(b, c))), stmts["MulAssoc"]},
		{"distributeMUL", func() *prop.PropWrapper { return realDistributeMUL(a, b, c) },
			eqT(realStarT(a, realPlusT(b, c)), realPlusT(realStarT(a, b), realStarT(a, c))),
			stmts["LeftDistrib"]},
		{"rightDistrib", func() *prop.PropWrapper { return realRightDistrib(a, b, c) },
			eqT(realStarT(realPlusT(a, b), c), realPlusT(realStarT(a, c), realStarT(b, c))),
			stmts["RightDistrib"]},
		{"oneMul", func() *prop.PropWrapper { return realOneMul(a) },
			eqT(realStarT(realLit(1), a), a), stmts["MulLeftId"]},
		{"addZeroR", func() *prop.PropWrapper { return realAddZeroR(a) },
			eqT(realPlusT(a, realLit(0)), a), stmts["AddRightId"]},
		{"zeroMul", func() *prop.PropWrapper { return realZeroMul(a) },
			eqT(realStarT(realLit(0), a), realLit(0)), stmts["MulLeftZero"]},
	}
	for _, tc := range cases {
		w := tc.run()
		if !w.Conclusion().AlphaEquals(tc.want) {
			t.Errorf("%s: got %v want %v", tc.name, w.Conclusion(), tc.want)
		}
		if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(tc.marker) {
			t.Errorf("%s: bundle field not bound (no marker hyp) — leaf degraded to placeholder", tc.name)
		}
	}
}

// TestRealLinProveMerged: an end-to-end forward proof whose replay must MERGE
// like terms through the real ring normalizer (x + x vs &2·x on the two sides).
func TestRealLinProveMerged(t *testing.T) {
	checkRealProve(t, "like-terms", rb("x + x <= &2 * x"))
}

// Real certificate-replay tests: each refutation/proof must run the full kernel
// composition (scale → sum → ring-normalize → cancel → close, plus the forward
// negate→refute→peel) and land the right conclusion + a hyp set among the
// inputs. Leaves are RealLemmaBundle placeholders, so soundness rides on the
// theorems the install binds (library/serve's binding tests); the plumbing is
// real kernel work and checked here.

// realCon builds a canonical real constraint from two real-parsed sides.
func realCon(l, r Term, op relOp) LinConstraint {
	return LinConstraint{Lhs: l, Rhs: r, Op: op}
}

func realConstraintTerm(c LinConstraint) Term {
	if c.Hyp != nil {
		return c.Hyp
	}
	switch c.Op {
	case opLE:
		return realLeT(c.Lhs, c.Rhs)
	case opLT:
		return realLtT(c.Lhs, c.Rhs)
	default:
		return eqT(c.Lhs, c.Rhs)
	}
}

// hypsAmong checks every hypothesis of w is one of the allowed terms.
func hypsAmong(t *testing.T, name string, w *prop.PropWrapper, allowed []Term) {
	t.Helper()
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
			t.Errorf("%s: stray hypothesis %v not among inputs", name, h)
		}
	}
}

func checkRealRefute(t *testing.T, name string, cs []LinConstraint) {
	t.Helper()
	w, ok := RealLinRefuteProof(cs)
	if !ok {
		t.Fatalf("%s: expected a real refutation, got none", name)
	}
	if !w.Conclusion().Equals(prop.F) {
		t.Errorf("%s: conclusion = %v, want ⊥", name, w.Conclusion())
	}
	allowed := make([]Term, len(cs))
	for i, c := range cs {
		allowed[i] = realConstraintTerm(c)
	}
	hypsAmong(t, name, w, allowed)
}

func TestRealLinRefuteProof(t *testing.T) {
	cases := []struct {
		name string
		cs   []LinConstraint
	}{
		{"x<x", []LinConstraint{realCon(rr("x"), rr("x"), opLT)}},
		{"x<y,y<x", []LinConstraint{realCon(rr("x"), rr("y"), opLT), realCon(rr("y"), rr("x"), opLT)}},
		{"&2<=x,x<=&1", []LinConstraint{realCon(rr("&2"), rr("x"), opLE), realCon(rr("x"), rr("&1"), opLE)}},
		{"x+y<=&1,&2<=x+y", []LinConstraint{
			realCon(rr("x + y"), rr("&1"), opLE), realCon(rr("&2"), rr("x + y"), opLE)}},
		{"cycle x<=y<=z<x", []LinConstraint{
			realCon(rr("x"), rr("y"), opLE), realCon(rr("y"), rr("z"), opLE), realCon(rr("z"), rr("x"), opLT)}},
		{"eq: x=y, y<x", []LinConstraint{realCon(rr("x"), rr("y"), opEQ), realCon(rr("y"), rr("x"), opLT)}},
	}
	for _, tc := range cases {
		checkRealRefute(t, tc.name, tc.cs)
	}
}

func checkRealProve(t *testing.T, name string, goal Term, hyps ...Term) {
	t.Helper()
	w, ok := RealLinProve(seqOf(hyps...), goal)
	if !ok {
		t.Fatalf("%s: expected a proof of the goal, got none", name)
	}
	if !w.Conclusion().AlphaEquals(goal) {
		t.Errorf("%s: conclusion = %v, want %v", name, w.Conclusion(), goal)
	}
	hypsAmong(t, name, w, hyps)
}

func TestRealLinProve(t *testing.T) {
	// transitivity: x<y, y<z ⊢ x<z
	checkRealProve(t, "trans", rb("x < z"), rb("x < y"), rb("y < z"))
	// weakening: x<y ⊢ x≤y
	checkRealProve(t, "lt⇒le", rb("x <= y"), rb("x < y"))
	// antisymmetry (the `=` path): x≤y, y≤x ⊢ x=y
	checkRealProve(t, "antisym", rb("x = y"), rb("x <= y"), rb("y <= x"))
	// constant slack: &2≤x ⊢ &1≤x
	checkRealProve(t, "const", rb("&1 <= x"), rb("&2 <= x"))
	// `>` goal via the bridge: x<y ⊢ y>x
	checkRealProve(t, "gt-bridge", rb("y > x"), rb("x < y"))
}

func TestRealLinProve_Unprovable(t *testing.T) {
	// x<y does NOT entail y<x — the negation is ℚ-satisfiable, so ok=false.
	if _, ok := RealLinProve(seqOf(rb("x < y")), rb("y < x")); ok {
		t.Errorf("y<x should not be provable from x<y")
	}
}

// TestRealCondPin_FoldsUnderGuard pins the syntactic pin fold behind every
// real case split (realCondSplit → realCondPin): for each piecewise operator
// the split's two pins read `{guard} ⊢ atom = value₀` and `{¬guard} ⊢ atom =
// value₁`, the guard read off the operator's defining COND and no decider
// consulted — the branch values are the def's own arms, unsimplified.
func TestRealCondPin_FoldsUnderGuard(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	x, a, b := realVar("x"), realVar("a"), realVar("b")
	zero, one := realLit(0), realLit(1)
	cases := []struct {
		name                string
		atom, guard, v0, v1 Term
	}{
		{"abs", realAbsT(x), realLeT(zero, x), x, realNegT(x)},
		{"max", realMaxT(a, b), realLeT(a, b), b, a},
		{"min", realMinT(a, b), realLeT(a, b), a, b},
		{"sgn", realSgnT(x), realLtT(zero, x), one, ext.Cond(realLtT(x, zero), realNegT(one), zero)},
		{"cond", ext.Cond(realLtT(a, b), a, b), realLtT(a, b), a, b},
	}
	for _, c := range cases {
		sa, ok := realFirstSplittable(nil, c.atom, nil)
		if !ok {
			t.Fatalf("%s: no split candidate in %v", c.name, c.atom)
		}
		if !sa.atom.AlphaEquals(c.atom) {
			t.Fatalf("%s: split on %v, want %v", c.name, sa.atom, c.atom)
		}
		for i, want := range []struct{ hyp, value Term }{{c.guard, c.v0}, {not(c.guard), c.v1}} {
			facts := sa.branches[i].facts
			pin := facts[len(facts)-1]
			if !pin.Conclusion().AlphaEquals(eqT(c.atom, want.value)) {
				t.Errorf("%s branch %d: pin %v, want %v = %v", c.name, i, pin.Conclusion(), c.atom, want.value)
			}
			if !slices.ContainsFunc(pin.Hyps(), want.hyp.AlphaEquals) {
				t.Errorf("%s branch %d: pin hyps %v lack %v", c.name, i, pin.Hyps(), want.hyp)
			}
		}
	}
}

// TestRealSplitCandidates_BinderFree pins the candidate walks behind the real
// case splits (realFirstSplittable / realComparisonAtomsOf): an operator or
// comparison atom under an enclosing ∀ is no candidate; the same shape free
// is.
func TestRealSplitCandidates_BinderFree(t *testing.T) {
	SetRealLemmaBundle(&RealLemmaBundle{})
	t.Cleanup(func() { SetRealLemmaBundle(nil) })
	x, a, b := realVar("x"), realVar("a"), realVar("b")
	bound := ext.ForAll(x)(realLeT(realLit(0), realAbsT(x))) // ∀x. &0 ≤ |x|
	if sa, ok := realFirstSplittable([]Term{bound}, realLeT(a, b), nil); ok {
		t.Errorf("|x| under ∀x offered as a split candidate: %v", sa.atom)
	}
	if sa, ok := realFirstSplittable([]Term{bound}, realLeT(a, realAbsT(a)), nil); !ok || !sa.atom.AlphaEquals(realAbsT(a)) {
		t.Errorf("free |a| not the split candidate: ok=%v atom=%v", ok, sa.atom)
	}
	atoms := realComparisonAtomsOf(and(ext.ForAll(x)(realLeT(x, a)), realLeT(a, b)))
	if len(atoms) != 1 || !atoms[0].AlphaEquals(realLeT(a, b)) {
		t.Errorf("comparison atoms under ∀x collected: %v", atoms)
	}
}

// TestRealNonzeroEvidence: the field layer divides by what the context shows
// nonzero, in each form the context holds that (real_nonzero.go) — the square
// the arith step rewrites a resident `x ≠ &0` into, a disequality or a
// positive absolute value that `z = &0` would contradict.
func TestRealNonzeroEvidence(t *testing.T) {
	installTestBundle(t)
	x, c := realVar("x"), realVar("c")
	offset := realSubT(x, c)
	zero := realLit(0)
	evidence := []struct {
		name string
		hyps []Term
		of   Term
	}{
		{"as written", []Term{not(eqT(x, zero))}, x},
		{"in the square form", []Term{realLtT(zero, realStarT(x, x))}, x},
		{"from a positive sign", []Term{realLtT(zero, x)}, x},
		{"from a negative sign", []Term{realLtT(x, zero)}, x},
		{"a difference, from the order of its terms", []Term{realLtT(c, x)}, offset},
		{"a difference, from its terms differing", []Term{not(eqT(x, c))}, offset},
		{"a difference, from a positive distance", []Term{realLtT(zero, realAbsT(offset))}, offset},
		{"a difference, from the square of the reversed one",
			[]Term{realLtT(zero, realStarT(realSubT(c, x), realSubT(c, x)))}, offset},
	}
	for _, e := range evidence {
		t.Run(e.name, func(t *testing.T) {
			w := realProveNeqZero(e.hyps, e.of)
			if w == nil {
				t.Fatalf("no evidence that %v is nonzero under %v", e.of, e.hyps)
			}
			if !w.Conclusion().AlphaEquals(not(eqT(e.of, zero))) {
				t.Errorf("proved %v", w.Conclusion())
			}
			for _, h := range w.Hyps() {
				if !slices.ContainsFunc(e.hyps, h.AlphaEquals) {
					t.Errorf("the evidence rests on %v, not a hypothesis", h)
				}
			}
		})
	}
	if w := realProveNeqZero([]Term{realLeT(zero, x)}, x); w != nil {
		t.Errorf("read `&0 ≤ x` as evidence that x is nonzero: %v", w.Conclusion())
	}
	if w := realProveNeqZero([]Term{not(eqT(x, c))}, x); w != nil {
		t.Errorf("read `x ≠ c` as evidence that x is nonzero: %v", w.Conclusion())
	}
	// The cancellation and the disequality goal, on that evidence.
	realDecidesTrue(t, "0<x·x ⊢ x·inv x=&1",
		eqT(realStarT(x, realInvT(x)), realLit(1)), realLtT(zero, realStarT(x, x)))
	realDecidesTrue(t, "x≠c ⊢ x−c≠&0", not(eqT(offset, zero)), not(eqT(x, c)))
	realDecidesTrue(t, "0<|x−c| ⊢ x−c≠&0", not(eqT(offset, zero)), realLtT(zero, realAbsT(offset)))
}

// TestRealUnitFacts: a factor and its inverse cancel wherever they stand in
// a monomial (real_unit_facts.go) — split across a product, behind a
// quotient, or only after the product is multiplied out.
func TestRealUnitFacts(t *testing.T) {
	installTestBundle(t)
	split := realStarT(realStarT(rr("a"), realInvT(rr("v"))), rr("v")) // (a · inv v) · v
	rows := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"the pair split across a product", []Term{pb("&0 < v")}, eqT(split, rr("a"))},
		{"behind a quotient", []Term{pb("&0 < v")}, pb("a / v * v = a")},
		{"a difference quotient times its offset",
			[]Term{not(eqT(rr("x"), rr("c")))}, pb("(f - p) / (x - c) * (x - c) = f - p")},
		{"the same, from a positive distance",
			[]Term{realLtT(realLit(0), realAbsT(rr("x - c")))}, pb("f = p + (f - p) / (x - c) * (x - c)")},
		{"two pairs, after multiplying out",
			[]Term{pb("&0 < u"), pb("&0 < l")},
			eqT(realStarT(realSubT(realInvT(rr("u")), realInvT(rr("l"))), rr("u * l")), rr("l - u"))},
		{"in an order", []Term{pb("&0 < v"), pb("a <= b")}, pb("a / v * v <= b")},
		// The chord's slope times the run is the rise (the mean value theorem).
		{"a divisor that is a positive difference",
			[]Term{pb("a < b")}, pb("(q - p) / (b - a) * (b - a) = q - p")},
		{"the adjacent pair still folds", []Term{pb("&0 < v")},
			eqT(realStarT(rr("a"), realStarT(rr("v"), realInvT(rr("v")))), rr("a"))},
		// Several pairs in ONE monomial: the second pair's cancellation is
		// read off the monomial the first pair's fact reduces it to.
		{"two pairs in one monomial", []Term{pb("&0 < u"), pb("&0 < l")}, pb("x / u * (y / l) * (u * l) = x * y")},
		{"three pairs in one monomial", []Term{pb("&0 < u"), pb("&0 < l"), pb("&0 < v")},
			pb("x / u * (y / l) * (z / v) * (u * l * v) = x * y * z")},
		{"two pairs under an order", []Term{pb("&0 < u"), pb("&0 < l"), pb("x * y <= c")},
			pb("x / u * (y / l) * (u * l) <= c")},
		// The inverse of a product is the product of the inverses, so a
		// divisor that is a product cancels factor by factor — on each
		// factor's own evidence, or on the product's.
		{"a quotient by a product", []Term{pb("&0 < u"), pb("&0 < l")}, pb("x / (u * l) * u * l = x")},
		{"a quotient by a product, one factor cancelled", []Term{pb("&0 < l")}, pb("x / (u * l) * l = x / u")},
		{"a quotient by a product, the product's sign the evidence", []Term{pb("&0 < u * l")}, pb("x / (u * l) * u * l = x")},
		{"a quotient by a product, the product nonzero the evidence",
			[]Term{not(eqT(rr("u * l"), realLit(0)))}, pb("x / (u * l) * (u * l) = x")},
	}
	for _, r := range rows {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// No evidence, no fact: v · inv v is not &1 at v = &0.
	if realDecides(t, nil, eqT(split, rr("a"))) {
		t.Error("cancelled v against its inverse with no evidence that v is nonzero")
	}
	if realDecides(t, []Term{pb("&0 <= v")}, pb("a / v * v = a")) {
		t.Error("cancelled v against its inverse from `&0 ≤ v`")
	}
	if facts := realUnitFacts([]Term{pb("&0 < w")}, pb("a / v * v = a")); len(facts) != 0 {
		t.Errorf("injected %d fact(s) about a divisor the context does not show nonzero", len(facts))
	}
	// A product of quotients is the quotient of the products with no
	// evidence at all: both sides are read in one basis.
	if !realDecides(t, nil, pb("x / u * (y / l) = x * y / (u * l)")) {
		t.Error("declined x/u · (y/l) = x·y / (u·l), a ring identity under the inverse basis")
	}
	// Two pairs, one divisor without evidence: its pair stays.
	if realDecides(t, []Term{pb("&0 < u")}, pb("x / u * (y / l) * (u * l) = x * y")) {
		t.Error("cancelled l against its inverse with no evidence that l is nonzero")
	}
	// The rounds: two pairs in one monomial ask for each pair under the
	// other's and, on the reduced monomial, each pair alone.
	if facts := realUnitFacts([]Term{pb("&0 < u"), pb("&0 < l")}, pb("x / u * (y / l) * (u * l) = x * y")); len(facts) != 4 {
		t.Errorf("got %d facts for two pairs in one monomial; want 4", len(facts))
	}
	// One fact per cofactor in sight, and none read off an injected fact.
	hyps := []Term{pb("&0 < v")}
	goal := pb("a / v * v = a")
	facts := realUnitFacts(hyps, goal)
	if len(facts) != 1 {
		t.Fatalf("got %d facts for one pair with one cofactor", len(facts))
	}
	if !realIsUnitFact(facts[0].Conclusion()) {
		t.Errorf("the injected fact is not recognized as one: %v", facts[0].Conclusion())
	}
	if again := realUnitFacts(append(hyps, facts[0].Conclusion()), goal); len(again) != 0 {
		t.Errorf("the re-entry injected %d more fact(s)", len(again))
	}
}

// TestRealStepMemos: the linear prover's answers and the decide chain's are
// memoized per question — the hypotheses in their order and the goal — and
// for the step alone (real_linarith.go linProveMemo, ReleaseStepMemos).
func TestRealStepMemos(t *testing.T) {
	installTestBundle(t)
	ReleaseStepMemos()
	hyps := []Term{pb("a <= b"), pb("b <= c")}
	goal := pb("a <= c")

	// The same question is answered from the memo, a proof and a decline
	// alike.
	first, ok := RealLinProve(slices.Values(hyps), goal)
	if !ok {
		t.Fatalf("declined %v under %v", goal, hyps)
	}
	if again, ok := RealLinProve(slices.Values(hyps), goal); !ok || again != first {
		t.Error("the second asking of a question was not answered from the memo")
	}
	if _, ok := RealLinProve(slices.Values(hyps), pb("c <= a")); ok {
		t.Fatal("proved c ≤ a from a ≤ b and b ≤ c")
	}
	if e, hit := realLinMemo.lookup(linQuestionKey(hyps, pb("c <= a")), hyps, pb("c <= a")); !hit || e.proof != nil {
		t.Error("a decline was not kept")
	}

	// Another context is another question: the goal under fewer hypotheses
	// is not handed the proof that rests on the missing one, and the
	// decide chain is not either.
	if w, ok := RealLinProve(slices.Values(hyps[:1]), goal); ok {
		t.Errorf("a ≤ c from a ≤ b alone, resting on %v", w.Hyps())
	}
	if _, ok := realProveDecAtom(slices.Values(hyps), goal); !ok {
		t.Fatalf("the decide chain declined %v under %v", goal, hyps)
	}
	if w, ok := realProveDecAtom(slices.Values(hyps[:1]), goal); ok {
		t.Errorf("the decide chain: a ≤ c from a ≤ b alone, resting on %v", w.Hyps())
	}
	// The order of the hypotheses is part of the question; the answer is
	// the same, from a run of its own.
	swapped := []Term{hyps[1], hyps[0]}
	if _, hit := realLinMemo.lookup(linQuestionKey(swapped, goal), swapped, goal); hit {
		t.Error("the memo answered a question it was never asked")
	}
	if _, ok := RealLinProve(slices.Values(swapped), goal); !ok {
		t.Error("declined the goal with its hypotheses in the other order")
	}

	// The proofs are bounded apart from the declines.
	ReleaseStepMemos()
	for i := range linMemoProofCap + 3 {
		realLinMemo.store(linQuestionKey(nil, realLit(uint64(i))), linAnswer{goal: realLit(uint64(i)), proof: first})
	}
	if kept := len(realLinMemo.proofs); kept > linMemoProofCap {
		t.Errorf("%d proofs kept, the bound is %d", kept, linMemoProofCap)
	}

	// The step's end releases every one of them.
	RealLinProve(slices.Values(hyps), goal)
	realProveDecAtom(slices.Values(hyps), goal)
	realSignBridge(rr("a * b"), rr("b * a"))
	_, linHeld := realLinMemo.lookup(linQuestionKey(hyps, goal), hyps, goal)
	_, decHeld := realDecMemo.lookup(linQuestionKey(hyps, goal), hyps, goal)
	_, bridgeHeld := realSignBridgeMemo.lookup(rr("a * b"), rr("b * a"))
	if !linHeld || !decHeld || !bridgeHeld {
		t.Fatalf("before the release: linear %v, decide %v, sign rows %v", linHeld, decHeld, bridgeHeld)
	}
	ReleaseStepMemos()
	if _, hit := realLinMemo.lookup(linQuestionKey(hyps, goal), hyps, goal); hit {
		t.Error("the linear prover's memo outlived the step")
	}
	if _, hit := realDecMemo.lookup(linQuestionKey(hyps, goal), hyps, goal); hit {
		t.Error("the decide chain's memo outlived the step")
	}
	if _, hit := realSignBridgeMemo.lookup(rr("a * b"), rr("b * a")); hit {
		t.Error("the sign rows' memo outlived the step")
	}
}

// TestRealNeqZero_FactorOfANonzeroProduct: a factor of what the context
// shows nonzero is nonzero — the evidence a divisor a·b hands its factors
// once inv(a·b) is read as inv(a)·inv(b) (real_nonzero.go realEqUnderZero).
func TestRealNeqZero_FactorOfANonzeroProduct(t *testing.T) {
	installTestBundle(t)
	a, b, c := realVar("a"), realVar("b"), realVar("c")
	zero := realLit(0)
	ab := realStarT(a, b)
	for _, row := range []struct {
		name string
		hyp  Term
		of   Term
	}{
		{"a disequality of the product, its left factor", not(eqT(ab, zero)), a},
		{"a disequality of the product, its right factor", not(eqT(ab, zero)), b},
		{"the disequality turned round", not(eqT(zero, ab)), a},
		{"a strict sign of the product", realLtT(zero, ab), b},
		{"a negative product", realLtT(ab, zero), a},
		{"a factor of a longer product", not(eqT(realStarT(ab, c), zero)), b},
		{"a product on each side", realLtT(realStarT(a, c), ab), a},
	} {
		w := realProveNeqZero([]Term{row.hyp}, row.of)
		if w == nil {
			t.Errorf("%s: no evidence that %v is nonzero under %v", row.name, row.of, row.hyp)
			continue
		}
		if !w.Conclusion().AlphaEquals(not(eqT(row.of, zero))) {
			t.Errorf("%s: proved %v", row.name, w.Conclusion())
		}
		if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(row.hyp) {
			t.Errorf("%s: the evidence does not rest on the resident fact alone", row.name)
		}
	}
	// A summand of a nonzero sum may be zero, and so may a factor of one
	// side where the other side does not vanish with it.
	if w := realProveNeqZero([]Term{not(eqT(realPlusT(a, b), zero))}, a); w != nil {
		t.Errorf("read `a + b ≠ &0` as evidence that a is nonzero: %v", w.Conclusion())
	}
	if w := realProveNeqZero([]Term{realLtT(c, ab)}, a); w != nil {
		t.Errorf("read `c < a·b` as evidence that a is nonzero: %v", w.Conclusion())
	}
}

// TestRealNeqZero_ZeroPutEndsAndRespectsBinders: the substitution of &0 for
// the divisor ends where the divisor is &0 itself — there is nothing to put,
// and no evidence — and leaves alone a bound variable that carries the
// divisor's name.
func TestRealNeqZero_ZeroPutEndsAndRespectsBinders(t *testing.T) {
	installTestBundle(t)
	a, b := realVar("a"), realVar("b")
	zero := realLit(0)
	for _, hyp := range []Term{not(eqT(a, zero)), not(eqT(realStarT(a, b), zero)), realLtT(zero, realStarT(a, b))} {
		if w := realProveNeqZero([]Term{hyp}, zero); w != nil {
			t.Errorf("read %v as evidence that &0 is nonzero: %v", hyp, w.Conclusion())
		}
	}
	if realDecides(t, []Term{pb("~(a = &0)")}, pb("x / &0 * &0 = x")) {
		t.Error("cancelled a division by &0")
	}

	realToReal := core.MakeFun(dsl.RealType, dsl.RealType)
	g := ext.Var("g", core.MakeFun(realToReal, dsl.RealType))
	inner := ext.Var("a", dsl.RealType)
	bound := ext.Apply(g, core.Abs(inner.AssertVar(), realPlusT(inner, realLit(1)))) // g(λa. a + &1)
	hyp := not(eqT(realStarT(a, bound), zero))
	w := realProveNeqZero([]Term{hyp}, a)
	if w == nil {
		t.Fatalf("no evidence that a is nonzero under %v", hyp)
	}
	if !w.Conclusion().AlphaEquals(not(eqT(a, zero))) {
		t.Errorf("proved %v", w.Conclusion())
	}
	if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(hyp) {
		t.Error("the evidence does not rest on the resident fact alone")
	}
}
