package omega

// The degree-2 products pass (real_products.go): the nlinarith shapes close,
// the result rests on the goal's hypotheses, and a context with nothing
// nonlinear in it is left to the linear layer.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

func TestRealProducts_NlinarithShapes(t *testing.T) {
	installTestBundle(t)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"the converse of a sign row: x·y = 1 ∧ 0 < x ⊢ 0 < y",
			[]Term{pb("x * y = &1"), pb("&0 < x")}, pb("&0 < y")},
		{"a square root's sign: 0 ≤ s ∧ s·s = y ∧ 0 < y ⊢ 0 < s",
			[]Term{pb("&0 <= s"), pb("s * s = y"), pb("&0 < y")}, pb("&0 < s")},
		{"a product of two hypotheses: a ≤ b ∧ c ≤ d ⊢ a·d + b·c ≤ a·c + b·d",
			[]Term{pb("a <= b"), pb("c <= d")}, pb("a * d + b * c <= a * c + b * d")},
		{"mixed strictness: 0 < a ∧ 0 ≤ b ∧ a·b ≤ c ⊢ 0 ≤ c",
			[]Term{pb("&0 < a"), pb("&0 <= b"), pb("a * b <= c")}, pb("&0 <= c")},
		{"a strict difference times a non-strict one: a point of a segment",
			[]Term{pb("&0 <= t"), pb("t <= &1"), pb("x < y")}, pb("x <= t * x + (&1 - t) * y")},
		{"a strict difference times a non-strict one: a slack product",
			[]Term{pb("t <= &1"), pb("A < r")}, pb("&0 <= (&1 - t) * (r - A)")},
		{"two strict bounds times two non-strict ones: a product below one",
			[]Term{pb("&0 - &1 < a"), pb("a < &1"), pb("&0 <= b"), pb("b <= &1")}, pb("a * b < &1")},
		{"a bound squared: 0 ≤ a ∧ a ≤ b ⊢ a·a ≤ b·b",
			[]Term{pb("&0 <= a"), pb("a <= b")}, pb("a * a <= b * b")},
		{"a strict product: 0 < a ∧ 0 < b ⊢ 0 < a·b + a",
			[]Term{pb("&0 < a"), pb("&0 < b")}, pb("&0 < a * b + a")},
		{"an equation times a sign: x·y = z ∧ 0 ≤ x ∧ 0 ≤ y ⊢ 0 ≤ z",
			[]Term{pb("x * y = z"), pb("&0 <= x"), pb("&0 <= y")}, pb("&0 <= z")},
		{"a goal through ≥", []Term{pb("x * y = &1"), pb("&0 < x")}, pb("y > &0")},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !realDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	// The equality atom under the same facts decides to ⊥ — the ≠ goal.
	if w := RealArithDecideWithHyps([]Term{pb("x * y = &1"), pb("&0 < x")})(pb("y = &0")); w == nil || !prop.Rhs(w).Equals(prop.F) {
		t.Error("x·y = 1 ∧ 0 < x must decide y = 0 to ⊥")
	}
	declines := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"nothing bounds c: a ≤ b ⊢ a·c ≤ b·c", []Term{pb("a <= b")}, pb("a * c <= b * c")},
		{"a false claim: 0 ≤ a ⊢ a·a ≤ a", []Term{pb("&0 <= a")}, pb("a * a <= a")},
		{"a false claim with an equation: x·y = 1 ⊢ 0 < y", []Term{pb("x * y = &1")}, pb("&0 < y")},
	}
	for _, r := range declines {
		t.Run(r.name, func(t *testing.T) {
			if realDecides(t, r.hyps, r.goal) {
				t.Errorf("decided %v under %v, which does not follow", r.goal, r.hyps)
			}
		})
	}
}

// TestRealProducts_HypSubset: the products are cut back, so the result's
// hypotheses are the goal's and nothing injected survives.
func TestRealProducts_HypSubset(t *testing.T) {
	installTestBundle(t)
	hyps := []Term{pb("x * y = &1"), pb("&0 < x")}
	w, ok := realProveProducts(hyps, pb("&0 < y"))
	if !ok {
		t.Fatal("realProveProducts declined x·y = 1 ∧ 0 < x ⊢ 0 < y")
	}
	if !w.Conclusion().AlphaEquals(pb("&0 < y")) {
		t.Errorf("conclusion = %v", w.Conclusion())
	}
	for i := 0; i < w.NumHyps(); i++ {
		if !slices.ContainsFunc(hyps, w.Hyp(i).AlphaEquals) {
			t.Errorf("stray hypothesis %v not among the goal's", w.Hyp(i))
		}
	}
}

// TestRealProducts_LinearContextDeclines: with no product monomial anywhere
// the pass does not run — a linear question is the linear layer's.
func TestRealProducts_LinearContextDeclines(t *testing.T) {
	installTestBundle(t)
	if _, ok := realProveProducts([]Term{pb("a <= b")}, pb("a <= b + &1")); ok {
		t.Error("the products pass must leave a linear context alone")
	}
	cs := realDomain.hypConstraints(slices.Values([]Term{pb("a <= b"), pb("b < a")}))
	if realHasProductContent(cs) {
		t.Error("a linear constraint set reported product content")
	}
}

// TestRealProducts_Facts: the base differences and their products are built
// as stated — `{l ≤ r} ⊢ &0 ≤ r − l`, and `{…} ⊢ &0 ≤ d₁·d₂`.
func TestRealProducts_Facts(t *testing.T) {
	installTestBundle(t)
	w := prop.Assume(pb("a <= b"))
	f, ok := realDiffFact(rr("a"), rr("b"), w, false)
	if !ok {
		t.Fatal("realDiffFact declined a ≤ b")
	}
	if !f.proof.Conclusion().AlphaEquals(pb("&0 <= b - a")) {
		t.Errorf("difference fact concludes %v", f.proof.Conclusion())
	}
	if f.proof.NumHyps() != 1 || !f.proof.Hyp(0).AlphaEquals(pb("a <= b")) {
		t.Errorf("difference fact rests on %v", f.proof.Hyps())
	}
	cs := realDomain.hypConstraints(slices.Values([]Term{pb("a <= b"), pb("&0 < c")}))
	facts := realProductFacts(cs)
	if len(facts) != 3 {
		t.Fatalf("two facts give three products, got %d", len(facts))
	}
	want := []Term{pb("&0 <= (b - a) * (b - a)"), pb("&0 <= (b - a) * c"), pb("&0 < c * c")}
	for i, f := range facts {
		if !f.Conclusion().AlphaEquals(want[i]) {
			t.Errorf("product %d concludes %v, want %v", i, f.Conclusion(), want[i])
		}
	}
}

// TestRealWeakenLt: the weakening reads neither side, so a difference
// carrying a subtraction — which the linear prover does not take as a goal
// side — weakens as a variable does, over the strict fact's own hypotheses.
func TestRealWeakenLt(t *testing.T) {
	installTestBundle(t)
	x, y, tt := realVar("x"), realVar("y"), realVar("t")
	for _, d := range []Term{y, realSubT(y, x), realSubT(realLit(1), tt), realStarT(realSubT(y, x), tt)} {
		strict := realLtT(realLit(0), d)
		w := realWeakenLt(realLit(0), d, prop.Assume(strict))
		if !w.Conclusion().AlphaEquals(realLeT(realLit(0), d)) {
			t.Errorf("conclusion = %v; want &0 ≤ %v", w.Conclusion(), d)
		}
		if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(strict) {
			t.Errorf("weakening of %v does not rest on the strict fact alone", strict)
		}
	}
}

// realProductsContext is what the products pass reads for `{hyps} ⊢ goal`:
// the hypotheses beside the negated goal, and their constraints.
func realProductsContext(t *testing.T, hyps []Term, goal Term) ([]Term, []LinConstraint) {
	t.Helper()
	_, nTerm, _, ok := realNegateGoal(goal)
	if !ok {
		t.Fatalf("no negation of the goal %s", ext.PrintTerm(goal))
	}
	all := append(slices.Clone(hyps), nTerm)
	return all, realDomain.hypConstraints(slices.Values(all))
}

// TestRealProducts_ProvesTheModelsProducts: the model's refutation names the
// products it combines, fewer than the pairs, and those alone, proved,
// refute — the proving half is not at every pair on these shapes.
func TestRealProducts_ProvesTheModelsProducts(t *testing.T) {
	installTestBundle(t)
	shapes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"x·y = 1 ∧ 0 < x ⊢ 0 < y", []Term{pb("x * y = &1"), pb("&0 < x")}, pb("&0 < y")},
		{"a ≤ b ∧ c ≤ d ⊢ a·d + b·c ≤ a·c + b·d",
			[]Term{pb("a <= b"), pb("c <= d")}, pb("a * d + b * c <= a * c + b * d")},
		{"0 < a ∧ 0 ≤ b ∧ a·b ≤ c ⊢ 0 ≤ c", []Term{pb("&0 < a"), pb("&0 <= b"), pb("a * b <= c")}, pb("&0 <= c")},
		{"0 ≤ a ∧ a ≤ b ⊢ a·a ≤ b·b", []Term{pb("&0 <= a"), pb("a <= b")}, pb("a * a <= b * b")},
		{"−1 < a < 1 ∧ 0 ≤ b ≤ 1 ⊢ a·b < 1",
			[]Term{pb("&0 - &1 < a"), pb("a < &1"), pb("&0 <= b"), pb("b <= &1")}, pb("a * b < &1")},
		// The negated goal is the equation y = &0, and its two differences
		// times the sign of x are product rows that state the sign of x·y:
		// the refutation combines one of them under its own pair.
		{"x·y = 1 ∧ 0 < x ⊢ y ≠ 0", []Term{pb("x * y = &1"), pb("&0 < x")}, not(eqT(rr("y"), realLit(0)))},
	}
	for _, r := range shapes {
		t.Run(r.name, func(t *testing.T) {
			all, cs := realProductsContext(t, r.hyps, r.goal)
			used, refutable := realProductsModel(cs)
			if !refutable {
				t.Fatal("the model declined")
			}
			facts := realProductFactsOf(cs, used)
			if len(facts) != len(used) {
				t.Fatalf("the model named %d products and %d were proved", len(used), len(facts))
			}
			if pairs := len(realProductFacts(cs)); len(used) >= pairs {
				t.Errorf("the model named %d products of %d pairs", len(used), pairs)
			}
			if _, ok := realRefuteWithProducts(all, facts); !ok {
				t.Errorf("the %d products the model named do not refute, proved", len(facts))
			}
		})
	}

	// The pair is the product of the differences it names.
	_, cs := realProductsContext(t, []Term{pb("a <= b"), pb("c <= d")}, pb("a * d + b * c <= a * c + b * d"))
	used, _ := realProductsModel(cs)
	facts := realProductFactsOf(cs, used)
	if len(facts) != 1 || !facts[0].Conclusion().AlphaEquals(pb("&0 <= (b - a) * (d - c)")) {
		t.Errorf("the model named %d products for (b − a)·(d − c); the first proved is %v", len(used), facts)
	}
}

// TestRealProducts_ModelReadsSignRows: a refutation that needs a product of
// two hypotheses and a square's unconditional sign is the model's to find —
// it reads the sign rows the proving half reads — in the context that
// states it, where no hypothesis bounds the squared term and no case split
// opens.
func TestRealProducts_ModelReadsSignRows(t *testing.T) {
	installTestBundle(t)
	hyps := []Term{pb("a <= b"), pb("c <= d")}
	goal := pb("a * d + b * c <= a * c + b * d + x * x")
	_, cs := realProductsContext(t, hyps, goal)
	used, refutable := realProductsModel(cs)
	if !refutable {
		t.Fatal("the model declined a product beside a square's sign")
	}
	if len(used) != 1 {
		t.Errorf("the model named %d products, the refutation is one product and the square's sign", len(used))
	}
	w, ok := realProveProducts(hyps, goal)
	if !ok {
		t.Fatal("realProveProducts declined a product beside a square's sign")
	}
	for i := 0; i < w.NumHyps(); i++ {
		if !slices.ContainsFunc(hyps, w.Hyp(i).AlphaEquals) {
			t.Errorf("stray hypothesis %v not among the goal's", w.Hyp(i))
		}
	}
	if !realDecides(t, hyps, goal) {
		t.Error("the decider declined a product beside a square's sign")
	}
}
