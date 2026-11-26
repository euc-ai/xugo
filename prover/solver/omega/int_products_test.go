package omega

// The degree-2 products pass over ℤ (int_products.go): real_products_test.go's
// shapes on the int vocabulary.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
)

func TestIntProducts_NlinarithShapes(t *testing.T) {
	installTestBundle(t)
	x, y, z, a, b, c, d, s := intVar("x"), intVar("y"), intVar("z"), intVar("a"), intVar("b"), intVar("c"), intVar("d"), intVar("s")
	zero, one := intLit(0), intLit(1)
	closes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"the converse of a sign row: x·y = 1 ∧ 0 < x ⊢ 0 < y",
			[]Term{eqT(intStarT(x, y), one), intLtT(zero, x)}, intLtT(zero, y)},
		{"a square root's sign: 0 ≤ s ∧ s·s = y ∧ 0 < y ⊢ 0 < s",
			[]Term{intLeT(zero, s), eqT(intStarT(s, s), y), intLtT(zero, y)}, intLtT(zero, s)},
		{"a product of two hypotheses: a ≤ b ∧ c ≤ d ⊢ a·d + b·c ≤ a·c + b·d",
			[]Term{intLeT(a, b), intLeT(c, d)},
			intLeT(intPlusT(intStarT(a, d), intStarT(b, c)), intPlusT(intStarT(a, c), intStarT(b, d)))},
		{"mixed strictness: 0 < a ∧ 0 ≤ b ∧ a·b ≤ c ⊢ 0 ≤ c",
			[]Term{intLtT(zero, a), intLeT(zero, b), intLeT(intStarT(a, b), c)}, intLeT(zero, c)},
		{"an equation times a sign: x·y = z ∧ 0 ≤ x ∧ 0 ≤ y ⊢ 0 ≤ z",
			[]Term{eqT(intStarT(x, y), z), intLeT(zero, x), intLeT(zero, y)}, intLeT(zero, z)},
		{"a strict difference times a non-strict one: a point of a segment",
			[]Term{intLeT(zero, s), intLeT(s, one), intLtT(x, y)},
			intLeT(x, intPlusT(intStarT(s, x), intStarT(intSubT(one, s), y)))},
	}
	for _, r := range closes {
		t.Run(r.name, func(t *testing.T) {
			if !intDecides(t, r.hyps, r.goal) {
				t.Errorf("declined %v under %v", r.goal, r.hyps)
			}
		})
	}
	if intDecides(t, []Term{intLeT(a, b)}, intLeT(intStarT(a, c), intStarT(b, c))) {
		t.Error("a ≤ b must not decide a·c ≤ b·c: nothing bounds c")
	}
	w, ok := intProveProducts([]Term{eqT(intStarT(x, y), one), intLtT(zero, x)}, intLtT(zero, y))
	if !ok {
		t.Fatal("intProveProducts declined x·y = 1 ∧ 0 < x ⊢ 0 < y")
	}
	hyps := []Term{eqT(intStarT(x, y), one), intLtT(zero, x)}
	for i := 0; i < w.NumHyps(); i++ {
		if !slices.ContainsFunc(hyps, w.Hyp(i).AlphaEquals) {
			t.Errorf("stray hypothesis %v not among the goal's", w.Hyp(i))
		}
	}
	if _, ok := intProveProducts([]Term{intLeT(a, b)}, intLeT(a, intPlusT(b, one))); ok {
		t.Error("the products pass must leave a linear context alone")
	}
}

// TestIntWeakenLt: the weakening reads neither side, so a difference carrying
// a subtraction weakens as a variable does, over the strict fact's own
// hypotheses.
func TestIntWeakenLt(t *testing.T) {
	installTestBundle(t)
	x, y := intVar("x"), intVar("y")
	for _, d := range []Term{y, intSubT(y, x), intStarT(intSubT(y, x), x)} {
		strict := intLtT(intLit(0), d)
		w := intWeakenLt(intLit(0), d, prop.Assume(strict))
		if !w.Conclusion().AlphaEquals(intLeT(intLit(0), d)) {
			t.Errorf("conclusion = %v; want &0 ≤ %v", w.Conclusion(), d)
		}
		if w.NumHyps() != 1 || !w.Hyp(0).AlphaEquals(strict) {
			t.Errorf("weakening of %v does not rest on the strict fact alone", strict)
		}
	}
}

// TestIntProducts_ProvesTheModelsProducts: over ℤ as over ℝ, the model's
// refutation names the products it combines and those alone, proved,
// refute; and it reads the sign rows, so a product beside a square's
// unconditional sign is found.
func TestIntProducts_ProvesTheModelsProducts(t *testing.T) {
	installTestBundle(t)
	x, y, a, b, c, d := intVar("x"), intVar("y"), intVar("a"), intVar("b"), intVar("c"), intVar("d")
	zero, one := intLit(0), intLit(1)
	products := intPlusT(intStarT(a, d), intStarT(b, c))
	bound := intPlusT(intStarT(a, c), intStarT(b, d))
	shapes := []struct {
		name string
		hyps []Term
		goal Term
	}{
		{"x·y = 1 ∧ 0 < x ⊢ 0 < y", []Term{eqT(intStarT(x, y), one), intLtT(zero, x)}, intLtT(zero, y)},
		{"a ≤ b ∧ c ≤ d ⊢ a·d + b·c ≤ a·c + b·d", []Term{intLeT(a, b), intLeT(c, d)}, intLeT(products, bound)},
		{"the same beside a square's sign", []Term{intLeT(a, b), intLeT(c, d)},
			intLeT(products, intPlusT(bound, intStarT(x, x)))},
	}
	for _, r := range shapes {
		t.Run(r.name, func(t *testing.T) {
			_, nTerm, _, ok := intNegateGoal(r.goal)
			if !ok {
				t.Fatal("no negation of the goal")
			}
			all := append(slices.Clone(r.hyps), nTerm)
			cs := intDomain.hypConstraints(slices.Values(all))
			used, refutable := intProductsModel(cs)
			if !refutable {
				t.Fatal("the model declined")
			}
			facts := intProductFactsOf(cs, used)
			if len(facts) != len(used) {
				t.Fatalf("the model named %d products and %d were proved", len(used), len(facts))
			}
			if pairs := len(intProductFacts(cs)); len(used) >= pairs {
				t.Errorf("the model named %d products of %d pairs", len(used), pairs)
			}
			if _, ok := intRefuteWithProducts(all, facts); !ok {
				t.Errorf("the %d products the model named do not refute, proved", len(facts))
			}
			if !intDecides(t, r.hyps, r.goal) {
				t.Error("the decider declined")
			}
		})
	}
}
