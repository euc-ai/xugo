package omega

import (
	"iter"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A split branch with nothing left to split, which the linear prover leaves
// open, goes to the domain's leaf prover (caseSplit, engine.go): the pin of
// a disjunctive hypothesis reaches a product there, and so do the guard and
// the pin of an operator's split.

// TestSplitLeaf_Real: a value known up to a finite disjunction, squared.
func TestSplitLeaf_Real(t *testing.T) {
	installTestBundle(t)
	s, y := realVar("s"), realVar("y")
	one := realLit(1)
	disj := or(eqT(s, one), eqT(s, realNegT(one)))
	goal := eqT(realStarT(s, s), one)
	if !realDecides(t, []Term{disj}, goal) {
		t.Error("s = &1 ∨ s = −&1 ⊢ s·s = &1 must close")
	}
	// An operator atom that has nothing to do with the claim is split too;
	// its guard is in no leaf's proof, so the split is pruned.
	if !realDecides(t, []Term{disj, realLeT(realAbsT(y), one)}, goal) {
		t.Error("an unrelated |y| in the context must not cost the close")
	}
	if realDecides(t, []Term{or(eqT(s, one), eqT(s, realLit(2)))}, goal) {
		t.Error("s = &1 ∨ s = &2 does not give s·s = &1")
	}
	// The linear prover alone, with no leaf prover, leaves the branch open.
	if _, ok := realProveSplit(RealLinProve, nil, []Term{disj}, goal, nil); ok {
		t.Error("the split closed with no leaf prover: the branch is not linear")
	}
}

// TestSplitLeaf_Int is the ℤ twin.
func TestSplitLeaf_Int(t *testing.T) {
	installTestBundle(t)
	s := intVar("s")
	one := intLit(1)
	disj := or(eqT(s, one), eqT(s, intNegT(one)))
	goal := eqT(intStarT(s, s), one)
	if !intDecides(t, []Term{disj}, goal) {
		t.Error("s = &1 ∨ s = −&1 ⊢ s·s = &1 must close")
	}
	if intDecides(t, []Term{or(eqT(s, one), eqT(s, intLit(2)))}, goal) {
		t.Error("s = &1 ∨ s = &2 does not give s·s = &1")
	}
	if _, ok := intProveSplit(IntLinProve, nil, []Term{disj}, goal, nil); ok {
		t.Error("the split closed with no leaf prover: the branch is not linear")
	}
}

// TestCaseSplit_LeafOnlyWhereNothingIsLeftToSplit pins the recursion: the
// leaf prover is asked at a branch with no splittable atom left, never at a
// branch a further split takes.
func TestCaseSplit_LeafOnlyWhereNothingIsLeftToSplit(t *testing.T) {
	installTestBundle(t)
	a, b, c := realVar("a"), realVar("b"), realVar("c")
	one := realLit(1)
	h1 := or(eqT(a, one), eqT(a, realLit(2)))
	h2 := or(eqT(b, one), eqT(b, realLit(2)))
	goal := eqT(realStarT(c, c), one) // nothing in the context decides it
	var leafHyps [][]Term
	leaf := func(hyps iter.Seq[Term], _ Term) (*prop.PropWrapper, bool) {
		var hs []Term
		for h := range hyps {
			hs = append(hs, h)
		}
		leafHyps = append(leafHyps, hs)
		return nil, false
	}
	if _, ok := realProveSplit(RealLinProve, leaf, []Term{h1, h2}, goal, nil); ok {
		t.Fatal("proved a claim nothing in the context decides")
	}
	// The first failing leaf ends the split: one call, under both pins.
	if len(leafHyps) != 1 {
		t.Fatalf("the leaf prover was asked %d times; want once", len(leafHyps))
	}
	if len(leafHyps[0]) != 4 {
		t.Errorf("the leaf saw %d hypotheses; want the two disjunctions and a pin of each", len(leafHyps[0]))
	}
	// An operator split asks it as a hypothesis split does, alone or under
	// one: its guard and pin are facts the root's handlers never read.
	contexts := [][]Term{
		{realLeT(realAbsT(a), one)},
		{h1, realLeT(realAbsT(b), one)},
		{not(eqT(a, one)), realLeT(realAbsT(b), one)},
		{imply(realLeT(a, one), realLeT(b, one)), realLeT(realAbsT(b), one)},
	}
	for _, hyps := range contexts {
		leafHyps = nil
		if _, ok := realProveSplit(RealLinProve, leaf, hyps, goal, nil); ok {
			t.Fatal("proved a claim nothing in the context decides")
		}
		if len(leafHyps) != 1 {
			t.Errorf("the leaf prover was asked %d times under %v; want once", len(leafHyps), hyps)
		}
	}
}

// TestCaseSplit_BranchReadAtItsPins: a pinned operator inside a monomial is
// replaced by its arm before the provers are asked again, in the goal and in
// the hypotheses, and the pin's own equation is left out; one that stands
// alone in a linear form stays as spelled, its pin a hypothesis.
func TestCaseSplit_BranchReadAtItsPins(t *testing.T) {
	installTestBundle(t)
	d, w, c := realVar("d"), realVar("w"), realVar("c")
	one := realLit(1)
	capped := realMinT(d, one)
	type question struct {
		hyps []Term
		goal Term
	}
	var asked []question
	leaf := func(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
		asked = append(asked, question{slices.Collect(hyps), goal})
		return nil, false
	}
	holdsCap := func(q question) bool {
		return slices.ContainsFunc(append(slices.Clone(q.hyps), q.goal), func(t Term) bool { return holdsTerm(t, capped) })
	}

	// Under a product: the leaf is asked about d·w, with d ≤ &1 beside it.
	open := eqT(realStarT(c, c), one) // nothing in the context decides it
	hyp := realLeT(realStarT(capped, w), c)
	if _, ok := realProveSplit(RealLinProve, leaf, []Term{hyp}, open, nil); ok {
		t.Fatal("proved a claim nothing in the context decides")
	}
	if len(asked) != 1 {
		t.Fatalf("the leaf prover was asked %d times; want once", len(asked))
	}
	if holdsCap(asked[0]) {
		t.Errorf("the leaf met the capped term under a product: %v ⊢ %v", asked[0].hyps, asked[0].goal)
	}
	if !slices.ContainsFunc(asked[0].hyps, realLeT(realStarT(d, w), c).AlphaEquals) {
		t.Errorf("the leaf's hypotheses lack d·w ≤ c: %v", asked[0].hyps)
	}
	if !slices.ContainsFunc(asked[0].hyps, realLeT(d, one).AlphaEquals) {
		t.Errorf("the leaf's hypotheses lack the guard d ≤ &1: %v", asked[0].hyps)
	}

	// Alone in a linear form: the leaf is asked about the branch as spelled.
	asked = nil
	if _, ok := realProveSplit(RealLinProve, leaf, []Term{realLeT(capped, c)}, open, nil); ok {
		t.Fatal("proved a claim nothing in the context decides")
	}
	if len(asked) != 1 {
		t.Fatalf("the leaf prover was asked %d times; want once", len(asked))
	}
	if !slices.ContainsFunc(asked[0].hyps, eqT(capped, d).AlphaEquals) {
		t.Errorf("the leaf's hypotheses lack the pin as spelled: %v", asked[0].hyps)
	}
}

// TestPinStandsInAnUnknown: where the linear reader takes a term holding a
// pinned operator as one unknown, and where the pin reaches the operator.
func TestPinStandsInAnUnknown(t *testing.T) {
	installTestBundle(t)
	a, b, w, x := realVar("a"), realVar("b"), realVar("w"), realVar("x")
	one, two := realLit(1), realLit(2)
	capped := realMinT(a, b)
	pin := eqT(capped, a)
	f := ext.Var("f", core.MakeFun(a.Type(), a.Type()))
	bound := ext.Var("u", a.Type())
	rows := []struct {
		name string
		hyps []Term
		goal Term
		pins []Term
		want bool
	}{
		{"a factor of a monomial", nil, realLeT(realStarT(capped, w), w), []Term{pin}, true},
		{"a factor of a hypothesis' monomial", []Term{realLeT(realStarT(w, capped), x)}, realLeT(x, w), []Term{pin}, true},
		{"the argument of an opaque atom", nil, eqT(ext.Apply(f, capped), ext.Apply(f, a)), []Term{pin}, true},
		{"a divisor", nil, realLeT(realDivT(x, capped), x), []Term{pin}, true},
		{"the base of a power", nil, realLeT(realPowT(capped, Numeral(2)), x), []Term{pin}, true},
		{"alone", nil, realLeT(capped, x), []Term{pin}, false},
		{"a numeral multiple in a sum", nil, realLeT(realPlusT(realStarT(two, capped), w), x), []Term{pin}, false},
		{"under a difference and a negation", nil, realLeT(realSubT(x, realNegT(capped)), one), []Term{pin}, false},
		{"inside another pinned operator", nil, realLeT(realAbsT(capped), x),
			[]Term{pin, eqT(realAbsT(capped), capped)}, false},
		{"inside an operator's arm that stands in a monomial", nil, realLeT(realStarT(realAbsT(capped), w), x),
			[]Term{pin, eqT(realAbsT(capped), capped)}, true},
		{"in a quantified hypothesis alone",
			[]Term{ext.ForAll(bound)(realLeT(realStarT(capped, bound), x))}, realLeT(x, w), []Term{pin}, false},
		{"no pin", nil, realLeT(realStarT(capped, w), w), nil, false},
	}
	for _, r := range rows {
		if got := realDomain.pinStandsInAnUnknown(r.hyps, r.goal, r.pins); got != r.want {
			t.Errorf("%s: got %v, want %v", r.name, got, r.want)
		}
	}
}

// TestReadAtPins: an operator that holds another, and one pinned to
// another, read as their pins spell them; and what is proved of the reading
// carried back to the branch as spelled.
func TestReadAtPins(t *testing.T) {
	installTestBundle(t)
	x, w, c := realVar("x"), realVar("w"), realVar("c")
	zero, one := realLit(0), realLit(1)

	// real_min(|x|, &1) pinned to |x|, and |x| to x, in either order.
	abs := realAbsT(x)
	capped := realMinT(abs, one)
	pinAbs, pinCap := eqT(abs, x), eqT(capped, abs)
	for _, pins := range [][]Term{{pinAbs, pinCap}, {pinCap, pinAbs}} {
		goal := realLeT(realStarT(capped, w), realPlusT(abs, c))
		r := readBranch(slices.Concat(pins, []Term{realLeT(abs, one)}), goal, pins, nil)
		if want := realLeT(realStarT(x, w), realPlusT(x, c)); !r.goal.AlphaEquals(want) {
			t.Errorf("pins %v: the goal reads %v; want %v", pins, r.goal, want)
		}
		if len(r.hyps) != 1 || !r.hyps[0].AlphaEquals(realLeT(x, one)) {
			t.Errorf("pins %v: the hypotheses read %v; want the guard at x alone", pins, r.hyps)
		}
	}

	// real_sgn(x) pinned to its inner conditional, and that to a literal.
	sgn := realSgnT(x)
	inner := ext.Cond(realLtT(x, zero), realNegT(one), zero)
	pins := []Term{eqT(sgn, inner), eqT(inner, zero)}
	r := readBranch(pins, realLeT(realStarT(sgn, w), c), pins, nil)
	if want := realLeT(realStarT(zero, w), c); !r.goal.AlphaEquals(want) {
		t.Errorf("the sign reads %v; want %v", r.goal, want)
	}

	// Carried back: a proof of the reading is a proof of the branch.
	hyp := realLeT(realStarT(capped, w), c)
	goal := realLeT(realStarT(abs, w), c)
	branch := []Term{hyp, pinAbs, pinCap}
	r = readBranch(branch, goal, []Term{pinAbs, pinCap}, nil)
	read := realLeT(realStarT(x, w), c)
	if !r.goal.AlphaEquals(read) || len(r.hyps) != 1 || !r.hyps[0].AlphaEquals(read) {
		t.Fatalf("the branch reads %v ⊢ %v; want %v on both sides", r.hyps, r.goal, read)
	}
	back := r.carryBack(prop.Assume(read))
	if !back.Conclusion().AlphaEquals(goal) {
		t.Errorf("carried back to %v; want %v", back.Conclusion(), goal)
	}
	for _, h := range back.Hyps() {
		if !slices.ContainsFunc(branch, h.AlphaEquals) {
			t.Errorf("carried back under %v, no hypothesis of the branch", h)
		}
	}
}
