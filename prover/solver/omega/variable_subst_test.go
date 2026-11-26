package omega

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// ruleFor is the rewrite the rule set of hyps gives the variable v at the
// carriers elem names, or nil.
func ruleFor(hyps []Term, elem func(Term) bool, v Term) *prop.PropWrapper {
	return eqHypSubst(hyps, elem, ArithPolicy{})(v)
}

// A value on either side defines the variable; the rewrite carries its
// hypothesis and fires on no other variable.
func TestVarEqSubst_AValueDefinesItsVariable(t *testing.T) {
	n, m, two := numVar("n"), numVar("m"), Numeral(2)
	for _, h := range []Term{eqT(n, two), eqT(two, n)} {
		w := ruleFor([]Term{h}, isNat, n)
		if w == nil || !w.Conclusion().AlphaEquals(eqT(n, two)) {
			t.Fatalf("%v: n must read as 2, got %v", h, w)
		}
		if !w.HasHyp(h) {
			t.Errorf("%v: the rewrite must carry its hypothesis", h)
		}
		if ruleFor([]Term{h}, isNat, m) != nil {
			t.Errorf("%v: the rule fired on m", h)
		}
	}
	if ruleFor([]Term{le(n, two)}, isNat, n) != nil {
		t.Error("a comparison is no definition")
	}
}

// The rule is one at every carrier: the same shapes define a real and an
// integer variable, and a carrier elem leaves out is not read.
func TestVarEqSubst_EveryCarrier(t *testing.T) {
	x, i := realVar("x"), intVar("i")
	hx, hi := eqT(x, realLit(0)), eqT(i, intLit(0))
	hyps := []Term{hx, hi}
	if w := ruleFor(hyps, carrierElem, x); w == nil || !w.Conclusion().AlphaEquals(hx) {
		t.Errorf("real: x must read as &0, got %v", w)
	}
	if w := ruleFor(hyps, carrierElem, i); w == nil || !w.Conclusion().AlphaEquals(hi) {
		t.Errorf("int: i must read as &0, got %v", w)
	}
	if ruleFor(hyps, isRealTerm, i) != nil {
		t.Error("an integer equation was read at the real carrier alone")
	}
}

// Between two variables the later in the variable order goes to the
// earlier, whichever side it is written on.
func TestVarEqSubst_TwoVariables(t *testing.T) {
	n, m := numVar("n"), numVar("m")
	from, to := n, m
	if m.Compare(n) > 0 {
		from, to = m, n
	}
	for _, h := range []Term{eqT(n, m), eqT(m, n)} {
		w := ruleFor([]Term{h}, isNat, from)
		if w == nil || !w.Conclusion().AlphaEquals(eqT(from, to)) {
			t.Errorf("%v: want %v read as %v, got %v", h, from, to, w)
		}
		if ruleFor([]Term{h}, isNat, to) != nil {
			t.Errorf("%v: both variables rewrite", h)
		}
	}
}

// A definition by a compound term is a rule whatever the names of its
// variables: `a = b + c` defines a though a comes first in the order.
func TestVarEqSubst_ADefinitionNeedsNoNameOrder(t *testing.T) {
	a, b, c := realVar("a"), realVar("b"), realVar("c")
	h := eqT(a, realPlusT(b, c))
	if w := ruleFor([]Term{h}, isRealTerm, a); w == nil || !w.Conclusion().AlphaEquals(h) {
		t.Fatalf("a must read as b + c, got %v", w)
	}
	// Written the other way round it is the same rule.
	hr := eqT(realPlusT(b, c), a)
	if w := ruleFor([]Term{hr}, isRealTerm, a); w == nil || !w.Conclusion().AlphaEquals(h) {
		t.Fatalf("b + c = a: a must read as b + c, got %v", w)
	}
}

// The rules are acyclic. A variable its own definition names is not
// defined; of two definitions that name each other the first stands and
// the second is refused; a chain is taken whole.
func TestVarEqSubst_Acyclic(t *testing.T) {
	a, b, c := realVar("a"), realVar("b"), realVar("c")
	one := realLit(1)
	if ruleFor([]Term{eqT(a, realPlusT(a, one))}, isRealTerm, a) != nil {
		t.Error("a = a + &1 defined a")
	}
	loop := []Term{eqT(a, realPlusT(b, one)), eqT(b, realPlusT(a, one))}
	if ruleFor(loop, isRealTerm, a) == nil {
		t.Error("the first of two definitions that name each other was not taken")
	}
	if ruleFor(loop, isRealTerm, b) != nil {
		t.Error("the second of two definitions that name each other was taken: the rules cycle")
	}
	// Through a third variable: a → b, b → c, and then c may not go to a.
	ring := []Term{eqT(a, realPlusT(b, one)), eqT(b, realPlusT(c, one)), eqT(c, realPlusT(a, one))}
	if ruleFor(ring, isRealTerm, a) == nil || ruleFor(ring, isRealTerm, b) == nil {
		t.Error("the two first definitions of a three-cycle were not taken")
	}
	if ruleFor(ring, isRealTerm, c) != nil {
		t.Error("the definition that closes a three-cycle was taken")
	}
	chain := []Term{eqT(a, realPlusT(b, one)), eqT(b, realPlusT(c, one))}
	if ruleFor(chain, isRealTerm, a) == nil || ruleFor(chain, isRealTerm, b) == nil {
		t.Error("a chain of definitions was not taken whole")
	}
}

// A variable has one rule, and a value outranks a definition wherever the
// two stand among the hypotheses.
func TestVarEqSubst_AValueOutranksADefinition(t *testing.T) {
	x, y, z := realVar("x"), realVar("y"), realVar("z")
	def, val := eqT(x, realPlusT(y, z)), eqT(x, realLit(3))
	for _, hyps := range [][]Term{{def, val}, {val, def}} {
		w := ruleFor(hyps, isRealTerm, x)
		if w == nil || !w.Conclusion().AlphaEquals(val) {
			t.Errorf("%v: x must read as &3, got %v", hyps, w)
		}
	}
	// Two definitions: the first among the hypotheses.
	other := eqT(x, realStarT(y, z))
	if w := ruleFor([]Term{def, other}, isRealTerm, x); w == nil || !w.Conclusion().AlphaEquals(def) {
		t.Errorf("of two definitions the first must stand, got %v", w)
	}
}

// The deep rewrite by the rules ends on every one of the sets above, and
// reads a chain through to its last link.
func TestVarEqSubst_TheRewriteEnds(t *testing.T) {
	a, b, c := realVar("a"), realVar("b"), realVar("c")
	one := realLit(1)
	sets := [][]Term{
		{eqT(a, realPlusT(a, one))},
		{eqT(a, realPlusT(b, one)), eqT(b, realPlusT(a, one))},
		{eqT(a, realPlusT(b, one)), eqT(b, realPlusT(c, one)), eqT(c, realPlusT(a, one))},
		{eqT(a, b), eqT(b, a)},
		{eqT(a, realStarT(b, b)), eqT(b, realStarT(c, c)), eqT(c, one)},
	}
	target := realStarT(realPlusT(a, b), c)
	for _, hyps := range sets {
		anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
		prop.DeepRewriteWithEnv(anyHyp, eqHypSubst(hyps, isRealTerm, ArithPolicy{}))(target)
	}
	last := sets[len(sets)-1]
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(last, pred) }
	w := prop.DeepRewriteWithEnv(anyHyp, eqHypSubst(last, isRealTerm, ArithPolicy{}))(a)
	want := realStarT(realStarT(one, one), realStarT(one, one))
	if w == nil || !prop.Rhs(w).AlphaEquals(want) {
		t.Errorf("a through b and c: want %v, got %v", want, w)
	}
}

// closesUnder reports whether the arith context of hyps decides goal ⊤,
// and requires the closing theorem to rest on hyps as written alone.
func closesUnder(t *testing.T, hyps []Term, goal Term) bool {
	t.Helper()
	w := NewArithCtx(hyps).Decide(goal)
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		return false
	}
	closed := w.EqSym().EqMP(prop.DerivesTrue)
	if !prop.IsStronger(closed, core.MakeProp(goal, hyps...)) {
		t.Fatalf("the closing theorem carries a hypothesis the goal lacks: %v", closed.Hyps())
	}
	return true
}

// A decision reads its target and its context at the definitions
// together: a hypothesis spelled at the variable decides a goal spelled at
// the definition, and the other way round.
func TestArithCtx_TargetAndContextAreReadTogether(t *testing.T) {
	a, n, m, k := numVar("a"), numVar("n"), numVar("m"), numVar("k")
	def := eqT(n, plus(m, k))
	atVariable, atDefinition := eqT(modT(a, n), Numeral(1)), eqT(modT(a, plus(m, k)), Numeral(1))
	if !closesUnder(t, []Term{def, atVariable}, atDefinition) {
		t.Error("a hypothesis at the variable did not decide the goal at the definition")
	}
	if !closesUnder(t, []Term{def, atDefinition}, atVariable) {
		t.Error("a hypothesis at the definition did not decide the goal at the variable")
	}
	// Without the definition the two spellings are two atoms.
	if closesUnder(t, []Term{atVariable}, atDefinition) {
		t.Error("the goal closed with no equation between n and m + k")
	}
}

// The reading is the decision's own. A hypothesis the decider does nothing
// with at the definition is not rewritten, and neither is such a goal: no
// rewrite respells a term at a definition.
func TestArithCtx_TheReadingAloneIsNoRewrite(t *testing.T) {
	a, n, m, k := numVar("a"), numVar("n"), numVar("m"), numVar("k")
	def := eqT(n, plus(m, k))
	fact := le(modT(a, n), k)
	ctx := NewArithCtx([]Term{def, fact})
	if w := ctx.DecideExcept(1, fact); w != nil {
		t.Errorf("the hypothesis was rewritten to %v", prop.Rhs(w))
	}
	if w := ctx.Decide(le(modT(a, n), a)); w != nil {
		t.Errorf("the goal was rewritten to %v", prop.Rhs(w))
	}
	// The definition's own equation is decided under the others, which
	// hold no definition without it.
	if w := ctx.DecideExcept(0, def); w != nil {
		t.Errorf("the definition was rewritten to %v", prop.Rhs(w))
	}
}

// What a decision returns rests on the hypotheses as written, whichever
// pass read them. The ground-congruence pass reads its rule off a
// hypothesis at the definition and before the pre-simp, the deciders
// after it; a certificate that carries either form is carried back to the
// hypothesis the author wrote.
func TestArithCtx_ACongruenceRuleReadAtADefinitionIsCarriedBack(t *testing.T) {
	n, m, k, x := numVar("n"), numVar("m"), numVar("k"), numVar("x")
	g := ext.Var("g", core.MakeFun(n.Type(), n.Type())).Core()
	def := eqT(n, plus(m, k))
	// (n + x) + 0 → 3: read at the definition it is ((m + k) + x) + 0 → 3,
	// and the pre-simp folds the `+ 0` of the hypothesis away.
	sum := plus(plus(n, x), Numeral(0))
	rule := eqT(sum, Numeral(3))
	goal := eqT(ext.Apply(g, sum), ext.Apply(g, Numeral(3)))
	if !closesUnder(t, []Term{def, rule}, goal) {
		t.Error("g((n + x) + 0) = g(3) did not close from (n + x) + 0 = 3")
	}
}

// A structure ring's own elements are constants of the rule: an equation
// with the ring's zero on one side pins the other side and defines
// nothing, while an unknown equal to the zero is defined by it.
func TestVarEqSubst_ARingsElementsAreConstants(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	p, r := w.x("p"), w.x("r")
	pinned := core.Eq(w.d(p, r), w.zero)
	elem, fixed := ruleScopeUnder([]Term{w.S, pinned})
	if subs := varEqSubsts([]Term{w.S, pinned}, elem, fixed, ArithPolicy{}); len(subs) != 0 {
		t.Errorf("p - r = zero made a rule for %v", subs[0].from)
	}
	isZero := core.Eq(p, w.zero)
	elem, fixed = ruleScopeUnder([]Term{w.S, isZero})
	subs := varEqSubsts([]Term{w.S, isZero}, elem, fixed, ArithPolicy{})
	if len(subs) != 1 || !subs[0].from.AlphaEquals(p) || !subs[0].to.AlphaEquals(w.zero) {
		t.Errorf("p = zero must define p as zero, got %v", subs)
	}
	// Written the other way round it is the same rule, not one for zero.
	elem, fixed = ruleScopeUnder([]Term{w.S, core.Eq(w.zero, p)})
	subs = varEqSubsts([]Term{w.S, core.Eq(w.zero, p)}, elem, fixed, ArithPolicy{})
	if len(subs) != 1 || !subs[0].from.AlphaEquals(p) {
		t.Errorf("zero = p must define p, got %v", subs)
	}
}
