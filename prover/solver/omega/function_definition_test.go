package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// A hypothesis `F = λx. e` with F a variable defines F, as an equation
// with a variable side defines a number: a decision the hypotheses do not
// make as written is made with F read at the λ wherever it stands, an
// application `F(s)` as e at s.
func TestArithCtx_AFunctionDefinitionIsRead(t *testing.T) {
	installTestBundle(t)
	sequence := core.MakeFun(dsl.NumType, dsl.NumType)
	x, a := ext.Var("x", sequence), ext.Var("a", sequence)
	h, i, j := numVar("h"), numVar("i"), numVar("j")
	jv, _ := j.AsVar()
	lambda := core.Abs(jv, plus(ext.Apply(x, j), h)) // λj. x(j) + h
	shifted := eqT(a, lambda)
	positive := lt(Numeral(0), h)
	above := lt(ext.Apply(x, i), ext.Apply(a, i)) // x(i) < a(i)

	if !closesUnder(t, []Term{shifted, positive}, above) {
		t.Error("x(i) < a(i) is not decided under a = λj. x(j) + h and 0 < h")
	}
	// The equation the other way round defines a as well.
	if !closesUnder(t, []Term{eqT(lambda, a), positive}, above) {
		t.Error("x(i) < a(i) is not decided under (λj. x(j) + h) = a and 0 < h")
	}
	// A hypothesis spelled at the function is read with the goal.
	bound := le(ext.Apply(a, i), Numeral(3)) // a(i) ≤ 3
	if !closesUnder(t, []Term{shifted, bound}, le(h, Numeral(3))) {
		t.Error("h ≤ 3 is not decided under a = λj. x(j) + h and a(i) ≤ 3")
	}
	// Controls: the definition is what decides it, and it decides nothing false.
	if closesUnder(t, []Term{positive}, above) {
		t.Error("x(i) < a(i) is decided with no definition of a")
	}
	if closesUnder(t, []Term{shifted}, above) {
		t.Error("x(i) < a(i) is decided with h of no sign")
	}
}

// A function definition that names its own variable, alone or through a
// number's definition, is no rule: the reading ends.
func TestArithCtx_AFunctionDefinitionIsAcyclic(t *testing.T) {
	installTestBundle(t)
	sequence := core.MakeFun(dsl.NumType, dsl.NumType)
	a := ext.Var("a", sequence)
	c, i, j := numVar("c"), numVar("i"), numVar("j")
	jv, _ := j.AsVar()
	one := Numeral(1)
	// a = λj. a(j) + 1
	own := eqT(a, core.Abs(jv, plus(ext.Apply(a, j), one)))
	if d := readAtDefinitions([]Term{own}, UnscopedArithPolicy()); d != nil {
		t.Error("a = λj. a(j) + 1 is read as a rule")
	}
	if closesUnder(t, []Term{own}, lt(ext.Apply(a, i), ext.Apply(a, i))) {
		t.Error("a(i) < a(i) is decided under a = λj. a(j) + 1")
	}
	// c = a(0) + 1 beside a = λj. c + 1: the number's definition is the
	// rule and the function's an equation, so a is read nowhere and c
	// once.
	through := []Term{
		eqT(c, plus(ext.Apply(a, Numeral(0)), one)),
		eqT(a, core.Abs(jv, plus(c, one))),
	}
	d := readAtDefinitions(through, UnscopedArithPolicy())
	if d == nil || !d.defines[0] || d.defines[1] {
		t.Fatalf("c = a(0) + 1 beside a = λj. c + 1: want the first a rule and the second none")
	}
	if w := d.target(ext.Apply(a, i)); w != nil {
		t.Errorf("a(i) is read %v under a definition that is no rule", prop.Rhs(w))
	}
	want := plus(ext.Apply(a, Numeral(0)), one)
	if w := d.target(c); w == nil || !prop.Rhs(w).AlphaEquals(want) {
		t.Errorf("c is not read as a(0) + 1")
	}
}

// The leaf read whole at its definitions names a defined function
// nowhere: an application is read at the body, a bare occurrence at the λ,
// and the definition's own equation is left out.
func TestArithCtx_LeafAtAFunctionDefinition(t *testing.T) {
	installTestBundle(t)
	sequence := core.MakeFun(dsl.NumType, dsl.NumType)
	x, a := ext.Var("x", sequence), ext.Var("a", sequence)
	p := ext.Var("P", core.MakeFun(sequence, core.TypeBool()))
	h, i, j := numVar("h"), numVar("i"), numVar("j")
	jv, _ := j.AsVar()
	lambda := core.Abs(jv, plus(ext.Apply(x, j), h))
	hyps := []Term{eqT(a, lambda), ext.Apply(p, a)}
	leaf, ok := NewArithCtx(hyps).LeafAtDefinitions(lt(ext.Apply(x, i), ext.Apply(a, i)))
	if !ok {
		t.Fatal("the hypotheses hold a definition and the leaf is not read")
	}
	if leaf.Hyps[0] != nil {
		t.Errorf("the definition's own equation is kept: %v", leaf.Hyps[0])
	}
	if want := ext.Apply(p, lambda); leaf.Hyps[1] == nil || !leaf.Hyps[1].AlphaEquals(want) {
		t.Errorf("P(a) is read %v, want P at the λ", leaf.Hyps[1])
	}
	want := lt(ext.Apply(x, i), plus(ext.Apply(x, i), h))
	if leaf.Concl == nil || !prop.Rhs(leaf.Concl).AlphaEquals(want) {
		t.Errorf("x(i) < a(i) is not read as x(i) < x(i) + h: %v", leaf.Concl)
	}
}
