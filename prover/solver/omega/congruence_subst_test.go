package omega

// The ground-congruence pass (congruence_subst.go): a hypothesis equation
// between two compound terms of one carrier, bigger side to smaller,
// substituted into the target before the leaves read it. These tests pin
// the positive shape over ℝ and ℤ — an opaque application whose argument is
// the equation's bigger side — and the three exclusions: a variable side,
// equal sizes, a smaller side naming a variable the bigger side lacks.

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

func TestCongruenceSubst_CompoundSideReachesInsideAnAtom(t *testing.T) {
	installTestBundle(t)
	f := ext.Var(ext.TermName("f"), core.MakeFun(dsl.RealType, dsl.RealType))
	half, two, one := rr("x / &2"), rr("&2"), rr("&1")
	// the PiBounds shape: pi/2 = 2 carries real_cos(pi/2) to real_cos(2)
	if !realDecides(t, []Term{eqT(half, two), realLeT(ext.Apply(f, two), one)}, realLeT(ext.Apply(f, half), one)) {
		t.Error("x/2 = 2 did not carry f(x/2) ≤ 1 to the resident f(2) ≤ 1")
	}
	// a sum against a literal, inside a product's opaque factor
	sum, three := rr("x + y"), rr("&3")
	if !realDecides(t, []Term{eqT(sum, three), realLeT(ext.Apply(f, three), one)}, realLeT(ext.Apply(f, sum), one)) {
		t.Error("x + y = 3 did not carry f(x + y) to f(3)")
	}
	// two rules chain, through opaque atoms the linear layer cannot solve
	// for: f(x) + f(x) = g(x) and g(x) = 2 carry h(f(x) + f(x)) to h(2)
	g := ext.Var(ext.TermName("g"), core.MakeFun(dsl.RealType, dsl.RealType))
	h := ext.Var(ext.TermName("h"), core.MakeFun(dsl.RealType, dsl.RealType))
	fx, gx := ext.Apply(f, rr("x")), ext.Apply(g, rr("x"))
	twice := realPlusT(fx, fx)
	if !realDecides(t, []Term{eqT(twice, gx), eqT(gx, two), realLeT(ext.Apply(h, two), one)}, realLeT(ext.Apply(h, twice), one)) {
		t.Error("the two rules f(x) + f(x) = g(x), g(x) = 2 did not chain into h")
	}
}

func TestCongruenceSubst_IntTwin(t *testing.T) {
	installTestBundle(t)
	g := ext.Var(ext.TermName("g"), core.MakeFun(dsl.IntType, dsl.IntType))
	a, b := intVar("a"), intVar("b")
	sum, three, one := intPlusT(a, b), intLit(3), intLit(1)
	if !intDecides(t, []Term{eqT(sum, three), intLeT(ext.Apply(g, three), one)}, intLeT(ext.Apply(g, sum), one)) {
		t.Error("over ℤ, a + b = 3 did not carry g(a + b) to g(3)")
	}
}

func TestCongruenceSubst_Exclusions(t *testing.T) {
	installTestBundle(t)
	f := ext.Var(ext.TermName("f"), core.MakeFun(dsl.RealType, dsl.RealType))
	x, y := rr("x"), rr("y")
	// a variable side is the variable-sided rule's, not this pass's
	if subs := compoundEqSubsts([]Term{eqT(x, rr("&2"))}); len(subs) != 0 {
		t.Errorf("a variable-sided equation became a compound rule: %v", subs)
	}
	// equal sizes — a permutation equation — are skipped
	if subs := compoundEqSubsts([]Term{eqT(rr("x * z"), rr("z * x"))}); len(subs) != 0 {
		t.Errorf("a same-size equation became a rule: %v", subs)
	}
	// the smaller side must name no variable the bigger side lacks
	if subs := compoundEqSubsts([]Term{eqT(ext.Apply(f, rr("x + x")), ext.Apply(f, y))}); len(subs) != 0 {
		t.Errorf("a rule introducing a new variable was accepted: %v", subs)
	}
	// and the one that qualifies is oriented bigger → smaller, a literal
	// the smallest spelling whatever its encoding's node count
	subs := compoundEqSubsts([]Term{eqT(rr("&2"), rr("x / &2"))})
	if len(subs) != 1 || !subs[0].from.AlphaEquals(rr("x / &2")) {
		t.Errorf("want one rule from x / 2, got %v", subs)
	}
	if subs := compoundEqSubsts([]Term{eqT(rr("&3"), rr("x + y"))}); len(subs) != 1 || !subs[0].from.AlphaEquals(rr("x + y")) {
		t.Errorf("want one rule from x + y towards the literal 3, got %v", subs)
	}
}

// TestCongruenceSubst_StructureRingCarrier: an equation at a structure
// ring's carrier is a rule as one over ℝ is — determinant's `opposite`
// leaf, `A′·B′ = −(A·B)` from `A′ = −A` and `B′ = B` with the memberships
// of A and B alone. The τ·q-side atoms A′, B′ have no membership, so the
// ring cannot read the goal as spelled; substituted towards the q side it
// is a ring identity over atoms the context holds.
func TestCongruenceSubst_StructureRingCarrier(t *testing.T) {
	fa := installFakeStructureRing(t)
	w := fa.abstract()
	AA := core.MakeFun(fa.A, fa.A)
	f := ext.Var(ext.TermName("f"), AA).Core()
	g := ext.Var(ext.TermName("g"), AA).Core()
	h := ext.Var(ext.TermName("h"), AA).Core()
	x := w.x("x")
	a, b := ext.Apply(f, x), ext.Apply(g, x)
	shifted := ext.Apply(h, ext.Apply(h, x)) // the τ·q side, a compound point
	aT, bT := ext.Apply(f, shifted), ext.Apply(g, shifted)
	hyps := []Term{w.SOn, w.in(a), w.in(b), core.Eq(aT, w.ng(a)), core.Eq(bT, b)}
	goal := core.Eq(w.t(aT, bT), w.ng(w.t(a, b)))
	subs := compoundEqSubsts(hyps)
	require.Len(t, subs, 2, "the two equations at the carrier are the pass's rules")
	require.True(t, subs[0].from.AlphaEquals(aT) && subs[1].from.AlphaEquals(bT), "oriented towards the q side")
	require.True(t, structureDecides(t, hyps, goal), "A′ = −A, B′ = B did not carry A′·B′ = −(A·B) to the ring identity")
	// Without the equations A′ and B′ are atoms without a membership, and the ring declines.
	require.False(t, structureDecides(t, []Term{w.SOn, w.in(a), w.in(b)}, goal))
}

// TestCongruenceSubst_SizeCountsUnderABinder: the orientation measures
// the whole term, an abstraction's body included — determinant's product
// equation `module_sum(…, λk. P(k, map(τ·q, k))) = module_sum(…, λk. P(k,
// map(q, k)))` differs only under its λ, and equal sizes drop the rule.
func TestCongruenceSubst_SizeCountsUnderABinder(t *testing.T) {
	installTestBundle(t)
	R := dsl.RealType
	F := ext.Var(ext.TermName("F"), core.MakeFun(core.MakeFun(R, R), R)).Core()
	f := ext.Var(ext.TermName("f"), core.MakeFun(R, R)).Core()
	k := core.Var(core.TermName("k"), R)
	thrice := ext.Apply(F, core.Abs(k, realPlusT(realPlusT(k, k), k)))
	once := ext.Apply(F, core.Abs(k, k))
	one := rr("&1")
	subs := compoundEqSubsts([]Term{eqT(thrice, once)})
	require.Len(t, subs, 1, "two sides differing only under a binder are not the same size")
	require.True(t, subs[0].from.AlphaEquals(thrice), "oriented from the bigger body")
	require.True(t, realDecides(t, []Term{eqT(thrice, once), realLeT(ext.Apply(f, once), one)}, realLeT(ext.Apply(f, thrice), one)),
		"F(λk. k + k + k) = F(λk. k) did not carry f(F(λk. k + k + k)) to the resident f(F(λk. k))")
}

// TestCongruenceSubst_BoundVariablesDoNotCount: the variable condition
// is over FREE carrier variables — a binder's variable is nobody's
// substitution target, and its name is the binder's to choose (the
// corpus's set-builders bind generated names that differ side to side).
func TestCongruenceSubst_BoundVariablesDoNotCount(t *testing.T) {
	installTestBundle(t)
	R := dsl.RealType
	F := ext.Var(ext.TermName("F"), core.MakeFun(core.MakeFun(R, R), R)).Core()
	f := ext.Var(ext.TermName("f"), core.MakeFun(R, R)).Core()
	k, j, x, one := core.Var(core.TermName("k"), R), core.Var(core.TermName("j"), R), rr("x"), rr("&1")
	big := ext.Apply(F, core.Abs(k, realPlusT(k, x)))
	small := ext.Apply(F, core.Abs(j, j))
	subs := compoundEqSubsts([]Term{eqT(big, small)})
	require.Len(t, subs, 1, "the smaller side's bound j is no variable the bigger side lacks")
	require.True(t, subs[0].from.AlphaEquals(big))
	require.True(t, realDecides(t, []Term{eqT(big, small), realLeT(ext.Apply(f, small), one)}, realLeT(ext.Apply(f, big), one)))
	// A FREE variable of the smaller side the bigger side lacks still refuses.
	require.Empty(t, compoundEqSubsts([]Term{eqT(ext.Apply(f, rr("x + x")), ext.Apply(f, rr("y")))}))
}

// TestCongruenceSubst_RoundTripIsNoProgress: the pass composed with an
// inner rewrite reports progress only where the composition moves the
// target. An inner that carries the pass's result back to the target —
// the arith normal form of a term is not always its smaller spelling,
// `&2 ^ n` against `&(2 ^ n)`, and an equation between the two is then a
// rule against the normalizer — is no rewrite of the target: nil, as a
// rewrite that does not fire answers. The pass alone, and the pass
// followed by an inner that goes elsewhere, stay progress.
func TestCongruenceSubst_RoundTripIsNoProgress(t *testing.T) {
	installTestBundle(t)
	R := dsl.RealType
	f := ext.Var(ext.TermName("f"), core.MakeFun(R, R)).Core()
	g := ext.Var(ext.TermName("g"), core.MakeFun(R, R)).Core()
	big, small := rr("x + x + x"), ext.Apply(g, rr("x"))
	rule := eqT(big, small)
	hyps := []Term{rule}
	target := realLeT(ext.Apply(f, big), rr("&1"))
	carried := realLeT(ext.Apply(f, small), rr("&1"))
	require.Len(t, compoundEqSubsts(hyps), 1)

	declines := func(Term) *prop.PropWrapper { return nil }
	w := withCompoundEqSubst(hyps, declines)(target)
	require.NotNil(t, w, "the pass alone is progress")
	require.True(t, prop.Rhs(w).AlphaEquals(carried))

	// inner undoes the pass: f(g(x)) back to f(x + x + x).
	back := prop.Assume(rule).EqSym() // {rule} ⊢ g(x) = x + x + x
	undo := prop.DeepRewrite(func(s Term) *prop.PropWrapper {
		if s.AlphaEquals(small) {
			return back
		}
		return nil
	})
	require.True(t, prop.Rhs(undo(carried)).AlphaEquals(target), "the inner rewrite carries the pass's result back")
	require.Nil(t, withCompoundEqSubst(hyps, undo)(target), "a round trip to the target is no rewrite of it")

	// inner goes elsewhere: f(g(x)) on to f(&0).
	zero := rr("&0")
	on := prop.Assume(eqT(small, zero)) // {g(x) = &0} ⊢ g(x) = &0
	onward := prop.DeepRewrite(func(s Term) *prop.PropWrapper {
		if s.AlphaEquals(small) {
			return on
		}
		return nil
	})
	w = withCompoundEqSubst(hyps, onward)(target)
	require.NotNil(t, w)
	require.True(t, prop.Rhs(w).AlphaEquals(realLeT(ext.Apply(f, zero), rr("&1"))))
}
