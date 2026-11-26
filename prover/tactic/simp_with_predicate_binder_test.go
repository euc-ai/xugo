package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// predicateBinderFixture: a quantifier reading whose left side applies a
// predicate binder P to its own bound variable — the shape of a
// quotient's "every class" reading, `(∀s. R(s, h) ⇒ P(s)) ⇔ ∀x. Q₂(x) ⇒
// P(f(x, h))` — and a goal whose matching subterm instantiates P at a
// compound predicate, so the match binds P to a λ.
func predicateBinderFixture() (h, s, x, a, R, f, P, Q, Q2 *ext.TermWrapper) {
	h = ext.WrapTerm(Var("h", TypeA))
	s = ext.WrapTerm(Var("s", TypeA))
	x = ext.WrapTerm(Var("x", TypeA))
	a = ext.WrapTerm(Var("a", TypeA))
	R = ext.WrapTerm(Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool))))
	f = ext.WrapTerm(Var("f", MakeFun(TypeA, MakeFun(TypeA, TypeA))))
	P = ext.WrapTerm(Var("P", MakeFun(TypeA, TypeBool)))
	Q = ext.WrapTerm(Var("Q", MakeFun(TypeA, TypeBool)))
	Q2 = ext.WrapTerm(Var("Q2", MakeFun(TypeA, TypeBool)))
	return
}

// The reading as an equation: (∀s. R(s, h) ⇒ P(s)) ⇔ ∀x. Q₂(x) ⇒ P(f(x, h)).
func predicateBinderReading(h, s, x, R, f, P, Q2 *ext.TermWrapper) *ext.TermWrapper {
	return ext.ForAll(s)(R.Apply(s, h).Imply(P.Apply(s))).
		Eq(ext.ForAll(x)(Q2.Apply(x).Imply(P.Apply(f.Apply(x, h)))))
}

// The goal ∀s. R(s, a) ⇒ Q(s) ∧ Q₂(s), and what the reading makes of it.
func predicateBinderGoal(s, x, a, R, f, Q, Q2 *ext.TermWrapper) (goal, want *ext.TermWrapper) {
	goal = ext.ForAll(s)(R.Apply(s, a).Imply(Q.Apply(s).And(Q2.Apply(s))))
	fx := f.Apply(x, a)
	want = ext.ForAll(x)(Q2.Apply(x).Imply(Q.Apply(fx).And(Q2.Apply(fx))))
	return
}

// The control: the reading with no guard fires, P bound to the λ the goal
// spells.
func TestSimpWith_PredicateBinderUnguardedFires(t *testing.T) {
	defer goleak.VerifyNone(t)
	h, s, x, a, R, f, P, Q, Q2 := predicateBinderFixture()
	rule := testProp(ext.ForAll(h, P)(predicateBinderReading(h, s, x, R, f, P, Q2)).Core())
	goal, want := predicateBinderGoal(s, x, a, R, f, Q, Q2)

	sg := SimpWithExpand(testProp(goal.Core()), []Prop{rule})
	require.NotNil(t, sg, "the unguarded reading must fire")
	assert.True(t, sg.ChildGoal(sg.Size()-1).Conclusion().AlphaEquals(want.Core()),
		"got %s", prop.PrintProp(sg.ChildGoal(sg.Size()-1)))
}

// The same reading under a guard `Q(h) ⇒ …`, the guard resident: the
// conditional path mines the instance at P := λs. Q(s) ∧ Q₂(s) and rewrites
// with it, the instance read up to β.
func TestSimpWith_PredicateBinderGuardedFires(t *testing.T) {
	defer goleak.VerifyNone(t)
	h, s, x, a, R, f, P, Q, Q2 := predicateBinderFixture()
	rule := testProp(ext.ForAll(h)(Q.Apply(h).Imply(ext.ForAll(P)(predicateBinderReading(h, s, x, R, f, P, Q2)))).Core())
	goal, want := predicateBinderGoal(s, x, a, R, f, Q, Q2)
	guard := Q.Apply(a).Core()

	sg := SimpWithExpand(testProp(goal.Core(), guard), []Prop{rule})
	require.NotNil(t, sg, "the guarded reading must fire with its guard resident")
	child := sg.ChildGoal(sg.Size() - 1)
	assert.True(t, child.Conclusion().AlphaEquals(want.Core()), "got %s", prop.PrintProp(child))
	assert.True(t, child.HasHyp(guard))
}
