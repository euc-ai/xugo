package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// Structure-law fixture: a law is `∀comps. S(comps) ⇒ body` with the
// operation and the distinguished elements ∀-bound COMPONENTS, so an
// equation's head is a flexible variable and a component may appear on
// the equation's right side only. add, mul, op : A→A→A; neg : A→A; zero,
// one, e, a : A; S : (A→A→A)→A→bool (a monoid predicate); G :
// (A→A→A)→A→(A→A)→bool (a group predicate); n : (A→A→A)→A (a choice-named
// identity); P : A→bool.
type structureFixture struct {
	add, mul, op, neg, zero, one, e, a, x, S, G, n, P *ext.TermWrapper
}

func structureVars() structureFixture {
	bin := MakeFun(TypeA, MakeFun(TypeA, TypeA))
	un := MakeFun(TypeA, TypeA)
	w := func(name string, ty core.HolType) *ext.TermWrapper { return ext.WrapTerm(Var(TermName(name), ty)) }
	return structureFixture{
		add: w("add", bin), mul: w("mul", bin), op: w("op", bin),
		neg:  w("neg", un),
		zero: w("zero", TypeA), one: w("one", TypeA), e: w("e", TypeA), a: w("a", TypeA), x: w("x", TypeA),
		S: w("S", MakeFun(bin, MakeFun(TypeA, TypeBool))),
		G: w("G", MakeFun(bin, MakeFun(TypeA, MakeFun(un, TypeBool)))),
		n: w("n", MakeFun(bin, TypeA)),
		P: w("P", MakeFun(TypeA, TypeBool)),
	}
}

// reconstructWithAssumed closes every child by assumption and checks the
// reconstructed theorem states the goal on the goal's own hypotheses —
// the flipped driver view must derive from the natural-direction rule.
func reconstructWithAssumed(t *testing.T, s *SubGoals, goal Prop) {
	t.Helper()
	thms := make([]Prop, s.Size())
	for i := range thms {
		g := s.ChildGoal(i)
		thms[i] = testThm(g.Conclusion(), g.Hyps()...)
	}
	r := s.Reconstruct(thms...)
	assert.True(t, r.Conclusion().AlphaEquals(goal.Conclusion()))
	assert.True(t, r.AllHyp(goal.HasHyp), "reconstruction must not leak a hypothesis: %s", r)
}

// A law whose equation head is a ∀-bound operation fires: `op(x, e)`
// reads first-order against `add(a, zero)` (op := add, x := a, e :=
// zero), the side condition discharges against the resident instance.
func TestSimpWith_StructureLaw_FlexibleHeadMatchesFirstOrder(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	rightIdentity := testProp(ForAll(v.op, v.e, v.x)(
		v.S.Apply(v.op, v.e).Imply(v.op.Apply(v.x, v.e).Eq(v.x))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.a, v.zero)).Core(), v.S.Apply(v.add, v.zero).Core())

	s := SimpWithExpand(goal, []Prop{rightIdentity})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(rightIdentity))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.a).Core()))
	reconstructWithAssumed(t, s, goal)
}

// A component the equation's LHS never mentions — the `zero` of
// `add(neg(x), x) = zero` — is pinned by the side condition matched
// against the resident instance (an assumption as a matcher).
func TestSimpWith_StructureLaw_ComponentOnlyOnRHS_PinnedByHyp(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	leftInverse := testProp(ForAll(v.add, v.zero, v.neg, v.x)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core(), v.G.Apply(v.add, v.zero, v.neg).Core())

	s := SimpWithExpand(goal, []Prop{leftInverse})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(leftInverse))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// The same law in its normalized clause form, and the group's identity
// only on the right: `¬G(add, zero, neg) ∨ (add(neg(x), x) = zero)`.
func TestSimpWith_StructureLaw_ClauseForm_PinnedByHyp(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	leftInverse := testProp(ForAll(v.add, v.zero, v.neg, v.x)(
		Not(v.G.Apply(v.add, v.zero, v.neg)).Or(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core(), v.G.Apply(v.add, v.zero, v.neg).Core())

	s := SimpWithExpand(goal, []Prop{leftInverse})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// The consumer's spelling: the instance is a ground factorial in the set
// (`comm_monoid(real_add, &0)` beside the law), no hypothesis at all.
// `n(op) = e` pins op off the goal and e off the fact.
func TestSimpWith_StructureLaw_PinnedByGroundFact(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	neutral := testProp(ForAll(v.op, v.e)(
		v.S.Apply(v.op, v.e).Imply(v.n.Apply(v.op).Eq(v.e))).Core())
	instance := testProp(v.S.Apply(v.add, v.zero).Core())
	goal := testProp(v.P.Apply(v.n.Apply(v.add)).Core())

	s := SimpWithExpand(goal, []Prop{neutral, instance})
	require.NotNil(t, s)
	require.Equal(t, 3, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(neutral))
	assert.True(t, s.ChildGoal(1).AlphaEquals(instance))
	assert.True(t, s.ChildGoal(2).Conclusion().AlphaEquals(v.P.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// Two instances of the structure resident on one carrier (ℝ's additive
// and multiplicative monoids): the operation the goal spells selects
// the instance, so the identity read off is that instance's.
func TestSimpWith_StructureLaw_TwoInstancesResident_GoalSelects(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	neutral := testProp(ForAll(v.op, v.e)(
		v.S.Apply(v.op, v.e).Imply(v.n.Apply(v.op).Eq(v.e))).Core())
	goal := testProp(v.P.Apply(v.n.Apply(v.mul)).Core(),
		v.S.Apply(v.add, v.zero).Core(), v.S.Apply(v.mul, v.one).Core())

	s := SimpWithExpand(goal, []Prop{neutral})
	require.NotNil(t, s)
	child := s.ChildGoal(s.Size() - 1)
	assert.True(t, child.Conclusion().AlphaEquals(v.P.Apply(v.one).Core()))
	reconstructWithAssumed(t, s, goal)
}

// A component nothing pins is never invented: with no instance resident
// and none in the set, the RHS-only law does not fire, and an
// unconditional rule beside it is unaffected.
func TestSimpWith_StructureLaw_UnpinnedComponentDoesNotFire(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	leftInverse := testProp(ForAll(v.add, v.zero, v.neg, v.x)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core())
	assert.Nil(t, SimpWithExpand(goal, []Prop{leftInverse}))

	negNeg := testProp(ForAll(v.x)(v.neg.Apply(v.neg.Apply(v.x)).Eq(v.x)).Core())
	goal2 := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.neg.Apply(v.a)), v.a)).Core())
	s := SimpWithExpand(goal2, []Prop{leftInverse, negNeg})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(negNeg))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.add.Apply(v.a, v.a)).Core()))
}

// The stated form of a law keeps the body's ∀ under the antecedent:
// `S(op, e) ⇒ ∀x. op(x, e) = x`. The inner block joins the binders.
func TestSimpWith_StructureLaw_InnerForallUnderAntecedent(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	rightIdentity := testProp(ForAll(v.op, v.e)(
		v.S.Apply(v.op, v.e).Imply(ForAll(v.x)(v.op.Apply(v.x, v.e).Eq(v.x)))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.a, v.zero)).Core(), v.S.Apply(v.add, v.zero).Core())

	s := SimpWithExpand(goal, []Prop{rightIdentity})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(rightIdentity))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.a).Core()))
	reconstructWithAssumed(t, s, goal)
}

// The normalizer keeps a bare variable on the equation's LEFT
// (`x = op(x, e)`): unflipped, that is a bare-binder LHS and the rule is
// not a rewrite at all; flipped, the clause form fires as `op(x, e) → x`
// and the rule child stays the natural-direction statement.
func TestSimpWith_StructureLaw_NormalizedOrientation_FiresFlipped(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	normalized := testProp(ForAll(v.op, v.e, v.x)(
		Not(v.S.Apply(v.op, v.e)).Or(v.x.Eq(v.op.Apply(v.x, v.e)))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.a, v.zero)).Core(), v.S.Apply(v.add, v.zero).Core())

	assert.Nil(t, SimpWithExpand(goal, []Prop{normalized}), "unflipped: a bare-binder LHS is no rewrite")
	assert.True(t, RuleFlippable(normalized))

	s := SimpWithExpandFlipped(goal, []Prop{normalized}, []bool{true})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(normalized), "the rule child is the natural-direction statement")
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.a).Core()))
	reconstructWithAssumed(t, s, goal)
}

// The Horn form with the ∀ under the antecedent flips the same way, the
// RHS-only component pinned from the hypothesis after the flip.
func TestSimpWith_StructureLaw_HornInnerForall_FiresFlipped(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	leftInverse := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(ForAll(v.x)(v.zero.Eq(v.add.Apply(v.neg.Apply(v.x), v.x))))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core(), v.G.Apply(v.add, v.zero, v.neg).Core())

	assert.True(t, RuleFlippable(leftInverse))
	s := SimpWithExpandFlipped(goal, []Prop{leftInverse}, []bool{true})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(leftInverse))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// RuleFlippable: an equation under ∀, a Horn matrix, a clause matrix —
// yes; a fact, a reflexive equation — no.
func TestSimpWith_RuleFlippable(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	assert.True(t, RuleFlippable(testProp(ForAll(v.x)(v.neg.Apply(v.neg.Apply(v.x)).Eq(v.x)).Core())))
	assert.True(t, RuleFlippable(testProp(ForAll(v.op, v.e)(
		v.S.Apply(v.op, v.e).Imply(ForAll(v.x)(v.op.Apply(v.x, v.e).Eq(v.x)))).Core())))
	assert.True(t, RuleFlippable(testProp(ForAll(v.op, v.e, v.x)(
		Not(v.S.Apply(v.op, v.e)).Or(v.x.Eq(v.op.Apply(v.x, v.e)))).Core())))
	assert.False(t, RuleFlippable(testProp(ForAll(v.op, v.e)(v.S.Apply(v.op, v.e)).Core())))
	assert.False(t, RuleFlippable(testProp(ForAll(v.x)(v.x.Eq(v.x)).Core())))
}

// A Horn clause PACK — one structure hypothesis over a conjunction of
// equations, the fold mechanism's `monoidal_op(op) ⇒ (iterated_op(op, ∅, f) =
// neutral_elem(op)) ∧ (∀x s. …)` — is one conditional rule per conjunct:
// both conjuncts fire, the side condition discharged once from the
// resident instance, and the rule child is the pack itself.
func TestSimpWith_StructureLaw_HornClausePack_FiresEachConjunct(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	pack := testProp(ForAll(v.op, v.e)(
		v.S.Apply(v.op, v.e).Imply(
			v.n.Apply(v.op).Eq(v.e).And(ForAll(v.x)(v.op.Apply(v.x, v.e).Eq(v.x))))).Core())
	// P(add(a, n(add))) under S(add, zero): n(add) ↦ zero, then add(a, zero) ↦ a.
	goal := testProp(v.P.Apply(v.add.Apply(v.a, v.n.Apply(v.add))).Core(), v.S.Apply(v.add, v.zero).Core())

	s := SimpWithExpand(goal, []Prop{pack})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(pack), "the rule child is the pack, not a conjunct")
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.a).Core()),
		"both conjuncts fired; got %v", s.ChildGoal(1).Conclusion())
	reconstructWithAssumed(t, s, goal)
}

// A GUARDED law: the guard sits under the structure law's inner ∀,
// `G(add, zero, neg) ⇒ ∀x. P(x) ⇒ add(neg(x), x) = zero` — a telescope
// of two segments, the shape every `S.Law("∀x. x ∈ c ⇒ …")` states. It
// is a conditional rewrite, not an inert fact: the structure fact and
// the guard both discharge against the resident hypotheses.
func TestSimpWith_StructureLaw_GuardUnderInnerForall(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	guarded := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(
			ForAll(v.x)(v.P.Apply(v.x).Imply(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))))).Core())
	require.Empty(t, ClosureSimpClauses(guarded))
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core())

	s := SimpWithExpand(goal, []Prop{guarded})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(guarded))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// Three segments: `G ⇒ ∀x. P(x) ⇒ ∀y. P(y) ⇒ add(neg(x), add(x, y)) = y`
// — a cancellation law guarded on both of its members. Every ∀ block
// joins the binders and every guard is a side condition.
func TestSimpWith_StructureLaw_GuardUnderInnerForall_ThreeSegments(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()
	y := ext.WrapTerm(Var(TermName("y"), TypeA))

	cancel := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(
			ForAll(v.x)(v.P.Apply(v.x).Imply(
				ForAll(y)(v.P.Apply(y).Imply(v.add.Apply(v.neg.Apply(v.x), v.add.Apply(v.x, y)).Eq(y))))))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.add.Apply(v.a, v.e))).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core(), v.P.Apply(v.e).Core())

	s := SimpWithExpand(goal, []Prop{cancel})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(cancel))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.e).Core()))
	reconstructWithAssumed(t, s, goal)
}

// A guard the goal holds as a CONJUNCT of one hypothesis — `P(a)` inside
// the resident `P(a) ∧ P(e)`, the one fact a structure law's proof holds
// its guards as — discharges by ∧-elimination from that hypothesis, and
// the reconstruction stands on the conjunction, not on the conjunct.
func TestSimpWith_StructureLaw_GuardInsideConjunctionHyp(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	guarded := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(
			ForAll(v.x)(v.P.Apply(v.x).Imply(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).And(v.P.Apply(v.e)).Core())

	s := SimpWithExpand(goal, []Prop{guarded})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(guarded))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// The conjunct may sit at any depth: `P(e) ∧ (P(a) ∧ P(x))` supplies
// `P(a)` — the shape of a three-member guard, `x ∈ c ∧ y ∈ c ∧ z ∈ c`.
func TestSimpWith_StructureLaw_GuardInsideNestedConjunctionHyp(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	guarded := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(
			ForAll(v.x)(v.P.Apply(v.x).Imply(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.e).And(v.P.Apply(v.a).And(v.P.Apply(v.x))).Core())

	s := SimpWithExpand(goal, []Prop{guarded})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// A guard the goal does not hold is not invented: the redex is there,
// the structure fact is resident, and the rule still fires nothing.
func TestSimpWith_StructureLaw_GuardUnderInnerForall_UnmetGuard(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	guarded := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(
			ForAll(v.x)(v.P.Apply(v.x).Imply(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.neg.Apply(v.a), v.a)).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core())

	require.Nil(t, SimpWithExpand(goal, []Prop{guarded}))
}

// The flip bit turns a guarded law's equation around in place, the
// telescope untouched: `add(x, zero) = add(zero, x)` fired right-to-left
// rewrites `add(zero, a)` to `add(a, zero)` under the resident guard.
func TestSimpWith_StructureLaw_GuardUnderInnerForall_Flipped(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()

	swap := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(
			ForAll(v.x)(v.P.Apply(v.x).Imply(v.add.Apply(v.x, v.zero).Eq(v.add.Apply(v.zero, v.x)))))).Core())
	require.True(t, RuleFlippable(swap))
	goal := testProp(v.P.Apply(v.add.Apply(v.zero, v.a)).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core())

	s := SimpWithExpandFlipped(goal, []Prop{swap}, []bool{true})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(swap), "the rule child is the stated direction")
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.add.Apply(v.a, v.zero)).Core()))
	reconstructWithAssumed(t, s, goal)
}

// A CONJUNCTIVE antecedent, the spelling every structure definition
// gives its closure conditions (`x ∈ c ∧ y ∈ c ⇒ …`): each conjunct is
// discharged on its own against the hypotheses, and the antecedent is
// rebuilt from the conjuncts.
func TestSimpWith_ConjunctiveAntecedent_SplitHyps(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()
	Q := ext.WrapTerm(Var(TermName("Q"), MakeFun(TypeA, TypeBool)))
	f := ext.WrapTerm(Var(TermName("f"), MakeFun(TypeA, TypeA)))

	law := testProp(ForAll(v.x)(v.P.Apply(v.x).And(Q.Apply(v.x)).Imply(f.Apply(v.x).Eq(v.x))).Core())
	goal := testProp(v.P.Apply(f.Apply(v.a)).Core(), v.P.Apply(v.a).Core(), Q.Apply(v.a).Core())

	s := SimpWithExpand(goal, []Prop{law})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(law))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.a).Core()))
	reconstructWithAssumed(t, s, goal)
}

// The associativity law of a structure on a set, guarded on all three
// members under the inner ∀: `G ⇒ ∀x y z. P(x) ∧ P(y) ∧ P(z) ⇒
// add(x, add(y, z)) = add(add(x, y), z)` — a telescope whose second
// segment's antecedent is a left-nested conjunction.
func TestSimpWith_ConjunctiveAntecedent_GuardedAssoc(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()
	y := ext.WrapTerm(Var(TermName("y"), TypeA))
	z := ext.WrapTerm(Var(TermName("z"), TypeA))

	assoc := testProp(ForAll(v.add, v.zero, v.neg)(
		v.G.Apply(v.add, v.zero, v.neg).Imply(
			ForAll(v.x, y, z)(v.P.Apply(v.x).And(v.P.Apply(y)).And(v.P.Apply(z)).Imply(
				v.add.Apply(v.x, v.add.Apply(y, z)).Eq(v.add.Apply(v.add.Apply(v.x, y), z)))))).Core())
	goal := testProp(v.P.Apply(v.add.Apply(v.a, v.add.Apply(v.e, v.one))).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core(), v.P.Apply(v.e).Core(), v.P.Apply(v.one).Core())

	s := SimpWithExpand(goal, []Prop{assoc})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(assoc))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(v.P.Apply(v.add.Apply(v.add.Apply(v.a, v.e), v.one)).Core()))
	reconstructWithAssumed(t, s, goal)
}

// One conjunct the goal does not hold keeps the rule from firing: the
// conjunction is rebuilt only from conjuncts that are discharged.
func TestSimpWith_ConjunctiveAntecedent_MissingConjunct(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()
	Q := ext.WrapTerm(Var(TermName("Q"), MakeFun(TypeA, TypeBool)))
	f := ext.WrapTerm(Var(TermName("f"), MakeFun(TypeA, TypeA)))

	law := testProp(ForAll(v.x)(v.P.Apply(v.x).And(Q.Apply(v.x)).Imply(f.Apply(v.x).Eq(v.x))).Core())
	goal := testProp(v.P.Apply(f.Apply(v.a)).Core(), v.P.Apply(v.a).Core())

	require.Nil(t, SimpWithExpand(goal, []Prop{law}))
}

// The conjuncts may come by different routes: one is a hypothesis, the
// other a fact rule of the set. Both the law and the fact are used.
func TestSimpWith_ConjunctiveAntecedent_HypAndFact(t *testing.T) {
	defer goleak.VerifyNone(t)
	v := structureVars()
	Q := ext.WrapTerm(Var(TermName("Q"), MakeFun(TypeA, TypeBool)))
	f := ext.WrapTerm(Var(TermName("f"), MakeFun(TypeA, TypeA)))

	law := testProp(ForAll(v.x)(v.P.Apply(v.x).And(Q.Apply(v.x)).Imply(f.Apply(v.x).Eq(v.x))).Core())
	fact := testProp(Q.Apply(v.a).Core())
	goal := testProp(v.P.Apply(f.Apply(v.a)).Core(), v.P.Apply(v.a).Core())

	s := SimpWithExpand(goal, []Prop{law, fact})
	require.NotNil(t, s)
	require.Equal(t, 3, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(law))
	assert.True(t, s.ChildGoal(1).AlphaEquals(fact))
	assert.True(t, s.ChildGoal(2).Conclusion().AlphaEquals(v.P.Apply(v.a).Core()))
	reconstructWithAssumed(t, s, goal)
}

// closureFixture is the carrier-membership setting: a structure
// G(add, zero, neg), a carrier predicate P, the closure of P under neg
// and under add (conjunctive guard), and a guarded law on members.
type closureFixture struct {
	structureFixture
	Q, f                      *ext.TermWrapper
	negIn, addIn, leftInverse Prop
}

func closureVars() closureFixture {
	v := structureVars()
	y := ext.WrapTerm(Var(TermName("y"), TypeA))
	c := closureFixture{structureFixture: v,
		Q: ext.WrapTerm(Var(TermName("Q"), MakeFun(TypeA, TypeBool))),
		f: ext.WrapTerm(Var(TermName("f"), MakeFun(TypeA, TypeA)))}
	G := v.G.Apply(v.add, v.zero, v.neg)
	c.negIn = testProp(ForAll(v.add, v.zero, v.neg)(G.Imply(
		ForAll(v.x)(v.P.Apply(v.x).Imply(v.P.Apply(v.neg.Apply(v.x)))))).Core())
	c.addIn = testProp(ForAll(v.add, v.zero, v.neg)(G.Imply(
		ForAll(v.x, y)(v.P.Apply(v.x).And(v.P.Apply(y)).Imply(v.P.Apply(v.add.Apply(v.x, y)))))).Core())
	c.leftInverse = testProp(ForAll(v.add, v.zero, v.neg)(G.Imply(
		ForAll(v.x)(v.P.Apply(v.x).Imply(v.add.Apply(v.neg.Apply(v.x), v.x).Eq(v.zero))))).Core())
	return c
}

// A guard that is a closure consequence of the hypotheses: the redex
// `add(neg(neg(a)), neg(a))` is the law at x := neg(a), whose guard
// `P(neg(a))` no hypothesis states — the closure rule for neg derives
// it from `P(a)`. Both the law and the closure rule are used.
func TestSimpWith_ClosureRule_DischargesAGuardOneHop(t *testing.T) {
	defer goleak.VerifyNone(t)
	c := closureVars()
	v := c.structureFixture
	require.NotEmpty(t, ClosureSimpClauses(c.negIn))
	require.Empty(t, ClosureSimpClauses(c.leftInverse))

	goal := testProp(c.Q.Apply(v.add.Apply(v.neg.Apply(v.neg.Apply(v.a)), v.neg.Apply(v.a))).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core())
	s := SimpWithExpand(goal, []Prop{c.leftInverse, c.negIn})
	require.NotNil(t, s)
	require.Equal(t, 3, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(c.leftInverse))
	assert.True(t, s.ChildGoal(1).AlphaEquals(c.negIn))
	assert.True(t, s.ChildGoal(2).Conclusion().AlphaEquals(c.Q.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// Two hops through a conjunctive closure: at x := add(a, neg(a)) the
// guard `P(add(a, neg(a)))` is the closure under add of `P(a)` and
// `P(neg(a))`, the latter the closure under neg of `P(a)`.
func TestSimpWith_ClosureRule_DischargesAGuardTwoHops(t *testing.T) {
	defer goleak.VerifyNone(t)
	c := closureVars()
	v := c.structureFixture
	member := v.add.Apply(v.a, v.neg.Apply(v.a))

	goal := testProp(c.Q.Apply(v.add.Apply(v.neg.Apply(member), member)).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core())
	s := SimpWithExpand(goal, []Prop{c.leftInverse, c.addIn, c.negIn})
	require.NotNil(t, s)
	require.Equal(t, 4, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(c.leftInverse))
	assert.True(t, s.ChildGoal(1).AlphaEquals(c.addIn))
	assert.True(t, s.ChildGoal(2).AlphaEquals(c.negIn))
	assert.True(t, s.ChildGoal(3).Conclusion().AlphaEquals(c.Q.Apply(v.zero).Core()))
	reconstructWithAssumed(t, s, goal)
}

// Without the closure rule the guard is not invented: the same goal
// and law alone fire nothing.
func TestSimpWith_ClosureRule_NotInTheSet(t *testing.T) {
	defer goleak.VerifyNone(t)
	c := closureVars()
	v := c.structureFixture

	goal := testProp(c.Q.Apply(v.add.Apply(v.neg.Apply(v.neg.Apply(v.a)), v.neg.Apply(v.a))).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core())
	require.Nil(t, SimpWithExpand(goal, []Prop{c.leftInverse}))
}

// A rule whose antecedent is no smaller than its conclusion
// (`P(f(x)) ⇒ P(x)`) is not a descent: the chain would not terminate,
// so the rule is never taken, and the step declines instead.
func TestSimpWith_ClosureRule_NonDescendingRuleIsNotTaken(t *testing.T) {
	defer goleak.VerifyNone(t)
	c := closureVars()
	v := c.structureFixture
	ascending := testProp(ForAll(v.x)(v.P.Apply(c.f.Apply(v.x)).Imply(v.P.Apply(v.x))).Core())
	require.NotEmpty(t, ClosureSimpClauses(ascending))

	goal := testProp(c.Q.Apply(v.add.Apply(v.neg.Apply(v.neg.Apply(v.a)), v.neg.Apply(v.a))).Core(),
		v.G.Apply(v.add, v.zero, v.neg).Core(), v.P.Apply(v.a).Core())
	require.Nil(t, SimpWithExpand(goal, []Prop{c.leftInverse, ascending}))
}
