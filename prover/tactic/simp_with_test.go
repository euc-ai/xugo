package tactic

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// simpFixture: f, g, h : A→A; P, Q : A→bool; a : A.
func simpVars() (x, a *ext.TermWrapper, f, g, h, P, Q *ext.TermWrapper) {
	x = ext.WrapTerm(Var("x", TypeA))
	a = ext.WrapTerm(Var("a", TypeA))
	fn := MakeFun(TypeA, TypeA)
	pr := MakeFun(TypeA, TypeBool)
	f = ext.WrapTerm(Var("f", fn))
	g = ext.WrapTerm(Var("g", fn))
	h = ext.WrapTerm(Var("h", fn))
	P = ext.WrapTerm(Var("P", pr))
	Q = ext.WrapTerm(Var("Q", pr))
	return
}

// Two unconditional rules chain in ONE simp_with call (joint fixpoint):
// f→g then g→h inside P(·).
func TestSimpWith_UnconditionalJointFixpoint(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, _ := simpVars()

	r1 := testProp(ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())
	r2 := testProp(ForAll(x)(g.Apply(x).Eq(h.Apply(x))).Core())
	goal := testProp(P.Apply(f.Apply(a)).Core())

	s := SimpWithExpand(goal, []Prop{r1, r2})
	require.NotNil(t, s)
	require.Equal(t, 3, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(r1))
	assert.True(t, s.ChildGoal(1).AlphaEquals(r2))
	assert.True(t, s.ChildGoal(2).Conclusion().AlphaEquals(P.Apply(h.Apply(a)).Core()))
}

// The residual reading is the last child of the step the same rules
// make — at the conclusion and at a hypothesis — and nil where no rule
// fires. It is built as a probe's step, whose reconstruction is not run.
func TestSimpResidualReading_IsTheStepsLastChild(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, Q := simpVars()

	r1 := testProp(ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())
	r2 := testProp(ForAll(x)(g.Apply(x).Eq(h.Apply(x))).Core())
	rules := []Prop{r1, r2}
	goal := testProp(P.Apply(f.Apply(a)).Core(), Q.Apply(f.Apply(a)).Core())

	step := SimpWithExpand(goal, rules)
	require.NotNil(t, step)
	reading := SimpResidualReading(goal, nil, rules, nil, nil)
	require.NotNil(t, reading)
	assert.True(t, reading.AlphaEquals(step.ChildGoal(step.Size()-1)))
	assert.True(t, reading.Conclusion().AlphaEquals(P.Apply(h.Apply(a)).Core()))

	hyp := 0
	atHyp, rewritten := SimpWithExpandFlippedAt(goal, hyp, rules, nil)
	require.NotNil(t, atHyp)
	reading = SimpResidualReading(goal, &hyp, rules, nil, nil)
	require.NotNil(t, reading)
	assert.True(t, reading.AlphaEquals(atHyp.ChildGoal(atHyp.Size()-1)))
	assert.True(t, reading.HasHyp(rewritten))

	settled := testProp(P.Apply(h.Apply(a)).Core())
	assert.Nil(t, SimpWithExpand(settled, rules))
	assert.Nil(t, SimpResidualReading(settled, nil, rules, nil, nil))

	gated := simpWithExpandUnder(fullSearch, goal, rules, nil, nil)
	require.NotNil(t, gated)
	assert.NotNil(t, gated.onOwnGoals, "a step a proof folds is reconstructed on its own goals as it is built")
	probe := simpWithExpandUnder(probeSearch(context.Background()), goal, rules, nil, nil)
	require.NotNil(t, probe)
	assert.Nil(t, probe.onOwnGoals, "the residual reading reconstructs nothing")
}

// A run of a rule set over a goal leaves in its cache the normal forms
// of the nodes its rules failed on, and a second run over the same goal
// through the same cache computes none: it is what a step's
// reconstruction reads, which runs the set again.
func TestSimpWith_ASecondRunReadsTheFirstRunsNormalForms(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, _, P, Q := simpVars()

	rule := testProp(ForAll(x)(f.Apply(f.Apply(x)).Eq(g.Apply(x))).Core())
	goal := testProp(P.Apply(f.Apply(a)).Imply(Q.Apply(a)).And(P.Apply(f.Apply(f.Apply(a)))).Core())
	want := P.Apply(f.Apply(a)).Imply(Q.Apply(a)).And(P.Apply(g.Apply(a))).Core()

	preCNF := new(prop.PreCNFCache)
	first := runSimpPipeline(preCNF, goal, []Prop{rule}, nil)
	require.NotNil(t, first)
	assert.True(t, prop.Rhs(first.bridge).AlphaEquals(want))
	held := preCNF.TermCacheSize()
	require.Positive(t, held, "the implication the rule fails on is read in its normal form")

	second := runSimpPipeline(preCNF, goal, []Prop{rule}, nil)
	require.NotNil(t, second)
	assert.True(t, prop.Rhs(second.bridge).AlphaEquals(prop.Rhs(first.bridge)))
	assert.Equal(t, held, preCNF.TermCacheSize(), "the second run computes no normal form")
}

// A conditional Horn rule fires with its side condition discharged
// against a goal hypothesis.
func TestSimpWith_ConditionalHorn_HypDischarge(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, _, P, Q := simpVars()

	rule := testProp(ForAll(x)(Q.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x)))).Core())
	goal := testProp(P.Apply(f.Apply(a)).Core(), Q.Apply(a).Core())

	s := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(rule))
	child := s.ChildGoal(1)
	assert.True(t, child.Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()))
	assert.True(t, child.HasHyp(Q.Apply(a).Core()))
}

// Same rule in its normalized clause form ¬Q(x) ∨ (f(x) = g(x)).
func TestSimpWith_ConditionalClauseForm_HypDischarge(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, _, P, Q := simpVars()

	rule := testProp(ForAll(x)(ext.Not(Q.Apply(x)).Or(f.Apply(x).Eq(g.Apply(x)))).Core())
	goal := testProp(P.Apply(f.Apply(a)).Core(), Q.Apply(a).Core())

	s := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()))
}

// Side condition discharged by a fact rule in the set.
func TestSimpWith_ConditionalHorn_FactDischarge(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, _, P, Q := simpVars()

	rule := testProp(ForAll(x)(Q.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x)))).Core())
	fact := testProp(ForAll(x)(Q.Apply(x)).Core())
	goal := testProp(P.Apply(f.Apply(a)).Core())

	s := SimpWithExpand(goal, []Prop{rule, fact})
	require.NotNil(t, s)
	require.Equal(t, 3, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(rule))
	assert.True(t, s.ChildGoal(1).AlphaEquals(fact))
	assert.True(t, s.ChildGoal(2).Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()))
}

// Side condition discharged by the set's own UNCONDITIONAL rewrites
// reducing it to ⊤ (route (c)).
func TestSimpWith_ConditionalHorn_RewriteDischarge(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, _, P, Q := simpVars()

	rule := testProp(ForAll(x)(Q.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x)))).Core())
	qTrue := testProp(ForAll(x)(Q.Apply(x).Eq(ext.T)).Core())
	goal := testProp(P.Apply(f.Apply(a)).Core())

	s := SimpWithExpand(goal, []Prop{rule, qTrue})
	require.NotNil(t, s)
	child := s.ChildGoal(s.Size() - 1)
	assert.True(t, child.Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()))
}

// An UNUSED rule must not appear among the children (dep hygiene).
func TestSimpWith_UnusedRuleNotCited(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, _ := simpVars()

	r1 := testProp(ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())
	// r2 rewrites h — absent from the goal.
	rUnused := testProp(ForAll(x)(h.Apply(x).Eq(f.Apply(x))).Core())
	goal := testProp(P.Apply(f.Apply(a)).Core())

	s := SimpWithExpand(goal, []Prop{r1, rUnused})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(r1))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()))
}

// Progress-or-fail: nothing fires → nil. A rule α-equal to the goal → nil.
func TestSimpWith_NoFireAndCircularGuard(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, _ := simpVars()

	r1 := testProp(ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())
	assert.Nil(t, SimpWithExpand(testProp(P.Apply(h.Apply(a)).Core()), []Prop{r1}))
	assert.Nil(t, SimpWithExpand(r1, []Prop{r1}))
	assert.Nil(t, SimpWithExpand(testProp(P.Apply(f.Apply(a)).Core()), nil))
}

// A conditional redex whose side condition has NO discharge route must
// not fire (and must not poison the rest of the set).
func TestSimpWith_UndischargeableConditionDoesNotFire(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, Q := simpVars()

	cond := testProp(ForAll(x)(Q.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x)))).Core())
	uncond := testProp(ForAll(x)(h.Apply(x).Eq(f.Apply(x))).Core())
	// Goal has no Q(a) hyp and no fact/rewrite route: only h→f fires.
	goal := testProp(P.Apply(h.Apply(a)).Core())

	s := SimpWithExpand(goal, []Prop{cond, uncond})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(uncond))
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(P.Apply(f.Apply(a)).Core()))
}

// A rewrite by an earlier rule EXPOSES a conditional redex mined in a
// later round — the pattern of nat_sum unfolding into monoidal.Union.
func TestSimpWith_RoundInteraction_UncondExposesConditional(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, Q := simpVars()

	unfold := testProp(ForAll(x)(h.Apply(x).Eq(f.Apply(x))).Core())
	condRule := testProp(ForAll(x)(Q.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x)))).Core())
	goal := testProp(P.Apply(h.Apply(a)).Core(), Q.Apply(a).Core())

	s := SimpWithExpand(goal, []Prop{condRule, unfold})
	require.NotNil(t, s)
	child := s.ChildGoal(s.Size() - 1)
	assert.True(t, child.Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()))
}

// The sum-over-a-union shape
// modeled with opaque function vars: (1) an unconditional def-unfold
// `ns(s,h) = it(plus,s,h)`, (2) the normalized-clause-form conditional
// union law with FOUR side conditions, (3) the ground fact
// mono(plus). One simp_with call must unfold ns, mine the conditional
// instance (mono via the fact, FIN/FIN/DISJ via hyps), rewrite, and
// leave a refl residual.
func TestSimpWith_NsumUnionShape(t *testing.T) {
	defer goleak.VerifyNone(t)

	opT := MakeFun(TypeA, MakeFun(TypeA, TypeA))
	hT := MakeFun(TypeA, TypeA)
	x := ext.WrapTerm(Var("x", TypeA))
	s := ext.WrapTerm(Var("s", TypeA))
	tt := ext.WrapTerm(Var("t", TypeA))
	h := ext.WrapTerm(Var("h", hT))
	op := ext.WrapTerm(Var("op", opT))
	plus := ext.WrapTerm(Var("plus", opT))
	un := ext.WrapTerm(Var("un", opT))
	fin := ext.WrapTerm(Var("FIN", MakeFun(TypeA, TypeBool)))
	disj := ext.WrapTerm(Var("DISJ", MakeFun(TypeA, MakeFun(TypeA, TypeBool))))
	mono := ext.WrapTerm(Var("mono", MakeFun(opT, TypeBool)))
	it := ext.WrapTerm(Var("it", MakeFun(opT, MakeFun(TypeA, MakeFun(hT, TypeA)))))
	ns := ext.WrapTerm(Var("ns", MakeFun(TypeA, MakeFun(hT, TypeA))))
	s0 := ext.WrapTerm(Var("s0", TypeA))
	t0 := ext.WrapTerm(Var("t0", TypeA))
	h0 := ext.WrapTerm(Var("h0", hT))
	_ = x

	// (1) def unfold: ∀s h. ns(s, h) = it(plus, s, h)
	natSumDef := testProp(ForAll(s, h)(ns.Apply(s, h).Eq(it.Apply(plus, s, h))).Core())
	// (2) the union law, normalized clause form:
	// ∀op s t h. ¬mono(op) ∨ ¬FIN(s) ∨ ¬FIN(t) ∨ ¬DISJ(s,t) ∨
	//            (it(op, un(s,t), h) = op(it(op,s,h), it(op,t,h)))
	iterateUnion := testProp(ForAll(op, s, tt, h)(
		ext.Not(mono.Apply(op)).
			Or(ext.Not(fin.Apply(s))).
			Or(ext.Not(fin.Apply(tt))).
			Or(ext.Not(disj.Apply(s, tt))).
			Or(it.Apply(op, un.Apply(s, tt), h).Eq(op.Apply(it.Apply(op, s, h), it.Apply(op, tt, h))))).Core())
	// (3) the ground fact mono(plus).
	monoidalAdd := testProp(mono.Apply(plus).Core())

	// Goal: FIN(s0), FIN(t0), DISJ(s0,t0) ⊢
	//       ns(un(s0,t0), h0) = plus(it(plus,s0,h0), it(plus,t0,h0))
	goal := testProp(
		ns.Apply(un.Apply(s0, t0), h0).
			Eq(plus.Apply(it.Apply(plus, s0, h0), it.Apply(plus, t0, h0))).Core(),
		fin.Apply(s0).Core(), fin.Apply(t0).Core(), disj.Apply(s0, t0).Core())

	sg := SimpWithExpand(goal, []Prop{natSumDef, iterateUnion, monoidalAdd})
	require.NotNil(t, sg, "the one-liner shape of nat_sum.Union must fire")
	require.Equal(t, 4, sg.Size(), "children: 3 used rules + residual")
	assert.True(t, sg.ChildGoal(0).AlphaEquals(natSumDef))
	assert.True(t, sg.ChildGoal(1).AlphaEquals(iterateUnion))
	assert.True(t, sg.ChildGoal(2).AlphaEquals(monoidalAdd))
	// Residual: both sides rewritten to the same term — a refl equation.
	wantBoth := plus.Apply(it.Apply(plus, s0, h0), it.Apply(plus, t0, h0)).Core()
	l, r, ok := MatchesEQ(sg.ChildGoal(3).Conclusion())
	require.True(t, ok)
	assert.True(t, l.AlphaEquals(wantBoth), "LHS fully rewritten, got %v", sg.ChildGoal(3))
	assert.True(t, r.AlphaEquals(wantBoth))
}

// Multi-condition rule: both conditions discharge from hyps.
func TestSimpWith_MultiCondition(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, _, P, Q := simpVars()
	R := ext.WrapTerm(Var("R", MakeFun(TypeA, TypeBool)))

	rule := testProp(ForAll(x)(Q.Apply(x).Imply(R.Apply(x).Imply(f.Apply(x).Eq(g.Apply(x))))).Core())
	goal := testProp(P.Apply(f.Apply(a)).Core(), Q.Apply(a).Core(), R.Apply(a).Core())

	s := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, s)
	child := s.ChildGoal(s.Size() - 1)
	assert.True(t, child.Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()))
}

// Regression: simp_with fires a pair-comprehension-membership-shaped HO rule (flexible
// predicate P under ∃-binders — Miller pattern) against a concrete
// comprehension membership? This is the load-bearing question for the
// lemma2 class (prop_b4dcf11ec981a1f1, the 51-step manual ladder).
func TestSimpWith_HOComprehensionRule(t *testing.T) {
	defer goleak.VerifyNone(t)

	A := TypeA
	B := TypeB // opaque "pair" carrier
	x := ext.WrapTerm(Var("x", A))
	y := ext.WrapTerm(Var("y", A))
	u := ext.WrapTerm(Var("u", A))
	v := ext.WrapTerm(Var("v", A))
	g := ext.WrapTerm(Var("g", B))
	P := ext.WrapTerm(Var("P", MakeFun(A, MakeFun(A, TypeBool))))
	q1 := ext.WrapTerm(Var("q1", MakeFun(A, TypeBool)))
	q2 := ext.WrapTerm(Var("q2", MakeFun(A, TypeBool)))
	a0 := ext.WrapTerm(Var("a0", A))
	b0 := ext.WrapTerm(Var("b0", A))
	mkp := ext.WrapTerm(Var("mkp", MakeFun(A, MakeFun(A, B))))
	setComprehension := ext.WrapTerm(Var("comp", MakeFun(MakeFun(B, TypeBool), MakeFun(B, TypeBool))))
	comprehensionSpec := ext.WrapTerm(Var("spec", MakeFun(B, MakeFun(TypeBool, MakeFun(B, TypeBool)))))

	// rule (pair-comprehension membership, flipped, applicative form):
	// ∀P u v. comp(λg. ∃x y. spec(g, P(x,y), mkp(x,y)))(mkp(u,v)) ⇔ P(u,v)
	comprehension := func(pred func(xx, yy *ext.TermWrapper) *ext.TermWrapper) *ext.TermWrapper {
		return setComprehension.Apply(g.To(ext.Exists(x, y)(comprehensionSpec.Apply(g, pred(x, y), mkp.Apply(x, y)))))
	}
	rule := testProp(ForAll(P, u, v)(
		comprehension(func(xx, yy *ext.TermWrapper) *ext.TermWrapper { return P.Apply(xx, yy) }).
			Apply(mkp.Apply(u, v)).
			Eq(P.Apply(u, v))).Core())

	// goal: comp(λg. ∃x y. spec(g, q1(x) ∧ q2(y), mkp(x,y)))(mkp(a0,b0))
	//       ⇔ (q1(a0) ∧ q2(b0))
	lhs := comprehension(func(xx, yy *ext.TermWrapper) *ext.TermWrapper { return q1.Apply(xx).And(q2.Apply(yy)) }).
		Apply(mkp.Apply(a0, b0))
	want := q1.Apply(a0).And(q2.Apply(b0))
	goal := testProp(lhs.Eq(want).Core())

	sg := SimpWithExpand(goal, []Prop{rule})
	if sg == nil {
		t.Fatalf("HO comprehension rule did NOT fire")
	}
	residual := sg.ChildGoal(sg.Size() - 1)
	l, r, ok := MatchesEQ(residual.Conclusion())
	require.True(t, ok)
	require.True(t, l.AlphaEquals(want.Core()), "LHS must rewrite to the β-reduced predicate instance, got %v", l)
	require.True(t, r.AlphaEquals(want.Core()))
}

// The shape met in a cardinality-of-a-union proof: a permutative rule pair (COMM + ASSOC) over a
// deep ground nest slips every fireWhistle blade but the
// ordered-permutation one — permuted RHSs are same-size (blade 1
// silent), don't path-embed their LHS (blade 2's growth run keeps
// resetting), and pairwise never embed each other (blade 3's WQO
// antichain stretches over the ~8!·Catalan(7) distinct AC forms while
// every allowed fire pays an O(traj) embed sweep). Unbounded, one
// SimpWithExpand call holds the session mutex and no probe budget_ms
// interrupts it.
//
// Contract under test: SimpWithExpand RETURNS in bounded time. The
// result's content is irrelevant (nil or a bridge both fine) — only
// termination is asserted.
func TestSimpWith_PermutativeStormTerminates(t *testing.T) {
	x := ext.WrapTerm(Var("x", TypeA))
	y := ext.WrapTerm(Var("y", TypeA))
	z := ext.WrapTerm(Var("z", TypeA))
	u := ext.WrapTerm(Var("u", MakeFun(TypeA, MakeFun(TypeA, TypeA))))
	P := ext.WrapTerm(Var("P", MakeFun(TypeA, TypeBool)))

	comm := testProp(ForAll(x, y)(
		u.Apply(x, y).Eq(u.Apply(y, x))).Core())
	assoc := testProp(ForAll(x, y, z)(
		u.Apply(u.Apply(x, y), z).Eq(u.Apply(x, u.Apply(y, z)))).Core())

	// 8 ground atoms in a right-nest — the shape from the live repro
	// (card(union(a, union(b, …))) with 8 sets).
	atoms := make([]*ext.TermWrapper, 8)
	for i := range atoms {
		atoms[i] = ext.WrapTerm(Var(core.TermName(fmt.Sprintf("c%d", i)), TypeA))
	}
	nest := atoms[len(atoms)-1]
	for i := len(atoms) - 2; i >= 0; i-- {
		nest = u.Apply(atoms[i], nest)
	}
	goal := testProp(P.Apply(nest).Core())

	done := make(chan struct{})
	go func() {
		defer close(done)
		SimpWithExpand(goal, []Prop{comm, assoc})
	}()
	select {
	case <-done:
	case <-time.After(60 * time.Second):
		t.Fatal("permutative COMM+ASSOC storm: SimpWithExpand did not return within 60s (fireWhistle blades all blind to same-size permutation churn)")
	}
}

// Same storm through the normalized POINTWISE form — the exact shape of
// the live wedge. union-class lemmas normalize to
// `∀s.∀t.∀ẋ. union(s,t,ẋ) ⇔ union(t,s,ẋ)`; rewriting a
// function-position occurrence (`card(union(a, …))`) η-lifts the rule
// and wraps one un-β-reduced λ-application layer PER FIRE, so every
// RHS is structurally fresh and the trajectory antichain never cuts.
// The first-order variant above self-limits (~1 s); this one is the
// >45 s live hang.
func TestSimpWith_PermutativePointwiseStormTerminates(t *testing.T) {
	SET := MakeFun(TypeA, TypeBool)
	s := ext.WrapTerm(Var("s", SET))
	tt := ext.WrapTerm(Var("t", SET))
	r := ext.WrapTerm(Var("r", SET))
	xd := ext.WrapTerm(Var("xd", TypeA))
	un := ext.WrapTerm(Var("un", MakeFun(SET, MakeFun(SET, SET))))
	card := ext.WrapTerm(Var("card", MakeFun(SET, TypeB)))

	// ∀s t ẋ. un(s,t)(ẋ) ⇔ un(t,s)(ẋ)
	commPW := testProp(ForAll(s, tt, xd)(
		un.Apply(s, tt).Apply(xd).Eq(un.Apply(tt, s).Apply(xd))).Core())
	// ∀s t r ẋ. un(un(s,t),r)(ẋ) ⇔ un(s,un(t,r))(ẋ)
	assocPW := testProp(ForAll(s, tt, r, xd)(
		un.Apply(un.Apply(s, tt), r).Apply(xd).
			Eq(un.Apply(s, un.Apply(tt, r)).Apply(xd))).Core())

	atoms := make([]*ext.TermWrapper, 12)
	for i := range atoms {
		atoms[i] = ext.WrapTerm(Var(core.TermName(fmt.Sprintf("d%d", i)), SET))
	}
	nestFwd := atoms[len(atoms)-1]
	for i := len(atoms) - 2; i >= 0; i-- {
		nestFwd = un.Apply(atoms[i], nestFwd)
	}
	nestRev := atoms[0]
	for i := 1; i < len(atoms); i++ {
		nestRev = un.Apply(atoms[i], nestRev)
	}
	// card(nestFwd) = card(nestRev) — the live repro's goal shape.
	goal := testProp(card.Apply(nestFwd).Eq(card.Apply(nestRev)).Core())

	done := make(chan struct{})
	go func() {
		defer close(done)
		SimpWithExpand(goal, []Prop{commPW, assocPW})
	}()
	select {
	case <-done:
	case <-time.After(60 * time.Second):
		t.Fatal("pointwise COMM+ASSOC storm: SimpWithExpand did not return within 60s (η-lift λ-wrapping makes every RHS fresh; trajectory antichain never cuts)")
	}
}

// Left-commutativity (x∘(y∘z) = y∘(x∘z)) is the storm shape the fire
// whistle's instance-level classifier CANNOT see: LC instances are
// unordered-DISTINCT trees (the swapped atoms sit at different depths),
// so PermutationFireAllowed never gates them. The rule-level variants
// test does — unifyEqRewriteImpl certifies the rule permutative
// (skeleton.PermutativeRulePattern) and gates every instance on strict
// Compare decrease, so an 8-atom reversed comb bubble-sorts and
// terminates instead of 2-cycling until the trajectory blade saturates.
// The full ac_simps-style triple (COMM+ASSOC+LC) is included: this is
// the Isabelle AC-normalization rule set.
func TestSimpWith_LeftCommOrderedTerminates(t *testing.T) {
	x := ext.WrapTerm(Var("x", TypeA))
	y := ext.WrapTerm(Var("y", TypeA))
	z := ext.WrapTerm(Var("z", TypeA))
	u := ext.WrapTerm(Var("u", MakeFun(TypeA, MakeFun(TypeA, TypeA))))
	P := ext.WrapTerm(Var("P", MakeFun(TypeA, TypeBool)))

	comm := testProp(ForAll(x, y)(
		u.Apply(x, y).Eq(u.Apply(y, x))).Core())
	assoc := testProp(ForAll(x, y, z)(
		u.Apply(u.Apply(x, y), z).Eq(u.Apply(x, u.Apply(y, z)))).Core())
	lc := testProp(ForAll(x, y, z)(
		u.Apply(x, u.Apply(y, z)).Eq(u.Apply(y, u.Apply(x, z)))).Core())

	// Reversed 8-atom right-comb: c7 ∘ (c6 ∘ (… ∘ c0)) — maximally
	// unsorted, so decreasing LC fires exist at every level. The atoms
	// are constants: the whistle's paths write every variable as one
	// token, under which each arrangement of eight variables embeds every
	// other and the trajectory blade cuts the sort.
	atoms := make([]*ext.TermWrapper, 8)
	for i := range atoms {
		atoms[i] = ext.TestConst(core.TermName(fmt.Sprintf("lcAtom%d", i)), TypeA)
	}
	nest := atoms[0]
	for i := 1; i < len(atoms); i++ {
		nest = un2(u, atoms[i], nest)
	}
	goal := testProp(P.Apply(nest).Core())

	before := skeleton.WhistleFires()
	done := make(chan struct{})
	var sg *SubGoals
	go func() {
		defer close(done)
		sg = SimpWithExpand(goal, []Prop{comm, assoc, lc})
	}()
	select {
	case <-done:
	case <-time.After(60 * time.Second):
		t.Fatal("LC storm: SimpWithExpand did not return within 60s (rule-level ordered rewriting must bound LC fires)")
	}
	// The reversed comb is maximally unsorted: the ordered AC set must
	// make progress, not just terminate, and it sorts with no cut.
	require.NotNil(t, sg, "ordered AC triple must fire on a reversed comb")
	assert.Equal(t, before, skeleton.WhistleFires(), "the sort ends by its order, not by the whistle")
	sorted := atoms[len(atoms)-1]
	for i := len(atoms) - 2; i >= 0; i-- {
		sorted = un2(u, atoms[i], sorted)
	}
	assert.True(t, sg.ChildGoal(sg.Size()-1).Conclusion().AlphaEquals(P.Apply(sorted).Core()))
}

// un2 applies a curried binary op — split out so the nest-builder loop
// above reads as a fold.
func un2(u, a, b *ext.TermWrapper) *ext.TermWrapper { return u.Apply(a, b) }

// A COND a rule INTRODUCES is decided by the resident guard — the
// context is read for it exactly as for a conditional rule's side
// condition (simpPipeline.condDecide / prop.CondDecideByHyps). The
// rule `f(x) = COND(Q(x), g(x), h(x))` unfolds f into a conditional;
// with Q(a) resident the residual is P(g(a)), with ¬Q(a) resident it is
// P(h(a)), and with neither the COND stays. The decision alone is not
// progress: a rule set that fires nothing fails as before even when a
// COND in the goal could be decided.
func TestSimpWith_CondDecidedByResidentGuard(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, Q := simpVars()
	rule := testProp(ForAll(x)(f.Apply(x).Eq(ext.Cond(Q.Apply(x), g.Apply(x), h.Apply(x)))).Core())
	conclusion := P.Apply(f.Apply(a)).Core()

	// Q(a) resident → the ⊤ branch.
	goal := testProp(conclusion, Q.Apply(a).Core())
	s := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(0).AlphaEquals(rule))
	child := s.ChildGoal(1)
	assert.True(t, child.Conclusion().AlphaEquals(P.Apply(g.Apply(a)).Core()),
		"the resident guard decides the COND the rule introduced: %s", prop.PrintProp(child))
	assert.True(t, child.HasHyp(Q.Apply(a).Core()))

	// ¬Q(a) resident → the ⊥ branch.
	goalNeg := testProp(conclusion, Not(Q.Apply(a)).Core())
	s = SimpWithExpand(goalNeg, []Prop{rule})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(P.Apply(h.Apply(a)).Core()),
		"the resident negated guard decides the COND: %s", prop.PrintProp(s.ChildGoal(1)))

	// A negated guard decided by the positive hyp: COND(¬Q(a), …) under Q(a).
	ruleNeg := testProp(ForAll(x)(f.Apply(x).Eq(ext.Cond(Not(Q.Apply(x)), g.Apply(x), h.Apply(x)))).Core())
	s = SimpWithExpand(goal, []Prop{ruleNeg})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(P.Apply(h.Apply(a)).Core()),
		"Q(a) decides COND(¬Q(a), …) to its ⊥ branch: %s", prop.PrintProp(s.ChildGoal(1)))

	// Nothing resident → the COND stays.
	goalBare := testProp(conclusion)
	s = SimpWithExpand(goalBare, []Prop{rule})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(
		P.Apply(ext.Cond(Q.Apply(a), g.Apply(a), h.Apply(a))).Core()),
		"no guard resident: the COND is left as the rule wrote it: %s", prop.PrintProp(s.ChildGoal(1)))

	// The decision alone is not progress: no rule fires, the step fails.
	condGoal := testProp(P.Apply(ext.Cond(Q.Apply(a), g.Apply(a), h.Apply(a))).Core(), Q.Apply(a).Core())
	inert := testProp(ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core()) // no f in the goal: no redex
	assert.Nil(t, SimpWithExpand(condGoal, []Prop{inert}),
		"a rule set that fires nothing fails even when the context decides a COND in the goal")
}

// The guard is compared to the hypothesis as a term: a guard mentioning
// a variable BOUND above the COND, spelled like a free variable of a
// hypothesis, is a different guard, and the capture-aware walk keeps
// it so — the COND under the binder stays.
func TestSimpWith_CondDecideDoesNotCaptureABinder(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, Q := simpVars()
	// f(a) = ∀x. P(COND(Q(x), g(x), h(x))) — bool-valued f here is
	// spelled through P: rule `P(f(y)) ⇔ ∀x. P(COND(Q(x), g(x), h(x)))`.
	y := ext.WrapTerm(Var("y", TypeA))
	body := ForAll(x)(P.Apply(ext.Cond(Q.Apply(x), g.Apply(x), h.Apply(x))))
	rule := testProp(ForAll(y)(P.Apply(f.Apply(y)).Eq(body)).Core())
	// The hyp Q(x) has x FREE; the goal's x under ∀ is a different x.
	goal := testProp(P.Apply(f.Apply(a)).Core(), Q.Apply(x).Core())
	s := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	got := s.ChildGoal(1).Conclusion()
	assert.True(t, got.AlphaEquals(body.Core()),
		"the bound x is not the hypothesis's free x; the COND stays: %s", prop.PrintProp(s.ChildGoal(1)))
}

// A side condition instantiated at a λ is read up to β: the rule's
// binder `k` is applied in its condition, the match binds it to a
// λ-term, and the instance `Q((λy. h(g(y)))(a))` is the resident
// `Q(h(g(a)))` — the form every hypothesis is kept in. Matched as
// substituted, the condition is found nowhere and the rule is silent.
func TestSimpWith_ConditionalHorn_SideConditionAtALambdaIsReadUpToBeta(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, _, g, h, P, Q := simpVars()
	fn := MakeFun(TypeA, TypeA)
	k := ext.WrapTerm(Var("k", fn))
	y := ext.WrapTerm(Var("y", TypeA))
	// F, G : (A → A) → A → A.
	F := ext.WrapTerm(Var("F", MakeFun(fn, MakeFun(TypeA, TypeA))))
	G := ext.WrapTerm(Var("G", MakeFun(fn, MakeFun(TypeA, TypeA))))

	rule := testProp(ForAll(k)(ForAll(x)(
		Q.Apply(k.Apply(x)).Imply(F.Apply(k, x).Eq(G.Apply(k, x))))).Core())
	composite := y.To(h.Apply(g.Apply(y)))
	resident := Q.Apply(h.Apply(g.Apply(a))).Core()
	goal := testProp(P.Apply(F.Apply(composite, a)).Core(), resident)

	s := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, s, "the side condition is resident up to β")
	require.Equal(t, 2, s.Size())
	child := s.ChildGoal(1)
	assert.True(t, child.Conclusion().AlphaEquals(P.Apply(G.Apply(composite, a)).Core()),
		"got %s", prop.PrintProp(child))
	assert.True(t, child.HasHyp(resident))
}

func TestSimpWith_BoundVariableDoesNotFeedRigidRule(t *testing.T) {
	j := core.Var("J", core.MakeVarType("A"))
	f := core.Var("f", core.MakeFun(core.MakeFun(j.Type(), j.Type()), j.Type()))
	p := core.Var("p", core.MakeFun(j.Type(), core.TypeBool()))
	rhs := core.Apply(f, core.Abs(j, j))
	rule := testProp(core.Eq(j, rhs))
	goal := testProp(core.Apply(p, j))
	before := skeleton.WhistleFires()
	s := SimpWithExpand(goal, []Prop{rule})
	require.NotNil(t, s)
	require.Equal(t, 2, s.Size())
	assert.True(t, s.ChildGoal(1).Conclusion().AlphaEquals(core.Apply(p, rhs)))
	assert.Equal(t, before, skeleton.WhistleFires())
}

func TestSimpWith_FailedConditionDoesNotRewriteBoundRuleVariable(t *testing.T) {
	j := ext.WrapTerm(core.Var("J", TypeA))
	x := ext.WrapTerm(core.Var("x", TypeA))
	a := ext.WrapTerm(core.Var("a", TypeA))
	c := ext.WrapTerm(core.Var("c", TypeA))
	d := ext.WrapTerm(core.Var("d", TypeA))
	f := ext.WrapTerm(core.Var("f", MakeFun(MakeFun(TypeA, TypeA), TypeA)))
	g := ext.WrapTerm(core.Var("g", MakeFun(TypeA, TypeA)))
	h := ext.WrapTerm(core.Var("h", MakeFun(TypeA, TypeA)))
	p := ext.WrapTerm(core.Var("p", MakeFun(TypeA, TypeBool)))
	q := ext.WrapTerm(core.Var("q", MakeFun(TypeA, TypeBool)))
	r := ext.WrapTerm(core.Var("R", MakeFun(TypeA, TypeBool)))
	rhs := f.Apply(j.To(j))
	rules := []Prop{
		testProp(j.Eq(rhs).Core()),
		testProp(r.Apply(c).Eq(r.Apply(d)).Core()),
		testProp(ForAll(x)(p.Apply(j).Imply(g.Apply(x).Eq(h.Apply(x)))).Core()),
	}
	goal := testProp(q.Apply(g.Apply(a)).And(r.Apply(c)).Core())
	before := skeleton.WhistleFires()
	result := SimpWithExpand(goal, rules)
	require.NotNil(t, result)
	assert.True(t, result.ChildGoal(result.Size()-1).Conclusion().AlphaEquals(
		q.Apply(g.Apply(a)).And(r.Apply(d)).Core()))
	assert.Equal(t, before, skeleton.WhistleFires())
}
