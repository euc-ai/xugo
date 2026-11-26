// apply_close_closure_test.go — the apply rung's carrier-membership
// decision: a chain of STRUCTURAL applies (every antecedent left to
// close a smaller term than its goal) spends no depth, so a membership
// nested however deep closes from the closure laws, as resident
// hypotheses or as named premises' stated forms taken inside an
// antecedent; a chain that does not descend keeps the depth contract
// (TestApplyClose_AntecedentIsALaw: three applies are the closer's).
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Resident closure laws: `P(0)` and the closure of P under f reach
// `P(f(f(f(0))))`, three applies, each a descent.
func TestApplyClose_StructuralChainSpendsNoDepth(t *testing.T) {
	closes := func(goalText string, strips int) (bool, string, *GoalStackNode) {
		t.Helper()
		res := dsl.ParsePropTextInScope(goalText, lawScope())
		require.Empty(t, res.Errors, "%s: %v", goalText, res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		for range strips {
			sec.Do(StripImp())
		}
		var claims []*GoalStackNode
		closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies})
		return closed, miss, sec
	}

	closed, miss, sec := closes("(∀n:num. P(n) ⇒ P(f(n))) ⇒ P(0) ⇒ (P(f(f(f(0)))) ⇒ Q) ⇒ Q", 3)
	require.True(t, closed, "three descents: %s", miss)
	require.True(t, sec.Proved())

	// A two-place closure, its antecedent a conjunction one of whose
	// conjuncts descends again: `P(g(0, f(0)))` from `P(0)`.
	closed, miss, sec = closes("(∀x y:num. P(x) ∧ P(y) ⇒ P(g(x, y))) ⇒ (∀n:num. P(n) ⇒ P(f(n))) ⇒ P(0) ⇒ "+
		"(P(g(0, f(0))) ⇒ Q) ⇒ Q", 4)
	require.True(t, closed, "a conjunctive closure over a descent: %s", miss)
	require.True(t, sec.Proved())

	// Not a descent: the antecedent is as large as the conclusion, so
	// the chain spends depth and three are the closer's.
	closed, _, _ = closes("(∀n:num. P(n) ⇒ H(n)) ⇒ (∀n:num. H(n) ⇒ K(n)) ⇒ (∀n:num. K(n) ⇒ M(n)) ⇒ P(0) ⇒ "+
		"(M(0) ⇒ Q) ⇒ Q", 5)
	require.False(t, closed, "a chain of equal-sized atoms is not structural")
}

// The closure laws as NAMED premises: inside an antecedent the rung
// takes a plain stated form as its head, installing it where it fires.
// The leaf holds only the structure fact and the member; the guarded
// law, the closure under inv and the closure under * are premises; the
// goal is the law at x * inv(x), whose guard is two closures deep.
//
//	law:   ∀x. P(x) ⇒ ∀y. zk(y) = g(x, y)
//	invIn: ∀x. P(x) ⇒ P(inv(x))
//	mulIn: ∀x y. P(x) ∧ P(y) ⇒ P(mul(x, y))
//	P(a)  ⊢  zk(b) = g(mul(a, inv(a)), b)
func TestByApply_ClosureLawsAsNamedPremisesInsideAnAntecedent(t *testing.T) {
	ind := TypeInd
	a := ext.Var("a", ind)
	b := ext.Var("b", ind)
	x := ext.Var("x", ind)
	y := ext.Var("y", ind)
	zk := ext.WrapTerm(zkConst)
	// Constants, not variables: a premise's normalized install closes
	// over its free variables, and a law over an arbitrary P or mul
	// would say far more than the stated one.
	g := ext.WrapTerm(core.NewConstDef(x.To(y.To(y)), "zz_closure_g"))
	mul := ext.WrapTerm(core.NewConstDef(x.To(y.To(x)), "zz_closure_mul"))
	inv := ext.WrapTerm(core.NewConstDef(x.To(x), "zz_closure_inv"))
	P := ext.WrapTerm(core.NewConstDef(x.To(x.Eq(x)), "zz_closure_p"))

	law := ext.ForAll(x)(P.Apply(x).Imply(ext.ForAll(y)(zk.Apply(y).Eq(g.Apply(x, y)))))
	invIn := ext.ForAll(x)(P.Apply(x).Imply(P.Apply(inv.Apply(x))))
	mulIn := ext.ForAll(x, y)(P.Apply(x).And(P.Apply(y)).Imply(P.Apply(mul.Apply(x, y))))
	member := P.Apply(a)
	concl := zk.Apply(b).Eq(g.Apply(mul.Apply(a, inv.Apply(a)), b))
	goal := prop.MakeProp(concl.Core(), member.Core())

	premise := func(stated *ext.TermWrapper, describe string) ByPremiseSpec {
		statedProp := prop.MakeProp(stated.Core())
		normalized, _ := prop.Normalize(statedProp)
		require.NotNil(t, normalized)
		return ByPremiseSpec{Install: normalized, Reference: statedProp, Describe: describe}
	}
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(member.Core()), Resident: true, Describe: "member"},
		premise(law, "guarded law"),
		premise(invIn, "closure under inv"),
		premise(mulIn, "closure under mul"),
	}}
	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "live By must close through the closure laws")
	assert.Empty(t, st.Proofs(), "keyless: the apply rung closed it, not the refuter")
	assert.Empty(t, st.Plans(), "and before the grounding stage, so no plan entry")

	// Strict replay from an empty store: the move records nothing.
	strict := groundTestEnv(t)
	newGroundByStore().wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), spec), "strict replay must close from an EMPTY store")

	// Without the closure under inv the guard is not invented: the leaf
	// reaches the refuter, which under the strict env is the cache MISS
	// panic.
	short := BySpec{Premises: []ByPremiseSpec{spec.Premises[0], spec.Premises[1], spec.Premises[3]}}
	strict2 := groundTestEnv(t)
	newGroundByStore().wire(strict2, true)
	strict2.RequireCNFCacheHit = true
	n3 := CreateGoalStack(goal)
	require.Panics(t, func() { ApplyByStep(n3, strict2, t.Context(), short) },
		"the guard P(inv(a)) has no closure law to come from")
}
