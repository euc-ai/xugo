// step_by_where_test.go — a premise pinned by name (Fact.Where / the
// session's sparse term_specialize):
//
//  1. SEEDED APPLY: a law whose conclusion is a RELATION applied to
//     terms — `R(x, k(x))` — has no first-order match against an
//     equation goal (the flex head binds to `=` and the arguments then
//     disagree); pinning R at the relation the author means turns the
//     conclusion into a first-order pattern, the remaining binder is
//     read off the goal, the antecedent from the context, and the leaf
//     closes by kernel apply — keyless, nothing recorded.
//  2. THE PIN IS AN INSTRUCTION: a named premise that does not apply
//     fails the By with the rung's nearest miss; it is never handed to
//     the closer as a bare law.
//  3. THE PIN NEEDS THE RUNG: the arith closer and Raw refuse it.
//  4. THE WIRE CARRIES IT: the recorded composite serializes the named
//     table beside the install.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// relationLawFixture: the law, the guard, and the goal —
//
//	∀R:ind→ind→bool. ∀x:ind. Q(x) ⇒ R(x, k(x)),   Q(a)   ⊢   zk(a) = k(a)
//
// and the relation the author pins: R := λu v. zk(u) = v.
func relationLawFixture(t *testing.T) (law, guard, goal Prop, relation core.Term) {
	t.Helper()
	ind := TypeInd
	rel := core.MakeFun(ind, core.MakeFun(ind, core.TypeBool()))
	R := ext.Var("R", rel)
	Q := ext.Var("Q", core.MakeFun(ind, core.TypeBool()))
	k := ext.Var("k", core.MakeFun(ind, ind))
	a := ext.Var("a", ind)
	x := ext.Var("x", ind)
	u := ext.Var("u", ind)
	v := ext.Var("v", ind)
	zk := ext.WrapTerm(zkConst)

	lawTerm := ext.ForAll(R)(ext.ForAll(x)(Q.Apply(x).Imply(R.Apply(x, k.Apply(x)))))
	guardTerm := Q.Apply(a)
	concl := zk.Apply(a).Eq(k.Apply(a))
	relation = lambda(u, lambda(v, zk.Apply(u).Eq(v).Core()))
	return prop.MakeProp(lawTerm.Core()), prop.MakeProp(guardTerm.Core()),
		prop.MakeProp(concl.Core(), guardTerm.Core()), relation
}

func whereBySpec(law, guard Prop, relation core.Term) BySpec {
	return BySpec{Premises: []ByPremiseSpec{
		{Install: guard, Resident: true, Describe: "guard"},
		{Install: law, Named: []NamedWitness{{Binder: "R", Witness: relation}}, Describe: "relation law"},
	}}
}

func TestByWhere_SeededRelationClosesKeyless(t *testing.T) {
	law, guard, goal, relation := relationLawFixture(t)

	// Control: bare, the rung's first-order approximation cannot read a
	// relation off an equation, so the law reaches the closer as a wide
	// ∀R-hypothesis and the close is a SEARCH — recorded under a key.
	{
		ctl := newGroundByStore()
		env := groundTestEnv(t)
		ctl.wire(env, true)
		bare := BySpec{Premises: []ByPremiseSpec{
			{Install: guard, Resident: true, Describe: "guard"},
			{Install: law, Describe: "relation law (bare)"},
		}}
		closed := func() (ok bool) {
			defer func() { _ = recover() }()
			return ApplyByStep(CreateGoalStack(goal), env, t.Context(), bare)
		}()
		if closed {
			assert.NotEmpty(t, ctl.Proofs(), "bare, the close is the refuter's and mints a key")
		}
	}

	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), whereBySpec(law, guard, relation)), "live By must close")
	assert.Empty(t, st.Proofs(), "keyless: the seeded apply closed it, not the refuter")
	assert.Empty(t, st.Plans(), "and no grounding plan was needed")
	open := 0
	for _, c := range n.Children() {
		if !c.Proved() {
			open++
		}
	}
	assert.Equal(t, 1, open, "one claim obligation — the law's on-demand install")

	strict := groundTestEnv(t)
	newGroundByStore().wire(strict, true)
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), whereBySpec(law, guard, relation)),
		"strict replay closes from an EMPTY store — the move records nothing")
}

func TestByWhere_PinIsAnInstruction(t *testing.T) {
	law, guard, goal, _ := relationLawFixture(t)
	ind := TypeInd
	u := ext.Var("u", ind)
	v := ext.Var("v", ind)
	// A relation that does not read the goal: R := λu v. u = v gives
	// the conclusion `x = k(x)`, which `zk(a) = k(a)` is not.
	wrong := lambda(u, lambda(v, u.Eq(v).Core()))

	t.Run("a seed the goal does not match names the miss", func(t *testing.T) {
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		mustPanicContaining(t, "pinned by name did not apply", func() {
			ApplyByStep(CreateGoalStack(goal), env, t.Context(), whereBySpec(law, guard, wrong))
		})
	})
	t.Run("an unknown binder name is refused", func(t *testing.T) {
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		_, _, _, relation := relationLawFixture(t)
		spec := BySpec{Premises: []ByPremiseSpec{
			{Install: guard, Resident: true, Describe: "guard"},
			{Install: law, Named: []NamedWitness{{Binder: "S", Witness: relation}}, Describe: "relation law"},
		}}
		mustPanicContaining(t, `no ∀-binder named "S"`, func() {
			ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec)
		})
	})
	t.Run("a resident premise takes no named table", func(t *testing.T) {
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		_, _, _, relation := relationLawFixture(t)
		spec := BySpec{Premises: []ByPremiseSpec{
			{Install: guard, Resident: true, Named: []NamedWitness{{Binder: "R", Witness: relation}}, Describe: "guard"},
		}}
		mustPanicContaining(t, "grounded positionally", func() {
			ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec)
		})
	})
}

func TestByWhere_NeedsTheApplyRung(t *testing.T) {
	law, guard, goal, relation := relationLawFixture(t)
	t.Run("arith closer", func(t *testing.T) {
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		spec := whereBySpec(law, guard, relation)
		spec.Arith = true
		mustPanicContaining(t, "the arith closer does not run the rung", func() {
			ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec)
		})
	})
	t.Run("raw shape", func(t *testing.T) {
		env := groundTestEnv(t)
		newGroundByStore().wire(env, true)
		spec := whereBySpec(law, guard, relation)
		spec.Shapes = []ByShape{Raw}
		mustPanicContaining(t, "Raw suppresses the conditioning stage", func() {
			ApplyByStep(CreateGoalStack(goal), env, t.Context(), spec)
		})
	})
}

func TestByWhere_RecordedOnTheWire(t *testing.T) {
	law, guard, goal, relation := relationLawFixture(t)
	env := groundTestEnv(t)
	newGroundByStore().wire(env, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), whereBySpec(law, guard, relation)))

	step, ok := n.miniStep.(_ByStep)
	require.True(t, ok, "the recorded ministep is the By composite")
	b := ext.NewPoolBuilder()
	byProto := step.proto(b).(*StepProto_By).By
	require.Len(t, byProto.GetPremises(), 2)
	named := byProto.GetPremises()[1].GetNamed()
	require.Len(t, named, 1, "the named table travels beside the install")
	assert.Equal(t, "R", named[0].GetBinder())
	assert.Empty(t, byProto.GetPremises()[1].GetWitnesses(), "and no positional tuple")
}

func TestFactWhere_ValueContract(t *testing.T) {
	_, _, _, relation := relationLawFixture(t)
	f := NamedFact(depName("law")).Where("R", relation)
	assert.Contains(t, f.describe(), `where R :=`)
	assert.Panics(t, func() { f.At(relation) }, "At after Where")
	assert.Panics(t, func() { NamedFact(depName("law")).At(relation).Where("R", relation) }, "Where after At")
	assert.Panics(t, func() { f.Where("R", relation) }, "a binder pinned twice")
	assert.Panics(t, func() { NamedFact(depName("law")).Where("", relation) }, "an empty binder name")
}

// lambda abstracts a test variable over a body: λv. body.
func lambda(v *ext.TermWrapper, body core.Term) core.Term {
	return core.Abs(v.Core().(core.VarTerm), body)
}
