package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A bare polymorphic law already in normal form, cited at a goal that
// holds it at two instances: set_order.UnionSubset under a conjunction
// of unions over sets of D and sets of E. The install is one instance,
// the single type adaptation, so one conjunct finds its instance
// resident and the other does not. The law being its own clause form,
// its stated form was no head of the apply rung, and that conjunct
// reached the refuter with the law at the other instance. Its stated
// form is a head, and the enumeration reaches both instances: the By
// closes keyless, with a claim obligation at each.
func TestByApply_BareLawInNormalFormAtTwoInstances(t *testing.T) {
	law := parseFor(t, "∀s t u:(A → bool). s ∪ t ⊆ u ⇔ s ⊆ u ∧ t ⊆ u")
	if nl, _ := Normalize(law); nl != nil {
		require.True(t, nl.AsProp().AlphaEquals(law), "the fixture's law is its own clause form")
	}
	goal := parseFor(t, "s:(D → bool), t:(D → bool), w:(D → bool), a:(E → bool), b:(E → bool), c:(E → bool), "+
		"s ⊆ w, t ⊆ w, a ⊆ c, b ⊆ c ⊢ s ∪ t ⊆ w ∧ a ∪ b ⊆ c")
	instanceAt := func(p core.Prop) core.HolType {
		binders, _ := ematch.StripGuardedForalls(p.Conclusion())
		require.Len(t, binders, 3)
		return binders[0].Type()
	}
	sets := []core.HolType{goalVarType(t, goal, "w"), goalVarType(t, goal, "c")}
	installed := typematch.TryAdaptLemmaTypes(law, goal)
	require.NotNil(t, installed, "the install is adapted to one of the goal's instances")
	require.True(t, slicesContainType(sets, instanceAt(installed)),
		"the install is at one of the goal's instances, got %s", ext.FormatType(instanceAt(installed)))

	st := newGroundByStore()
	env := groundTestEnv(t)
	st.wire(env, true)
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(goal.Hyp(0)), Resident: true, Describe: "hyp 0"},
		{Install: prop.MakeProp(goal.Hyp(1)), Resident: true, Describe: "hyp 1"},
		{Install: prop.MakeProp(goal.Hyp(2)), Resident: true, Describe: "hyp 2"},
		{Install: prop.MakeProp(goal.Hyp(3)), Resident: true, Describe: "hyp 3"},
		{Install: prop.MakeProp(law.Conclusion()), Describe: "set_order.UnionSubset"},
	}}
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, env, t.Context(), spec), "the By closes")
	assert.Empty(t, st.Proofs(), "the apply rung closed both conjuncts, so no certificate")
	for _, want := range sets {
		found := false
		for _, c := range n.Children() {
			found = found || instanceAt(c.Goal).Equals(want)
		}
		require.True(t, found, "no claim obligation at the goal's instance %s", ext.FormatType(want))
	}
}

// slicesContainType reports whether ty is one of types.
func slicesContainType(types []core.HolType, ty core.HolType) bool {
	for _, t := range types {
		if t.Equals(ty) {
			return true
		}
	}
	return false
}

// goalVarType is the type of the goal's free variable name.
func goalVarType(t *testing.T, goal core.Prop, name string) core.HolType {
	t.Helper()
	for _, h := range append(goal.Hyps(), goal.Conclusion()) {
		for _, v := range h.Frees(nil) {
			if string(v.Name()) == name {
				return v.Type()
			}
		}
	}
	t.Fatalf("no free variable %s in %s", name, prop.PrintProp(goal))
	return nil
}
