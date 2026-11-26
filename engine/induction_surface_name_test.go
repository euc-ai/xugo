package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A strip subscripts every ∀-binder of the conclusion, the ones it
// leaves bound among them (prop.SubscriptUnivVars is a deep rewrite), so
// after it the goal's variables are spelled `m₀`, `k₀` where the
// statement wrote `m`, `k`. `induction` names its variable by the
// spelling the goal prints or by that surface name.

// surfaceNameGoal is `P(m₀) ⊢ ∀k₀. Q(k₀, m₀)`, the shape a strip_quant
// and a strip_imp leave of `∀m. P(m) ⇒ ∀k. Q(k, m)`.
func surfaceNameGoal() (goal core.Prop, m0, k0 core.VarTerm) {
	_, zeroMeta, _, _ := inductionTestEnv()
	num := zeroMeta.AbsType()
	P := ext.Var("P", core.MakeFun(num, core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(num, core.MakeFun(num, core.TypeBool())))
	m0 = ext.Var("m_0", num).AssertVar()
	k0 = ext.Var("k_0", num).AssertVar()
	return prop.MakeProp(ext.ForAll(k0)(Q.Apply(k0, m0)), P.Apply(m0)), m0, k0
}

func TestResolveInductionVar_SurfaceNameOfAStrippedVariable(t *testing.T) {
	goal, m0, k0 := surfaceNameGoal()
	for name, want := range map[string]core.VarTerm{"k": k0, "k₀": k0, "k_0": k0, "m": m0, "m₀": m0} {
		got, err := resolveInductionVar(goal, name)
		require.NoError(t, err, "%q", name)
		assert.True(t, got.Equals(want), "%q resolves to %s", name, ext.PrintTerm(got))
	}
}

// A variable literally named by the spelling owns it: the surface name
// is read only where no variable of the goal carries the name itself.
func TestResolveInductionVar_AVariableOfThatNameOwnsIt(t *testing.T) {
	_, zeroMeta, _, _ := inductionTestEnv()
	num := zeroMeta.AbsType()
	Q := ext.Var("Q", core.MakeFun(num, core.MakeFun(num, core.TypeBool())))
	k := ext.Var("k", num).AssertVar()
	k0 := ext.Var("k_0", num).AssertVar()
	goal := prop.MakeProp(ext.ForAll(k0)(Q.Apply(k0, k)))
	got, err := resolveInductionVar(goal, "k")
	require.NoError(t, err)
	assert.True(t, got.Equals(k))
}

// Two variables that read as one surface name leave it naming neither:
// the refusal lists them, and each is named as the goal prints it.
func TestResolveInductionVar_SurfaceNameOfTwoVariablesIsRefused(t *testing.T) {
	_, zeroMeta, _, _ := inductionTestEnv()
	num := zeroMeta.AbsType()
	Q := ext.Var("Q", core.MakeFun(num, core.MakeFun(num, core.TypeBool())))
	k0 := ext.Var("k_0", num).AssertVar()
	k1 := ext.Var("k_1", num).AssertVar()
	goal := prop.MakeProp(ext.ForAll(k1)(Q.Apply(k1, k0)))
	_, err := resolveInductionVar(goal, "k")
	require.Error(t, err)
	assert.Contains(t, err.Error(), `induction variable "k" reads as more than one variable of the focused goal (k₀, k₁)`)
	got, err := resolveInductionVar(goal, "k₁")
	require.NoError(t, err)
	assert.True(t, got.Equals(k1))
}

// TestInduction_NamesABinderAnOuterStripRenamed: in nat_num/nat_arith, the
// strips of `∀m. m = m ⇒ ∀k. k * m = m * k` leave `m₀ = m₀ ⊢ ∀k₀. k₀ *
// m₀ = m₀ * k₀`; `induction` on `k`, the name the statement gives the
// binder, peels the ∀ and splits as it does on `k₀`.
func TestInduction_NamesABinderAnOuterStripRenamed(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	for _, name := range []string{"k", "k₀"} {
		t.Run("named "+name, func(t *testing.T) {
			e, s := boundSession(t, "nat_num/nat_arith")
			addTextGoal(t, s, "∀m:num. m = m ⇒ ∀k:num. k * m = m * k")
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
			res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{
				GoalID: soleGoal(t, e, s.ID).ID, Tactic: TacticReq{Type: "induction", Const: name}})
			require.NoError(t, err)
			require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
			require.Equal(t, 2, res.State.NumOpen, "the base case and the step")
		})
	}
}
