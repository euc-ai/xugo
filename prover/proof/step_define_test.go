package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// TestDefineStep_DirectSection: a definition section (root = the
// characterizing statement) closes with ONE _DefineStep and zero
// children, and the recorded proto carries the Define tag whose pool
// ref decodes back to the minted const — the wire contract emit
// renders from.
func TestDefineStep_DirectSection(t *testing.T) {
	env := makeStepTestEnv()
	equation, defVar := dvdEquation("zz_dvd_step")
	dd, err := AnalyzeDirectDefinition(equation, defVar)
	require.NoError(t, err)
	c, characterizing, err := MintDirectDefinition(env, dd)
	require.NoError(t, err)

	ctx := NewScript(env)
	sec := ctx.Section(characterizing)
	sec.Do(DefineStep(c))
	require.True(t, sec.Proved(), "define section must close outright on the direct shape")

	// Exactly one recorded ministep, the composite, no children.
	var defNode *GoalStackNode
	var walk func(n *GoalStackNode)
	walk = func(n *GoalStackNode) {
		if _, ok := n.miniStep.(_DefineStep); ok {
			require.Nil(t, defNode, "exactly one define composite expected")
			defNode = n
		}
		for _, ch := range n.children {
			walk(ch)
		}
	}
	walk(sec)
	require.NotNil(t, defNode, "the define close must record a `define` ministep")
	require.Empty(t, defNode.children, "the direct shape has no obligation children")

	// Proto round-trip: the recorded step serializes under the Define
	// tag and its pool ref resolves back to the minted const.
	dp := sec.DetailedProofProto()
	require.NotNil(t, dp)
	var tag *StepProto_Define
	for _, st := range dp.Steps {
		if d, ok := st.Step.(*StepProto_Define); ok {
			require.Nil(t, tag, "exactly one Define tag expected")
			tag = d
		}
	}
	require.NotNil(t, tag, "the recorded section must carry the Define tag")
	pool := ext.NewPoolReader(dp.Pool, env.ProofService.LoadConstMeta)
	decoded := pool.Term(tag.Define.GetConst())
	dc, ok := decoded.AsConst()
	require.True(t, ok, "Define payload must decode to a const")
	require.Equal(t, c.Name(), dc.Name())

	// Replay-equivalence by construction: a fresh step built from the
	// decoded const re-closes the same goal through the same executor.
	replay := ctx.Section(characterizing)
	replay.Do(DefineStep(dc))
	require.True(t, replay.Proved())
}

// TestDefineStep_HilbertObligation: on an ε-minted const the composite
// surfaces exactly one child — the existence obligation — and the
// section closes once that child is proved, with the residual folded
// (the goal IS the characterizing form).
func TestDefineStep_HilbertObligation(t *testing.T) {
	env := makeStepTestEnv()
	// zz_pickT := εx:bool. x ⇔ ⊤ — the simplest Hilbert-shape mint.
	x := Var("x", TypeBool)
	c := core.NewConstDef(x.SuchThat(x.Eq(WrapTerm(T))).Core(), "zz_pickT")
	_, existed := env.ProofService.LoadOrStoreConstMeta(c.Meta())
	require.False(t, existed)

	// The characterizing goal: zz_pickT ⇔ ⊤.
	goal := prop.MakeProp(WrapTerm(c).Eq(WrapTerm(T)))

	ctx := NewScript(env)
	sec := ctx.Section(goal)
	sec.Do(DefineStep(c))
	require.False(t, sec.Proved(), "the existence obligation must stay open")
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1, "exactly one obligation child")

	// Close the obligation by hand: ⊢ ∃x. x ⇔ ⊤ at witness ⊤.
	leaves[0].Do(Witness(WrapTerm(T)))
	leaves[0].Do(TrivialSimplify())
	require.True(t, sec.Proved(), "closing the existence obligation closes the definition section")
}
