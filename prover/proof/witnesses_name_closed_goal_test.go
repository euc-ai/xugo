package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
)

// TestWitnessesNameClosedGoal_PolymorphicReference: a witnessed cite of
// a polymorphic statement whose install closed the goal is checked by
// the tuple reproducing the closed goal (Lean's `exact foo a b`). The
// reference is the statement as cited, `∀x:A. x = x`, and the tuple is
// at the instance the install took, `x₀ : ind`; the binder's letter is
// read at the witness's type, as every other door reads a witness
// (FitWitness), so the tuple names the closed goal `x₀ = x₀`. On the
// old code the binder's type had to EQUAL the witness's, and every
// polymorphic reference failed the check.
func TestWitnessesNameClosedGoal_PolymorphicReference(t *testing.T) {
	A := core.MakeVarType("A")
	x := ext.Var("x", A)
	law := prop.MakeProp(ext.ForAll(x)(x.Eq(x)).Core())
	x0 := ext.Var("x_0", TypeInd)
	closed := x0.Eq(x0).Core()
	assert.True(t, witnessesNameClosedGoal(law, []Term{x0.Core()}, closed),
		"the tuple (x₀) names the instance that closed x₀ = x₀")
	y0 := ext.Var("y_0", TypeInd)
	assert.False(t, witnessesNameClosedGoal(law, []Term{y0.Core()}, closed),
		"the tuple (y₀) names another instance")
}
