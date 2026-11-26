// step_by_set_vocabulary_note_test.go — a plain By on a leaf that is
// true by a set definition alone fails, the refuter unfolding no
// definition, and the failure says which closer reads such a leaf.

package proof

import (
	"context"
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// byFailure runs the By and returns its panic text ("" when it closed).
func byFailure(goal Prop, spec BySpec) (text string) {
	defer func() {
		if r := recover(); r != nil {
			text = fmt.Sprint(r)
		}
	}()
	ApplyByStep(CreateGoalStack(goal), makeStepTestEnv(), context.Background(), spec)
	return ""
}

func TestBy_FailureOnASetVocabularyLeafNamesTheSetDriver(t *testing.T) {
	m := makeMiniSetTheory()
	in := m.at(m.in, m.elemT)
	union := m.at(m.union, m.elemT)
	x := ext.Var("x", m.elemT)
	s := ext.Var("s", m.setT)
	u := ext.Var("u", m.setT)

	// x ∈ s ⊢ x ∈ s ∪ u: true by the definition of ∪, which the refuter
	// does not open.
	inS := in.Apply(x, s).Core()
	goal := prop.MakeProp(in.Apply(x, union.Apply(s, u)).Core(), inS)
	resident := BySpec{Premises: []ByPremiseSpec{{
		Install: prop.MakeProp(inS), Resident: true, Describe: "hyp x ∈ s",
	}}}

	failure := byFailure(goal, resident)
	require.NotEmpty(t, failure, "the refuter does not unfold ∪, so the plain By must fail")
	assert.Contains(t, failure, "set vocabulary by name (union)")
	assert.Contains(t, failure, "BySets(")
	assert.Contains(t, failure, "settac:true")

	withDriver := resident
	withDriver.Settac = true
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, makeStepTestEnv(), t.Context(), withDriver), "the set driver closes the same leaf")
	require.True(t, n.Proved())

	// Membership alone is no set vocabulary to unfold: a leaf that spells
	// nothing else fails without the note.
	plain := prop.MakeProp(in.Apply(x, u).Core(), inS)
	failure = byFailure(plain, resident)
	require.NotEmpty(t, failure, "x ∈ s does not give x ∈ u")
	assert.NotContains(t, failure, "set vocabulary")
}
