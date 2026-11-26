package typematch

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
)

// TestTypeOnlyMatch_SwapsTwoSourceLetters pins the matcher at an
// instance that swaps two of the source's type letters, σ = {B ↦ D, D ↦
// B}: the goal spells the source's own letters, so a bound letter's
// image is itself a name the matcher may bind. The accumulated
// bindings are read through core.MatchTypeInto's environment and
// never substituted into the pattern ahead of the walk: a source
// letter is looked up as the source's, whatever the goal calls it.
func TestTypeOnlyMatch_SwapsTwoSourceLetters(t *testing.T) {
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{})
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop
	}
	body := func(p core.Prop) (core.VarPredicate, core.Term) {
		vars, body := ext.DecomposesFORALL(p.Conclusion())
		return func(v core.VarTerm) bool { return vars.Has(v) }, body
	}
	slot, source := body(parse("f:(B → bool), g:(D → bool), h:(B → D → bool) ⊢ ∀x:B. ∀y:D. f(x) ∧ g(y) ⇒ h(x)(y)"))
	tB, tD := core.MakeVarType("B"), core.MakeVarType("D")
	swap := []core.TypeSubst{core.MakeTypeSubst(tB, tD), core.MakeTypeSubst(tD, tB)}
	swapped := source.TypeSubstitute(swap...)

	substs, ok := TypeOnlyMatch(source, swapped, slot, utils.FullPredicate)
	require.True(t, ok, "the swap of B and D is a type instance")
	require.True(t, source.TypeSubstitute(substs...).AlphaEquals(swapped),
		"σ must carry the source onto the goal: got %s", formatTypeSubsts(substs))

	// A goal reading the source's B at two letters is no instance: x
	// at D and z at E, where the source binds both at B. The
	// pre-substituted walk once accepted it, binding the goal's D on
	// to E as if it were the source's.
	_, two := body(parse("f:(B → bool), k:(B → bool), g:(D → bool), h:(B → D → bool) ⊢ ∀x:B. ∀z:B. ∀y:D. f(x) ∧ k(z) ∧ g(y) ⇒ h(x)(y)"))
	twoSlot := patternVarsByName("x", "z", "y")
	_, split := body(parse("f:(D → bool), k:(E → bool), g:(B → bool), h:(D → B → bool) ⊢ ∀x:D. ∀z:E. ∀y:B. f(x) ∧ k(z) ∧ g(y) ⇒ h(x)(y)"))
	_, ok = TypeOnlyMatch(two, split, twoSlot, utils.FullPredicate)
	require.False(t, ok, "B cannot be read at D and at E")
}
