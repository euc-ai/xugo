package typematch

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/stretchr/testify/require"
)

// TestEnumerateLemmaTypeAdaptations_FreeLetterKeepsApartFromGoal pins the
// name a renamed-apart retry gives a letter it leaves free. A law over
// points of A and values of B, read at families: the retry binds its A
// to A → bool (the first sweep drops that binding as recursive by name)
// and nothing binds its B, which no constant of the law carries and
// which the goal spells too, at an unrelated y : B. The instance's B is
// the law's own, still free, and must not become the goal's B: it
// takes the first letter neither the goal nor the instance spells.
func TestEnumerateLemmaTypeAdaptations_FreeLetterKeepsApartFromGoal(t *testing.T) {
	parse := func(text string) core.Prop {
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{})
		require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
		return res.Prop
	}
	lemma := parse("Q:(B → bool) ⊢ ∀s:(A → bool). ∀f:(A → B). ∀x:A. x ∈ s ⇒ Q(f(x))")
	goal := parse("P:(B → bool), y:B, u:(A → bool), S:((A → bool) → bool) ⊢ P(y) ∧ u ∈ S")
	goalNames := map[core.TypeName]bool{}
	ext.TermAnyTypeVar(goal.Conclusion(), func(v core.VarType) bool { goalNames[v.Name()] = true; return false })
	require.True(t, goalNames["A"] && goalNames["B"], "the goal must spell both of the law's letters")

	instances := EnumerateLemmaTypeAdaptations(lemma, goal)
	require.Len(t, instances, 1)
	binders, _ := ematch.StripGuardedForalls(instances[0].Conclusion())
	require.Len(t, binders, 3)
	require.True(t, binders[2].Type().Equals(goalVarType(t, goal, "u")),
		"x must be read at the family's element type, got %s", ext.FormatType(binders[2].Type()))
	fType, ok := binders[1].Type().(core.CompositeType)
	require.True(t, ok)
	codomain, ok := fType.SubType(1).(core.VarType)
	require.True(t, ok, "f's codomain is the law's free letter, got %s", ext.FormatType(binders[1].Type()))
	require.False(t, goalNames[codomain.Name()],
		"the law's free letter was renamed to the goal's %s", codomain.Name())
	require.False(t, strings.HasPrefix(string(codomain.Name()), "?apart"), "a reserved letter escaped: %s", codomain.Name())

	// The identity adaptation in disguise is still dropped: a goal that
	// also offers the law at its own A yields that one instance and no
	// second one at the goal's letters.
	both := parse("P:(B → bool), y:B, u:(A → bool), S:((A → bool) → bool), v:A, T:(A → bool) ⊢ P(y) ∧ u ∈ S ∧ v ∈ T")
	require.Len(t, EnumerateLemmaTypeAdaptations(lemma, both), 1)
}
