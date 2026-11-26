package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// A bare polymorphic law cited at an instance holding its own letter,
// at a leaf no apply closes: set_order.UnionSubset at
// `A ↦ prod(B, C) → A`, with `s ∪ t ⊆ w` denied in the context. The
// install's adaptation drops that binding by its by-name occurs-check
// and commits nothing, so the law's A is captured as the goal's: the
// closer would receive a law about sets of A, an instance the goal
// holds nowhere. The install retries renamed apart, and the By closes
// at `prod(B, C) → A` as it does at `prod(B, C) → D`. Without the law
// it closes at neither.
func TestBy_BareLawWithACapturedLetterInstallsAtTheGoalsInstance(t *testing.T) {
	law := parseFor(t, "∀s t u:(A → bool). s ∪ t ⊆ u ⇔ s ⊆ u ∧ t ⊆ u")
	for _, letter := range []string{"D", "A"} {
		el := fmt.Sprintf("(prod(B, C) → %s)", letter)
		goal := parseFor(t, fmt.Sprintf("s:(%[1]s → bool), t:(%[1]s → bool), w:(%[1]s → bool), ¬(s ∪ t ⊆ w) ⊢ ¬(s ⊆ w) ∨ ¬(t ⊆ w)", el))
		run := func(withLaw bool) (closed bool) {
			env := groundTestEnv(t)
			newGroundByStore().wire(env, true)
			premises := []ByPremiseSpec{{Install: prop.MakeProp(goal.Hyp(0)), Resident: true, Describe: "hyp 0"}}
			if withLaw {
				premises = append(premises, ByPremiseSpec{Install: prop.MakeProp(law.Conclusion()), Describe: "set_order.UnionSubset"})
			}
			defer func() {
				if r := recover(); r != nil {
					closed = false
				}
			}()
			return ApplyByStep(CreateGoalStack(goal), env, t.Context(), BySpec{Premises: premises})
		}
		require.False(t, run(false), "letter %s: closes without the law", letter)
		require.True(t, run(true), "letter %s: the By does not close with the law", letter)
	}
}
