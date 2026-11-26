// apply_close_split_fold_test.go — the apply rung's modus ponens on a
// leaf where the split's two branches fold into one.
//
// SplitHypImplyAt on the head `Aᵢ ⇒ rest` leaves `Γ, ¬Aᵢ ⊢ C` and
// `Γ, rest ⊢ C`, and the tactic folds a branch into the other where the
// other is stronger (makeSubGoalsAt): where Γ already holds ¬Aᵢ — a
// contradictory leaf, since the rung made Aᵢ resident — the consequent's
// branch folds into ¬Aᵢ's, and where Γ already holds `rest`, ¬Aᵢ's
// branch folds into the consequent's. The commit knows each branch by
// its statement, not its position, and closes either shape. The set
// driver's case analysis hands the rung the first shape: the economy
// audit's premise probe on class_number.fieldNormCoordinateBound leaves
// `i < n` beside `¬(i < n)` under the head `i < n ⇒ …`.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// P(a), ¬P(a), ∀x. P(x) ⇒ C(x) ⊢ C(a): the leaf holds the antecedent
// beside its denial, the one branch the split leaves holds the denial,
// and the contradiction closes the leaf whole.
func TestApplyClose_SplitFoldsIntoTheDenialBranch(t *testing.T) {
	require.True(t, rungCloses(t, "C(a)", []string{"P(a)", "¬P(a)", "∀x:num. P(x) ⇒ C(x)"}),
		"the rung closes a leaf that holds an antecedent beside its denial")
}

// P(a), k(a), k(a) ⇒ C(a), ∀x. P(x) ⇒ k(x) ⇒ C(x) ⊢ C(a), applied at the
// quantified law: after the first modus ponens its consequent
// `k(a) ⇒ C(a)` is already resident, the one branch the split leaves is
// the consequent's, and the second modus ponens runs on it.
func TestApplyClose_SplitFoldsIntoTheConsequentBranch(t *testing.T) {
	head := parseGuardSupply(t, "∀x:num. P(x) ⇒ k(x) ⇒ C(x)")
	hyps := []core.Term{head}
	for _, h := range []string{"P(a)", "k(a)", "k(a) ⇒ C(a)"} {
		hyps = append(hyps, parseGuardSupply(t, h))
	}
	goal := prop.MakeProp(parseGuardSupply(t, "C(a)"), hyps...)
	idx, err := alphaHypIndex(goal, head)
	require.NoError(t, err)
	var claims []*GoalStackNode
	applies := rungOpts{depth: antecedentApplies, claims: &claims}
	run, miss := planApplyWith(goal, head, "the law", nil, applies)
	require.NotNil(t, run, "the dry run validates the apply: %s", miss)
	leaf := CreateGoalStack(goal)
	commitApply(leaf, idx, run)
	require.True(t, leaf.Proved(), "the commit closes the leaf through the folded split")
}
