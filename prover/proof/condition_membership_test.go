// condition_membership_test.go — the conditioning stage reads every
// membership in a set-builder the leaf spells as its condition at the
// point before any closer meets the leaf (step_condition.go, the
// strips), so the refuter — which unfolds no definition — never meets
// `x ∈ {i | i < n}` as an opaque atom. Measured before: a membership
// whose condition the context contradicts ran the refuter to its
// ceiling (#1539), and a three-part membership closed alone by set_tac
// but not under By, nor as the side condition of a law (#1488).
package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
)

// comprehensionSection opens a section on text, parsed with the
// set-builder vocabulary, and declares that vocabulary to the script's
// own scope so the body's term texts read it too.
func comprehensionSection(t *testing.T, text string) (*Script, *GoalStackNode) {
	t.Helper()
	scope := comprehensionScope()
	res := dsl.ParsePropTextInScope(text, scope)
	require.Empty(t, res.Errors, "%s: %v", text, res.Errors)
	ctx := NewScript(makeStepTestEnv())
	for name, ty := range scope.Vars {
		ctx.ParseScope.Vars[name] = ty
	}
	if ctx.ParseScope.ConstMetas == nil {
		ctx.ParseScope.ConstMetas = map[string]core.ConstTermMeta{}
	}
	for name, meta := range setBuilderVocabulary() {
		ctx.ParseScope.ConstMetas[name] = meta
	}
	return ctx, ctx.Section(res.Prop)
}

func TestConditionMembership_ConditionTheContextContradicts(t *testing.T) {
	ctx, sec := comprehensionSection(t,
		"COND(a < n, f(a), 0) = 0 ⇒ a ∈ {y:num | COND(y < n, f(y), 0) ≠ 0} ⇒ a ∈ {i:num | i < n}")
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(func(a *Argument) {
			zero := a.Assume()
			nonzero := a.Assume()
			a.Show("the two memberships contradict", By(zero, nonzero))
		}).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
}

func TestConditionMembership_GeneralFormUnderBy(t *testing.T) {
	ctx, sec := comprehensionSection(t, "a < n ⇒ f(a) ∈ {f(k) | k:num | k < n}")
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(func(a *Argument) {
			below := a.Assume()
			a.Show("the image point", By(below))
		}).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
}

func TestConditionMembership_GeneralFormAsASideCondition(t *testing.T) {
	ctx, sec := comprehensionSection(t, "(∀x:num. x ∈ {f(k) | k:num | k < n} ⇒ P(x)) ⇒ a < n ⇒ P(f(a))")
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(func(a *Argument) {
			law := a.Assume()
			below := a.Assume()
			a.Show("P at the image point", By(law, below))
		}).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
}

// A Let naming the set-builder: the set driver reads the membership
// through the Let's equation (the control for #1533's simple shape).
func TestConditionMembership_LetNamesTheSetBuilder(t *testing.T) {
	ctx, sec := comprehensionSection(t, "P(a) ⇒ a ∈ {y:num | P(y)}")
	ok := provesInHand(t, func() *GoalStackNode {
		Derive(func(a *Argument) {
			pa := a.Assume()
			sDef := a.Let("S", a.Term("{y:num | P(y)}"))
			a.Show("a is in S", BySets(sDef, pa))
		}).applyAction(ctx, sec)
		return sec
	})
	require.True(t, ok != nil && sec.Proved())
}
