package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/typematch"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Tests for chooseTypeAdaptedStep's type selection when a lemma is
// matched, and for its no-recompute invariant: it returns the SubGoals it
// already computed, so the winning tactic is applied during selection and
// never again at commit.

func lemmaMakeStep(lemma Prop, key core.PropKey) _Step {
	return _LemmaTactic{lemma: lemma, polymorphicSourceKey: key}
}

func leanRwMakeStep(lemma Prop, key core.PropKey) _Step {
	return _LeanRwTactic{lemma: lemma, polymorphicSourceKey: key}
}

// stepLemmaHasTypeVars reports whether the lemma carried by a chosen step
// still has polymorphic type variables. The whole point of type adaptation
// is to drive this to false so a later `instantiate` (which filters hyp
// binders by HolType.Equals) can see the lemma's binders.
func stepLemmaHasTypeVars(t *testing.T, s _Step) bool {
	t.Helper()
	switch step := s.(type) {
	case _LemmaTactic:
		return ext.PropHasTypeVars(step.lemma)
	case _LeanRwTactic:
		return ext.PropHasTypeVars(step.lemma)
	default:
		t.Fatalf("unexpected step type %T", s)
		return false
	}
}

// requireSameSubGoals asserts two SubGoals are interchangeable: same arity
// and α-equal child goals. This is the property commitStep relies on —
// the SubGoals chooseTypeAdaptedStep returns must equal what re-applying the
// chosen step would produce, otherwise dropping the third apply would change
// behavior.
func requireSameSubGoals(t *testing.T, want, got *SubGoals) {
	t.Helper()
	require.NotNil(t, want)
	require.NotNil(t, got)
	require.Equal(t, want.Size(), got.Size(), "subgoal count differs")
	for i := range want.Size() {
		assert.Truef(t, want.ChildGoal(i).AlphaEquals(got.ChildGoal(i)),
			"child %d differs:\n want %v\n  got %v", i, want.ChildGoal(i), got.ChildGoal(i))
	}
}

// Ground (type-var-free) lemma: the fast path. chooseTypeAdaptedStep must
// apply the original exactly once and return those SubGoals; no adaptation.
func TestChooseTypeAdaptedStep_GroundLemma_ReturnsComputedSubGoals(t *testing.T) {
	// Ground lemma ∀z:bool. z=z (no type vars) closes goal ⊢ y=y. (A lemma
	// literally α-equal to the goal would hit the α-circular guard, so we
	// use the ∀-wrapped form.)
	z := core.Var("z", core.TypeBool())
	lemma := core.MakeProp(ext.ForAll(z)(ext.WrapTerm(core.Eq(z, z))).Core())
	y := core.Var("y", core.TypeBool())
	goal := core.MakeProp(core.Eq(y, y))

	require.False(t, ext.PropHasTypeVars(lemma), "precondition: lemma is ground")

	n := CreateGoalStack(goal)
	step, sg := chooseTypeAdaptedStep(n, lemma, lemmaMakeStep)

	require.NotNil(t, sg, "ground lemma must produce SubGoals (applied once inside)")
	assert.False(t, stepLemmaHasTypeVars(t, step), "ground lemma stays ground")
	// Commit-time invariant: returned SubGoals == fresh re-apply of the step.
	requireSameSubGoals(t, step.apply(goal), sg)
}

// Conservatism branch: a polymorphic lemma that already CLOSES the goal
// (origSG.Size() <= 1) must keep the ORIGINAL form — speculative type
// adaptation is not allowed to rewrite a direct close into a different
// theorem instance. Adaptation is genuinely available here (asserted), so
// we are exercising the switch, not the adapted==nil fast path.
func TestChooseTypeAdaptedStep_OrigClosesGoal_KeepsOrig(t *testing.T) {
	xA := core.Var("x", core.TypeA())
	lemma := core.MakeProp(ext.ForAll(xA)(ext.WrapTerm(core.Eq(xA, xA))).Core()) // ∀x:A. x=x
	y := core.Var("y", core.TypeBool())
	goal := core.MakeProp(core.Eq(y, y)) // ⊢ y=y

	require.NotNil(t, typematch.TryAdaptLemmaTypes(lemma, goal),
		"precondition: adaptation must be available so we test the switch, not the fast path")

	n := CreateGoalStack(goal)
	step, sg := chooseTypeAdaptedStep(n, lemma, lemmaMakeStep)

	require.NotNil(t, sg)
	require.LessOrEqual(t, sg.Size(), 1, "precondition: original must close the goal (≤1 subgoal)")
	assert.True(t, stepLemmaHasTypeVars(t, step),
		"conservatism: original (polymorphic) form kept when it already closes the goal")
	requireSameSubGoals(t, step.apply(goal), sg)
}

// makeUnaryConst returns a polymorphic unary const meta `F : T → bool`.
func makeUnaryConst(name core.TermName, argType core.HolType) core.ConstTermMeta {
	return core.MakeConstMeta(name, core.MakeFun(argType, core.TypeBool()))
}

// Adapted-chosen branch (regression guard for the type-var binder bug):
// when the ORIGINAL polymorphic lemma fails to apply because its type-var
// instance differs from the goal's (strict HolType.Equals prefilter in the
// rewrite path), the type-adapted candidate must be selected, and the chosen
// lemma must carry CONCRETE binder types so downstream tactics can match it.
func TestChooseTypeAdaptedStep_OrigFailsLeanRw_PicksConcreteAdapted(t *testing.T) {
	defA := core.MakeVarType("?defA_choose")
	goalA := TypeInd

	// Lemma: ∀x:?defA. F(x) = ⊤   (F : ?defA → bool)
	fMeta := makeUnaryConst("Fchoose", defA)
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(defA, core.TypeBool()))
	x := core.Var("x", defA)
	body := core.Eq(core.Apply(fLemma, x), prop.T)
	lemma := core.MakeProp(ext.ForAll(x)(ext.WrapTerm(body)).Core())

	// Goal: ⊢ F(c)   with F materialized at ?goalA (distinct instance).
	fGoal := core.MakeConstTerm(fMeta, core.MakeFun(goalA, core.TypeBool()))
	c := core.Var("c", goalA)
	goal := core.MakeProp(core.Apply(fGoal, c))

	// Sanity: the unadapted lemma's rewrite genuinely fails on the goal's
	// instance (otherwise this would not exercise the origSG==nil branch).
	require.Nil(t, leanRwMakeStep(lemma, "").apply(goal),
		"precondition: unadapted polymorphic leanRw must fail on the cross-instance goal")
	require.NotNil(t, typematch.TryAdaptLemmaTypes(lemma, goal),
		"precondition: adaptation must be available")

	n := CreateGoalStack(goal)
	step, sg := chooseTypeAdaptedStep(n, lemma, leanRwMakeStep)

	require.NotNil(t, sg, "adapted leanRw must fire even though the original failed")
	assert.False(t, stepLemmaHasTypeVars(t, step),
		"type-adapted (concrete-binder) form must be chosen so later tactics can match")
	requireSameSubGoals(t, step.apply(goal), sg)
}

// End-to-end: ApplyLeanRw on the same cross-instance lemma must succeed and
// produce children equal to the chosen step's SubGoals — i.e. commitStep
// committing the precomputed SubGoals is behaviorally identical to the old
// runStep(step) that re-applied.
func TestApplyLeanRw_CrossInstance_CommitsSelectedSubGoals(t *testing.T) {
	defA := core.MakeVarType("?defA_commit")
	goalA := TypeInd

	fMeta := makeUnaryConst("Fcommit", defA)
	fLemma := core.MakeConstTerm(fMeta, core.MakeFun(defA, core.TypeBool()))
	x := core.Var("x", defA)
	lemma := core.MakeProp(ext.ForAll(x)(ext.WrapTerm(core.Eq(core.Apply(fLemma, x), prop.T))).Core())

	fGoal := core.MakeConstTerm(fMeta, core.MakeFun(goalA, core.TypeBool()))
	c := core.Var("c", goalA)
	goal := core.MakeProp(core.Apply(fGoal, c))

	// Predict the selection independently.
	predStep, predSG := chooseTypeAdaptedStep(CreateGoalStack(goal), lemma, leanRwMakeStep)
	require.NotNil(t, predSG)

	n := CreateGoalStack(goal)
	require.True(t, ApplyLeanRw(n, lemma), "ApplyLeanRw must succeed via the adapted candidate")

	require.Equal(t, predSG.Size(), len(n.children), "committed child count must match selection")
	for i := range n.children {
		assert.Truef(t, predStep.apply(goal).ChildGoal(i).AlphaEquals(n.children[i].Goal),
			"committed child %d must equal the selected step's subgoal", i)
	}
}

// TestApplyCiteNode_BasicReuse: prove ψ = (y=y) once via Refl in a "target"
// node, then cite it into a separate "focus" node. After cite-node, the
// focus should have two children:
//   - children[0] = the cited proof of ψ (inherited from target's clone),
//     marked Proved().
//   - children[1] = focus's new goal `Γ_focus, ψ ⊢ G` (open, with ψ as a
//     fresh hyp).
func TestApplyCiteNode_BasicReuse(t *testing.T) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)

	// Target: ⊢ y = y, closed by ApplyRefl.
	target := CreateGoalStack(MakeProp(y.Eq(y)))
	require.True(t, ApplyRefl(target), "ApplyRefl on `y=y` should succeed")
	require.True(t, target.Proved(), "target should be Proved after Refl")

	// Focus: ⊢ x = x. We want to install `y = y` as a new hyp via cite-node.
	focus := CreateGoalStack(MakeProp(x.Eq(x)))

	require.True(t, ApplyCiteNode(focus, target), "ApplyCiteNode should succeed")
	require.Len(t, focus.children, 2, "cite-node opens assert's two-child structure")

	firstChild := focus.children[0]
	secondChild := focus.children[1]

	assert.True(t, firstChild.Proved(),
		"first child should be auto-closed by cited subtree (provedThm inherited from target)")
	assert.False(t, secondChild.Proved(),
		"second child should be the new open focus")

	// Second child carries ψ = y=y as a fresh hyp.
	assert.True(t, secondChild.Goal.HasHyp(y.Eq(y)),
		"second child should have y=y as a new hyp (the cited conclusion)")

	// Re-parenting check: first child's children must point back at firstChild,
	// not at target (the original tree's root). Without proper re-parenting, a
	// later traversal from firstChild would walk into target's parent slot
	// (nil) and miss the parent-pointer integrity invariant.
	for i, c := range firstChild.children {
		assert.Same(t, firstChild, c.parent,
			"firstChild's child #%d parent should be firstChild, not target", i)
	}
}

// TestApplyCiteNode_RejectUnprovedTarget: ApplyCiteNode's contract is that
// callers ensure target.Proved(). It is the engine RPC layer's job (per
// engine.go "cite-node" dispatch) to refuse an open target — but a defense-
// in-depth assertion at the prover layer would be nice. For now we just
// document that calling with an unproved target panics inside the underlying
// Clone path's Reconstruct or returns a malformed first child. This test is
// a placeholder if we add a hard precondition.
//
// Skipped — see comment above.
func TestApplyCiteNode_RejectUnprovedTarget(t *testing.T) {
	t.Skip("precondition is currently caller-enforced (engine dispatch); revisit if a defensive check is added to ApplyCiteNode")
}
