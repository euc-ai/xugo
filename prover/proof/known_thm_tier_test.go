package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// TestApplyKnown_TypeInstanceHitRecordsTypeInst pins the tier-aware
// recording contract of commitFoundThmStep: a FindProvedThm tier-3
// (type-instance) hit must be RECORDED as _TypeInstStep carrying the
// polymorphic source — never as _KnownThmStep carrying the per-goal
// instance, whose statement has no stable identity outside the session
// and panics emit ("external lemma has no DAG-level classification").
// Live regression this pins: cardinality.HasSizeProduct — the agent-facing
// `known` tactic closed an fst-at-cart-types instance
// through s.autoMatchCache's tier-3 and stored the unresolvable shape.
func TestApplyKnown_TypeInstanceHitRecordsTypeInst(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Polymorphic source: ⊢ ∀x:A. P(x) ⇒ Q(x) (same non-tautology
	// fixture as TestThmCache_LoadMatchThm).
	xA := Var("x", TypeA)
	PA := Var("P", MakeFun(TypeA, TypeBool))
	QA := Var("Q", MakeFun(TypeA, TypeBool))
	source := core.TestThm(ForAll(xA)(PA.Apply(xA).Imply(QA.Apply(xA))))
	require.False(t, source.IsZero())
	normalized, _ := Normalize(source)

	var cache ThmCache
	cache.SaveThm(source, normalized.AsThmCert())

	// Goal: the concrete type instance at bool — tier 1/2 miss (different
	// α-keys), tier 3 hits.
	xBool := Var("x", TypeBool)
	Pb := Var("P", MakeFun(TypeBool, TypeBool))
	Qb := Var("Q", MakeFun(TypeBool, TypeBool))
	goal := MakeProp(ForAll(xBool)(Pb.Apply(xBool).Imply(Qb.Apply(xBool))))

	n := CreateGoalStack(goal)
	require.True(t, ApplyKnown(n, &cache), "tier-3 hit should close the goal")
	require.True(t, n.Proved())

	// The recorded ministep must be _TypeInstStep with the POLYMORPHIC
	// source — that is what reaches the wire and what emit resolves.
	ti, ok := n.miniStep.(_TypeInstStep)
	require.True(t, ok, "tier-3 close must record _TypeInstStep, got %T", n.miniStep)
	nSrc, _ := Normalize(ti.source)
	assert.Equal(t, normalized.AlphaKey(), nSrc.AlphaKey(),
		"recorded source must be the polymorphic form, not the instance")

	// And the serialized proto must carry the type_inst tag.
	detailed := n.DetailedProofProto()
	require.NotNil(t, detailed)
	require.NotEmpty(t, detailed.Steps)
	_, isTypeInst := detailed.Steps[0].Step.(*StepProto_TypeInst)
	assert.True(t, isTypeInst, "wire step must be type_inst, got %T", detailed.Steps[0].Step)
}

// TestApplyKnown_NormalizedHitStillRecordsKnownThm pins the tier-2
// behavior: normalized-key hits keep the legacy _KnownThmStep shape
// (whose equivalentThm, when set, is normalize-equal to strongerGoal —
// resolvable at emit through the normalize tier).
func TestApplyKnown_NormalizedHitStillRecordsKnownThm(t *testing.T) {
	defer goleak.VerifyNone(t)

	xA := Var("x", TypeA)
	PA := Var("P", MakeFun(TypeA, TypeBool))
	QA := Var("Q", MakeFun(TypeA, TypeBool))
	source := core.TestThm(ForAll(xA)(PA.Apply(xA).Imply(QA.Apply(xA))))
	require.False(t, source.IsZero())
	normalized, _ := Normalize(source)

	var cache ThmCache
	cache.SaveThm(source, normalized.AsThmCert())

	// Goal: α-equal to the source itself (same type vars) — tier 1/2 hit.
	goal := MakeProp(ForAll(xA)(PA.Apply(xA).Imply(QA.Apply(xA))))
	n := CreateGoalStack(goal)
	require.True(t, ApplyKnown(n, &cache))
	require.True(t, n.Proved())
	_, ok := n.miniStep.(_KnownThmStep)
	assert.True(t, ok, "α/normalized hit must keep _KnownThmStep, got %T", n.miniStep)
}

// TestKnownThmProto_BackstopPanicsOnInstanceShape pins the store-time
// backstop: serializing a _KnownThmStep whose equivalentThm is NOT
// normalize-equal to strongerGoal (the per-instance shape that
// regression stored) must panic at proto() — the poison dies at
// the producer's stack, not at corpus-emit time.
func TestKnownThmProto_BackstopPanicsOnInstanceShape(t *testing.T) {
	xA := Var("x", TypeA)
	PA := Var("P", MakeFun(TypeA, TypeBool))
	QA := Var("Q", MakeFun(TypeA, TypeBool))
	source := core.TestThm(ForAll(xA)(PA.Apply(xA).Imply(QA.Apply(xA))))
	require.False(t, source.IsZero())

	xB := Var("x", TypeBool)
	Pb := Var("P", MakeFun(TypeBool, TypeBool))
	Qb := Var("Q", MakeFun(TypeBool, TypeBool))
	instance := core.TestThm(ForAll(xB)(Pb.Apply(xB).Imply(Qb.Apply(xB))))
	require.False(t, instance.IsZero())

	bad := _KnownThmStep{strongerGoal: instance, equivalentThm: source}
	pb := ext.NewPoolBuilder()
	require.Panics(t, func() { bad.proto(pb) },
		"per-instance KnownThm payload must be refused at serialization")

	// Sanity: the legit shape (equivalentThm normalize-equal) serializes.
	good := _KnownThmStep{strongerGoal: source, equivalentThm: source}
	require.NotPanics(t, func() { good.proto(pb) })
}
