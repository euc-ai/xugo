package engine

// The per-rule `normalized: true` bit on a simp_with entry — the
// session twin of the Go `Fwd(MakeFact(ctx.DepNormalized(name)))`.

import (
	"context"
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestSimpWith_Normalized_ServesTheNormalizerOrientation: `nat_arith.AddEqZero`
// is stated `m + n = 0 ⇔ m = 0 ∧ n = 0` and normalizes to
// `0 = m + n ⇔ …`. On a goal spelling the sum on the RIGHT of the
// zero — the shape a flipped `list_length(l) = 0` rule leaves behind — the
// stated rule has no redex and the entry's normalized form fires; the
// rule child closes against the entry through the type-instance
// channel, and emit renders the rule as MakeFact(ctx.DepNormalized(<var>)).
func TestSimpWith_Normalized_ServesTheNormalizerOrientation(t *testing.T) {
	entry, ok := registry.ByName(nat_arith.AddEqZero.DepName())
	require.True(t, ok, "nat_arith.AddEqZero is registered")
	stated := entry.Statement().Prop
	normalized := proof.NormalizedForm(stated)
	require.False(t, stated.AlphaEquals(normalized),
		"the fixture needs an entry the normalizer re-orients: stated %s", prop.PrintProp(stated))

	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	res := dsl.ParsePropText("a:num, b:num ⊢ (0 = a + b) ⇔ (a = 0 ∧ b = 0)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	// Stated orientation: no redex, progress-or-fail.
	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: nat_arith.AddEqZero.DepName()}}},
	})
	if err == nil {
		require.False(t, out.Success, "the stated form `m + n = 0` has no redex in `0 = a + b`")
	}

	// normalized beside a specialization is refused by name.
	out, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{
			{Key: nat_arith.AddEqZero.DepName(), Normalized: true, TermSpecialize: map[string]string{"m": "a"}}}},
	})
	assert.Contains(t, refusalText(out, err), "normalized:true beside type_specialize / term_specialize")

	// The normalizer's orientation fires.
	out, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: nat_arith.AddEqZero.DepName(), Normalized: true}}},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "normalized:true must fire; diagnostics: %v", out.Diagnostics)

	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1, "the rule child closes against the entry; one residual remains: %+v", state.Goals)
	out, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, out.Success, "the residual is reflexive; diagnostics: %v", out.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	// The record carries the normalized form, and emit names the Go
	// target that serves it.
	emitted, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_SumIsZero", Family: "nat_num/nat_arith"})
	require.NoError(t, err)
	parsesAsGo(t, emitted.Go)
	assert.Contains(t, emitted.Go, `Simp(Fwd(MakeFact(ctx.DepNormalized(AddEqZero))))`, "--- source: ---\n%s", emitted.Go)
	assert.NotContains(t, emitted.Go, "SimpWith(", "the fusion must not decline to the pinned form\n--- source: ---\n%s", emitted.Go)
	assert.Contains(t, emitted.DepNames, nat_arith.AddEqZero.DepName())
}

// TestSimpWith_Normalized_RefusedOnByAndAutoWith: the bit is a simp_with
// rule form; the two install moves refuse it by name rather than drop it.
func TestSimpWith_Normalized_RefusedOnByAndAutoWith(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	res := dsl.ParsePropText("a:num, b:num ⊢ (0 = a + b) ⇔ (a = 0 ∧ b = 0)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	for _, tac := range []string{"by", "auto_with"} {
		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid,
			Tactic: TacticReq{Type: tac, WithLemmas: []LemmaWithSpec{{Key: nat_arith.AddEqZero.DepName(), Normalized: true}}},
		})
		assert.Contains(t, refusalText(out, err), "normalized is a simp_with rule form", "%s must refuse normalized by name", tac)
	}
}

// refusalText is what a refused step said: the error when the step
// errored, else the failed step's diagnostics. A step that succeeded
// reports "" — the assertion then fails naming the empty text.
func refusalText(out *StepResult, err error) string {
	if err != nil {
		return err.Error()
	}
	if out == nil || out.Success {
		return ""
	}
	var parts []string
	for _, d := range out.Diagnostics {
		parts = append(parts, d.Message)
	}
	return strings.Join(parts, "\n")
}

// TestSimpWith_Normalized_AtTypeInstance: a POLYMORPHIC entry served
// normalized on a goal at a concrete instance — the multi-instance
// expansion adapts the normalized form to the instance, the copy
// records verbatim, and emit renders the target that serves exactly
// that copy: ctx.AtTypes(ctx.DepNormalized(<var>.Name), τ).
// `list.LengthEqNil` is stated `list_length(l) = 0 ⇔ l = nil` and normalizes
// to `(l = nil) ⇔ (0 = list_length(l))`, so the normalized rule rewrites an
// `a = nil` at list(num) that the stated form never touches.
func TestSimpWith_Normalized_AtTypeInstance(t *testing.T) {
	entry, ok := registry.ByName(list.LengthEqNil.DepName())
	require.True(t, ok, "list.LengthEqNil is registered")
	stated := entry.Statement().Prop
	require.False(t, stated.AlphaEquals(proof.NormalizedForm(stated)),
		"the fixture needs an entry the normalizer re-orients: stated %s", prop.PrintProp(stated))

	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	// The goal is built from the entry's own terms at num (the text
	// parser has no list vocabulary here — `list_length` typed from text
	// would be a free variable, not the chapter's constant): from the
	// normalized instance `(l = nil) ⇔ (0 = list_length(l))`, the
	// implication `(l = nil) ⇒ (0 = list_length(l))`.
	normBody := instanceBodyAtNum(proof.NormalizedForm(stated))
	lhs, rhs, ok := core.MatchesEQ(normBody)
	require.True(t, ok, "the normalized instance is an iff: %s", ext.PrintTerm(normBody))
	goal := prop.MakeProp(ext.WrapTerm(lhs).Imply(rhs).Core())
	gid := s.AddGoal(goal)
	s.rebuildGoalIndex()

	// The stated form has no redex in `l = nil`.
	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: list.LengthEqNil.DepName()}}},
	})
	if err == nil {
		require.False(t, out.Success, "the stated form rewrites `list_length(l) = 0`, which the goal does not spell")
	}

	out, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: list.LengthEqNil.DepName(), Normalized: true}}},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "the normalized form at list(num) must fire; diagnostics: %v", out.Diagnostics)
	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1, "the adapted rule child closes against the entry; one residual remains: %+v", state.Goals)
	out, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, out.Success, "the residual is `p ⇒ p`; diagnostics: %v", out.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	emitted, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_NilHasLengthZero", Family: "datatypes/list"})
	require.NoError(t, err)
	parsesAsGo(t, emitted.Go)
	assert.Contains(t, emitted.Go, `Simp(Fwd(ctx.AtTypes(ctx.DepNormalized(LengthEqNil), NumType)))`, "--- source: ---\n%s", emitted.Go)
	assert.Contains(t, emitted.DepNames, list.LengthEqNil.DepName())
}
