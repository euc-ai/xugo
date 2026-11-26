package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean" // the ℝ instance family
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A session bound to vector/euclidean reads and writes the chapter's
// spelling: a goal text may leave the ring's components out
// (`vec_add(u, v)`), the claim preview completes them, and emit-section
// hands back the short spelling — the observing step for the three
// session-side surfaces of ext/dsl/implicit.go.
func TestFamilySession_ImplicitArgs(t *testing.T) {
	env := familySessionEnv()
	env.ProofService.CNFStore = proof.NewMemoryCNFStore() // the session's refutes, read back by emit
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "vector/euclidean", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	require.NotNil(t, s.ImplicitBindings()["add"], "the family binds the ring's components")

	// The goal, in the chapter's spelling, read at the session's
	// statement door — the scope the CLI's add-goal path parses with.
	scope := s.StatementDoorScope()
	short := dsl.ParsePropTextInScope("∀u v w z:(num → real). vec_add(u, v) = w ∧ w = z ⇒ vec_add(u, v) = z", scope)
	require.Empty(t, short.Errors)
	long := dsl.ParsePropTextInScope("∀u v w z:(num → real). vec_add(real_add, u, v) = w ∧ w = z ⇒ vec_add(real_add, u, v) = z", scope)
	require.Empty(t, long.Errors)
	require.Equal(t, long.Prop.AlphaKey(), short.Prop.AlphaKey(), "short and explicit are one statement")
	goalID := s.AddGoal(short.Prop)

	// The claim preview under the session completes the same way.
	preview, err := e.ParsePropInGoalScope(info.ID, goalID, "∀u v:(num → real). vec_add(u, v) = vec_add(v, u)")
	require.NoError(t, err)
	require.Empty(t, preview.Errors, "preview: %v", preview.Errors)
	assert.Contains(t, ext.PrintTerm(preview.Prop.Conclusion()), "real_add")

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, res.Success, "auto should close the equality chain; diagnostics: %v", res.Diagnostics)

	// The session is bound, so the family is the default.
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ImplicitProbe"})
	require.NoError(t, err)
	// The headline text carries the chapter's spelling — the component
	// elided and the operation folded into its notation (vec_add declares
	// `u + v`); the display labels go through the output door and spell
	// it too (TestFamilySession_OutputDoorSpellsTheChapter).
	// The statement is family.Theorem's first argument, inline.
	headline := headlineOf(t, out.Go)
	assert.Equal(t, "∀u v w z:(num → real). u + v = w ∧ w = z ⇒ u + v = z", headline,
		"emit hands back the chapter's spelling:\n%s", out.Go)
	assert.NotContains(t, headline, "real_add", "a parsed text must not spell the bound component")
	for _, line := range strings.Split(out.Go, "\n") {
		if strings.Contains(line, "PropText(") {
			assert.NotContains(t, line, "real_add", "a parsed text must not spell the bound component")
		}
	}
}

// The member's texts are written for the family it lands in: a session
// bound to vector/euclidean, emitting into a family that binds no ring,
// spells the component its own family leaves out, and the destination's
// statement door reads the headline back as the session's statement.
func TestEmitSection_WritesForTheDestinationsBindings(t *testing.T) {
	env := familySessionEnv()
	env.ProofService.CNFStore = proof.NewMemoryCNFStore()
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "vector/euclidean", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	goal := dsl.ParsePropTextInScope("∀u v w z:(num → real). vec_add(u, v) = w ∧ w = z ⇒ vec_add(u, v) = z", s.StatementDoorScope())
	require.Empty(t, goal.Errors)
	goalID := s.AddGoal(goal.Prop)
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.True(t, res.Success, "%v", res.Diagnostics)

	dest, ok := registry.FamilyByName("iterate/real/real_sum")
	require.True(t, ok)
	require.Empty(t, dest.ImplicitBindings(), "the destination binds no ring")
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ImplicitProbe", Family: dest.Name})
	require.NoError(t, err)
	headline := headlineOf(t, out.Go)
	assert.Contains(t, headline, "vec_add(real_add, u, v)")
	back := dsl.ParsePropTextInScope(headline, StatementDoorScope(dest))
	require.Empty(t, back.Errors, "the destination's statement door reads %q", headline)
	assert.Equal(t, goal.Prop.AlphaKey(), back.Prop.AlphaKey())
}

// TestFamilySession_OutputDoorSpellsTheChapter: every text the session
// serves about a goal goes through the output door (spelling.go) and
// comes out in the chapter's spelling — the display statement, the
// indexed hypotheses, the parse-faithful text, the hyps a step adds,
// the closed subtrees — and so do the Show / Have / Case labels and
// context comments emit writes. The kernel printers are untouched: the
// door reads their text back through dsl.ChapterSpelling under the
// family's bindings.
func TestFamilySession_OutputDoorSpellsTheChapter(t *testing.T) {
	env := familySessionEnv()
	env.ProofService.CNFStore = proof.NewMemoryCNFStore()
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "vector/euclidean", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	scope := &dsl.ParseScope{
		ConstResolver:    registryConstResolver,
		TypeResolver:     registryTypeResolver,
		Syntax:           constSyntax(),
		ImplicitBindings: s.ImplicitBindings(),
		StrictResolution: true,
	}
	res := dsl.ParsePropTextInScope("∀n:num. ∀u v:(num → real). ‖u‖_n ≤ ‖u + v‖_n ⇒ ∃w:(num → real). ‖u‖_n ≤ ‖w‖_n", scope)
	require.Empty(t, res.Errors)
	s.AddGoal(res.Prop)

	// The kernel printer spells the long form; the door spells the chapter's.
	long := prop.PrintProp(res.Prop)
	assert.Contains(t, long, "vec_norm(n, u)")
	assert.Contains(t, long, "vec_add(real_add, u, v)")
	door := s.Spelling()
	assert.Equal(t, "⊢ ∀n u v. ‖u‖_n ≤ ‖u + v‖_n ⇒ ∃w. ‖u‖_n ≤ ‖w‖_n", door.Prop(res.Prop))
	typed, ok := door.Typed(res.Prop)
	require.True(t, ok)
	assert.Equal(t, "∀n:num. ∀u v:(num → real). ‖u‖_n ≤ ‖u + v‖_n ⇒ ∃w:(num → real). ‖u‖_n ≤ ‖w‖_n", typed)

	// Open the goal to its hypothesis: intro until the conclusion is the ∃.
	var last *StepResult
	for range 4 {
		ins, err := e.Inspect(ctx, info.ID, &InspectRequest{})
		require.NoError(t, err)
		require.Len(t, ins.Goals, 1)
		if strings.HasPrefix(ext.PrintTerm(ins.Goals[0].Statement.Conclusion()), "∃") {
			break
		}
		last, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: ins.Goals[0].ID, Tactic: TacticReq{Type: "intro"}})
		require.NoError(t, err)
		require.True(t, last.Success, "intro: %v", last.Diagnostics)
	}
	// The hyp the last intro added, as the step result serves it.
	require.NotNil(t, last)
	require.Len(t, last.NewHyps, 1)
	assert.Equal(t, "‖u₀‖_n₀ ≤ ‖u₀ + v₀‖_n₀", last.NewHyps[0].Term)
	ins, err := e.Inspect(ctx, info.ID, &InspectRequest{})
	require.NoError(t, err)
	require.NotNil(t, ins.Spelling, "an inspect view carries the session's door")
	require.Len(t, ins.Goals, 1)
	g := ins.Goals[0]
	assert.Equal(t, "‖u₀‖_n₀ ≤ ‖u₀ + v₀‖_n₀ ⊢ ∃w. ‖u₀‖_n₀ ≤ ‖w‖_n₀", ins.Spelling.Prop(g.Statement))
	require.Len(t, g.Hypotheses, 1)
	assert.Equal(t, "‖u₀‖_n₀ ≤ ‖u₀ + v₀‖_n₀", ins.Spelling.Hyp(g.Hypotheses[0]))
	typed, ok = ins.Spelling.Typed(g.Statement)
	require.True(t, ok)
	assert.Contains(t, typed, "‖u₀‖_n₀ ≤ ‖u₀ + v₀‖_n₀ ⊢ ∃w:(num → real). ‖u₀‖_n₀ ≤ ‖w‖_n₀")
	assert.NotContains(t, typed, "vec_norm")

	// A claim under the goal (an assert), then both goals close: the
	// emitted proof's Case labels and context comments are in the
	// chapter's spelling, the bound binders under their own names, and
	// its parsed payload too, in the minted spelling the Script's door
	// reads.
	claim, err := e.ParsePropInGoalScope(info.ID, g.ID, "‖u‖_n ≤ ‖u + v‖_n ∨ ‖u + v‖_n ≤ ‖u‖_n")
	require.NoError(t, err)
	require.Empty(t, claim.Errors, "claim: %v", claim.Errors)
	last, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: TacticReq{Type: "assert", Claim: claim.Prop}})
	require.NoError(t, err)
	require.True(t, last.Success, "assert: %v", last.Diagnostics)
	for range 2 {
		ins, err := e.Inspect(ctx, info.ID, &InspectRequest{})
		require.NoError(t, err)
		require.NotEmpty(t, ins.Goals)
		last, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: ins.Goals[0].ID, Tactic: TacticReq{Type: "auto"}})
		require.NoError(t, err)
		require.True(t, last.Success, "auto: %v", last.Diagnostics)
	}
	require.True(t, s.sections[0].root.Proved())
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_DoorProbe"})
	require.NoError(t, err)
	for _, line := range []string{
		`func(a *Argument, n *Expr[Nat], u, v *Arrow[Nat, Real], _ Fact) {`,
		`AssertStep(ctx.MakePropText("‖u₀‖_n₀ ≤ ‖u₀ + v₀‖_n₀ ∨ ‖u₀ + v₀‖_n₀ ≤ ‖u₀‖_n₀")`,
		"Case(\n\t\t\t\t\t\t\"claim: ‖u‖_n ≤ ‖u + v‖_n ∨ ‖u + v‖_n ≤ ‖u‖_n\"",
		`//   h0: ‖u‖_n ≤ ‖u + v‖_n`,
		`//   concl: ∃w. ‖u‖_n ≤ ‖w‖_n`,
	} {
		assert.Contains(t, out.Go, line, "the emitted text spells the chapter's notation:\n%s", out.Go)
	}
	assert.NotContains(t, out.Go, "vec_norm(", "no served or emitted text spells the kernel's form:\n%s", out.Go)
	assert.NotContains(t, out.Go, "real_add", "no served or emitted text spells the bound component:\n%s", out.Go)
}

// TestFamilySession_ProjectionOnASkolem: once strip_quant has minted
// M₀ for a module value, every text the session serves spells the
// record projections on it under that one name — the display, the
// typed text and the hypothesis strip_imp reports in new_hyps — never
// `M_0.carrier` beside `M₀`.
func TestFamilySession_ProjectionOnASkolem(t *testing.T) {
	env := familySessionEnv()
	env.ProofService.CNFStore = proof.NewMemoryCNFStore()
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "algebra/module/module", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	res := dsl.ParsePropTextInScope("∀M:module_ops(A, B). ∀N:set(B). M.zero ∈ N ⇒ N ⊆ M.carrier", s.StatementDoorScope())
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	goalID := s.AddGoal(res.Prop)
	step, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "strip_quant"}})
	require.NoError(t, err)
	require.True(t, step.Success, "strip_quant: %v", step.Diagnostics)
	ins, err := e.Inspect(ctx, info.ID, &InspectRequest{})
	require.NoError(t, err)
	require.Len(t, ins.Goals, 1)
	g := ins.Goals[0]
	assert.Equal(t, "⊢ M₀.zero ∈ N₀ ⇒ N₀ ⊆ M₀.carrier", ins.Spelling.Prop(g.Statement))
	typed, ok := ins.Spelling.Typed(g.Statement)
	require.True(t, ok)
	assert.Contains(t, typed, "M₀.zero ∈ N₀ ⇒ N₀ ⊆ M₀.carrier", typed)
	step, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: TacticReq{Type: "strip_imp"}})
	require.NoError(t, err)
	require.True(t, step.Success, "strip_imp: %v", step.Diagnostics)
	require.Len(t, step.NewHyps, 1)
	assert.Equal(t, "M₀.zero ∈ N₀", step.NewHyps[0].Term)
}
