package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestEmitSection_AClaimReadsBackBesideTheMembersDeclarations: a member's
// claim text is parsed at replay beside every variable the member
// declares at script scope, not only the claim's own. Section 0 strips
// its ring to env₀, a binder its closure cannot take (the scaffold binds
// the Go name env), so the member declares env₀; section 1 binds its ring
// S₀ at its closure's boundary. Section 1's claim spells `*` at S₀'s
// carrier, which reads as S₀'s multiplication in the session (S₀ is the
// claim's only record) and as two structures beside env₀ in the emitted
// member. The emitted claim spells the component where the short form
// would not read back there, and the member replays.
func TestEmitSection_AClaimReadsBackBesideTheMembersDeclarations(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "algebra/field/field")
	addStatement(t, s, "∀env:ring_ops(A). comm_ring(env) ⇒ ∀x:A. env.zero * (x * x) = env.zero")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
		{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "comm_ring(")}}}})
	require.True(t, s.sections[0].root.Proved())

	addStatement(t, s, "∀S:ring_ops(A). ∀y:A. comm_ring(S) ⇒ S.zero * ((y * y) * (y * y)) = S.zero")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	claim := "S₀.zero * y₀ = S₀.zero"
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: claim})
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	if len(state.Goals) == 2 {
		// The claim, where no proved section closed it on its own.
		claimGoal := func(g core.Prop) bool { return g.NumHyps() == 1 }
		applyTo(t, e, s, claimGoal, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
			{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, claimGoal, "comm_ring(")}}}})
	}
	_, closedID := sectionIDs(s, 0)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
		{Key: closedID, ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "comm_ring(")}}}})
	require.True(t, s.sections[1].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 1, FuncName: "Build_ZzDeclaredScope", Family: "algebra/field/field", IncludePrior: []int{0},
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, `ctx.Var("env_0"`, "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "func(a *Argument, S *Expr[RingOps[A]], y *Expr[A], h Fact)", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, unspaced(out.Go), unspaced(`MakePropText("S₀.zero * y₀ = S₀.zero")`), "--- source: ---\n%s", out.Go)
	replayEmittedInFamily(t, "algebra/field/field", "ZzDeclaredScope", out)
}

// TestEmitSection_ABinderNameIsNoDeclarationAtTheScriptsDoor: a text the
// Script parses inside a closure reads beside the Skolems the closure's
// boundary declares, never beside a binder's name, which only the
// closure's claim door aliases. The closure binds the field M, its Skolem
// M₀; the statement's binder M is held at field_ops(A) and a cited module
// law's binder M at module_ops(A, B). The one assert's claim spells `*`
// at M₀, the one record the replay's scope holds there: every emission
// renders the claim so — the same member each time, whichever M the
// symbol table iterates last — and the member replays.
func TestEmitSection_ABinderNameIsNoDeclarationAtTheScriptsDoor(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "algebra/field/field_extension")
	addStatement(t, s, "∀M:field_on(A). ∀a b c:A. a ∈ M.carrier ∧ b ∈ M.carrier ∧ c = a / b ⇒ c = a * M.inv(b)")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "lemma", LemmaKey: "module_record.RestrictModuleCarrier"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "a₀ * M₀.inv(b₀) = a₀ / b₀"})
	const asserted = "field_mul(M₀, a₀, field_inv(M₀, b₀)) = field_div(M₀, a₀, b₀)"
	claimGoal, afterGoal := lacking(asserted), holding(asserted)
	applyTo(t, e, s, claimGoal, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(*hypAt(t, e, s, claimGoal, "((a₀ ∈"))},
		WithLemmas: []LemmaWithSpec{{Key: "field.DivMulInvOn", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, claimGoal, "field_on(")}}}})
	applyTo(t, e, s, afterGoal, TacticReq{Type: "by", ByHyps: []ByHypSpec{
		hyp(*hypAt(t, e, s, afterGoal, "field_mul(")), hyp(*hypAt(t, e, s, afterGoal, "((a₀ ∈"))}})

	out := emitSoleResult(t, e, s, "Build_ZzBinderNameScope")
	for range 31 {
		again := emitSoleResult(t, e, s, "Build_ZzBinderNameScope")
		require.Equal(t, out.Go, again.Go, "two emissions of one session differ")
	}
	assert.Contains(t, out.Go, "func(arg *Argument, M field.FieldFact[on.M], a, b, c *Expr[A], h Fact)", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, `AssertStep(ctx.MakePropText("a₀ * M₀.inv(b₀) = a₀ / b₀")`, "--- source: ---\n%s", out.Go)
	replayEmittedInFamily(t, "algebra/field/field_extension", "ZzBinderNameScope", out)
}

// TestEmitSection_AClaimReadsBackBesideItsClosuresSkolems: the Skolems a
// closure's boundary declares are in the Script's scope whether or not a
// text spells them. The closure binds the rings R and S, their Skolems R₀
// and S₀; the claim speaks of S₀ alone, and `*` would read as two
// structures beside R₀ at replay. The emitted claim spells the component,
// and the member replays.
func TestEmitSection_AClaimReadsBackBesideItsClosuresSkolems(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "algebra/field/field")
	addStatement(t, s, "∀R S:ring_ops(A). ∀y:A. comm_ring(R) ⇒ comm_ring(S) ⇒ S.mul(S.zero, S.mul(S.mul(y, y), S.mul(y, y))) = S.zero")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "S₀.mul(S₀.zero, y₀) = S₀.zero"})
	const asserted = "ring_mul(S₀, ring_zero(S₀), y₀) = ring_zero(S₀)"
	claimGoal, afterGoal := lacking(asserted), holding(asserted)
	ring := func(keep func(core.Prop) bool) []LemmaWithSpec {
		return []LemmaWithSpec{{Key: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, keep, "comm_ring(S₀)")}}}
	}
	applyTo(t, e, s, claimGoal, TacticReq{Type: "by", WithLemmas: ring(claimGoal)})
	applyTo(t, e, s, afterGoal, TacticReq{Type: "by", WithLemmas: ring(afterGoal)})

	out := emitSoleResult(t, e, s, "Build_ZzClosureSkolems")
	assert.Contains(t, out.Go, "func(a *Argument, R, S *Expr[RingOps[A]], y *Expr[A], _, h2 Fact)", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "AssertStep(ctx.MakePropText(", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, unspaced(out.Go), unspaced(`MakePropText("S₀.zero * y₀ = S₀.zero")`), "--- source: ---\n%s", out.Go)
	replayEmittedInFamily(t, "algebra/field/field", "ZzClosureSkolems", out)
}
