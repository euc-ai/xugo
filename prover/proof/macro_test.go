package proof

import (
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// TestAssertAction_Split2ChildrenInOrder verifies the wire shape of the
// assert step (the session's `assert`, the chapter's a.Have). Given a
// goal Γ ⊢ G and claim φ, we expect:
//
//	children[0].Goal == Γ ⊢ φ      (the asserted claim)
//	children[1].Goal == Γ, φ ⊢ G   (residual with φ appended)
//
// The brief makes the [claim, residual] order load-bearing for the wire
// — agents read subgoals[0] and subgoals[1] positionally.
func TestAssertAction_Split2ChildrenInOrder(t *testing.T) {
	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)
	R := Var("R", TypeBool)

	// Γ = {R}, G = Q, φ = P
	goal := MakeProp(Q, R)
	claim := MakeProp(P)

	n := CreateGoalStack(goal)
	require.True(t, ApplyAssert(n, claim))
	require.Equal(t, 2, len(n.children))

	// child(0) — claim subgoal under current hyps.
	assert.True(t, n.children[0].Goal.AlphaEquals(MakeProp(P, R)),
		"child(0) must be the claim under the current hyps")

	// child(1) — residual with φ appended as the highest-index hyp.
	assert.True(t, n.children[1].Goal.AlphaEquals(MakeProp(Q, R, P)),
		"child(1) must be the residual with φ added")
}

// TestAssertAction_ReconstructionMatchesDirectProof verifies that
// closing both children with trivial test-thms yields a Thm whose
// shape matches a direct hyp-free proof of Γ ⊢ G. The kernel chain
// inside AssertTactic.reconstruct must produce a Thm with concl=G and
// the same Γ as the original goal — i.e. the asserted hyp is discharged.
func TestAssertAction_ReconstructionMatchesDirectProof(t *testing.T) {
	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)

	goal := MakeProp(Q)
	claim := MakeProp(P)

	n := CreateGoalStack(goal)
	require.True(t, ApplyAssert(n, claim))

	// Close child(0): proves ⊢ P.
	n.children[0].miniStep = _KnownThmStep{strongerGoal: core.TestThm(P)}
	n.children[0].subGoals = nil
	n.children[0].provedThm = core.TestThm(P)
	// Close child(1): proves P ⊢ Q.
	n.children[1].miniStep = _KnownThmStep{strongerGoal: core.TestThm(Q, P)}
	n.children[1].subGoals = nil
	n.children[1].provedThm = core.TestThm(Q, P)

	// Manually run the reconstruction chain — bypassing updateUpwards
	// (which we'd otherwise wire through child.runStep), because
	// _KnownThmStep dispatch above is set in test-mode without going
	// through runStep. The point of the test is the reconstruction
	// math, not the runStep machinery (covered elsewhere).
	thms := []prop.Prop{n.children[0].provedThm, n.children[1].provedThm}
	reconstructed := n.subGoals.Reconstruct(thms...)
	require.True(t, reconstructed.Proved())
	// Conclusion must match the original goal's, hyps must be empty
	// (since Γ in the test was empty).
	assert.True(t, reconstructed.Conclusion().AlphaEquals(Q),
		"reconstructed conclusion must α-equal the original goal's conclusion")
	assert.Equal(t, 0, reconstructed.NumHyps(),
		"reconstructed thm must have the asserted hyp discharged")
}

// TestAssertScript_BridgeTermNotInGoal is the Script-level integration
// test for the assert step. It mimics the step-case shape of left distributivity
// using uninterpreted predicate / function vars in place of nat-arith.
//
// Proves
//
//	∀x. ∀y. f(x, y) = g(x, y),
//	∀u. g(u, h(u)) = q
//	  ⊢  f(a, h(a)) = q
//
// The natural bridge term `g(a, h(a))` (a non-trivial application of
// both hyps) does not appear in the goal — exactly the pattern that
// the `trans` tactic could not handle and that `assert` is designed
// to address. Without `assert`, an agent would have to first apply one
// hyp (rewriting f → g or g → q) and then the other in the right
// order, which the size-monotone refuter path can fail on. With
// `assert g(a, h(a)) = q`, the residual reduces to substituting along
// the asserted equation.
//
// The proof is verified through the kernel — the section's Thm comes
// back Proved() with the expected conclusion.
func TestAssertScript_BridgeTermNotInGoal(t *testing.T) {
	defer goleak.VerifyNone(t)

	var cnfCache utils.Map[core.TermKey, Prop]
	env := &ProverEnv{
		ProofService:          MockConstMetaService(),
		CnfRefuterTimeout:     3 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     NewCNFNormalizeCache(),
	}
	ctx := NewScript(env)

	// Uninterpreted symbols — exercising the assert mechanism without
	// needing arithmetic infrastructure or registry access.
	a := Var("a", TypeInd)
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	u := Var("u", TypeInd)
	q := Var("q", TypeInd)
	h := Var("h", MakeFun(TypeInd, TypeInd))
	f := Var("f", MakeFun(TypeInd, TypeInd, TypeInd))
	g := Var("g", MakeFun(TypeInd, TypeInd, TypeInd))

	hypFG := ext.ForAll(x, y)(f.Apply(x, y).Eq(g.Apply(x, y)))
	hypGQ := ext.ForAll(u)(g.Apply(u, h.Apply(u)).Eq(q))

	// Goal: with both hyps available, prove f(a, h(a)) = q.
	goalConcl := f.Apply(a, h.Apply(a)).Eq(q)
	goalProp := prop.MakeProp(goalConcl, hypFG, hypGQ)

	// Bridge: assert g(a, h(a)) = q — the natural rewriting target
	// that is not present as a subterm of the goal.
	bridge := prop.MakeProp(g.Apply(a, h.Apply(a)).Eq(q))

	sec := ctx.Section(goalProp)
	// Apply assert directly via runStep — the chained Apply API
	// requires single-leaf outputs, but assert deliberately produces
	// two children. We commit each child via Auto in turn.
	require.True(t, sec.runStep(_AssertStep{claim: bridge}))
	require.Equal(t, 2, len(sec.children))

	// child(0): hyps ⊢ g(a, h(a)) = q — derives from hypGQ by ∀-elim.
	require.True(t, env.AutoExpand().Apply(sec.children[0]),
		"AutoExpand must close the asserted bridge")

	// child(1): hyps + g(a, h(a)) = q ⊢ f(a, h(a)) = q — derives by
	// instantiating hypFG at (a, h(a)) and chaining with the new hyp.
	require.True(t, env.AutoExpand().Apply(sec.children[1]),
		"AutoExpand must close the residual using the asserted hyp")

	require.True(t, sec.Proved())
	provedThm := sec.ProvedThm()
	require.False(t, provedThm.IsZero())
	assert.True(t, provedThm.Conclusion().AlphaEquals(goalConcl),
		"reconstructed conclusion must match the original goal")
}

// TestAssertScript_MS_PreorderChain demonstrates the ministep-level
// API: Script.AssertStep + Script.Do chains close child(0) then
// child(1) in preorder, mirroring how DetailedProofProto serializes
// session proofs. The end result must still produce a kernel-verified
// Thm whose conclusion matches the goal.
func TestAssertScript_MS_PreorderChain(t *testing.T) {
	defer goleak.VerifyNone(t)

	var cnfCache utils.Map[core.TermKey, Prop]
	env := &ProverEnv{
		ProofService:          MockConstMetaService(),
		CnfRefuterTimeout:     3 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     NewCNFNormalizeCache(),
	}
	ctx := NewScript(env)

	// Prove ⊢ R from {P ⇒ Q, Q ⇒ R, P} via an intermediate assert(Q).
	// The claim Q is NOT a hyp of the original goal, so AssertTactic
	// fires; the residual then uses Q to chain modus-ponens to R.
	// Verifies the preorder traversal: ctx.Do picks child(0) (the
	// claim subgoal) before child(1) (the residual).
	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)
	R := Var("R", TypeBool)
	hyps := []core.Term{P, P.Imply(Q), Q.Imply(R)}

	goalProp := prop.MakeProp(R, hyps...)
	claim := prop.MakeProp(Q)

	sec := ctx.Section(goalProp)
	ctx.Do(sec, ctx.AssertStep(claim))
	// child(0) = hyps ⊢ Q — closes by AutoExpand via MP on P ⇒ Q.
	require.True(t, env.AutoExpand().Apply(sec.unsolvedLeaf(0)))
	// child(1) = hyps, Q ⊢ R — closes by AutoExpand via MP on Q ⇒ R.
	require.True(t, env.AutoExpand().Apply(sec.unsolvedLeaf(0)))

	require.True(t, sec.Proved())
	// Note: we don't ClaimProved here because the goal happens to be a
	// propositional tautology (Normalize folds it to ⊤), which the
	// section-claim machinery rejects (a trivially-true section carries
	// no proof content). The kernel certificate is what matters for
	// this test — the assert chain produced it.
	assert.True(t, sec.ProvedThm().Conclusion().AlphaEquals(R))
}

// --- Const-definition closing + hints (TryCloseByConstDef / ConstDefDefiningHints) ---
//
// These cover the three constant-introduction kinds the def_eq hint and the
// `known` const-def fallback must handle, built synthetically (no registry):
//   - NewConstDef λ-const          → def-eq `c = body`, closes + hint
//   - NewConstDef polymorphic      → closes at a CONCRETE type instance (type-generic match)
//   - NewTypeDef abs/rep           → hint surfaces abs(rep a)=a / P(r)⇔… ; getDefThm-based close declines
//   - non-def-equation goal        → TryCloseByConstDef is a clean no-op

// TestTryCloseByConstDef_NewConstDef closes a constant's own defining equation
// `c = body` via the const-def fallback, and confirms the hint surfaces it.
func TestTryCloseByConstDef_NewConstDef(t *testing.T) {
	defer goleak.VerifyNone(t)

	// c := body, body = λx:A. x  (closed, identity at A)
	x := ext.Var("x", TypeA)
	body := x.To(x.Core())
	c := core.NewConstDef(body.Core(), "id_probe_const")

	// Goal IS the defining equation: ⊢ c = (λx. x)
	goal := prop.MakeProp(ext.WrapTerm(c).Eq(body.Core()).Core())
	node := CreateGoalStack(goal)
	require.True(t, TryCloseByConstDef(node),
		"TryCloseByConstDef must close a const's own defining equation `c = body`")
	require.True(t, node.Proved(), "node must carry a kernel-verified proof after close")

	// Hint: ConstDefDefiningHints surfaces the `def` equation.
	hints, _ := ConstDefDefiningHints(c)
	require.Len(t, hints, 1)
	assert.Equal(t, "def", hints[0].Role)
	l, _, ok := ext.MatchesEQ(hints[0].Prop.Conclusion())
	require.True(t, ok, "def hint must be an equation")
	assert.True(t, l.Equals(c), "def hint LHS must be the const")
}

// TestTryCloseByConstDef_Polymorphic closes the defining equation at a CONCRETE
// type instance — exercising the type-generic match (makeAxiomDefSubGoals'
// IsTypeMatchOf), the Q2 case. The const is defined at ?def_A; the goal states
// its equation at ?goal_A.
func TestTryCloseByConstDef_Polymorphic(t *testing.T) {
	defer goleak.VerifyNone(t)

	defA := core.MakeVarType("?def_A")
	goalA := core.MakeVarType("?goal_A")

	// c := λx:def_A. x   (polymorphic identity)
	x := ext.Var("x", defA)
	body := x.To(x.Core())
	c := core.NewConstDef(body.Core(), "poly_id_probe")

	// Goal at goal_A: ⊢ c⟨goal_A⟩ = (λx:goal_A. x)
	cAtGoal := ext.Const(c.Meta(), core.MakeFun(goalA, goalA))
	gx := ext.Var("x", goalA)
	goalBody := gx.To(gx.Core())
	goal := prop.MakeProp(cAtGoal.Eq(goalBody.Core()).Core())

	node := CreateGoalStack(goal)
	require.True(t, TryCloseByConstDef(node),
		"TryCloseByConstDef must close a polymorphic const's defining equation "+
			"at a concrete type instance (type-generic IsTypeMatchOf)")
	require.True(t, node.Proved())
}

// TestConstDefDefiningHints_TypeDefAbsRep surfaces the abs/rep type-definition
// axioms for a NewTypeDef pair — the b-case generality (these are tricky-shaped,
// so the reminder matters).
func TestConstDefDefiningHints_TypeDefAbsRep(t *testing.T) {
	defer goleak.VerifyNone(t)

	// P := λr:A. T  (trivially-nonempty subset predicate); source ⊢ P(εr.P r).
	r := ext.Var("r", TypeA)
	pred := r.To(ext.WrapTerm(prop.T))
	witness := core.Hilbert(r.AssertVar(), prop.T)           // εr. T : A
	source := core.TestThm(core.Apply(pred.Core(), witness)) // ⊢ P(εr.T)

	_, absC, repC := core.NewTypeDef(source, "probe_ty", "probe_abs", "probe_rep")

	// ABS hint: abs(rep a) = a  (Role typedef_abs) + P(r) ⇔ … (Role typedef_rep).
	absHints, _ := ConstDefDefiningHints(absC)
	require.NotEmpty(t, absHints, "abs const must surface type-def hints")
	roles := map[string]bool{}
	for _, h := range absHints {
		roles[h.Role] = true
		assert.NotNil(t, h.Prop)
	}
	assert.True(t, roles["typedef_abs"], "must surface the abs(rep a)=a axiom")
	assert.True(t, roles["typedef_rep"], "must surface the P(r) ⇔ rep(abs r)=r axiom")

	// rep const surfaces the same pair (TypeDefExpand is orientation-symmetric).
	repHints, _ := ConstDefDefiningHints(repC)
	assert.NotEmpty(t, repHints, "rep const must surface type-def hints too")
}

// TestTryCloseByConstDef_NoOpOnNonDefGoal confirms the fallback does NOT fire on
// a goal that merely MENTIONS a definable const but isn't its defining equation.
func TestTryCloseByConstDef_NoOpOnNonDefGoal(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := ext.Var("x", TypeA)
	body := x.To(x.Core())
	c := core.NewConstDef(body.Core(), "noop_probe_const")

	// Goal mentions c applied to a, but is `c(a) = c(a)` (reflexivity), NOT
	// `c = body`. The const-def fallback must decline (return false, no mutation).
	a := ext.Var("a", TypeA)
	app := ext.Const(c.Meta(), core.MakeFun(TypeA, TypeA)).Apply(a.Core())
	goal := prop.MakeProp(app.Eq(app.Core()).Core())

	node := CreateGoalStack(goal)
	assert.False(t, TryCloseByConstDef(node),
		"TryCloseByConstDef must NOT fire on a goal that isn't the const's defining equation")
	assert.False(t, node.Proved(), "node must be left untouched on a non-match")
}
