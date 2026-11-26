package engine

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// These tests cover `term_specialize` on a lemma's sequent-level FREE
// variables (free in the conclusion or any hypothesis, NOT an outer
// ∀-binder of the conclusion) — binary induction stated with its predicate
// free, where an outer-binder-only specialize would refuse:
//
//	apply lemma({"key":...},
//	            "term_specialize":{"P":"λn:num. P₀(n)"})
//	→ `∀-binder "P" not found in lemma's outer binders; available: [n]`
//
// Free-var specialization is standard instantiation of a theorem's free
// variables — sound. The engine implements it for the `lemma` install
// path: hypMatching auto-generalizes the lemma's free vars to the
// OUTERMOST ∀-positions of the added hyp, and the post-install chain
// peels them by name (see applyLemmaTermSpecializeChain).

// TestApply_LemmaTermSpecialize_SequentFreeVar_InstallAsHyp is the
// happy path, mirroring the shape of the boolean case axiom: the lemma
// `⊢ tv ∨ ¬tv` carries tv:bool FREE at the sequent level. Loading it
// with term_specialize={tv: b} must install the GROUND hyp `b ∨ ¬b`
// (the install auto-generalizes tv to `∀tv. tv ∨ ¬tv`; the chain then
// peels ∀tv at the goal-side witness b).
func TestApply_LemmaTermSpecialize_SequentFreeVar_InstallAsHyp(t *testing.T) {
	h := makeLemmaSpecHarness()
	tv := ext.Var("tv", core.TypeBool())
	b := core.Var("b", core.TypeBool())

	// Lemma: ⊢ tv ∨ ¬tv (tv free — no ∀-binder anywhere).
	lemma := prop.MakeProp(tv.Or(ext.Not(tv.Core()).Core()).Core())
	// Goal: b=b ⊢ Qspec. The vacuous hyp puts `b` in the goal's scope
	// so resolveTermWithFallback can pick it up as the witness.
	target := prop.MakeProp(h.Qconst, core.Eq(b, b))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"tv": "b"},
	})
	require.True(t, res.Success, "lemma+free-var specialize must apply; res=%+v", res)

	workingHyps := findWorkingHyps(t, res, h.Qconst)
	expectedGround := core.Var("b", core.TypeBool())
	expected := ext.WrapTerm(expectedGround).Or(ext.Not(expectedGround).Core()).Core()
	foundGround := false
	for _, hyp := range workingHyps {
		if hyp.AlphaEquals(expected) {
			foundGround = true
		}
		assert.True(t, ext.MatchesFORALL(hyp).IsZero(), "no hyp may be ∀-headed after free-var specialize; got %s", ext.PrintTerm(hyp))
	}
	assert.True(t, foundGround,
		"working goal must carry the ground hyp b ∨ ¬b; hyps=%v",
		printedHyps(workingHyps))
}

// TestApply_Lemma_StatedShape_FreePredicate_NoTermSpecialize is
// the engine-level regression for the `Should not happen.` panic on
// binary induction's stated form (free predicate var + hyps + ∀-concl):
// plain `apply lemma` (no term_specialize) must succeed via the
// whole-conclusion unification retry in lemmaConclMatchTactic, leaving
// the conjunction of the instantiated lemma hyps as the residual goal.
func TestApply_Lemma_StatedShape_FreePredicate_NoTermSpecialize(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	pTy := core.MakeFun(numType, core.TypeBool())
	fMeta := core.MakeConstMeta("fbi", core.MakeFun(numType, numType))
	gMeta := core.MakeConstMeta("gbi", core.MakeFun(numType, numType))
	zMeta := core.MakeConstMeta("zbi", numType)
	f := ext.WrapTerm(core.MakeConstTerm(fMeta, fMeta.AbsType()))
	g := ext.WrapTerm(core.MakeConstTerm(gMeta, gMeta.AbsType()))
	z := core.MakeConstTerm(zMeta, zMeta.AbsType())

	n := ext.Var("n", numType)
	P := ext.Var("Pbi", pTy) // free predicate VARIABLE at sequent level
	q := ext.Var("q", pTy)   // goal-side rigid predicate (free in goal concl)

	// Lemma (binary induction's stated shape):
	//   P(z), ∀n.(P(n) ⇒ P(f(n)) ∧ P(g(n))) ⊢ ∀n.P(n)
	lemma := prop.MakeProp(
		ext.ForAll(n)(P.Apply(n)).Core(),
		P.Apply(z).Core(),
		ext.ForAll(n)(P.Apply(n).Imply(
			P.Apply(f.Apply(n.Core()).Core()).And(P.Apply(g.Apply(n.Core()).Core())).Core())).Core(),
	)
	// Goal: (∀n.q(f(n))) ∧ (∀n.q(g(n))) ⊢ ∀n.q(n)
	target := prop.MakeProp(
		ext.ForAll(n)(q.Apply(n)).Core(),
		ext.ForAll(n)(q.Apply(f.Apply(n.Core()).Core())).And(
			ext.ForAll(n)(q.Apply(g.Apply(n.Core()).Core()))).Core(),
	)

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:  "lemma",
		Lemma: lemma,
	})
	require.True(t, res.Success,
		"plain apply of the free-predicate stated form must succeed (whole-concl retry); res=%+v", res)

	// The residual demands the instantiated lemma hyps (P ↦ q). The
	// conclusion-match child starts as `⊢ q(z) ∧ ∀n.(q(n) ⇒ q(f(n)) ∧ q(g(n)))`;
	// simplifyNewGoal then ∧-splits the goal hyp and discharges the step
	// conjunct against the split hyps, so the surviving obligation is the
	// base case q(z) (possibly still inside the conjunction if the
	// simplify didn't fire). Look for it among the open goals.
	wantBase := q.Apply(z).Core()
	foundBase := false
	require.NotNil(t, res.State)
	for _, gv := range res.State.Goals {
		concl := gv.Statement.Conclusion()
		conjuncts := []core.Term{concl}
		if l, r, ok := ext.MatchesAND(concl); ok {
			conjuncts = []core.Term{l, r}
		}
		for _, c := range conjuncts {
			if c.AlphaEquals(wantBase) {
				foundBase = true
			}
		}
	}
	assert.True(t, foundBase,
		"residual must demand the instantiated base case q(z); got %d goals: %v",
		len(res.State.Goals), func() []string {
			var out []string
			for _, gv := range res.State.Goals {
				out = append(out, prop.PrintProp(gv.Statement))
			}
			return out
		}())
}

// TestApply_LemmaTermSpecialize_FreeVarConsumedByConclMatch pins the
// diagnostic when term_specialize names a free var but the install's
// conclusion-match path consumes the lemma (instantiating the free var
// by unification) — there is no added ∀-headed hyp to peel, so the
// chain reports an actionable error instead of a silent no-op.
func TestApply_LemmaTermSpecialize_FreeVarConsumedByConclMatch(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	pTy := core.MakeFun(numType, core.TypeBool())
	fMeta := core.MakeConstMeta("fcc", core.MakeFun(numType, numType))
	gMeta := core.MakeConstMeta("gcc", core.MakeFun(numType, numType))
	zMeta := core.MakeConstMeta("zcc", numType)
	f := ext.WrapTerm(core.MakeConstTerm(fMeta, fMeta.AbsType()))
	g := ext.WrapTerm(core.MakeConstTerm(gMeta, gMeta.AbsType()))
	z := core.MakeConstTerm(zMeta, zMeta.AbsType())

	n := ext.Var("n", numType)
	P := ext.Var("Pcc", pTy)
	q := ext.Var("q", pTy)

	lemma := prop.MakeProp(
		ext.ForAll(n)(P.Apply(n)).Core(),
		P.Apply(z).Core(),
		ext.ForAll(n)(P.Apply(n).Imply(
			P.Apply(f.Apply(n.Core()).Core()).And(P.Apply(g.Apply(n.Core()).Core())).Core())).Core(),
	)
	target := prop.MakeProp(
		ext.ForAll(n)(q.Apply(n)).Core(),
		ext.ForAll(n)(q.Apply(f.Apply(n.Core()).Core())).And(
			ext.ForAll(n)(q.Apply(g.Apply(n.Core()).Core()))).Core(),
	)

	err := applyToSingleGoalExpectErr(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"Pcc": "q"},
	})
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "conclusion-match",
		"diagnostic must explain that conclusion matching consumed the lemma")
	assert.Contains(t, err.Error(), "Drop `term_specialize`",
		"diagnostic must tell the agent the plain apply works")
}

// TestApply_LemmaTermSpecialize_UnknownKeyListsFreeVars: an unknown
// key still errors, and the message now also lists the sequent-level
// free vars (when the lemma has any) so the agent can self-correct.
func TestApply_LemmaTermSpecialize_UnknownKeyListsFreeVars(t *testing.T) {
	h := makeLemmaSpecHarness()
	tv := ext.Var("tv", core.TypeBool())
	b := core.Var("b", core.TypeBool())

	lemma := prop.MakeProp(tv.Or(ext.Not(tv.Core()).Core()).Core())
	target := prop.MakeProp(h.Qconst, core.Eq(b, b))

	err := applyToSingleGoalExpectErr(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"nosuch": "b"},
	})
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "not found in lemma's outer binders")
	assert.Contains(t, err.Error(), "sequent-level free vars",
		"error must list the lemma's free vars as specializable alternatives")
	assert.Contains(t, err.Error(), "tv")
}

// TestApply_LeanRwTermSpecialize_FreeVarNotSupported: the rewrite-path
// verbs (lean_rw / simp_with / auto_with route through
// buildTermSpecializedLemma) do NOT support free-var specialization —
// the pre-substituted lemma child couldn't be closed against the
// cited entry. The error must say so and point at `lemma`.
func TestApply_LeanRwTermSpecialize_FreeVarNotSupported(t *testing.T) {
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	zMeta := core.MakeConstMeta("zlr", numType)
	z := core.MakeConstTerm(zMeta, zMeta.AbsType())
	hv := ext.Var("hv", core.MakeFun(numType, numType)) // free fun var
	b := core.Var("b", core.TypeBool())

	// Lemma: ⊢ hv(z) = z (hv free at sequent level; concl IS an equality
	// so it passes lean_rw's shape gate — the term_specialize resolve
	// runs first and must reject the free-var key with the typed error).
	lemma := prop.MakeProp(core.Eq(ext.Apply(hv.Core(), z), z))
	target := prop.MakeProp(core.Eq(b, b))

	err := applyToSingleGoalExpectErr(t, target, TacticReq{
		Type:           "lean_rw",
		Lemma:          lemma,
		TermSpecialize: map[string]string{"hv": "b"},
	})
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "sequent-level FREE variable")
	assert.Contains(t, err.Error(), "supported for the `lemma` tactic only")
}
