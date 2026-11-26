package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// termTypeVarNames collects the free type-variable names appearing
// anywhere in a Term — the assertion helper for the override tests.
func termTypeVarNames(t core.Term) map[string]bool {
	names := map[string]bool{}
	pred := core.VarTypePredicate(func(v core.VarType) bool {
		names[string(v.Name())] = true
		return false // keep visiting
	})
	_ = ext.TermAnyTypeVar(t, pred)
	return names
}

// TestLemmaTypeSpecialize_VarTargetNotOverriddenByGoalContext: the
// install path (ApplyLemmaPreserveWithSource → chooseTypeAdaptedStep →
// TryAdaptLemmaTypes) must not re-adapt an explicitly specialized lemma
// against the goal: `lemma({key, type_specialize: {A: "?27845"}})`
// installs the hyp at ?27845, never at the GOAL-CONTEXT type instance.
// An override could bite only when the σ target is itself a type
// VARIABLE (a ground target leaves nothing for the adapter to rebind),
// which is exactly the multi-type-instance navigation pattern of zip and the two-list map.
//
// Contract (soundness-first, no silent fallbacks): an explicit
// type_specialize is honored EXACTLY or the tactic hard-errors. The
// goal below carries the shared polymorphic const P at a competing type
// instance C — the anchor TryAdaptLemmaTypes would latch onto — while
// the agent requests the unrelated type var E. The installed ∀-hyp must
// be at E, not C.
func TestLemmaTypeSpecialize_VarTargetNotOverriddenByGoalContext(t *testing.T) {
	// Polymorphic const P : A → bool — shared between lemma and goal so
	// the adapter has a live anchor to compute a competing σ from.
	A := core.TypeA()
	pTyA := core.MakeFun(A, core.TypeBool())
	pMeta := core.MakeConstMeta("PadaptOverride", pTyA)
	pA := core.MakeConstTerm(pMeta, pTyA)

	// Lemma: ∀x:A. P⟨A⟩(x)
	x := ext.Var("x", A)
	lemma := prop.MakeProp(ext.ForAll(x)(ext.Apply(pA, x.Core())))

	// Goal: P⟨C⟩(c) ⊢ Q — the goal context carries P at type C, the
	// instance the adapter would pick over the agent's explicit choice.
	C := core.MakeVarType("C")
	pTyC := core.MakeFun(C, core.TypeBool())
	pC := core.MakeConstTerm(pMeta, pTyC)
	cVar := core.Var("c", C)
	qMeta := core.MakeConstMeta("QadaptOverride", core.TypeBool())
	Qconst := core.MakeConstTerm(qMeta, core.TypeBool())
	target := prop.MakeProp(Qconst, ext.Apply(pC, cVar))

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TypeSpecialize: map[string]string{"A": "var:E"},
	})
	require.True(t, res.Success,
		"lemma with an explicit type_specialize must install; diagnostics: %+v",
		res.Diagnostics)

	hyps := findWorkingHyps(t, res, Qconst)
	var installed core.Term
	for _, h := range hyps {
		if !ext.MatchesFORALL(h).IsZero() {
			installed = h
			break
		}
	}
	require.NotNil(t, installed,
		"an installed ∀-headed lemma hyp must exist; hyps=%v", printedHyps(hyps))

	names := termTypeVarNames(installed)
	assert.True(t, names["E"],
		"explicit type_specialize {A: var:E} must be honored exactly — the "+
			"installed hyp must be at type E; got type vars %v in %s",
		names, ext.PrintTerm(installed))
	assert.False(t, names["C"],
		"explicit type_specialize was silently overridden by the goal-context "+
			"type adaptation (TryAdaptLemmaTypes rebound the σ target to the "+
			"goal's instance C); installed hyp: %s", ext.PrintTerm(installed))
}

// TestLemmaTypeSpecialize_TwoLoadsAtDistinctInstances covers the second
// symptom from a depth-3 report on a list lemma: a SECOND `lemma` load of
// the same polymorphic lemma at a DIFFERENT type_specialize didn't
// produce a distinct usable ∀-hyp. Root cause was the same override —
// both loads were re-adapted to the SAME goal-context instance, so the
// second install collided with the first (already-a-hyp). With the σ
// honored exactly, two loads at two σs install two distinct hyps.
func TestLemmaTypeSpecialize_TwoLoadsAtDistinctInstances(t *testing.T) {
	A := core.TypeA()
	pTyA := core.MakeFun(A, core.TypeBool())
	pMeta := core.MakeConstMeta("PadaptTwoLoads", pTyA)
	pA := core.MakeConstTerm(pMeta, pTyA)
	x := ext.Var("x", A)
	lemma := prop.MakeProp(ext.ForAll(x)(ext.Apply(pA, x.Core())))

	// Goal context anchor at a THIRD instance G, so the adapter bait is
	// present for both loads.
	G := core.MakeVarType("G")
	pG := core.MakeConstTerm(pMeta, core.MakeFun(G, core.TypeBool()))
	gVar := core.Var("g", G)
	qMeta := core.MakeConstMeta("QadaptTwoLoads", core.TypeBool())
	Qconst := core.MakeConstTerm(qMeta, core.TypeBool())
	target := prop.MakeProp(Qconst, ext.Apply(pG, gVar))

	res, e, sid, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lemma",
		Lemma:          lemma,
		TypeSpecialize: map[string]string{"A": "var:E"},
	})
	require.True(t, res.Success, "first load (A:=E) must install; %+v", res.Diagnostics)

	// Locate the residual goal (the one whose conclusion is still Q) and
	// load the SAME lemma at a second, distinct instance.
	var residualID string
	for _, g := range res.State.Goals {
		if g.Statement.Conclusion().AlphaEquals(Qconst) {
			residualID = g.ID
		}
	}
	require.NotEmpty(t, residualID, "residual goal must exist")
	res2, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: residualID,
		Tactic: TacticReq{
			Type:           "lemma",
			Lemma:          lemma,
			TypeSpecialize: map[string]string{"A": "var:F"},
		},
	})
	require.NoError(t, err)
	require.True(t, res2.Success,
		"second load at a DISTINCT type_specialize (A:=F) must install a "+
			"distinct hyp, not dedupe against the first; %+v", res2.Diagnostics)

	hyps := findWorkingHyps(t, res2, Qconst)
	seen := map[string]bool{}
	for _, h := range hyps {
		if ext.MatchesFORALL(h).IsZero() {
			continue
		}
		for n := range termTypeVarNames(h) {
			seen[n] = true
		}
	}
	assert.True(t, seen["E"] && seen["F"],
		"both ∀-hyp instances (at E and at F) must be resident; ∀-hyp type vars seen: %v, hyps=%v",
		seen, printedHyps(hyps))
}

// TestLeanRwTypeSpecialize_VarTargetNotOverriddenByGoalContext is the
// lean_rw twin: the rewrite-rule dispatch had the same adapt-after-σ
// hole (ApplyLeanRwWithSource → chooseTypeAdaptedStep) for
// type_specialize-only calls.
//
// Setup mirrors the lemma test but with an equational rule so lean_rw's
// equality gate passes: rule `∀x:A. f⟨A⟩(x) = x`, goal conclusion
// containing f at the agent-requested var type E, with a COMPETING
// instance f⟨C⟩ resident in a hyp. The rewrite must fire on the E
// instance (σ honored); under the override it re-adapts to C and the
// rewrite misses its redex.
func TestLeanRwTypeSpecialize_VarTargetNotOverriddenByGoalContext(t *testing.T) {
	A := core.TypeA()
	fTyA := core.MakeFun(A, A)
	fMeta := core.MakeConstMeta("FrwOverride", fTyA)
	fA := core.MakeConstTerm(fMeta, fTyA)

	// Rule: ∀x:A. f⟨A⟩(x) = x
	x := ext.Var("x", A)
	rule := prop.MakeProp(ext.ForAll(x)(core.Eq(ext.Apply(fA, x.Core()), x.Core())))

	// Goal conclusion carries BOTH instances — f⟨E⟩(e) (the agent's
	// requested redex) and f⟨C⟩(c) (the competing goal-context instance
	// the adapter can rebind the σ target to):
	//
	//	⊢ P2(f⟨E⟩(e), f⟨C⟩(c))
	//
	// With σ honored, the rewrite fires on the E instance only →
	// P2(e, f⟨C⟩(c)). Under the override (σ target re-adapted to C) it
	// fires on the C instance instead → P2(f⟨E⟩(e), c).
	C := core.MakeVarType("C")
	E := core.MakeVarType("E")
	fC := core.MakeConstTerm(fMeta, core.MakeFun(C, C))
	fE := core.MakeConstTerm(fMeta, core.MakeFun(E, E))
	cVar := core.Var("c", C)
	eVar := core.Var("e", E)
	p2Ty := core.MakeFun(E, C, core.TypeBool())
	p2Meta := core.MakeConstMeta("PrwOverride2", p2Ty)
	p2 := core.MakeConstTerm(p2Meta, p2Ty)

	target := prop.MakeProp(
		ext.Apply(p2, ext.Apply(fE, eVar), ext.Apply(fC, cVar)),
	)

	res, _, _, _ := applyToSingleGoal(t, target, TacticReq{
		Type:           "lean_rw",
		Lemma:          rule,
		TypeSpecialize: map[string]string{"A": "var:E"},
	})
	require.True(t, res.Success,
		"lean_rw with explicit type_specialize {A: var:E} must fire on the "+
			"conclusion's f⟨E⟩ redex; diagnostics: %+v", res.Diagnostics)

	// The conclusion must have been rewritten at the E instance ONLY.
	expected := ext.Apply(p2, eVar, ext.Apply(fC, cVar))
	overridden := ext.Apply(p2, ext.Apply(fE, eVar), cVar)
	found, foundOverridden := false, false
	for _, g := range res.State.Goals {
		if g.Statement.Conclusion().AlphaEquals(expected) {
			found = true
		}
		if g.Statement.Conclusion().AlphaEquals(overridden) {
			foundOverridden = true
		}
	}
	assert.False(t, foundOverridden,
		"explicit type_specialize was silently overridden: the rewrite fired "+
			"on the goal-context C instance instead of the requested E instance")
	assert.True(t, found,
		"conclusion must be rewritten to P2(e, f(c)) — the E redex only; goals=%+v",
		res.State)
}
