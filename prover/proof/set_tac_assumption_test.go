// set_tac_assumption_test.go — the set driver's terminal on a residual
// whose GOAL is α-identical to a resident hypothesis.
//
// Background (words/bit_set's BitSetIsFinite, BySets(premise) spelling):
// the membership driver rewrites the conclusion internally, and the
// residual can come out α-equal to the installed premise (renamed
// binder). A terminal that handed every residual to the CNF refuter
// unconditionally would make an assumption-closable leaf demand a
// recorded CNF cache key at strict replay — a key for a refute with no
// content. These tests pin:
//
//  1. Basic() DOES close goal-equals-∀-hyp modulo binder renaming
//     (HasHyp compares α-aware) — the byClosesUnderBasic oracle is not
//     defective on that shape.
//  2. The set driver's terminal (both modes) closes such a residual by
//     assumption WITHOUT reaching the refuter: under
//     RequireCNFCacheHit (which panics on any refuter reach with an
//     empty cache) the step still closes.
//  3. The BySets composite (settac closer) inherits the same guarantee
//     end-to-end.
//  4. The ordinary By closes such a residual at its apply rung, before
//     any closer and with no key. Its CNF closer does NOT pre-check
//     assumption (see byClosesUnderBasic) — on a leaf the rung does
//     not take, the MISS diagnostic reports the Basic() escape hatch.
//  5. The mechanism that makes two PRINT-identical sequents genuinely
//     different: a polymorphic const at two type instances prints the
//     same but is not α-equal, and Basic correctly declines.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// alphaHypGoal builds the minimal shape of the BitSetIsFinite residual:
//
//	∀i. b(i) ⇒ q(i)  ⊢  ∀x. b(x) ⇒ q(x)
//
// — the same statement under a renamed binder (α-equal, not Equals).
func alphaHypGoal(t *testing.T) Prop {
	t.Helper()
	predT := core.MakeFun(TypeInd, core.TypeBool())
	b := ext.Var("b", predT)
	q := ext.Var("q", predT)
	i := ext.Var("i", TypeInd)
	x := ext.Var("x", TypeInd)

	hyp := ext.ForAll(i)(b.Apply(i).Imply(q.Apply(i)))
	concl := ext.ForAll(x)(b.Apply(x).Imply(q.Apply(x)))

	require.False(t, hyp.Core().Equals(concl.Core()),
		"fixture must be a strict α-variant (different binder names)")
	require.True(t, hyp.Core().AlphaEquals(concl.Core()),
		"fixture hyp and conclusion must be α-equal")
	return prop.MakeProp(concl.Core(), hyp.Core())
}

// strictEnv is a test env in which ANY refuter reach is loud: the mock
// ProofService carries no CNF cache, and RequireCNFCacheHit turns the
// guaranteed MISS into a panic instead of a live search. A step that
// closes under this env provably never invoked the refuter.
func strictEnv() *ProverEnv {
	env := makeStepTestEnv()
	env.RequireCNFCacheHit = true
	return env
}

// TestBasic_ClosesAlphaVariantForallHyp decides claim (b): a goal whose
// conclusion is an α-variant of a resident ∀-hypothesis closes under a
// plain Basic() — simplestTrivialTactic's h ⊢ h branch goes through
// HasHyp, whose Term.Compare is α-aware. The byClosesUnderBasic oracle
// therefore answers true on this exact sequent.
func TestBasic_ClosesAlphaVariantForallHyp(t *testing.T) {
	defer goleak.VerifyNone(t)
	goal := alphaHypGoal(t)

	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_BasicTactic{}),
		"Basic() must fire on goal-equals-∀-hyp modulo binder renaming")
	assert.True(t, n.Proved(), "Basic() must close the goal outright")

	// The oracle itself, on a fresh stack of the same sequent.
	n2 := CreateGoalStack(goal)
	assert.True(t, byClosesUnderBasic(t.Context(), n2, nil),
		"byClosesUnderBasic must report true on an α-identical h ⊢ h leaf")
}

// TestSetTacMembership_AlphaResidual_ClosesWithoutRefuter decides claim
// (a): the membership-mode set driver must close a residual whose goal
// is a resident hyp by ASSUMPTION, without invoking the CNF refuter
// (strictEnv makes any refuter reach panic on the empty cache). Before
// the terminal pre-check this panicked:
//
//	tryCNFRefute[RequireCNFCacheHit]: CNF cache MISS …
func TestSetTacMembership_AlphaResidual_ClosesWithoutRefuter(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := strictEnv()

	n := CreateGoalStack(alphaHypGoal(t))
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_MEMBERSHIP, nil),
		"membership set_tac must close an assumption-closable residual without the refuter")
	assert.True(t, n.Proved())
}

// TestSetTacLegacy_AlphaResidual_ClosesWithoutRefuter: the legacy mode
// shares the terminal, so it inherits the same assumption pre-check.
func TestSetTacLegacy_AlphaResidual_ClosesWithoutRefuter(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := strictEnv()

	n := CreateGoalStack(alphaHypGoal(t))
	require.True(t,
		ApplySetTacMode(n, env, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_LEGACY, nil),
		"legacy set_tac must close an assumption-closable residual without the refuter")
	assert.True(t, n.Proved())
}

// TestApplyByStep_SettacCloser_AlphaResidentPremise is the end-to-end
// BySets(premise) shape of that member: ambient hyp
// named as a resident premise, conclusion an α-variant of it, settac
// closer. Must close with no refuter reach and no claim children.
func TestApplyByStep_SettacCloser_AlphaResidentPremise(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := strictEnv()

	goal := alphaHypGoal(t)
	n := CreateGoalStack(goal)
	spec := BySpec{
		Premises: []ByPremiseSpec{{
			Install:  prop.MakeProp(goal.Hyp(0)),
			Resident: true,
			Describe: "hyp ∀i. b(i) ⇒ q(i)",
		}},
		Settac: true,
	}
	require.True(t, ApplyByStep(n, env, t.Context(), spec),
		"BySets(resident premise) must close when the residual goal α-equals the premise")
	assert.True(t, n.Proved(), "resident premise ⇒ no claim children ⇒ proved outright")
}

// TestApplyByStep_CnfCloser_AlphaResident_ClosesByAssumption pins the
// ordinary By CNF closer's behavior on the same sequent under the apply
// rung: a leaf whose conclusion is α-resident closes by the rung's
// degenerate case — Lean's `exact h` — before any closer runs, with NO
// key. By never SUBSTITUTES a cheaper closer behind the author's back,
// and this is no substitution: the apply rung is By's documented first
// move. A Basic()-closable leaf that is not α-resident reaches the
// closer, and on a miss gets the Basic() diagnostic.
func TestApplyByStep_CnfCloser_AlphaResident_ClosesByAssumption(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := strictEnv()

	goal := alphaHypGoal(t)
	n := CreateGoalStack(goal)
	spec := BySpec{
		Premises: []ByPremiseSpec{{
			Install:  prop.MakeProp(goal.Hyp(0)),
			Resident: true,
			Describe: "hyp ∀i. b(i) ⇒ q(i)",
		}},
	}
	require.True(t, ApplyByStep(n, env, t.Context(), spec),
		"an α-resident conclusion closes by the apply rung under strict replay — no key needed")
	assert.True(t, n.Proved())
}

// TestBasic_DeclinesTypeDivergentPrintIdentical pins two sides of the
// `card(𝕌)` shape — a polymorphic const whose type argument is
// unconstrained by the rest of the statement:
//
//   - Basic correctly DECLINES the pair (they are not α-equal, however
//     similar they look), so a refute of it has real content; and
//   - the printer tells them apart: the recoverability analysis
//     (ext.ConstConflictSet) annotates an instance the printed term
//     cannot re-derive, so the two statements print DIFFERENTLY
//     (⟨A:ind⟩ vs ⟨A:bool⟩) — the injectivity contract.
func TestBasic_DeclinesTypeDivergentPrintIdentical(t *testing.T) {
	defer goleak.VerifyNone(t)

	genSetT := core.MakeFun(core.TypeA(), core.TypeBool())
	// universe-like nullary-ish const: λx:A. x = x  :  A → bool.
	xa := ext.Var("x", core.TypeA())
	univC := core.NewConstDef(xa.To(xa.Eq(xa)).Core(), "UnivAlphaTest")
	// card-like observer of a set: λs:A→bool. s = s  :  (A → bool) → bool.
	sa := ext.Var("s", genSetT)
	dimC := core.NewConstDef(sa.To(sa.Eq(sa)).Core(), "DimAlphaTest")

	at := func(ty core.HolType) *ext.TermWrapper {
		subst := core.MakeTypeSubst(core.TypeA(), ty)
		return ext.WrapTerm(dimC.TypeSubstitute(subst)).
			Apply(ext.WrapTerm(univC.TypeSubstitute(subst)))
	}

	predT := core.MakeFun(TypeInd, core.TypeBool())
	b := ext.Var("b", predT)
	x := ext.Var("x", TypeInd)
	hyp := ext.ForAll(x)(b.Apply(x).Imply(at(TypeInd)))
	concl := ext.ForAll(x)(b.Apply(x).Imply(at(core.TypeBool())))

	require.NotEqual(t, ext.PrintTerm(hyp.Core()), ext.PrintTerm(concl.Core()),
		"the printer must annotate the unrecoverable instances — distinct statements must not print identically")
	require.False(t, hyp.Core().AlphaEquals(concl.Core()),
		"the pair is NOT α-equal (different type instances)")

	n := CreateGoalStack(prop.MakeProp(concl.Core(), hyp.Core()))
	closed := byClosesUnderBasic(t.Context(), n, nil)
	assert.False(t, closed,
		"Basic must decline the type-divergent pair — a 'does NOT close under Basic' "+
			"verdict on a print-identical sequent is honest, not a defect")
}
