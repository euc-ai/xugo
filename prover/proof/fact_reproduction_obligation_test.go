// fact_reproduction_obligation_test.go — closeReproductionObligation's
// obligation-vs-rewritten-goal decision (fact.go).
//
// The decision needs two tests because a polymorphic lemma type-adapts
// on install (chooseTypeAdaptedStep), so the obligation leaf carries the
// INSTANTIATED statement — same printed form as the schematic source,
// α-unequal types — which IsStronger alone cannot equate. These tests
// pin both sides: an instantiated obligation must CLOSE (through the
// cache matcher's type-instance tier), and a leaf that really is the
// rewritten goal must stay OPEN.
//
// The fixture mirrors the live corpus shape (snd cited on a goal whose
// pair is a VARIABLE): a closed polymorphic projection lemma, and a
// goal that pins the type instance while offering no literal-pair redex
// — so the preserving install adds the hypothesis instead of firing as
// a rewrite, and the reproduction obligation is the instantiated closed
// statement. A lemma with FREE schematic-typed variables would NOT
// close through the type-instance tier (Normalize ∀-closes frees in an
// order that need not match the instantiated side's — the same
// adjacent-binder α-limitation seed_alpha_matches documents), which is
// fine: no corpus dep has that shape, and such an install stays open
// exactly like a rewrite consumption.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// obligationFixture: a closed polymorphic ⊢ ∀y:B. ∀x:A. y = psnd((x,y))
// saved in the env cache, and a section whose goal ⊢ Q(psnd(p)) — p a
// variable pair at ind — pins A,B := ind on install without giving the
// equation a redex.
func obligationFixture(t *testing.T) (*Script, *GoalStackNode, Prop) {
	t.Helper()
	env := makeStepTestEnv()

	prodAB := ext.MakeProdType(TypeA, TypeB)
	psndMeta := core.MakeConstMeta("psnd", MakeFun(prodAB, TypeB))
	env.ProofService.LoadOrStoreConstMeta(psndMeta)
	env.ProofService.LoadOrStoreConstMeta(ext.CommaConstMeta)

	xA, yB := Var("x", TypeA), Var("y", TypeB)
	commaAB := ext.WrapTerm(core.MakeConstTerm(ext.CommaConstMeta,
		MakeFun(TypeA, MakeFun(TypeB, prodAB))))
	psndAB := ext.WrapTerm(core.MakeConstTerm(psndMeta, MakeFun(prodAB, TypeB)))
	source := core.TestThm(ForAll(yB)(ForAll(xA)(
		yB.Eq(psndAB.Apply(commaAB.Apply(xA, yB))))))
	require.False(t, source.IsZero())
	nsrc, _ := Normalize(source)
	env.ThmCache.SaveThm(source, nsrc.AsThmCert())

	ctx := NewScript(env)
	prodII := ext.MakeProdType(TypeInd, TypeInd)
	p := Var("p", prodII)
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	psndII := ext.WrapTerm(core.MakeConstTerm(psndMeta, MakeFun(prodII, TypeInd)))
	sec := ctx.Section(prop.MakeProp(Q.Apply(psndII.Apply(p))))
	return ctx, sec, source
}

// TestCloseReproductionObligation_TypeInstantiatedObligation: after a
// type-adapting preserving install, the obligation leaf's statement is
// the INSTANTIATED lemma — IsStronger(schematic, instantiated) is false
// while the leaf IS the obligation, and it must close (the cache
// matcher's type-instance tier records the replay-stable _TypeInstStep).
// The IsStronger-only guard mis-classified this as a rewrite
// consumption and skipped the close, leaving the obligation as the
// FIRST unsolved leaf — where By's later premise installs, grounding
// and terminal refutation would all land.
func TestCloseReproductionObligation_TypeInstantiatedObligation(t *testing.T) {
	defer goleak.VerifyNone(t)
	ctx, sec, source := obligationFixture(t)

	require.True(t, ApplyLemmaPreserve(sec, source), "preserving install must apply")

	// Pin the test's premise: the first unsolved leaf is the hyp-free
	// obligation, and the install DID type-adapt (IsStronger false).
	obligation := sec.unsolvedLeaf(0)
	require.NotNil(t, obligation)
	require.Zero(t, obligation.Goal.NumHyps(), "fixture drifted: leaf 0 is not the obligation")
	require.False(t, IsStronger(source, obligation.Goal),
		"fixture drifted: install did not type-adapt, IsStronger already holds")

	closeReproductionObligation(ctx, sec, source)

	// The obligation must be closed; the surviving leaf is the
	// hyp-extended goal.
	require.True(t, obligation.Proved(),
		"the type-instantiated reproduction obligation is still open:\n%s",
		prop.PrintProp(obligation.Goal))
	remaining := sec.unsolvedLeaf(0)
	require.NotNil(t, remaining, "the hyp-extended goal should survive")
	require.NotZero(t, remaining.Goal.NumHyps(),
		"surviving leaf should be the hyp-extended goal, got:\n%s",
		prop.PrintProp(remaining.Goal))
}

// TestCloseReproductionObligation_RewriteConsumptionStaysOpen: when the
// remaining leaf is NOT the obligation — the state a goal-rewrite
// consumption leaves behind — closeReproductionObligation must leave it
// open and must not panic (the unguarded CiteKnown's "no matching
// cached thm" was exactly that panic). The leaf here is unrelated to L
// by construction, so both the IsStronger test and every cache tier
// miss; the live rewrite-consumption sites in the corpus are
// the end-to-end version of this contract.
func TestCloseReproductionObligation_RewriteConsumptionStaysOpen(t *testing.T) {
	defer goleak.VerifyNone(t)
	ctx, _, source := obligationFixture(t)

	// A second section whose goal has nothing to do with the source.
	c := Var("c", TypeInd)
	W := Var("W", MakeFun(TypeInd, TypeBool))
	sec := ctx.Section(prop.MakeProp(W.Apply(c)))
	before := sec.unsolvedLeaf(0)
	require.NotNil(t, before)

	closeReproductionObligation(ctx, sec, source)

	remaining := sec.unsolvedLeaf(0)
	require.NotNil(t, remaining,
		"a non-obligation leaf must stay open — closeReproductionObligation over-closed")
	require.Equal(t, before, remaining, "the leaf must be untouched")
}
