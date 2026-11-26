package proof

import (
	"context"
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// residentBySpec names every hypothesis of goal as a resident premise.
func residentBySpec(goal Prop) BySpec {
	var premises []ByPremiseSpec
	for i := range goal.NumHyps() {
		premises = append(premises, ByPremiseSpec{Install: prop.MakeProp(goal.Hyp(i)), Resident: true, Describe: "premise"})
	}
	return BySpec{Premises: premises}
}

// byFailureUnder is the failure text of a By over spec on goal, run
// under env.
func byFailureUnder(env *ProverEnv, goal Prop, spec BySpec) (text string) {
	defer func() {
		if r := recover(); r != nil {
			text = fmt.Sprint(r)
		}
	}()
	ApplyByStep(CreateGoalStack(goal), env, context.Background(), spec)
	return ""
}

// threeLinkChain is a chain of three links of one size: no rewrite
// shrinks its target, none makes the conclusion a hypothesis, so Basic()
// does not close it and a By over it reaches the refuter.
func threeLinkChain() Prop {
	ind := TypeInd
	fun := core.MakeFun(ind, ind)
	f, g, h, k := ext.Var("f", fun), ext.Var("g", fun), ext.Var("h", fun), ext.Var("k", fun)
	a, b, c, d := ext.Var("a", ind), ext.Var("b", ind), ext.Var("c", ind), ext.Var("d", ind)
	return prop.MakeProp(f.Apply(a).Eq(k.Apply(d)).Core(),
		f.Apply(a).Eq(g.Apply(b)).Core(), g.Apply(b).Eq(h.Apply(c)).Core(), h.Apply(c).Eq(k.Apply(d)).Core())
}

// residentByStep is a By over goal's hypotheses, each a resident premise,
// on env. Its failure says what it tried unless a caller marks it unread.
func residentByStep(env *ProverEnv, ctx context.Context, goal Prop) _ByStep {
	premises := make([]byPremise, goal.NumHyps())
	for i := range premises {
		premises[i] = byPremise{install: prop.MakeProp(goal.Hyp(i)), resident: true, describe: "premise"}
	}
	return _ByStep{premises: premises, env: env, ctx: ctx, spine: CreateGoalStack(goal)}
}

// failureOf is the panic of one attempt of step on goal, as text.
func failureOf(step _ByStep, goal Prop) (text string) {
	defer func() {
		if r := recover(); r != nil {
			text = fmt.Sprint(r)
		}
	}()
	step.applyInner(goal)
	return ""
}

// TestBy_AnUnreadFailureIsRaisedAsItIs: an attempt whose caller reads its
// failure only as "did not close" renders no message, whose notes walk
// the proof tree, and raises the close's own cause. The attempt whose
// failure is read says what it tried.
func TestBy_AnUnreadFailureIsRaisedAsItIs(t *testing.T) {
	goal := threeLinkChain()
	step := residentByStep(strictEnv(), withCNFCacheOnlyProbe(t.Context()), goal)

	read := failureOf(step, goal)
	require.Contains(t, read, "CNF cache MISS", "fixture: the By must reach the refuter: %s", read)
	require.Contains(t, read, "failed with premises")

	step.failureUnread = true
	unread := failureOf(step, goal)
	assert.Contains(t, unread, "CNF cache MISS")
	assert.NotContains(t, unread, "failed with premises")
}

// _BreachingCNFStore fails an assertion when a close reads it: at the
// exact key a close asks first, and at a certificate.
type _BreachingCNFStore struct{ CNFStore }

func (_BreachingCNFStore) ReadExactKey(core.PropKey) core.PropKey {
	utils.Assert(false)
	return ""
}

func (_BreachingCNFStore) ReadProof(core.PropKey) *refuter.CNFRefuteProofProto {
	utils.Assert(false)
	return nil
}

// TestBy_AProbeRaisesABreachInsideItsClose: a failed assertion inside the
// close of a rung-1 probe reaches rungFailure as the assertion it is and
// is raised again, so a later rung cannot close over it.
func TestBy_AProbeRaisesABreachInsideItsClose(t *testing.T) {
	goal := threeLinkChain()
	env := strictEnv()
	env.ProofService.CNFStore = _BreachingCNFStore{env.ProofService.CNFStore}
	step := residentByStep(env, t.Context(), goal)

	defer func() {
		r := recover()
		require.NotNil(t, r, "the probe must raise the breach")
		assert.True(t, utils.IsAssertionFailure(r), "raised as an assertion: %v", r)
	}()
	step.probeBare(goal)
}

// TestBy_AFailureUnderACacheOnlyContextIsRead: a session's resume runs
// under the cache-only context (CNFCacheOnlyContext) and hands the By's
// failure to the reader as the divergence, so that context alone marks no
// failure unread; only the ladder's own probes do.
func TestBy_AFailureUnderACacheOnlyContextIsRead(t *testing.T) {
	goal := threeLinkChain()
	diverged := func() (text string) {
		defer func() {
			if r := recover(); r != nil {
				text = fmt.Sprint(r)
			}
		}()
		ApplyByStep(CreateGoalStack(goal), makeStepTestEnv(), CNFCacheOnlyContext(t.Context()), residentBySpec(goal))
		return ""
	}()
	require.NotEmpty(t, diverged, "fixture: a cache-only By over an unrecorded leaf fails")
	assert.Contains(t, diverged, "failed with premises")
}

// TestBy_StrictMissThatBasicDoesNotCloseNamesTheShapeRepairs: the MISS
// of a leaf Basic() does not close offers more than "record it" and "a
// wrong instance" — the shaping repairs that sit between the two, that
// a shaping can move a key without removing it, and the recorder's
// read-only run; and it names the recorder's own package.
func TestBy_StrictMissThatBasicDoesNotCloseNamesTheShapeRepairs(t *testing.T) {
	goal := threeLinkChain()

	miss := byFailureUnder(strictEnv(), goal, residentBySpec(goal))
	require.Contains(t, miss, "CNF cache MISS", "fixture: the By must reach the refuter: %s", miss)
	require.Contains(t, miss, "does NOT close under Basic()")
	assert.Contains(t, miss, "DenotedAs(name, term)")
	assert.Contains(t, miss, "RELOCATE the key")
	assert.Contains(t, miss, "XUGO_RECORD_CNF_DRY_RUN=1")
	assert.Contains(t, miss, "./library/integrity/gates/", "the recorder's package")
	assert.NotContains(t, miss, "./library/proofs/)")
}

// TestBy_ClosesAFunctionEquationInArgumentPosition: with `g = h`
// between functions resident and `g` standing as an ARGUMENT, the By
// closes — the refuter recovers the equation from its pointwise clause
// (FUNEXT, ext/clause/funext.go) and rewrites the argument. The control
// fails for want of a premise: Q(k(x)) does not follow from k(x) = c.
func TestBy_ClosesAFunctionEquationInArgumentPosition(t *testing.T) {
	e := makeSimpStatedEnv()
	functions := prop.MakeProp(e.P.Apply(e.g).Core(), e.g.Eq(e.h).Core(), e.P.Apply(e.h).Core())
	assert.Empty(t, byFailureUnder(makeStepTestEnv(), functions, residentBySpec(functions)),
		"P(g) follows from g = h and P(h)")

	x := ext.Var("x", TypeInd)
	points := prop.MakeProp(e.Q.Apply(e.k.Apply(x)).Core(), e.k.Apply(x).Eq(e.c).Core())
	require.NotEmpty(t, byFailureUnder(makeStepTestEnv(), points, residentBySpec(points)),
		"fixture: Q(k(x)) does not follow from k(x) = c")
}

// A set-driver close that fails inside a By prints the leaf the driver
// received and the residual it could not close, as the refuter's
// failure prints its leaf (#1455, ProjectiveLineBiaffine).
func TestBySets_FailurePrintsTheLeafAndTheResidual(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	defer func() {
		r := recover()
		require.NotNil(t, r)
		msg := fmt.Sprint(r)
		require.Contains(t, msg, "the set driver's residual leaves, after its membership rewrite, that did not close:\n  x₀ ∈ s₀\n\t⊢ x₀ ∈ t₀")
		require.Contains(t, msg, "did not close the leaf\n  on leaf goal: x₀ ∈ s₀\n\t⊢ x₀ ∈ t₀")
	}()
	ctx.Theorem("∀s t:(num → bool). ∀x:num. x ∈ s ⇒ x ∈ t",
		func(a *Argument, s, tt *ext.Expr[natSet], x *ext.Expr[ext.Nat], xIn Fact) {
			a.Show("not a theorem: the driver says where it stopped", BySets(xIn))
		})
}
