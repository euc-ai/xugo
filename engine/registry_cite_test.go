package engine

// A session cites the proof registry and nothing else: the auto-match
// pass, the type-variant close and instantiate's type adaptation all
// read the entry that states a leaf or a hyp.

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// serveLikeEnv wires a prover env the way the serve does: constants
// resolve through the process's constant registry (the engine's
// built-ins and every chapter's mints). Nothing is served yet —
// servedEnv adds the corpus's builders.
func serveLikeEnv(t *testing.T) *proof.ProverEnv {
	t.Helper()
	mgr := registry.GetConstMetaManager()
	var cnfCache utils.Map[core.TermKey, core.Prop]
	env := &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        mgr.LoadConstMeta,
			LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
			Syntax:               mgr,
		},
		CnfRefuterTimeout:     2 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
	}
	return env
}

// servedEnv is serveLikeEnv with every registry entry's builder
// registered (serve.RegisterAll), so an auto-close carries the
// entry's real promise.
func servedEnv(t *testing.T) *proof.ProverEnv {
	t.Helper()
	env := serveLikeEnv(t)
	serve.RegisterAll(env)
	return env
}

// pairConsts reads the pair constructor and the two projections off
// the process's constant registry (the pairs chapter mints them).
func pairConsts(t *testing.T) (pairMeta, fstMeta, sndMeta core.ConstTermMeta) {
	t.Helper()
	mgr := registry.GetConstMetaManager()
	var ok bool
	pairMeta, ok = mgr.LoadConstMeta(",")
	require.True(t, ok, "the pair constructor is not minted")
	fstMeta, ok = mgr.LoadConstMeta("fst")
	require.True(t, ok, "fst is not minted")
	sndMeta, ok = mgr.LoadConstMeta("snd")
	require.True(t, ok, "snd is not minted")
	return
}

// pIntForInstantiate is the *int the instantiate wire shape takes.
func pIntForInstantiate(i int) *int { return &i }

// TestApplyLemma_TypeVariantOfEntryCloses: a goal that IS a member's
// statement up to the names of its type variables is closed by a cite
// of the member. The install would succeed too, by adding the member
// as a hypothesis beside a goal it already proves.
func TestApplyLemma_TypeVariantOfEntryCloses(t *testing.T) {
	snd, ok := registry.ByServesAs("snd_of_pair")
	require.True(t, ok, "no entry serves snd_of_pair: the fixture names what the corpus no longer has")
	pairMeta, _, sndMeta := pairConsts(t)

	// `∀x:A'. ∀y:B'. snd((x, y)) = y` — Snd's statement at fresh type
	// variable names.
	A := core.MakeVarType("?variant_A")
	B := core.MakeVarType("?variant_B")
	prodAB := core.MakeCompositeType(core.MakeMetaType("prod", 2), A, B)
	sndConst := core.MakeConstTerm(sndMeta, core.MakeFun(prodAB, B))
	pairConst := core.MakeConstTerm(pairMeta, core.MakeFun(A, core.MakeFun(B, prodAB)))
	x := core.Var("x", A)
	y := core.Var("y", B)
	body := core.Eq(ext.Apply(sndConst, ext.Apply(pairConst, x, y)), y)
	goal := prop.MakeProp(ext.ForAll(x)(ext.ForAll(y)(ext.WrapTerm(body))).Core())

	e := newEngine(serveLikeEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	gid := s.AddGoal(goal)
	s.rebuildGoalIndex()

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "lemma", LemmaKey: snd.Name},
	})
	require.NoError(t, err)
	require.True(t, out.Success,
		"citing the member must apply to a goal that is its own type variant: %+v", out.Diagnostics)
	assert.Equal(t, "close", out.Effect, "the member proves this goal: the cite closes it")
	assert.True(t, s.sections[0].root.Proved())
}

// TestKnown_ClosesLeafStatedByEntry: `known` closes a leaf whose
// statement is a registered member's, on the member's promise — and
// the automatic pipeline does not: a member enters a proof only where
// the author names it.
func TestKnown_ClosesLeafStatedByEntry(t *testing.T) {
	snd, ok := registry.ByServesAs("snd_of_pair")
	require.True(t, ok, "no entry serves snd_of_pair: the fixture names what the corpus no longer has")
	e := newEngine(servedEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	gid := s.AddGoal(snd.Statement().Prop)
	s.rebuildGoalIndex()

	assert.Empty(t, s.runAutoMatch(), "the automatic pipeline never cites the library")
	require.False(t, s.sections[0].root.Proved())

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "known"}})
	require.NoError(t, err)
	require.True(t, out.Success, "known closes the member's own statement: %+v", out.Diagnostics)
	assert.True(t, s.sections[0].root.Proved())
}

// TestApplyLemma_NormalizeEqualGoalCloses: a hyp-free goal that IS a
// member modulo Normalize — its contrapositive here — is closed by a
// cite of the member, as Go's `Cite` closes it at its normalize tier.
// The install would succeed too, by adding the member as a hypothesis
// beside a goal it already proves, and answer `effect: simplify` on a
// goal the member states.
func TestApplyLemma_NormalizeEqualGoalCloses(t *testing.T) {
	entry, ok := registry.ByName("finite_set.FiniteSubset")
	require.True(t, ok, "finite_set.FiniteSubset is not linked: the fixture names what the corpus no longer has")
	stmt := entry.Statement().Prop
	goal, err := parsePropTextInGoalScope(
		"∀s:(A → bool). ∀t:(A → bool). ¬finite(s) ∧ s ⊆ t ⇒ ¬finite(t)", stmt, nil)
	require.NoError(t, err)
	normGoal, _ := prop.Normalize(goal)
	normStmt, _ := prop.Normalize(stmt)
	require.Equal(t, normStmt.AlphaKey(), normGoal.AlphaKey(),
		"fixture: the goal must be the member modulo Normalize")
	require.False(t, goal.AlphaEquals(stmt), "fixture: and not the member as stated")

	e := newEngine(serveLikeEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	gid := s.AddGoal(goal)
	s.rebuildGoalIndex()

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "lemma", LemmaKey: entry.Name},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
	assert.Equal(t, "close", out.Effect, "the member proves this goal: the cite closes it")
	assert.True(t, s.sections[0].root.Proved())
}
