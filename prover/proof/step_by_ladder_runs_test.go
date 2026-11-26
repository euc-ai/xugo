// step_by_ladder_runs_test.go — the two runs of the By ladder's
// conditioned rung. A plan the store holds for the leaf is applied as
// recorded. With none the rung grounds to the whole leaf, the instances
// added and every source kept, and, where that fails and a match pinned
// a source in full, to the pruned one, each such source replaced by its
// instances. These tests hold which closes each run makes, what such a
// close records and that the recording replays, and what a By that
// closes at no rung says.
package proof

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// zpConst and zqConst are test-local opaque predicates (constantly true
// by definition, never def-expanded by the pipeline): the e-match
// trigger needs a const-headed atom mentioning the binder.
var (
	zpConst = core.NewConstDef(ext.Var("zzpx", TypeInd).To(ext.T), "zz_kept_wide_p")
	zqConst = core.NewConstDef(ext.Var("zzqx", TypeInd).To(ext.T), "zz_kept_wide_q")
)

// zTagConst, zFstConst and zSndConst are test-local opaque constants in
// the roles of a pair with a boolean first part and its two projections:
// zTag(b, v) the pair, zFst(p) and zSnd(p) what the laws of the fixture
// say they read off it.
var (
	zTagConst = core.NewConstDef(ext.Var("zztb", core.TypeBool()).To(ext.Var("zztv", TypeInd).To(ext.Var("zztv", TypeInd))), "zz_ladder_tag")
	zFstConst = core.NewConstDef(ext.Var("zzfp", TypeInd).To(ext.T), "zz_ladder_fst")
	zSndConst = core.NewConstDef(ext.Var("zzsp", TypeInd).To(ext.Var("zzsp", TypeInd)), "zz_ladder_snd")
)

// lawElsewhereFixture is a leaf whose close needs a law at a point no
// term of it spells, beside a point one does:
//
//	∀x. P(x) ⇒ Q(x),  ∀y. Q(y) ⇒ P(f(y)),  ∀z. Q(f(z)) ⇒ r,  P(a)  ⊢  r
//
// The grounding stage grounds each law at a, the one point the leaf
// spells. The first law's instance `P(a) ⇒ Q(a)` has its antecedent in
// the leaf, so a pruning stage replaces that law; the others' instances
// are guesses at antecedents the leaf does not hold, and their laws stay
// under either stage. The close runs P(a), Q(a), P(f(a)), Q(f(a)), r,
// and the fourth step is the first law at f(a): pruned, the leaf
// saturates without it. With closes false the leaf is the first law and
// P(a) alone, and r follows at no rung.
func lawElsewhereFixture(t *testing.T, closes bool) Prop {
	t.Helper()
	P, Q := ext.WrapTerm(zpConst), ext.WrapTerm(zqConst)
	f := ext.Var("f", core.MakeFun(TypeInd, TypeInd))
	a := ext.Var("a", TypeInd)
	x, y, z := ext.Var("x", TypeInd), ext.Var("y", TypeInd), ext.Var("z", TypeInd)
	r := ext.Var("r", core.TypeBool())

	hyps := []core.Term{
		ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x))).Core(),
		P.Apply(a).Core(),
	}
	if closes {
		hyps = append(hyps,
			ext.ForAll(y)(Q.Apply(y).Imply(P.Apply(f.Apply(y)))).Core(),
			ext.ForAll(z)(Q.Apply(f.Apply(z)).Imply(r)).Core())
	}
	return prop.MakeProp(r.Core(), hyps...)
}

// uniqueFromWitnessFixture is the leaf every proof of a unique existence
// from a witness and an "every witness is z" fact closes:
//
//	∀y. P(y) ∧ Q(y) ⇒ y = z,  P(z) ∧ Q(z)  ⊢  ∃!x. P(x) ∧ Q(x)
//
// The stage grounds the first fact at z, through its antecedent and the
// witness fact, to `P(z) ∧ Q(z) ⇒ z = z`. Uniqueness wants the fact at
// the two witnesses the refutation of the goal makes, which no term of
// the leaf spells.
func uniqueFromWitnessFixture(t *testing.T) Prop {
	t.Helper()
	P, Q := ext.WrapTerm(zpConst), ext.WrapTerm(zqConst)
	x, y, z := ext.Var("x", TypeInd), ext.Var("y", TypeInd), ext.Var("z", TypeInd)
	only := ext.ForAll(y)(P.Apply(y).And(Q.Apply(y)).Imply(y.Eq(z)))
	witness := P.Apply(z).And(Q.Apply(z))
	return prop.MakeProp(ext.Unique(x)(P.Apply(x).And(Q.Apply(x))).Core(), only.Core(), witness.Core())
}

// taggedPairFixture is the leaf `By(Normalized, written, pairs.Fst,
// pairs.Snd)` closes where a pair's first part is a truth value:
//
//	∀x y. zFst(zTag(x, y)) ⇔ x,  ∀x y. zSnd(zTag(x, y)) = y,
//	p = zTag(b, v) ∧ Q(v)  ⊢  (zFst(p) ⇔ b) ∧ Q(zSnd(p))
//
// The stage grounds both laws at (b, v), every binder pinned. With the
// laws kept, the shaping's Basic() splits on the first one's boolean
// binder and leaves a fan the By, which declares no Broadcast, does not
// close; with each replaced by its instance the leaf is ground and
// closes.
func taggedPairFixture(t *testing.T) Prop {
	t.Helper()
	tag, fst, snd := ext.WrapTerm(zTagConst), ext.WrapTerm(zFstConst), ext.WrapTerm(zSndConst)
	Q := ext.WrapTerm(zqConst)
	x, y := ext.Var("x", core.TypeBool()), ext.Var("y", TypeInd)
	p, b, v := ext.Var("p", TypeInd), ext.Var("b", core.TypeBool()), ext.Var("v", TypeInd)
	first := ext.ForAll(x, y)(fst.Apply(tag.Apply(x, y)).Eq(x))
	second := ext.ForAll(x, y)(snd.Apply(tag.Apply(x, y)).Eq(y))
	written := p.Eq(tag.Apply(b, v)).And(Q.Apply(v))
	concl := fst.Apply(p).Eq(b).And(Q.Apply(snd.Apply(p)))
	return prop.MakeProp(concl.Core(), first.Core(), second.Core(), written.Core())
}

func ladderRunsEnv(t *testing.T) *ProverEnv {
	t.Helper()
	env := makeStepTestEnv()
	for _, c := range []core.ConstTerm{zpConst, zqConst, zkConst, zTagConst, zFstConst, zSndConst} {
		_, _ = env.ProofService.LoadOrStoreConstMeta(c.Meta())
	}
	return env
}

// forallHypOver is goal's first ∀-headed hypothesis that spells the
// named constant.
func forallHypOver(t *testing.T, goal Prop, constant string) core.Term {
	t.Helper()
	for i := range goal.NumHyps() {
		if h := goal.Hyp(i); !ext.MatchesFORALL(h).IsZero() && strings.Contains(ext.PrintTerm(h), constant) {
			return h
		}
	}
	t.Fatalf("no ∀-hypothesis over %s", constant)
	return nil
}

// hypIndexOfForall is the index of goal's first ∀-headed hypothesis that
// spells the named constant.
func hypIndexOfForall(t *testing.T, goal Prop, constant string) int {
	t.Helper()
	idx, err := findHypIndex(goal, forallHypOver(t, goal, constant))
	require.NoError(t, err)
	return idx
}

// onlyPlan is the one plan st holds.
func onlyPlan(t *testing.T, st *MemoryCNFStore) *ByConditionPlanProto {
	t.Helper()
	require.Len(t, st.Plans(), 1)
	for _, entry := range st.Plans() {
		return entry
	}
	return nil
}

// byRoute applies the By naming every hypothesis of goal on env, under
// shapes, and returns whether it closed and the routes of the close.
func byRoute(t *testing.T, env *ProverEnv, goal Prop, shapes ...ByShape) (closed bool, route string) {
	t.Helper()
	spec := guardedBySpec(goal)
	spec.Shapes = shapes
	spec.Closed = func(r string) { route = r }
	n := CreateGoalStack(goal)
	closed = ApplyByStep(n, env, t.Context(), spec) && n.Proved()
	return closed, route
}

// requireFirstRun fails unless route is that of a close the conditioned
// rung made in its first run, on the whole leaf.
func requireFirstRun(t *testing.T, route string) {
	t.Helper()
	require.NotContains(t, route, byPrunedRoute, "not on the pruned leaf")
}

// TestByLadder_UniqueFromAWitnessClosesInTheFirstRun: the conditioned
// rung closes the unique existence in its first run, with the "only"
// fact kept beside its instance. A pruning stage replaces that fact, and
// the leaf it leaves does not close: the fact is gone at the witnesses
// of the refutation. The close records one plan, which replaces
// nothing, and replays strictly from it — a close the bare retry made
// would record none.
func TestByLadder_UniqueFromAWitnessClosesInTheFirstRun(t *testing.T) {
	goal := uniqueFromWitnessFixture(t)
	only := forallHypOver(t, goal, "zz_kept_wide_p")

	env := ladderRunsEnv(t)
	c := &conditioner{env: env, ctx: t.Context(), s4: &byS4State{}}
	root := CreateGoalStack(goal)
	c.conditionLeaf(root, conditionOpts{ground: true, prune: true})
	leaf := byWorkingLeaf(root, nil)
	require.False(t, leaf.Goal.HasHyp(only), "a pruning stage replaces the fact by its instance at z")
	require.False(t, leaf.runStep(_CNFRefute{env: env, ctx: t.Context()}), "and the pruned leaf does not close")

	st := NewMemoryCNFStore()
	rec := ladderRunsEnv(t)
	rec.ProofService.CNFStore = st
	closed, route := byRoute(t, rec, goal)
	require.True(t, closed, "the By closes")
	requireFirstRun(t, route)
	entry := onlyPlan(t, st)
	require.Len(t, entry.Groundings, 1, "the fact grounded at z")
	require.Empty(t, entry.Replaced, "and kept")

	strict := ladderRunsEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	closed, _ = byRoute(t, strict, goal)
	require.True(t, closed, "strict replay applies the recorded plan and reads the certificate")
}

// TestByLadder_TheFirstRunKeepsALawTheCloseNeedsElsewhere: the close
// wants the first law at f(a), a point only another law's instance
// produces. The rung's first run keeps the law and closes; the plan
// records each law's grounding and no replacement, and replays strictly.
func TestByLadder_TheFirstRunKeepsALawTheCloseNeedsElsewhere(t *testing.T) {
	goal := lawElsewhereFixture(t, true)
	st := NewMemoryCNFStore()

	rec := ladderRunsEnv(t)
	rec.ProofService.CNFStore = st
	closed, route := byRoute(t, rec, goal)
	require.True(t, closed, "the By closes")
	requireFirstRun(t, route)
	entry := onlyPlan(t, st)
	require.Len(t, entry.Groundings, 3, "each law grounded at a")
	require.Empty(t, entry.Replaced, "and none replaced")
	require.NotEmpty(t, st.Proofs())

	strict := ladderRunsEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	closed, _ = byRoute(t, strict, goal)
	require.True(t, closed, "strict replay applies the recorded plan, which replaces nothing, and reads the certificate")
}

// TestByLadder_ThePrunedRunClosesWhereAShapingDiscardsTheInstances: the
// shaping's Basic() discards an instance that stands beside its source,
// and over the whole leaf here it fans on the law it kept. The rung's
// first run fails; on the pruned leaf, which is ground, it closes. The
// close says so by its route and records the plans of that run, which
// replace; strict replay applies them in its one conditioned rung. The
// same leaf with no shaping closes in the first run, and that plan
// replaces nothing.
func TestByLadder_ThePrunedRunClosesWhereAShapingDiscardsTheInstances(t *testing.T) {
	goal := taggedPairFixture(t)

	whole := ladderRunsEnv(t)
	c := &conditioner{env: whole, ctx: t.Context(), s4: &byS4State{}}
	root := CreateGoalStack(goal)
	c.conditionLeaf(root, conditionOpts{ground: true})
	before := byWorkingLeaf(root, nil).Goal.NumHyps()
	byWorkingLeaf(root, nil).runBasicUntil(t.Context())
	leaves := byWorkingLeaves(root, nil)
	require.Greater(t, len(leaves), 1, "Basic() fans over the whole leaf")
	require.Less(t, leaves[0].Goal.NumHyps(), before, "and discards the instances that stood beside their laws")

	st := NewMemoryCNFStore()
	rec := ladderRunsEnv(t)
	rec.ProofService.CNFStore = st
	closed, route := byRoute(t, rec, goal, Normalized)
	require.True(t, closed, "the By closes")
	require.Contains(t, route, byPrunedRoute, "the route names the run")
	require.NotEmpty(t, st.Plans(), "a conditioned close: the bare retry records no plan")
	for _, entry := range st.Plans() {
		require.NotEmpty(t, entry.Replaced, "the plan of the pruned run replaces")
	}

	strict := ladderRunsEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	closed, route = byRoute(t, strict, goal, Normalized)
	require.True(t, closed, "strict replay applies the recorded plans and reads the certificates")
	require.NotContains(t, route, byPrunedRoute, "in its one conditioned rung")

	plain := NewMemoryCNFStore()
	unshaped := ladderRunsEnv(t)
	unshaped.ProofService.CNFStore = plain
	closed, route = byRoute(t, unshaped, goal)
	require.True(t, closed)
	requireFirstRun(t, route)
	for _, entry := range plain.Plans() {
		require.Empty(t, entry.Replaced, "the first run keeps")
	}
}

// TestByLadder_AShapedByIsRunOnTheWholeLeafFirst: a shaping does not
// change which leaf is first. The close wants the first law at a point
// only another law's instance produces; under Normalized, as without
// it, the rung closes in its first run with the law kept.
func TestByLadder_AShapedByIsRunOnTheWholeLeafFirst(t *testing.T) {
	goal := lawElsewhereFixture(t, true)
	st := NewMemoryCNFStore()
	rec := ladderRunsEnv(t)
	rec.ProofService.CNFStore = st
	closed, route := byRoute(t, rec, goal, Normalized)
	require.True(t, closed, "the By closes")
	requireFirstRun(t, route)
	require.NotEmpty(t, st.Plans(), "a conditioned close: the bare retry records no plan")
	for _, entry := range st.Plans() {
		require.Empty(t, entry.Replaced, "the plan of the first run replaces nothing")
	}

	strict := ladderRunsEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	closed, _ = byRoute(t, strict, goal, Normalized)
	require.True(t, closed)
}

// recordPruned records, in st, the close of goal a pruning stage and the
// refuter make: the plan, which replaces, and the certificate of the
// pruned leaf, where the refuter closes it.
func recordPruned(t *testing.T, st *MemoryCNFStore, goal Prop) (closed bool) {
	t.Helper()
	env := ladderRunsEnv(t)
	env.ProofService.CNFStore = st
	c := &conditioner{env: env, ctx: t.Context(), s4: &byS4State{}}
	root := CreateGoalStack(goal)
	c.conditionLeaf(root, conditionOpts{ground: true, prune: true})
	closed = byWorkingLeaf(root, nil).runStep(_CNFRefute{env: env, ctx: t.Context()})
	c.persistConditionPlans()
	require.NotEmpty(t, onlyPlan(t, st).Replaced, "the stored plan replaces")
	return closed
}

// TestByLadder_ThePrunedRunFollowsAWholeLeafThatDidNotClose: where the
// rung's first run, on the whole leaf, does not close and its grounding
// kept a source a match pinned in full, the rung is run on the pruned
// leaf. The search is taken away here — a budget of zero aborts every
// refutation the store holds no certificate for — and the store holds
// the pruned leaf's certificate alone: the whole leaf fails, the pruned
// leaf closes, the route names the run and the plan recorded replaces.
func TestByLadder_ThePrunedRunFollowsAWholeLeafThatDidNotClose(t *testing.T) {
	goal := groundFixture(t)
	recorded := NewMemoryCNFStore()
	require.True(t, recordPruned(t, recorded, goal), "the pruned leaf closes")
	st := certificatesOnly(recorded)

	noSearch := ladderRunsEnv(t)
	noSearch.CnfRefuterTimeout = 0
	noSearch.ProofService.CNFStore = st
	closed, route := byRoute(t, noSearch, goal)
	require.True(t, closed, "the By closes")
	require.Contains(t, route, byPrunedRoute, "the route names the run")
	require.NotEmpty(t, onlyPlan(t, st).Replaced, "the plan of the pruned run replaces")

	strict := ladderRunsEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	closed, route = byRoute(t, strict, goal)
	require.True(t, closed, "strict replay applies the recorded plan in its one conditioned rung")
	require.NotContains(t, route, byPrunedRoute)

	empty := ladderRunsEnv(t)
	empty.CnfRefuterTimeout = 0
	empty.ProofService.CNFStore = NewMemoryCNFStore()
	failure := func() (r any) {
		defer func() { r = recover() }()
		byRoute(t, empty, goal)
		return nil
	}()
	require.NotNil(t, failure, "with no certificate either leaf closes on, the By fails")
	require.Equal(t, 1, strings.Count(anyToString(failure), byPrunedNote), "and says the pruned leaf was run")
}

// TestByLadder_AStoredPlanIsAppliedAsRecorded: a recording made on the
// pruned leaf stays the leaf's recording. The rung's first run applies
// the stored plan, which replaces, and reads the certificate: no plan
// and no certificate is written, in a live run as in a strict one.
func TestByLadder_AStoredPlanIsAppliedAsRecorded(t *testing.T) {
	goal := groundFixture(t)
	st := NewMemoryCNFStore()
	require.True(t, recordPruned(t, st, goal), "the pruned leaf closes")
	plan, proofs := onlyPlan(t, st), len(st.Proofs())

	live := ladderRunsEnv(t)
	live.ProofService.CNFStore = st
	closed, route := byRoute(t, live, goal)
	require.True(t, closed)
	requireFirstRun(t, route)
	require.Contains(t, route, "cnf cached certificate", "the recorded certificate closes the leaf")
	require.Same(t, plan, onlyPlan(t, st), "the stored plan stands")
	require.Len(t, st.Proofs(), proofs, "and no certificate is added")

	strict := ladderRunsEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	closed, _ = byRoute(t, strict, goal)
	require.True(t, closed, "strict replay closes on the same two rows")
}

// TestByLadder_AStoredPlanTheLeafDoesNotCloseOnIsNotPassedOver: the
// store holds, for the leaf, a plan that replaces a law the close needs
// elsewhere — a recording that no longer closes. The conditioned rung
// applies it, as it applies every stored plan, and fails; it does not
// ground afresh past it. The bare retry closes the leaf, and the stored
// plan stands as it was.
func TestByLadder_AStoredPlanTheLeafDoesNotCloseOnIsNotPassedOver(t *testing.T) {
	goal := lawElsewhereFixture(t, true)
	st := NewMemoryCNFStore()
	require.False(t, recordPruned(t, st, goal), "the pruned leaf does not close")
	plan := onlyPlan(t, st)
	require.Empty(t, st.Proofs())

	live := ladderRunsEnv(t)
	live.ProofService.CNFStore = st
	closed, route := byRoute(t, live, goal)
	require.True(t, closed, "the By closes")
	requireFirstRun(t, route)
	require.Same(t, plan, onlyPlan(t, st), "the stored plan stands: no run of the rung grounded afresh")
	require.Len(t, st.Proofs(), 1, "the bare retry's certificate")
}

// TestGroundStage_TheWideClosersStagePassesOverAPlanThatReplaces: the
// stage of the closer that reads its facts wide passes over a stored
// plan that replaces and grounds afresh, the law staying in the leaf
// beside its instance; any other stage applies the plan as recorded.
func TestGroundStage_TheWideClosersStagePassesOverAPlanThatReplaces(t *testing.T) {
	goal := lawElsewhereFixture(t, true)
	law := forallHypOver(t, goal, "zz_kept_wide_p")
	conditioned := func(st *MemoryCNFStore, opts conditionOpts) Prop {
		env := ladderRunsEnv(t)
		env.ProofService.CNFStore = st
		c := &conditioner{env: env, ctx: t.Context(), s4: &byS4State{}}
		root := CreateGoalStack(goal)
		c.conditionLeaf(root, opts)
		return byWorkingLeaf(root, nil).Goal
	}

	replacing := NewMemoryCNFStore()
	recordPruned(t, replacing, goal)
	require.False(t, conditioned(replacing, conditionOpts{ground: true}).HasHyp(law),
		"as recorded: the stored plan replaces the law")
	wide := conditioned(replacing, conditionOpts{ground: true, wide: true})
	require.True(t, wide.HasHyp(law), "read wide: the law stays in the leaf")
	require.Greater(t, wide.NumHyps(), goal.NumHyps(), "beside its instance")

	require.Panics(t, func() { conditioned(NewMemoryCNFStore(), conditionOpts{ground: true, prune: true, wide: true}) },
		"a closer that reads its facts wide is handed no pruned leaf")
}

// TestGroundStage_KeepingTellsTheLadderThereIsAPrunedLeaf: a stage that
// keeps a source a pruning stage replaces tells the ladder it runs under
// (byLadderState.prunable); a pruning stage, and one that keeps only
// guesses' sources, tell it nothing.
func TestGroundStage_KeepingTellsTheLadderThereIsAPrunedLeaf(t *testing.T) {
	run := func(goal Prop, opts conditionOpts) (*byLadderState, Prop) {
		st := &byLadderState{}
		ctx := context.WithValue(t.Context(), byLadderStateKey{}, st)
		c := &conditioner{env: ladderRunsEnv(t), ctx: ctx, s4: &byS4State{}}
		root := CreateGoalStack(goal)
		c.conditionLeaf(root, opts)
		return st, byWorkingLeaf(root, nil).Goal
	}
	goal := lawElsewhereFixture(t, true)
	law := forallHypOver(t, goal, "zz_kept_wide_p")
	st, leaf := run(goal, conditionOpts{ground: true})
	require.True(t, st.prunable, "the first law is one a pruning stage replaces")
	require.True(t, leaf.HasHyp(law), "and the stage kept it")

	st, leaf = run(goal, conditionOpts{ground: true, prune: true})
	require.False(t, st.prunable)
	require.False(t, leaf.HasHyp(law), "a pruning stage replaces it")

	st, _ = run(guessFixture(t), conditionOpts{ground: true})
	require.False(t, st.prunable, "a guess's source stays under either stage: there is no pruned leaf")
}

// TestByLadder_AByNoRungClosesSaysThePrunedLeafWasRun: the failure
// reported is the conditioned rung's on the whole leaf, which names the
// grounding and no replacement, and it says once that the pruned leaf
// was run as well.
func TestByLadder_AByNoRungClosesSaysThePrunedLeafWasRun(t *testing.T) {
	goal := lawElsewhereFixture(t, false)
	env := ladderRunsEnv(t)
	env.ProofService.CNFStore = NewMemoryCNFStore()
	n := CreateGoalStack(goal)
	failure := func() (r any) {
		defer func() { r = recover() }()
		ApplyByStep(n, env, t.Context(), guardedBySpec(goal))
		return nil
	}()
	require.NotNil(t, failure, "the By fails")
	text := anyToString(failure)
	require.Contains(t, text, "grounded ∀x.(zz_kept_wide_p(x) ⇒ zz_kept_wide_q(x)) at (a)", "the first run's own account")
	require.NotContains(t, text, "[wide form replaced]", "which replaced nothing")
	require.Equal(t, 1, strings.Count(text, byPrunedNote))
	require.Empty(t, env.ProofService.CNFStore.(*MemoryCNFStore).Plans(), "a By that fails records no plan")
}
