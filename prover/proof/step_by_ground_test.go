// step_by_ground_test.go — the grounding stage's store contract (the
// manual's S4), pinned end-to-end on an in-memory CNF store:
//
//  1. RECORD: a live By whose leaf needs grounding runs the e-match
//     search, closes, and persists BOTH artifacts — the certificate
//     under the CONDITIONED key, the plan entry under the BARE leaf
//     key (the groundings; the wide source stays beside its instance,
//     so the plan replaces nothing).
//  2. STRICT REPLAY: with only those two artifacts installed and
//     RequireCNFCacheHit armed, the same By closes — the plan applies
//     mechanically (zero search) and the certificate hits.
//  3. THE PLAN IS LOAD-BEARING: strict replay with the certificate but
//     WITHOUT the plan panics on the certificate MISS — the
//     deterministic stages alone cannot reproduce the conditioned key.
//  4. Rows recorded before S4 replay untouched: a certificate recorded under
//     the BARE key (a row recorded before the stage existed) still
//     closes at strict replay via the ladder's rung-1 probe, with no
//     plan entry and no re-record.
package proof

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// zkConst is a test-local opaque unary const (defined as the identity,
// but never def-expanded by the pipeline): the e-match L2 subterm
// trigger needs a CONST-headed applied subterm mentioning the binder,
// which no free-var-headed fixture can provide.
var zkConst = core.NewConstDef(ext.Var("zzgx", TypeInd).To(ext.Var("zzgx", TypeInd)), "zz_ground_k")

// groundFixture builds the minimal leaf the grounding stage serves:
//
//	∀x. zk(x) = g(x),  g(a) = h(a),  h(a) = k(a)  ⊢  zk(a) = k(a)
//
// Bare, the refuter faces a wide ∀-equation; e-matching finds the L2
// trigger zk(ǝ) in the conclusion's zk(a) and grounds x := a with every
// binder pinned by the match. The By's conditioned rung keeps the wide
// source beside the instance; a stage that prunes replaces it. The
// conditioned refutation is three ground paramodulations. The links
// are of one size, so Basic() closes nothing here: no rewrite shrinks
// its target, and none makes the conclusion a hypothesis.
func groundFixture(t *testing.T) Prop {
	t.Helper()
	indFun := core.MakeFun(TypeInd, TypeInd)
	g, h, k := ext.Var("g", indFun), ext.Var("h", indFun), ext.Var("k", indFun)
	a := ext.Var("a", TypeInd)
	x := ext.Var("x", TypeInd)
	zk := ext.WrapTerm(zkConst)

	wide := ext.ForAll(x)(zk.Apply(x).Eq(g.Apply(x)))
	ground := g.Apply(a).Eq(h.Apply(a))
	step := h.Apply(a).Eq(k.Apply(a))
	concl := zk.Apply(a).Eq(k.Apply(a))
	return prop.MakeProp(concl.Core(), wide.Core(), ground.Core(), step.Core())
}

// groundChainFixture is groundFixture with its law at the one point the
// close reads it and no other:
//
//	zk(a) = g(a),  g(a) = h(a),  h(a) = k(a)  ⊢  zk(a) = k(a)
//
// Nothing is grounded, the refutation is the same three ground
// paramodulations, and Basic() closes nothing of it.
func groundChainFixture(t *testing.T) Prop {
	t.Helper()
	indFun := core.MakeFun(TypeInd, TypeInd)
	g, h, k := ext.Var("g", indFun), ext.Var("h", indFun), ext.Var("k", indFun)
	a := ext.Var("a", TypeInd)
	zk := ext.WrapTerm(zkConst)
	return prop.MakeProp(zk.Apply(a).Eq(k.Apply(a)).Core(),
		zk.Apply(a).Eq(g.Apply(a)).Core(), g.Apply(a).Eq(h.Apply(a)).Core(), h.Apply(a).Eq(k.Apply(a)).Core())
}

// copyOfStore is a store holding st's certificates and plans.
func copyOfStore(st *MemoryCNFStore) *MemoryCNFStore {
	out := certificatesOnly(st)
	for k, p := range st.Plans() {
		out.WritePlan(k, p)
	}
	return out
}

// certificatesOnly is a store holding st's certificate table and an
// EMPTY plan table — the recording with its plans lost, which is the
// one shape test 3 must show unreplayable. (No env can hold half a
// store any more; the shape exists here only as a second store.)
func certificatesOnly(st *MemoryCNFStore) *MemoryCNFStore {
	out := NewMemoryCNFStore()
	for k, p := range st.Proofs() {
		out.WriteProof(k, p)
	}
	return out
}

func groundTestEnv(t *testing.T) *ProverEnv {
	t.Helper()
	env := makeStepTestEnv()
	// The plan pool serializes the zk const; decode needs its meta.
	_, _ = env.ProofService.LoadOrStoreConstMeta(zkConst.Meta())
	return env
}

// groundBySpec names every hypothesis of goal as a resident premise:
// the wide law as "wide", the ground equations as "ground".
func groundBySpec(goal Prop) BySpec {
	var premises []ByPremiseSpec
	for h := range goal.HypIter() {
		describe := "ground"
		if !ext.MatchesFORALL(h).IsZero() {
			describe = "wide"
		}
		premises = append(premises, ByPremiseSpec{Install: prop.MakeProp(h), Resident: true, Describe: describe})
	}
	return BySpec{Premises: premises}
}

func TestByGrounding_RecordThenStrictReplay(t *testing.T) {
	goal := groundFixture(t)
	st := NewMemoryCNFStore()

	// 1. RECORD — live run, empty store: rung 1's cache-only probe
	// misses, rung 2 conditions (S4 searches), the refute closes live.
	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), groundBySpec(goal)), "live By must close")
	require.True(t, n.Proved())

	plans := st.Plans()
	require.Len(t, plans, 1, "exactly one plan entry (one working leaf)")
	require.NotEmpty(t, st.Proofs(), "the conditioned refutation must persist a certificate")
	var bareKey core.PropKey
	var entry *ByConditionPlanProto
	for k, p := range plans {
		bareKey, entry = k, p
	}
	require.NotEmpty(t, entry.Groundings, "the plan carries the e-match groundings")
	require.Empty(t, entry.Replaced, "the rung's first run keeps the wide source beside its instance")
	require.NotEqual(t, string(bareKey), entry.ConditionedGoalKey,
		"conditioning must move the leaf off its bare key")
	// The certificate is keyed by the CNF key of the CONDITIONED clause
	// set — under the bare-leaf spelling nothing was stored (that is
	// what test 3 leans on).

	// 2. STRICT REPLAY — certificates + plans installed, no live search
	// allowed anywhere.
	strict := groundTestEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), groundBySpec(goal)),
		"strict replay must close from the recorded plan + certificate")
	require.True(t, n2.Proved())

	// 3. THE PLAN IS LOAD-BEARING — same certificates, plan table
	// withheld: the deterministic stages cannot reproduce the
	// conditioned key, and strict mode reports the certificate MISS.
	noPlan := groundTestEnv(t)
	noPlan.ProofService.CNFStore = certificatesOnly(st)
	noPlan.RequireCNFCacheHit = true
	n3 := CreateGoalStack(goal)
	func() {
		defer func() {
			r := recover()
			require.NotNil(t, r, "strict replay without the plan must fail loudly")
			assert.Contains(t, strings.ToLower(anyToString(r)), "cnf cache miss",
				"the failure is the certificate MISS, surfaced by the strict gate")
		}()
		ApplyByStep(n3, noPlan, t.Context(), groundBySpec(goal))
	}()
}

// TestByGrounding_BareRecordedRowReplaysUntouched is the replay guarantee
// in miniature: a row whose certificate was recorded on the BARE spelling
// (Raw disables the ladder, so its live refute keys the bare clause set)
// keeps closing at strict replay through rung 1's probe — no plan entry, no
// conditioning, no re-record.
func TestByGrounding_BareRecordedRowReplaysUntouched(t *testing.T) {
	goal := groundFixture(t)
	st := NewMemoryCNFStore()

	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	rawSpec := groundBySpec(goal)
	rawSpec.Shapes = []ByShape{Raw}
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), rawSpec), "the bare (Raw) spelling closes live")
	require.Empty(t, st.Plans(), "a bare close records no plan entry")
	require.NotEmpty(t, st.Proofs(), "the bare refutation persisted its certificate")

	strict := groundTestEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), groundBySpec(goal)),
		"the un-shaped By must replay the bare-keyed certificate via the rung-1 probe")
	require.True(t, n2.Proved())
}

func anyToString(v any) string {
	if s, ok := v.(string); ok {
		return s
	}
	if e, ok := v.(error); ok {
		return e.Error()
	}
	return ""
}

// guardedFixture is the guarded-lemma shape every `iterate/monoidal`
// law has — the content stated behind an antecedent:
//
//	∀x. P(x) ⇒ ∀y. zk(y) = g(x, y),  P(a)  ⊢  zk(b) = g(a, b)
//
// Read at the surface ∀-prefix alone the premise has ONE binder, x;
// grounding it leaves `P(a) ⇒ ∀y. …` wide and the refuter searching.
// Read through the guard it has [x y], the equation is an L1 trigger
// over the conclusion, both are pinned by the match, and the REPLACE
// instance is the guarded ground fact `P(a) ⇒ zk(b) = g(a, b)`, which
// closes by one modus ponens.
func guardedFixture(t *testing.T) Prop { return guardedFixtureGuard(t, false) }

// guardedFixtureGuard is guardedFixture with the resident guard
// optionally spelled `¬¬P(a)`. Spelled `P(a)` the leaf is an instance
// of the law with its antecedent in the context and closes by the
// apply rung with no key; spelled `¬¬P(a)` the apply rung declines —
// it discharges antecedents by α-match, and the double negation is
// the refuter's to absorb — so that is the spelling on which the
// grounding stage's store contract is pinned, with the law's L1
// whole-atom trigger untouched.
func guardedFixtureGuard(t *testing.T, doubleNegatedGuard bool) Prop {
	t.Helper()
	ind2 := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	g := ext.Var("g", ind2)
	P := ext.Var("P", core.MakeFun(TypeInd, core.TypeBool()))
	a := ext.Var("a", TypeInd)
	b := ext.Var("b", TypeInd)
	x := ext.Var("x", TypeInd)
	y := ext.Var("y", TypeInd)
	zk := ext.WrapTerm(zkConst)

	guarded := ext.ForAll(x)(P.Apply(x).Imply(ext.ForAll(y)(zk.Apply(y).Eq(g.Apply(x, y)))))
	guard := P.Apply(a)
	if doubleNegatedGuard {
		guard = ext.Not(ext.Not(guard))
	}
	concl := zk.Apply(b).Eq(g.Apply(a, b))
	return prop.MakeProp(concl.Core(), guarded.Core(), guard.Core())
}

func guardedBySpec(goal Prop) BySpec {
	var prem []ByPremiseSpec
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		desc := "guard"
		if !ext.MatchesFORALL(h).IsZero() {
			desc = "guarded law"
		}
		prem = append(prem, ByPremiseSpec{Install: prop.MakeProp(h), Resident: true, Describe: desc})
	}
	return BySpec{Premises: prem}
}

// TestByGrounding_GuardedLemma is the store contract on the guarded
// shape: the live run grounds the law at BOTH stated binders through
// its guard; strict replay closes from the recorded plan and
// certificate alone. The guard is spelled ¬¬P(a) so the apply rung
// (which closes the plain spelling keylessly — step_by_apply_test.go)
// declines and the stage is what closes it. The plan's witnesses come
// from the law's conclusion alone, and its instance's guard `P(a)` is
// not held as written — `¬¬P(a)` is the refuter's to absorb — so the
// stage KEEPS the wide source beside the instance (guessedInstance):
// the plan records no replacement.
func TestByGrounding_GuardedLemma(t *testing.T) {
	goal := guardedFixtureGuard(t, true)
	st := NewMemoryCNFStore()

	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), guardedBySpec(goal)), "live By must close through the guard")
	require.True(t, n.Proved())

	plans := st.Plans()
	require.Len(t, plans, 1)
	var entry *ByConditionPlanProto
	for _, p := range plans {
		entry = p
	}
	require.Len(t, entry.Groundings, 1, "one grounding of the guarded law")
	require.Len(t, entry.Groundings[0].Witnesses, 2,
		"both binders — the one before the guard and the one behind it — are pinned")
	require.Empty(t, entry.Replaced,
		"matched through the conclusion with the guard not held as written: the wide source is kept")

	strict := groundTestEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), guardedBySpec(goal)),
		"strict replay must close from the recorded plan + certificate")
	require.True(t, n2.Proved())
}

// groundByStore is the fixture the sibling contract tests share: a
// MemoryCNFStore plus wire, which installs it on env — or, with
// withPlans false, installs certificatesOnly's copy, the plan table
// withheld.
type groundByStore struct{ *MemoryCNFStore }

func newGroundByStore() *groundByStore { return &groundByStore{NewMemoryCNFStore()} }

func (st *groundByStore) wire(env *ProverEnv, withPlans bool) {
	if withPlans {
		env.ProofService.CNFStore = st.MemoryCNFStore
		return
	}
	env.ProofService.CNFStore = certificatesOnly(st.MemoryCNFStore)
}

// guardedFixtureHeld is the guarded law with its guard `P(a)` resident
// as written and the goal one step past the law's conclusion:
//
//	∀x. P(x) ⇒ ∀y. zk(y) = g(x, y),  P(a),  ¬¬(zk(b) = g(a, b)) ⇒ r  ⊢  r
//
// The apply rung declines — the step's antecedent is a double
// negation no conclusion matches — and the grounding stage matches the
// law's conclusion against the equation inside it: a plan at (a, b)
// through the conclusion whose guard IS held, so a stage that prunes
// replaces the wide source.
func guardedFixtureHeld(t *testing.T) Prop {
	t.Helper()
	ind2 := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	g := ext.Var("g", ind2)
	P := ext.Var("P", core.MakeFun(TypeInd, core.TypeBool()))
	a := ext.Var("a", TypeInd)
	b := ext.Var("b", TypeInd)
	x := ext.Var("x", TypeInd)
	y := ext.Var("y", TypeInd)
	r := ext.Var("r", core.TypeBool())
	zk := ext.WrapTerm(zkConst)

	guarded := ext.ForAll(x)(P.Apply(x).Imply(ext.ForAll(y)(zk.Apply(y).Eq(g.Apply(x, y)))))
	step := ext.Not(ext.Not(zk.Apply(b).Eq(g.Apply(a, b)))).Imply(r)
	return prop.MakeProp(r.Core(), guarded.Core(), P.Apply(a).Core(), step.Core())
}

// TestGroundStage_APruningStageReplacesWhereTheGuardIsHeld pins what a
// pruning stage replaces: a plan matched through the conclusion whose
// instance's guard the leaf holds is no guess, and the wide source goes;
// the plan it persists says so. The same leaf under the By closes in the
// rung's first run, which keeps the law, and that plan replaces nothing.
func TestGroundStage_APruningStageReplacesWhereTheGuardIsHeld(t *testing.T) {
	goal := guardedFixtureHeld(t)
	law := goal.Hyp(hypIndexOfForall(t, goal, "zz_ground_k"))

	pruned := groundTestEnv(t)
	prunedStore := NewMemoryCNFStore()
	pruned.ProofService.CNFStore = prunedStore
	c := &conditioner{env: pruned, ctx: t.Context(), s4: &byS4State{}}
	root := CreateGoalStack(goal)
	c.conditionLeaf(root, conditionOpts{ground: true, prune: true})
	require.False(t, byWorkingLeaf(root, nil).Goal.HasHyp(law), "the guard is held: the instance stands in for the law")
	c.persistConditionPlans()
	require.Len(t, prunedStore.Plans(), 1)
	for _, entry := range prunedStore.Plans() {
		require.Len(t, entry.Groundings, 1)
		require.Len(t, entry.Groundings[0].Witnesses, 2)
		require.Len(t, entry.Replaced, 1, "the plan records the law as replaced")
	}

	st := NewMemoryCNFStore()
	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), guardedBySpec(goal)), "live By must close")
	require.True(t, n.Proved())
	require.Len(t, st.Plans(), 1)
	for _, entry := range st.Plans() {
		require.Len(t, entry.Groundings, 1)
		require.Empty(t, entry.Replaced, "the By's first run keeps the law beside its instance")
	}

	strict := groundTestEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), guardedBySpec(goal)))
	require.True(t, n2.Proved())
}

// guessFixture is the shape the known leaf `(∀d. d ∈ s ⇒ disjoint(x, d))
// ⊢ disjoint(x, ⋃s)` has, over the test constant:
//
//	∀d. zk(d) = a ⇒ zk(zk(d)) = b,
//	(∀d. ¬(zk(d) = a) ∨ zk(zk(d)) = b) ⇒ zk(zk(c)) = b   ⊢  zk(zk(c)) = b
//
// The law's conclusion matches the goal at d := c, an instance whose
// antecedent `zk(c) = a` nothing holds — a guess. The close needs the
// law WIDE: the refuter's clause form of the second hypothesis asks
// for it at a Skolem point. The apply rung declines (the second
// hypothesis's antecedent is the law in another spelling, not its
// α-copy).
func guessFixture(t *testing.T) Prop {
	t.Helper()
	a, b, c := ext.Var("a", TypeInd), ext.Var("b", TypeInd), ext.Var("c", TypeInd)
	d := ext.Var("d", TypeInd)
	zk := ext.WrapTerm(zkConst)

	law := ext.ForAll(d)(zk.Apply(d).Eq(a).Imply(zk.Apply(zk.Apply(d)).Eq(b)))
	clauseForm := ext.ForAll(d)(ext.Not(zk.Apply(d).Eq(a)).Or(zk.Apply(zk.Apply(d)).Eq(b)))
	step := clauseForm.Imply(zk.Apply(zk.Apply(c)).Eq(b))
	return prop.MakeProp(zk.Apply(zk.Apply(c)).Eq(b).Core(), law.Core(), step.Core())
}

// TestByGrounding_GuessedInstanceKeepsTheWideSource: a plan matched
// through the conclusion alone, with an antecedent the leaf does not
// hold, keeps its source under a stage that prunes too. The conditioned
// rung closes the leaf with the law wide — the plan records the grounding
// and no replacement — and strict replay closes from the plan and the
// certificate.
func TestByGrounding_GuessedInstanceKeepsTheWideSource(t *testing.T) {
	goal := guessFixture(t)
	st := NewMemoryCNFStore()

	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), guardedBySpec(goal)), "live By must close")
	require.True(t, n.Proved())

	plans := st.Plans()
	require.Len(t, plans, 1, "the conditioned rung closed the leaf and recorded its plan")
	var entry *ByConditionPlanProto
	for _, p := range plans {
		entry = p
	}
	require.Len(t, entry.Groundings, 1, "the law grounded at c")
	require.Empty(t, entry.Replaced, "the wide law stays beside its instance")

	law := goal.Hyp(hypIndexOfForall(t, goal, "zz_ground_k"))
	c := &conditioner{env: groundTestEnv(t), ctx: t.Context(), s4: &byS4State{}}
	root := CreateGoalStack(goal)
	c.conditionLeaf(root, conditionOpts{ground: true, prune: true})
	require.True(t, byWorkingLeaf(root, nil).Goal.HasHyp(law), "a guess: a pruning stage keeps the law as well")

	strict := groundTestEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n2, strict, t.Context(), guardedBySpec(goal)))
	require.True(t, n2.Proved())
}

// TestByGrounding_PlanIgnoresFreeNames: a plan recorded on one spelling
// of a leaf applies, under strict replay, to the same leaf with its
// free variables renamed. The plan's key and its stored terms are under
// canonical names (prop.CanonicalFreeRenaming), so a member's binder
// names are no part of its recording — a renamed statement replays.
func TestByGrounding_PlanIgnoresFreeNames(t *testing.T) {
	goal := groundFixture(t)
	renamed := renameFrees(goal, map[string]string{"g": "p", "h": "q", "k": "r", "a": "u"})
	require.NotEqual(t, goal.AlphaKey(), renamed.AlphaKey(), "the raw keys differ: the renaming is real")
	require.Equal(t, planKey(goal), planKey(renamed), "one plan key for both spellings")

	st := NewMemoryCNFStore()
	rec := groundTestEnv(t)
	rec.ProofService.CNFStore = st
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, rec, t.Context(), groundBySpec(goal)), "live By must close")
	require.Len(t, st.Plans(), 1, "one plan entry, for the one working leaf")

	strict := groundTestEnv(t)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(renamed)
	require.True(t, ApplyByStep(n2, strict, t.Context(), groundBySpec(renamed)),
		"strict replay must close the renamed leaf from the plan and certificate recorded on the original")
	require.True(t, n2.Proved())
}

// renameFrees is goal with the free variables names maps renamed.
func renameFrees(goal Prop, names map[string]string) Prop {
	var subst []core.TermSubst
	seen := map[core.TermKey]bool{}
	collect := func(t core.Term) {
		for _, v := range t.Frees(func(core.VarTerm) bool { return true }) {
			if to, ok := names[string(v.Name())]; ok && !seen[v.AlphaKey()] {
				seen[v.AlphaKey()] = true
				subst = append(subst, core.MakeTermSubst(v, ext.Var(core.TermName(to), v.Type()).Core()))
			}
		}
	}
	collect(goal.Conclusion())
	for h := range goal.HypIter() {
		collect(h)
	}
	hyps := make([]core.Term, 0, goal.NumHyps())
	for h := range goal.HypIter() {
		hyps = append(hyps, h.Substitute(subst...))
	}
	return core.MakeProp(goal.Conclusion().Substitute(subst...), hyps...)
}
