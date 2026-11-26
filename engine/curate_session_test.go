package engine

// What a session reads beside its goal (library/chapter_constitution.md
// §"The session"):
//
//   - a proved sibling section acts as an in-session lemma, the chapter's
//     `Use(lemmaK)`, with no registry entry behind it;
//   - an explicit `lemma {key}` cite names a registry entry, and a key no
//     entry has is refused.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"

	// Populates the proof registry in the engine test binary: the
	// tests of this package read the corpus's entries.
	_ "github.com/euc-ai/xugo/library/proofs"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// curateF builds an uninterpreted predicate F : ind → bool. Statements
// over F don't normalize to ⊤ (nothing is provable about F), which keeps
// them out of the trivial-true short-circuits the sibling matcher skips.
func curateF() (core.ConstTermMeta, *ext.TermWrapper) {
	metaF := core.MakeConstMeta("F", core.MakeFun(TypeInd, core.TypeBool()))
	F := ext.Const(metaF, core.MakeFun(TypeInd, core.TypeBool()))
	return metaF, F
}

// closeSectionTrusted closes a section root with a trusted thm of its own
// statement — a white-box stand-in for "the agent proved this section",
// letting sibling-match tests run registry-free and without depending on
// auto's proving power.
func closeSectionTrusted(t *testing.T, root *proof.GoalStackNode) {
	t.Helper()
	thm := core.TestThm(root.Goal.Conclusion(), root.Goal.Hyps()...)
	normalized, _ := prop.Normalize(thm)
	cache := &proof.ThmCache{}
	cache.SaveThm(thm, normalized)
	require.True(t, proof.ApplyKnown(root, cache), "trusted close should apply")
	require.True(t, root.Proved())
}

// closeReproductionChildrenTrusted closes, white-box, every hyp-free
// open leaf under root — the reproduction child an inline lemma load
// leaves for its author to prove. A stand-in for "the author proved
// the statement"; the tests using it measure what happens next.
func closeReproductionChildrenTrusted(t *testing.T, s *Session, root *proof.GoalStackNode) {
	t.Helper()
	s.mu.Lock()
	defer s.mu.Unlock()
	for _, leaf := range root.UnsolvedLeaves() {
		if leaf.Goal.NumHyps() == 0 {
			closeSectionTrusted(t, leaf)
		}
	}
	s.rebuildGoalIndex()
}

// TestCurateSession_SiblingSectionMatch_RootTwin: a proved sibling
// section closes an α-equal root in another section — registry-free.
// The minimal form of the Use(lemmaK) semantics.
func TestCurateSession_SiblingSectionMatch_RootTwin(t *testing.T) {
	_, F := curateF()
	x := ext.Var("x", TypeInd)
	y := ext.Var("y", TypeInd)
	propA := prop.MakeProp(ext.ForAll(x)(F.Apply(x))) // ∀x. F(x)
	propB := prop.MakeProp(ext.ForAll(y)(F.Apply(y))) // α-twin

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	s.AddGoal(propA)
	closeSectionTrusted(t, s.sections[0].root)

	s.AddGoal(propB)
	require.False(t, s.sections[1].root.Proved())

	matched := s.runAutoMatch()
	require.Len(t, matched, 1, "sibling match should close the α-twin")
	require.NotNil(t, matched[0].MatchedSection)
	assert.Equal(t, 0, *matched[0].MatchedSection)
	assert.Empty(t, matched[0].MatchedKey, "sibling closes carry no entry key")
	assert.True(t, s.sections[1].root.Proved())
}

// TestCurateSession_SiblingMatch_LemmaObligation: the realistic Use()
// shape — section 1 cites section 0 via the `lemma` tactic; the lemma's
// obligation leaf is closed by the sibling pass inside ApplyStep's
// post-tactic auto pipeline, and the main goal then closes by auto
// (unit resolution from the cited ∀-hyp). End-to-end through the
// public ApplyStep API, registry-free.
func TestCurateSession_SiblingMatch_LemmaObligation(t *testing.T) {
	_, F := curateF()
	x := ext.Var("x", TypeInd)
	a := ext.Var("a", TypeInd)
	lemmaProp := prop.MakeProp(ext.ForAll(x)(F.Apply(x))) // ∀x. F(x)
	goalProp := prop.MakeProp(F.Apply(a))                 // F(a), free a

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	s.AddGoal(lemmaProp)
	closeSectionTrusted(t, s.sections[0].root)

	goalID := s.AddGoal(goalProp)

	// Cite the sibling: lemma (inline Prop) creates the obligation leaf,
	// which the curate sibling pass closes against section 0.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "lemma", Lemma: lemmaProp},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "lemma apply should succeed; diagnostics: %v", res.Diagnostics)

	foundSibling := false
	for _, m := range res.AutoMatched {
		if m.MatchedSection != nil && *m.MatchedSection == 0 {
			foundSibling = true
		}
	}
	assert.True(t, foundSibling,
		"the lemma obligation should be auto-closed against sibling section 0; auto_matched: %+v",
		res.AutoMatched)

	// Finish the main goal: F(a) from hyp ∀x.F(x) is one auto.
	if !s.sections[1].root.Proved() {
		res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: firstOpenGoalID(s, 1),
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
		require.True(t, res.Success, "auto should close F(a) under ∀x.F(x)")
	}
	assert.True(t, s.sections[1].root.Proved())
}

// firstOpenGoalID returns any open goal ID in the given section. Helper
// for tests that don't care which leaf they target.
func firstOpenGoalID(s *Session, sectionID int) string {
	for id, entry := range s.goalIndex {
		if entry.sectionID == sectionID {
			return id
		}
	}
	return ""
}

// TestCurateSession_LemmaKeyAdmission pins the key slot's admission:
// only a registry entry is citable (TestCurateSession_RegistryLemmaResolution);
// a key or name that is no entry's is refused with a diagnostic that
// says so.
func TestCurateSession_LemmaKeyAdmission(t *testing.T) {
	_, F := curateF()
	mk := func(arity int) core.Prop {
		vs := make([]core.Term, arity)
		for i := range vs {
			vs[i] = ext.Var(core.TermName("x_"+string(rune('a'+i))), TypeInd)
		}
		body := F.Apply(vs[0])
		for i := 1; i < arity; i++ {
			body = body.Eq(F.Apply(vs[i]))
		}
		return prop.MakeProp(ext.ForAll(vs...)(body))
	}
	normalizedKey := func(p core.Prop) string {
		n, _ := prop.Normalize(p)
		return string(n.AlphaKey())
	}

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(mk(3))

	// (a) A statement's key that no entry has is refused as such.
	unregistered := normalizedKey(mk(4))
	_, err = e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: unregistered}, s.sections[0].root.Goal)
	require.Error(t, err, "a key no entry has is not citable")
	assert.Contains(t, err.Error(), "names no proof-registry entry")

	// (b) A name no entry is registered under is refused the same way.
	_, err = e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: "test_thm"}, s.sections[0].root.Goal)
	require.Error(t, err)
	assert.Contains(t, err.Error(), "names no proof-registry entry")

	// (c) End-to-end: ApplyStep reports the refusal as a failed step
	// carrying the same diagnostic.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "lemma", LemmaKey: unregistered},
	})
	require.NoError(t, err)
	require.False(t, res.Success, "a key no entry has is not citable")
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "names no proof-registry entry")
}
