package engine

// A session `by` citing a law whose conclusion is an ∃ over a SET
// equality — listing.Enumerates, `∀s. finite(s) ⇒ ∃l. set_of_list(l) = s
// ∧ list_length(l) = card(s)` — at the leaf that is its instance closes on
// the apply rung, keyless, cited BARE as much as grounded. The report
// this pins against (listing.ListOfSetProperties: "the bare by closes
// through the REFUTER … costs a recorded key") was re-measured here on
// a fresh serve at HEAD and does not reproduce: the normalizer's
// pointwise expansion of the equality lives in the premise's CLAUSE
// install (the second child dump-section shows, certified against the
// entry), not in the rung's conclusion match, which reads the STATED
// form. The control below is what the instrument reads when the
// refuter does run.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// existsOverSetEqualityInstance is an entry's `∀s. A(s) ⇒ C(s)` at a
// fresh s0: the antecedent, the conclusion, and s0.
func existsOverSetEqualityInstance(t *testing.T, e *registry.ProofEntry) (ante, concl core.Term) {
	t.Helper()
	abs := ext.MatchesFORALL(e.Statement().Prop.Conclusion())
	require.False(t, abs.IsZero())
	s0 := core.Var("s0", abs.Var().Type())
	body := abs.Body().Substitute(core.MakeTermSubst(abs.Var(), s0))
	ante, concl, ok := ext.MatchesIMPLY(body)
	require.True(t, ok)
	return ante, concl
}

// recordingSession is a served session whose refutes record into st —
// so "nothing recorded" reads "the rung closed it".
func recordingSession(t *testing.T) (*Engine, *Session, string, *proof.MemoryCNFStore) {
	t.Helper()
	env := servedEnv(t)
	st := proof.NewMemoryCNFStore()
	env.ProofService.CNFStore = st
	e := newEngine(env)
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	return e, s, info.ID, st
}

func TestBy_ExistsOverSetEquality_ClosesOnTheRungBareOrGrounded(t *testing.T) {
	entry, ok := registry.ByName("listing.Enumerates")
	require.True(t, ok, "listing.Enumerates is not registered: the fixture names what the corpus no longer has")
	zero := 0
	for _, tc := range []struct {
		name string
		spec LemmaWithSpec
	}{
		{"bare", LemmaWithSpec{Key: "listing.Enumerates"}},
		{"grounded", LemmaWithSpec{Key: "listing.Enumerates", TermSpecialize: map[string]string{"s": "s0"}}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			ante, concl := existsOverSetEqualityInstance(t, entry)
			e, s, sid, st := recordingSession(t)
			gid := s.AddGoal(prop.MakeProp(concl, ante))
			s.rebuildGoalIndex()
			out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
				GoalID: gid,
				Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}}, WithLemmas: []LemmaWithSpec{tc.spec}},
			})
			require.NoError(t, err)
			require.True(t, out.Success, "by: %+v", out.Diagnostics)
			require.True(t, s.sections[0].root.Proved())
			require.Empty(t, st.Proofs(), "the rung closed the leaf: no certificate recorded")
			require.Empty(t, st.Plans(), "and no conditioning plan")
		})
	}

	// The instrument's control: with the conjuncts swapped the stated
	// conclusion matches nothing syntactically, the refuter closes the
	// leaf, and the store shows it.
	t.Run("control: the refuter records", func(t *testing.T) {
		ante, concl := existsOverSetEqualityInstance(t, entry)
		exAbs := ext.MatchesEXISTS(concl)
		require.False(t, exAbs.IsZero())
		l, r, ok := ext.MatchesAND(exAbs.Body())
		require.True(t, ok)
		swapped := ext.Exists(ext.WrapTerm(exAbs.Var()))(ext.WrapTerm(r).And(ext.WrapTerm(l))).Core()
		e, s, sid, st := recordingSession(t)
		gid := s.AddGoal(prop.MakeProp(swapped, ante))
		s.rebuildGoalIndex()
		out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: gid,
			Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}}, WithLemmas: []LemmaWithSpec{{Key: "listing.Enumerates"}}},
		})
		require.NoError(t, err)
		require.True(t, out.Success, "by: %+v", out.Diagnostics)
		require.NotEmpty(t, st.Proofs(), "the refuter ran and recorded a certificate")
	})
}

// The path the report took: the consumer's leaf, the existence claim
// asserted in text, the bare cite on the claim child.
func TestBy_ExistsOverSetEquality_AssertedClaimClosesOnTheRung(t *testing.T) {
	consumer, ok := registry.ByName("listing.ListOfSetProperties")
	require.True(t, ok, "listing.ListOfSetProperties is not registered: the fixture names what the corpus no longer has")
	ante, concl := existsOverSetEqualityInstance(t, consumer)
	e, s, sid, st := recordingSession(t)
	gid := s.AddGoal(prop.MakeProp(concl, ante))
	s.rebuildGoalIndex()
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid,
		Tactic: TacticReq{Type: "assert", ClaimText: "∃l:list(A). set_of_list(l) = s0 ∧ list_length(l) = card(s0)"}})
	require.NoError(t, err)
	require.True(t, out.Success, "assert: %+v", out.Diagnostics)
	var claimID string
	for id, en := range s.goalIndex {
		if !ext.MatchesEXISTS(en.node.Goal.Conclusion()).IsZero() {
			claimID = id
		}
	}
	require.NotEmpty(t, claimID, "the claim child is the ∃ leaf")
	zero := 0
	out, err = e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: claimID,
		Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}}, WithLemmas: []LemmaWithSpec{{Key: "listing.Enumerates"}}}})
	require.NoError(t, err)
	require.True(t, out.Success, "by: %+v", out.Diagnostics)
	require.Empty(t, st.Proofs(), "the bare cite on the asserted claim closes on the rung")
	require.Empty(t, st.Plans())
}
