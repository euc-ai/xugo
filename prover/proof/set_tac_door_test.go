// set_tac_door_test.go — the set door (SetTac(), the session's
// `set_tac`): the modes in SetTacOrder tried in turn, the step of the
// mode that closed recorded, a strict replay that closes on a record
// whichever mode made it, and a loud MISS when nothing recorded closes.

package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// TestSetTacDoor_RecordsTheModeThatClosed: live, on a goal both modes
// close, the door records the membership step — the first mode in
// SetTacOrder — and never itself.
func TestSetTacDoor_RecordsTheModeThatClosed(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeMiniSetTheory()
	env := makeStepTestEnv()
	n := CreateGoalStack(m.unionsInsertGoal())
	consts := DefaultSetTacConsts()
	require.True(t, ApplySetTac(n, env, t.Context(), consts, nil))
	require.True(t, n.Proved())
	require.Equal(t, fmt.Sprintf("SetTac(%d consts, SET_TAC_MEMBERSHIP)", len(consts)), n.StepDescription())
}

// TestSetTacDoor_StrictReplayOnALegacyRecord: a goal recorded in the
// legacy mode alone — a chapter's `SetTacLegacy()` — replays through the
// door under strict replay, where no refute may search.
func TestSetTacDoor_StrictReplayOnALegacyRecord(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeMiniSetTheory()
	goal := m.unionsInsertGoal()
	st := NewMemoryCNFStore()
	register := func(env *ProverEnv) {
		for _, c := range []core.ConstTerm{m.in, m.union, m.insert, m.unions} {
			_, _ = env.ProofService.LoadOrStoreConstMeta(c.Meta())
		}
	}

	rec := makeStepTestEnv()
	register(rec)
	rec.ProofService.CNFStore = st
	n := CreateGoalStack(goal)
	require.True(t, ApplySetTacMode(n, rec, t.Context(), DefaultSetTacConsts(), SetTacMode_SET_TAC_LEGACY, nil),
		"the legacy record")
	require.NotEmpty(t, st.Proofs(), "the legacy refutes persist their certificates")

	strict := makeStepTestEnv()
	register(strict)
	strict.ProofService.CNFStore = st
	strict.RequireCNFCacheHit = true
	n2 := CreateGoalStack(goal)
	require.True(t, ApplySetTac(n2, strict, t.Context(), DefaultSetTacConsts(), nil),
		"strict replay through the door closes on the record")
	require.True(t, n2.Proved())
}

// TestSetTacDoor_StrictMissIsLoud: under strict replay with nothing
// recorded, on a residual both modes hand to the refuter (the chain of
// three that does not descend, set_tac_rung_test.go), the first mode's
// MISS reads as that mode not closing and the last mode's MISS is the
// panic the door raises.
func TestSetTacDoor_StrictMissIsLoud(t *testing.T) {
	defer goleak.VerifyNone(t)
	m := makeSetRungTheory()
	inV := func(e *ext.TermWrapper) *ext.TermWrapper { return m.in.Apply(e, m.v) }
	goal := ext.ForAll(m.z)(m.P.Apply(m.z).Imply(m.member(m.z, m.P.Apply(m.x).And(inV(m.f.Apply(m.x))))))
	ffz := m.f.Apply(m.f.Apply(m.z))
	first := ext.ForAll(m.w)(m.S.Apply(m.f.Apply(m.w)).Imply(inV(m.w)))
	second := ext.ForAll(m.z)(m.Q.Apply(ffz).Imply(m.S.Apply(ffz)))
	third := ext.ForAll(m.z)(m.P.Apply(m.z).Imply(m.Q.Apply(ffz)))
	n := CreateGoalStack(prop.MakeProp(goal.Core(), first.Core(), second.Core(), third.Core()))

	var raised string
	func() {
		defer func() { raised = fmt.Sprint(recover()) }()
		ApplySetTac(n, strictEnv(), t.Context(), DefaultSetTacConsts(), nil)
	}()
	require.Contains(t, raised, "CNF cache MISS", "the door's last mode panics with the refuter's MISS")
	require.False(t, n.Proved())
}
