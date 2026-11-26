package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// TestHypHandle_FactKeepsItsContentBesideAResidentEquivalence: a handle
// names a proposition, and the Unfold's tidy applies no resident
// equation. With the equivalence C ⇔ Q(b) resident beside the fact C,
// the unfold opens the goal and leaves both where they stand — the
// fact goes on naming C, the premise a By citing it supplies, and the
// equivalence is the author's to rewrite by.
//
//	C := HandleTrackBoth(R, T, b)
//	(C ⇔ Q(b)) ⇒ C ⇒ (∀x. HandleTrackBoth(R, T, x) ⇒ T(x)) ⇒ HandleTrackAt(T, b)
func TestHypHandle_FactKeepsItsContentBesideAResidentEquivalence(t *testing.T) {
	e := makeHandleTrackEnv()
	x := Var("x", TypeInd)
	c := e.both.Apply(e.R, e.T, e.b)
	qAtB := e.Q.Apply(e.b)
	sec := e.ctx.Section(prop.MakeProp(c.Eq(qAtB).Imply(
		c.Imply(ext.ForAll(x)(e.both.Apply(e.R, e.T, x).Imply(e.T.Apply(x))).Imply(e.at.Apply(e.T, e.b)))).Core()))
	sec.Do(Derive(func(arg *Argument) {
		arg.Assume() // the equivalence
		fact := arg.Assume()
		implies := arg.Assume()
		arg.Do(Unfold(handleTrackAtDefinition))
		leaf := arg.cur
		require.True(t, leaf.Goal.AnyHyp(c.Core().AlphaEquals), "the tidy leaves C resident")
		require.False(t, leaf.Goal.AnyHyp(qAtB.Core().AlphaEquals), "the tidy reads nothing off the equivalence")
		require.True(t, leaf.Goal.AnyHyp(c.Eq(qAtB).Core().AlphaEquals), "the tidy leaves the equivalence where it stands")
		requireFactNames(t, arg, fact, c)
		arg.Show("T at b, from the fact as stated", By(implies, fact))
	}))
	require.True(t, sec.Proved())
}
