package omega

// Hypothesis-bearing ring leaves: a structure ring's leaves read the
// general laws at a RESIDENT fact and carry it ({comm_ring(R)} ⊢ a+b =
// b+a). This pins that the composition below the leaves — the full ring
// prover, the hyp-aware deep/fixpoint decider (under a binder too),
// linarith's replay, the hyp loop — carries such a hypothesis through,
// and that IsStronger is what refuses a close whose fact the goal lacks.
// Every nat ring leaf is weakened to carry an opaque S, the shape of the
// structure ring's leaves without a structure.

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

func probeWeaken(S Term) func(*prop.PropWrapper) *prop.PropWrapper {
	return func(w *prop.PropWrapper) *prop.PropWrapper {
		if w == nil {
			return nil
		}
		return w.PromoteHyp(S).DemoteHyp() // Γ ⊢ c  →  Γ ∪ {S} ⊢ c
	}
}

func withHypBearingNatRing(t *testing.T, S Term) {
	t.Helper()
	saved := *natRing
	wk := probeWeaken(S)
	wrapped := saved
	wrapped.commuteADD = func(a, b Term) *prop.PropWrapper { return wk(saved.commuteADD(a, b)) }
	wrapped.associateADD = func(a, b, c Term) *prop.PropWrapper { return wk(saved.associateADD(a, b, c)) }
	wrapped.commuteMUL = func(a, b Term) *prop.PropWrapper { return wk(saved.commuteMUL(a, b)) }
	wrapped.associateMUL = func(a, b, c Term) *prop.PropWrapper { return wk(saved.associateMUL(a, b, c)) }
	wrapped.distributeMUL = func(a, b, c Term) *prop.PropWrapper { return wk(saved.distributeMUL(a, b, c)) }
	wrapped.rightDistrib = func(a, b, c Term) *prop.PropWrapper { return wk(saved.rightDistrib(a, b, c)) }
	wrapped.oneMul = func(a Term) *prop.PropWrapper { return wk(saved.oneMul(a)) }
	wrapped.addZeroR = func(a Term) *prop.PropWrapper { return wk(saved.addZeroR(a)) }
	wrapped.zeroMul = func(a Term) *prop.PropWrapper { return wk(saved.zeroMul(a)) }
	wrapped.mulZeroR = func(a Term) *prop.PropWrapper { return wk(saved.mulZeroR(a)) }
	wrapped.mulSort = func(a Term) *prop.PropWrapper { return wk(saved.mulSort(a)) }
	wrapped.sucBridge = func(a Term) *prop.PropWrapper { return wk(saved.sucBridge(a)) }
	wrapped.normAdd = func(l, r Term) (*prop.PropWrapper, bool) { w, ok := saved.normAdd(l, r); return wk(w), ok }
	wrapped.normMul = func(l, r Term) (*prop.PropWrapper, bool) { w, ok := saved.normMul(l, r); return wk(w), ok }
	*natRing = wrapped
	resetConstraintMemos()
	t.Cleanup(func() { *natRing = saved; resetConstraintMemos() })
}

func hypKeys(w prop.Prop) []string {
	var out []string
	for _, h := range w.Hyps() {
		out = append(out, ext.PrintTerm(h))
	}
	slices.Sort(out)
	return out
}

func TestRingLeavesCarryAHypothesis(t *testing.T) {
	S := ext.Var("S", core.TypeBool()).Core()
	withHypBearingNatRing(t, S)
	d := natDomain
	a, b := ext.Var("a", d.numeral(_Integer{}).Type()).Core(), ext.Var("b", d.numeral(_Integer{}).Type()).Core()
	ab := d.plus(a, b)
	lhs := d.star(ab, ab)
	rhs := d.plus(d.plus(d.star(a, a), d.star(d.numeral(integerOf(2)), d.star(a, b))), d.star(b, b))

	// 1. The full ring prover composes hyp-bearing leaves: {S} ⊢ l = r.
	w, ok := RingProveFull(lhs, rhs)
	require.True(t, ok)
	require.Equal(t, []string{"S"}, hypKeys(w), "every leaf carried S; the composite carries exactly S")

	// 2. The hyp-aware decider, S resident: {S} ⊢ (l = r) ⇔ ⊤, and the
	// closing theorem passes IsStronger against a goal carrying S.
	concl := core.Eq(lhs, rhs)
	dec := ArithDecideWithHyps([]Term{S})(concl)
	require.NotNil(t, dec)
	require.True(t, prop.Rhs(dec).Equals(prop.T), "decided to ⊤")
	closed := dec.EqSym().EqMP(prop.DerivesTrue) // {S} ⊢ l = r
	goalWithS := core.MakeProp(concl, S)
	require.True(t, prop.IsStronger(closed, goalWithS), "hyps ⊆ goal hyps when S is resident")

	// 3. S NOT resident: the decider still answers (it does not know
	// what S means), the closing theorem carries S, and IsStronger
	// refuses it — the audit, not the leaf, is what keeps a missing
	// structure fact from closing a goal.
	dec2 := ArithDecideWithHyps(nil)(concl)
	require.NotNil(t, dec2)
	closed2 := dec2.EqSym().EqMP(prop.DerivesTrue)
	require.Equal(t, []string{"S"}, hypKeys(closed2))
	require.False(t, prop.IsStronger(closed2, core.MakeProp(concl)), "a goal without S cannot be closed by S-bearing leaves")

	// 4. Under a binder: ∀k. (a+k)·(a+k) = a·a + 2·a·k + k·k — the
	// capture-aware deep rewrite lifts the S-bearing equality through ∀.
	k := ext.Var("k", a.Type())
	ak := d.plus(a, k.Core())
	body := core.Eq(d.star(ak, ak), d.plus(d.plus(d.star(a, a), d.star(d.numeral(integerOf(2)), d.star(a, k.Core()))), d.star(k.Core(), k.Core())))
	forall := ext.ForAll(k)(ext.WrapTerm(body)).Core()
	dec3 := ArithDecideWithHyps([]Term{S})(forall)
	require.NotNil(t, dec3)
	require.True(t, prop.Rhs(dec3).Equals(prop.T))
	require.True(t, prop.IsStronger(dec3.EqSym().EqMP(prop.DerivesTrue), core.MakeProp(forall, S)))

	// 5. With a comparison hypothesis beside S — linarith's replay
	// normalizes through the same leaves: {S, x ≤ y} ⊢ x + 1 ≤ y + 1.
	x, y := ext.Var("x", a.Type()).Core(), ext.Var("y", a.Type()).Core()
	h := ext.Apply(natLe, x, y)
	g := ext.Apply(natLe, d.plus(x, d.numeral(integerOf(1))), d.plus(y, d.numeral(integerOf(1))))
	ctx := NewArithCtx([]Term{S, h})
	dec4 := ctx.Decide(g)
	require.NotNil(t, dec4)
	require.True(t, prop.Rhs(dec4).Equals(prop.T))
	require.True(t, prop.IsStronger(dec4.EqSym().EqMP(prop.DerivesTrue), core.MakeProp(g, S, h)))
	// The hyp loop: S under the others decides nothing; h under S alone
	// decides nothing (it is not redundant).
	require.Nil(t, ctx.DecideExcept(0, S))
	require.Nil(t, ctx.DecideExcept(1, h))
}
