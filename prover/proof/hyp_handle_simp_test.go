package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// The kernel keeps a goal's hypotheses sorted (core.MakeProp orders them
// by Term.Compare and merges α-equal ones), so a hypothesis rewritten in
// its place by `handle.Simp` lands wherever its NEW content sorts, not at
// the index its old content held. The handle must follow the content.
//
// The rule rewrites the atom Q(k(a)) into the conjunction
// Q(a) ∧ ∃y. Q(y); a term headed by an application sorts after every
// term headed by a constant, so the conjunction sorts after the other
// hypothesis Q(k(k(a))) that the atom sorted before.
func simpHandleEnv(t *testing.T) (*simpStatedEnv, core.Term) {
	t.Helper()
	e := makeSimpStatedEnv()
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	rule := ext.ForAll(x)(e.Q.Apply(e.k.Apply(x)).Eq(e.Q.Apply(x).And(ext.Exists(y)(e.Q.Apply(y)))))
	serveThm(e.ctx, "simp_handle_rule", core.TestThm(rule.Core()))
	rewritten := e.Q.Apply(e.a).And(ext.Exists(y)(e.Q.Apply(y))).Core()
	return e, rewritten
}

// TestHypHandle_SimpFollowsContentWhenSlotMoves: the rewritten
// hypothesis sorts past its neighbour; the handle names it, not the
// neighbour now standing at the old index.
//
//	Q(k(a)) ⇒ Q(k(k(a))) ⇒ Q(c)
func TestHypHandle_SimpFollowsContentWhenSlotMoves(t *testing.T) {
	e, rewritten := simpHandleEnv(t)
	atom := e.Q.Apply(e.k.Apply(e.a))
	neighbour := e.Q.Apply(e.k.Apply(e.k.Apply(e.a)))
	sec := e.ctx.Section(prop.MakeProp(atom.Imply(neighbour.Imply(e.Q.Apply(e.c))).Core()))
	h := NewHypHandle("h")
	sec.Do(Chain(h.From(StripImp()), StripImp()))
	leaf := sec.UnsolvedLeaves()[0]
	require.Equal(t, 0, leaf.resolveHypIndex(t, h), "the atom sorts before its neighbour")

	sec.Do(h.Simp(Fwd(depName("simp_handle_rule"))))
	leaf = sec.UnsolvedLeaves()[0]
	require.Equal(t, 2, leaf.Goal.NumHyps())
	require.True(t, rewritten.AlphaEquals(h.boundTerm(leaf)), "the handle names the rewritten hypothesis, got %s", ext.PrintTerm(h.boundTerm(leaf)))
	require.Equal(t, 1, leaf.resolveHypIndex(t, h), "the rewritten hypothesis now sorts after its neighbour")
}

// TestHypHandle_SimpFollowsContentWhenMergedWithResident: the rewritten
// hypothesis is α-equal to a resident one, so the kernel keeps a single
// copy; the handle names that copy and the goal has one hypothesis fewer.
//
//	Q(k(a)) ⇒ (Q(a) ∧ ∃y. Q(y)) ⇒ Q(c)
func TestHypHandle_SimpFollowsContentWhenMergedWithResident(t *testing.T) {
	e, rewritten := simpHandleEnv(t)
	atom := e.Q.Apply(e.k.Apply(e.a))
	sec := e.ctx.Section(prop.MakeProp(atom.Imply(ext.WrapTerm(rewritten).Imply(e.Q.Apply(e.c))).Core()))
	h := NewHypHandle("h")
	sec.Do(Chain(h.From(StripImp()), StripImp(), h.Simp(Fwd(depName("simp_handle_rule")))))
	leaf := sec.UnsolvedLeaves()[0]
	require.Equal(t, 1, leaf.Goal.NumHyps(), "the two copies merge")
	require.True(t, rewritten.AlphaEquals(h.boundTerm(leaf)), "the handle names the merged hypothesis, got %s", ext.PrintTerm(h.boundTerm(leaf)))
	require.Equal(t, 0, leaf.resolveHypIndex(t, h))
}

// resolveHypIndex is the handle's index on this leaf, failing the test
// on a resolution error.
func (n *GoalStackNode) resolveHypIndex(t *testing.T, h *HypHandle) int {
	t.Helper()
	idx, err := h.resolve(n)
	require.NoError(t, err)
	return idx
}
