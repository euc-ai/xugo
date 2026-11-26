// given_each_test.go — GivenEach (derive.go, branch.go): an induction
// step over a constructor with several recursive arguments hands its
// branch every hypothesis it grants, in the constructor's order.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// btreeTestEnv serves a binary-tree principle under the name the
// induction tactic reads — ∀P t. P(Leaf) ∧ (∀l a r. P(l) ⇒ P(r) ⇒
// P(Node(l, a, r))) ⇒ P(t) — and a predicate Q over trees of num to
// induct for.
type btreeTestEnv struct {
	ctx      *Script
	treeNum  core.HolType
	leafTerm Term
	nodeTerm Term
	Q        *ext.TermWrapper
}

func makeBtreeTestEnv() *btreeTestEnv {
	env := makeStepTestEnv()
	elem := core.TypeA()
	treeA := core.MakeCompositeType(core.MakeMetaType("btree", 1), elem)
	leafMeta := core.MakeConstMeta("Leaf", treeA)
	nodeMeta := core.MakeConstMeta("Node", MakeFun(treeA, elem, treeA, treeA))
	leaf := ext.WrapTerm(core.MakeConstTerm(leafMeta, treeA))
	node := ext.WrapTerm(core.MakeConstTerm(nodeMeta, MakeFun(treeA, elem, treeA, treeA)))
	P := ext.Var("P", MakeFun(treeA, TypeBool))
	t := ext.Var("t", treeA)
	l, a, r := ext.Var("l", treeA), ext.Var("a", elem), ext.Var("r", treeA)
	stepCase := ForAll(l)(ForAll(a)(ForAll(r)(
		P.Apply(l).Imply(P.Apply(r).Imply(P.Apply(node.Apply(l, a, r)))))))
	principle := ForAll(P)(ForAll(t)(P.Apply(leaf).And(stepCase).Imply(P.Apply(t))))
	env.LibraryThms = map[string]Thm{
		"btree_induction": core.TestThm(principle),
	}
	atNum := core.MakeTypeSubst(core.TypeA(), numType)
	treeNum := core.MakeCompositeType(core.MakeMetaType("btree", 1), numType)
	ctx := NewScript(env)
	return &btreeTestEnv{
		ctx:      ctx,
		treeNum:  treeNum,
		leafTerm: leaf.TypeSubstitute(atNum),
		nodeTerm: node.TypeSubstitute(atNum),
		Q:        ctx.Var("Q", MakeFun(treeNum, TypeBool)),
	}
}

// treeGoal is the principle's own shape at Q, its step law with the two
// hypotheses: Q(Leaf), ∀l a r. Q(l) ⇒ Q(r) ⇒ Q(Node(l, a, r)) ⊢ ∀t. Q(t).
func (e *btreeTestEnv) treeGoal() (goal Prop, stepLaw Term) {
	t := Var("t", e.treeNum)
	l, a, r := Var("l", e.treeNum), Var("a", numType), Var("r", e.treeNum)
	stepLaw = ForAll(l)(ForAll(a)(ForAll(r)(
		e.Q.Apply(l).Imply(e.Q.Apply(r).Imply(e.Q.Apply(ext.Apply(e.nodeTerm, l, a, r))))))).Core()
	goal = MakeProp(ForAll(t)(e.Q.Apply(t)), e.Q.Apply(e.leafTerm), stepLaw)
	return goal, stepLaw
}

// TestGivenEach_TwoHypothesesInConstructorOrder: the Node step hands the
// closure its two induction hypotheses, the left subtree's first — the
// left one is the induction variable's own — and each is the fact the
// goal carries, usable as a premise.
func TestGivenEach_TwoHypothesesInConstructorOrder(t *testing.T) {
	e := makeBtreeTestEnv()
	goal, stepLaw := e.treeGoal()
	sec := e.ctx.Section(goal)
	var seen []string
	sec.Do(Derive(func(a *Argument) {
		tree := a.Binder("t")
		a.Induct(tree)
		a.Base("Q holds at Leaf by hypothesis", Assumption())
		a.Step("at Node(l, x, r): the step law at the two subtrees' hypotheses", func(b *Argument, left, right Fact) {
			seen = []string{left.describe(), right.describe()}
			b.Show("the step law applied", By(left, right, b.Hyp(stepLaw)))
		})
	}))
	require.True(t, sec.Proved())
	require.Len(t, seen, 2)
	require.Contains(t, seen[0], "Q(t)", "the left subtree IS the induction variable, so its hypothesis is Q(t)")
	require.NotEqual(t, seen[0], seen[1], "the right subtree's hypothesis is at the minted right argument")
}

// TestGivenEach_SliceFormAndArityRefusals: the slice form takes them
// all; a two-Fact closure on a one-hypothesis step, a one-Fact closure
// on a two-hypothesis step, and a wrong arity are each refused by name.
func TestGivenEach_SliceFormAndArityRefusals(t *testing.T) {
	e := makeBtreeTestEnv()
	goal, stepLaw := e.treeGoal()

	t.Run("slice form", func(t *testing.T) {
		sec := e.ctx.Section(goal)
		var n int
		sec.Do(Derive(func(a *Argument) {
			a.Induct(a.Binder("t"))
			a.Base("by hypothesis", Assumption())
			a.Step("both subtrees", func(b *Argument, ihs []Fact) {
				n = len(ihs)
				b.Show("the step law applied", By(ihs[0], ihs[1], b.Hyp(stepLaw)))
			})
		}))
		require.True(t, sec.Proved())
		require.Equal(t, 2, n)
	})
	t.Run("one Fact on a two-hypothesis step", func(t *testing.T) {
		sec := e.ctx.Section(goal)
		msg := panicMessage(func() {
			sec.Do(Derive(func(a *Argument) {
				a.Induct(a.Binder("t"))
				a.Base("by hypothesis", Assumption())
				a.Step("wrong shape", func(b *Argument, ih Fact) { b.Show("never", Assumption()) })
			}))
		})
		require.Contains(t, msg, "introduced 2 hypotheses, not one")
	})
	t.Run("two Facts on the base case", func(t *testing.T) {
		sec := e.ctx.Section(goal)
		msg := panicMessage(func() {
			sec.Do(Derive(func(a *Argument) {
				a.Induct(a.Binder("t"))
				a.Base("wrong shape", func(b *Argument, l, r Fact) { b.Show("never", Assumption()) })
			}))
		})
		require.Contains(t, msg, "grants no hypothesis")
	})
	t.Run("wrong arity", func(t *testing.T) {
		le := makeListTestEnv()
		lgoal, _ := le.listGoal()
		sec := le.ctx.Section(lgoal)
		msg := panicMessage(func() {
			sec.Do(Derive(func(a *Argument) {
				a.Induct(a.Binder("l"))
				a.Base("by hypothesis", Assumption())
				a.Step("wrong shape", func(b *Argument, l, r Fact) { b.Show("never", Assumption()) })
			}))
		})
		require.Contains(t, msg, "grants ONE hypothesis")
	})
}
