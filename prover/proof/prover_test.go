package proof

import (
	"context"
	"slices"
	"sync"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

var MakeProp = prop.MakeProp

func TestAutoExpand(t *testing.T) {
	defer goleak.VerifyNone(t)

	var cnfNormalizationCache utils.Map[core.TermKey, Prop]
	env := &ProverEnv{
		ProofService:          MockConstMetaService(),
		CnfRefuterTimeout:     time.Second,
		CnfNormalizationCache: &cnfNormalizationCache,
		CnfNormalizeCache:     NewCNFNormalizeCache(),
	}

	autoExpand := func(goal Prop) {
		node := CreateGoalStack(goal)
		assert.True(t, env.AutoExpand().Apply(node))
		assert.True(t, node.Proved())
	}

	var goal Prop

	{
		x := Var("x", TypeBool)
		u := Var("u", TypeBool)
		v := Var("v", TypeBool)
		w := Var("w", TypeBool)
		f := Var("f", MakeFun(TypeBool, TypeBool))
		R := Var("R", MakeFun(TypeBool, TypeBool))
		S := Var("S", MakeFun(TypeBool, TypeBool, TypeBool))

		// ⊢ ¬∀x.x
		goal = MakeProp(Not(ForAll(x)(x)))
		autoExpand(goal)

		// x ⇒ u, u ⇒ v, v ⇒ x, (x = ¬u) ∨ (x = ¬v) ⊢ ⊥
		goal = MakeProp(ext.F, x.Imply(u), u.Imply(v), v.Imply(x), x.Eq(Not(u)).Or(x.Eq(Not(v))))
		autoExpand(goal)

		// ⊢ ¬(∃x.∃S.∀u.(S(x, u) = ¬S(u, u))))
		goal = MakeProp(Not(Exists(x, S)(ForAll(u)(S.Apply(x, u).Eq(Not(S.Apply(u, u)))))))
		autoExpand(goal)

		// ⊢ ∃u.(S(x, u) = S(u, u))
		goal = MakeProp(Exists(u)(S.Apply(x, u).Eq(S.Apply(u, u))))
		autoExpand(goal)

		// ⊢ ∀x.R(x) = (R(⊤) ∧ R(⊥))
		goal = MakeProp(ForAll(x)(R.Apply(x)).Eq(R.Apply(ext.T).And(R.Apply(ext.F))))
		autoExpand(goal)

		// ⊢ ∃x.R(x) = (R(⊤) ∨ R(⊥))
		goal = MakeProp(Exists(x)(R.Apply(x)).Eq(R.Apply(ext.T).Or(R.Apply(ext.F))))
		autoExpand(goal)

		// ∀v.∀w.(¬R(v) ∨ R(f(w))),
		// ∀u.(R(u) ∨ R(f(u))),
		// ∀x.(¬R(x) ∨ ¬R(f(x)))
		// ⊢ ⊥
		goal = MakeProp(
			ext.F,
			ForAll(u)((R.Apply(u)).Or(R.Apply(f.Apply(u)))),
			ForAll(v, w)((Not(R.Apply(v))).Or(R.Apply(f.Apply(w)))),
			ForAll(x)(Not(R.Apply(x)).Or(Not(R.Apply(f.Apply(x))))))
		autoExpand(goal)
	}

	{
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		P := Var("P", MakeFun(TypeA, TypeBool))
		D := Var("D", MakeFun(TypeA, TypeBool))

		// ∃x.P(x) ⊢ ∃x.P(x) ∧ (D(x) ⇒ ∀y.(P(y) ⇒ D(y)))
		g := Exists(x)(P.Apply(x).And(D.Apply(x).Imply(ForAll(y)(P.Apply(y).Imply(D.Apply(y))))))
		goal := MakeProp(g, Exists(x)(P.Apply(x)))
		autoExpand(goal)

		// ∃x.∀y.(P(y) ⇔ (x = y)) ⇔ ∃x.P(x) ∧ ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
		g0 := Exists(x)(P.Apply(x)).And(ForAll(x, y)(P.Apply(x).And(P.Apply(y)).Imply(x.Eq(y))))
		g1 := Exists(x)(ForAll(y)(P.Apply(y).Eq(x.Eq(y))))
		goal = MakeProp(g0.Eq(g1))
		autoExpand(goal)

		// P(x) ⇔ ∀y.((x = y) ⇒ P(y))
		goal = MakeProp(P.Apply(x).Eq(ForAll(y)(x.Eq(y).Imply(P.Apply(y)))))
		autoExpand(goal)

		// P(x) ⇔ ∃y.((x = y) ∧ P(y))
		goal = MakeProp(P.Apply(x).Eq(Exists(y)(x.Eq(y).And(P.Apply(y)))))
		autoExpand(goal)
	}

	{
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		z := Var("z", TypeA)
		P := Var("P", MakeFun(TypeA, TypeA, TypeA))
		I := Var("Inv", MakeFun(TypeA, TypeA))
		One := Var("One", TypeA)

		// ∀x.∀y.∀z.(P(x, P(y, z)) = P(P(x, y), z)),
		// ∀x.(P(One, x) = x),
		// ∀x.(P(Inv(x), x) = One)
		// 	⊢ ∀x.(P(x, Inv(x)) = One)
		g0 := ForAll(x, y, z)(P.Apply(x, P.Apply(y, z)).Eq(P.Apply(P.Apply(x, y), z)))
		g1 := ForAll(x)(P.Apply(One, x).Eq(x))
		g2 := ForAll(x)(P.Apply(I.Apply(x), x).Eq(One))
		g := ForAll(x)(P.Apply(x, I.Apply(x)).Eq(One))
		goal = MakeProp(g, g0, g1, g2)
		autoExpand(goal)
	}
}

func TestConcurrentLazyCNFNormalizeCache(t *testing.T) {
	defer goleak.VerifyNone(t)

	var cnfNormalizationCache utils.Map[core.TermKey, Prop]
	env := &ProverEnv{
		ProofService:          MockConstMetaService(),
		CnfRefuterTimeout:     time.Second,
		CnfNormalizationCache: &cnfNormalizationCache,
	}

	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	goal := MakeProp(x, y, x.Eq(y))

	var wg sync.WaitGroup
	for range 16 {
		wg.Go(func() {
			assert.NotNil(t, env.tryCNFRefute(context.Background(), goal))
		})
	}
	wg.Wait()
}

func TestUnresolvedLeaf(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeBool)
	goal := MakeProp(x, x)
	thm := core.TestThm(x, x)

	provedNode := &GoalStackNode{Goal: goal}
	provedNode.miniStep = _AxiomDefStep{}
	provedNode.provedThm = thm
	assert.True(t, provedNode.Proved())

	root := provedNode
	assert.Equal(t, root.NumUnsolvedLeaves(), 0)
	leaf, n := root.unsolvedLeafImpl(0)
	assert.Nil(t, leaf)
	assert.Equal(t, n, 0)
	leaf, n = root.unsolvedLeafImpl(1)
	assert.Nil(t, leaf)
	assert.Equal(t, n, 0)
	leaf, n = root.unsolvedLeafImpl(2)
	assert.Nil(t, leaf)
	assert.Equal(t, n, 0)

	root = &GoalStackNode{}
	assert.Equal(t, root.NumUnsolvedLeaves(), 1)
	leaf, n = root.unsolvedLeafImpl(0)
	assert.Equal(t, leaf, root)
	assert.Equal(t, n, -1)
	leaf, n = root.unsolvedLeafImpl(1)
	assert.Nil(t, leaf)
	assert.Equal(t, n, 1)
	leaf, n = root.unsolvedLeafImpl(2)
	assert.Nil(t, leaf)
	assert.Equal(t, n, 1)

	A := &GoalStackNode{Goal: MakeProp(Var("A", TypeBool))}
	B := &GoalStackNode{Goal: MakeProp(Var("B", TypeBool))}
	C := &GoalStackNode{Goal: MakeProp(Var("C", TypeBool))}
	D := &GoalStackNode{Goal: MakeProp(Var("D", TypeBool))}
	E := &GoalStackNode{Goal: MakeProp(Var("E", TypeBool))}
	F := &GoalStackNode{Goal: MakeProp(Var("F", TypeBool))}

	dummy := _AxiomDefStep{}
	root.miniStep = dummy
	root.children = []*GoalStackNode{A, B, C}
	A.miniStep = dummy
	A.children = []*GoalStackNode{D, provedNode, E}
	B.miniStep = dummy
	B.children = []*GoalStackNode{D, provedNode, F}
	E.miniStep = dummy
	E.children = []*GoalStackNode{C, F}

	assert.True(t, slices.Equal(
		root.UnsolvedLeaves(),
		[]*GoalStackNode{D, C, F, D, F, C}))
	assert.Equal(t, root.NumUnsolvedLeaves(), len(root.UnsolvedLeaves()))

	for i, l := range root.UnsolvedLeaves() {
		ll, j := root.unsolvedLeafImpl(i)
		assert.Equal(t, l, ll)
		assert.Equal(t, j, -1)
	}
	for i := range 3 {
		_, j := root.unsolvedLeafImpl(root.NumUnsolvedLeaves() + i)
		assert.Equal(t, j, root.NumUnsolvedLeaves())
	}

	assert.True(t, slices.Equal(
		root.UnsolvedLeaves(),
		slices.Collect(root.unsolvedLeavesIter())))
}
