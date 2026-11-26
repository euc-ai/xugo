package clause

import (
	"sync"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

var loadConstMeta = ext.InitConstMetaMap().Load

// rtClause round-trips a clause through a fresh pool (serialize into a builder,
// deserialize from a reader over that pool).
func rtClause(c *Clause) *Clause {
	b := ext.NewPoolBuilder()
	p := SerializeClause(c, b)
	return DeserializeClause(p, ext.NewPoolReader(b.Pool(), loadConstMeta))
}

func rtClauseThm(t *ClauseThm) *ClauseThm {
	b := ext.NewPoolBuilder()
	p := SerializeClauseThm(t, b)
	return DeserializeClauseThm(p, ext.NewPoolReader(b.Pool(), loadConstMeta))
}

func TestClauseProto(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	h := Var("h", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	clause := MakeClause(ForAll(b)(P.Apply(b).Or(P.Apply(c))))
	assert.True(t, clause.Term().AlphaEquals(rtClause(clause).Term()))
	assert.True(t, clause.Term().AlphaEquals(rtClause(rtClause(clause)).Term()))

	clause = MakeClause(ForAll(a, b)(P.Apply(b).Or(Not(D.Apply(a)))))
	assert.True(t, clause.Term().AlphaEquals(rtClause(clause).Term()))
	assert.True(t, clause.Term().AlphaEquals(rtClause(rtClause(clause)).Term()))

	clause = MakeClause(ForAll(b)(P.Apply(b).Or(P.Apply(h)).Or(h.Eq(c)).Or(c.Eq(h))))
	assert.True(t, clause.Term().AlphaEquals(rtClause(clause).Term()))
	assert.True(t, clause.Term().AlphaEquals(rtClause(rtClause(clause)).Term()))
}

func TestClauseThmProto(t *testing.T) {
	defer goleak.VerifyNone(t)
	wg := sync.WaitGroup{}
	defer wg.Wait()

	assertReconstruct := func(clauseThm *ClauseThm) {
		reconstructed := rtClauseThm(clauseThm)
		assertPropAlphaEqual(t, reconstructed.Thm, clauseThm.Thm)
		reconstructed = rtClauseThm(reconstructed)
		assertPropAlphaEqual(t, reconstructed.Thm, clauseThm.Thm)
	}

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	var c, c0, c1 *Clause

	c0 = MakeClause(ForAll(x)(Q.Apply(x)))
	c1 = MakeClause(ForAll(y)(Not(Q.Apply(y))))
	assertReconstruct(c0.Contradicts(c1))

	c = MakeClause(ForAll(x)(P.Apply(y).Neq(P.Apply(x)).Or(Not(Q.Apply(x)))))
	resultChan := make(chan *ClauseThm, 100)
	wg.Go(func() { c.Factor(t.Context(), resultChan) })
	count := 0
	for clauseThm := range resultChan {
		count++
		assertReconstruct(clauseThm)
	}
	assert.Greater(t, count, 0)

	I := Var("Inv", MakeFun(TypeA, TypeA))
	One := Var("One", TypeA)

	c0 = MakeClause(x.Neq(I.Apply(x)))
	c1 = MakeClause((One.Eq(I.Apply(One))).Or(x.Eq(I.Apply(x))))
	assertReconstruct(c0.Simplifies(c1))

	P = Var("P", MakeFun(TypeA, TypeA))
	Q = Var("Q", MakeFun(TypeA, TypeA))

	c0 = MakeClause(ForAll(x)(P.Apply(x).Eq(y)))
	c1 = MakeClause((P.Apply(y).Eq(Q.Apply(y))))
	resultChan = make(chan *ClauseThm, 100)
	wg.Go(func() {
		c0.Resolve(t.Context(), c1, resultChan)
	})
	count = 0
	for clauseThm := range resultChan {
		count++
		assertReconstruct(clauseThm)
	}
	assert.Greater(t, count, 0)

}
