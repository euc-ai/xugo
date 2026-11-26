package clause

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestMakeClauseThm(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	h := Var("h", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	c0 := MakeClause(ForAll(b)(P.Apply(b).Or(P.Apply(c))))
	c1 := MakeClause(ForAll(a, b)(P.Apply(b).Or(Not(D.Apply(a)))))
	c2 := MakeClause(ForAll(a, b)(P.Apply(b).Or(Not(D.Apply(a)).Or(h.Eq(b)))))

	thm := testThm(F, c0.Term(), c1.Term(), c2.Term())

	clauseThm := MakeClauseThm(thm, FClause, c0, c1, c2)
	assertPropAlphaEqual(t, thm, clauseThm.AsThmCert())
	for i, h := range thm.Hyps() {
		assertTermAlphaEqual(t, h, clauseThm.HypClause(i).Term())
	}
	clauseThm = MakeClauseThm(thm, FClause, c2, c1, c0)
	assertPropAlphaEqual(t, thm, clauseThm.AsThmCert())
	for i, h := range thm.Hyps() {
		assertTermAlphaEqual(t, h, clauseThm.HypClause(i).Term())
	}
	assert.Panics(t, func() { MakeClauseThm(thm, FClause, c2, c1) })

	thm = testThm(c0.Term(), c1.Term(), c2.Term())

	clauseThm = MakeClauseThm(thm, c0, c1, c2)
	assertPropAlphaEqual(t, thm, clauseThm.AsThmCert())
	for i, h := range thm.Hyps() {
		assertTermAlphaEqual(t, h, clauseThm.HypClause(i).Term())
	}
	clauseThm = MakeClauseThm(thm, c0, c2, c1)
	assertPropAlphaEqual(t, thm, clauseThm.AsThmCert())
	for i, h := range thm.Hyps() {
		assertTermAlphaEqual(t, h, clauseThm.HypClause(i).Term())
	}
	assert.Panics(t, func() { MakeClauseThm(thm, FClause, c1, c2) })
}
