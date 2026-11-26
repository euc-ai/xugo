package refuter

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestClauseWhistle_PolicySizedCap: goals with small init clauses keep
// the old flat cap; comprehension-heavy goals get 2× their largest
// init clause.
func TestClauseWhistle_PolicySizedCap(t *testing.T) {
	P := Var("P", MakeFun(TypeA, TypeBool))
	c := Var("c", TypeA)

	small := clause.MakeClause(P.Apply(c).Core())
	w := newClauseWhistle(ClauseMap{small.Key(): small})
	assert.Equal(t, _CLAUSE_SIZE_LIMIT, w.sizeLimit,
		"small init clauses keep the flat cap")

	// Build a deliberately large init clause: P(f(f(...f(c)...))) with
	// enough applications to exceed _CLAUSE_SIZE_LIMIT/2.
	f := Var("f", MakeFun(TypeA, TypeA))
	big := c
	for range _CLAUSE_SIZE_LIMIT {
		big = f.Apply(big)
	}
	bigClause := clause.MakeClause(P.Apply(big).Core())
	w = newClauseWhistle(ClauseMap{bigClause.Key(): bigClause})
	assert.Equal(t, 2*bigClause.Size(), w.sizeLimit,
		"large init clauses size the cap at 2× the largest")
}

// TestClauseWhistle_GrowthChainCut: a self-application tower — each
// derived clause strictly containing (path-embedding) its input — is
// admitted for _WHISTLE_GROWTH_BACKSTOP rungs and cut afterwards,
// while a non-growing derivation resets the chain.
func TestClauseWhistle_GrowthChainCut(t *testing.T) {
	P := Var("P", MakeFun(TypeA, TypeBool))
	f := Var("f", MakeFun(TypeA, TypeA))
	c := Var("c", TypeA)

	// tower(n) = P(fⁿ(c)) as a unit clause.
	tower := func(n int) *Clause {
		x := c
		for range n {
			x = f.Apply(x)
		}
		return clause.MakeClause(P.Apply(x).Core())
	}

	init := tower(0)
	w := newClauseWhistle(ClauseMap{init.Key(): init})
	// Keep the cap out of the way — this test isolates the chain cut.
	w.sizeLimit = 1 << 20

	step := func(n int) *clause.ClauseThm {
		concl, hyp := tower(n), tower(n-1)
		thm := core.TestThm(concl.Term(), hyp.Term())
		return clause.TestClauseThm(thm, concl, hyp)
	}

	// Rungs 1.._WHISTLE_GROWTH_BACKSTOP admitted; the next one cut.
	for n := 1; n <= _WHISTLE_GROWTH_BACKSTOP; n++ {
		require.False(t, w.Rejects(step(n), tower(n)),
			"tower rung %d must be admitted", n)
		assert.Equal(t, n, w.chainDepth(tower(n)))
	}
	cutAt := _WHISTLE_GROWTH_BACKSTOP + 1
	assert.True(t, w.Rejects(step(cutAt), tower(cutAt)),
		"tower rung %d must be cut by the whistle", cutAt)
	assert.Equal(t, int64(1), w.Fires())

	// A non-growing derivation (output does not contain the input's
	// structure) resets: derive Q(c) from the deep tower rung.
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	qc := clause.MakeClause(Q.Apply(c).Core())
	hyp := tower(_WHISTLE_GROWTH_BACKSTOP)
	thm := core.TestThm(qc.Term(), hyp.Term())
	require.False(t, w.Rejects(clause.TestClauseThm(thm, qc, hyp), qc),
		"non-growing derivation must be admitted")
	assert.Equal(t, 0, w.chainDepth(qc), "non-growing derivation resets the chain")
}
