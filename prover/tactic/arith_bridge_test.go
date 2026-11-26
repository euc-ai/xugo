package tactic

// Regression tests for the arith no-hurt contract (bridge emission +
// hyp retention) — see emitArithBridges and the RETENTION rule in
// arithRewriteTactic.
//
// The counterexample class behind the contract (probe shapes of
// nat_divides.DividesLessEqStrong): an arith fast-path that rewrites `m*x ≠ 0*x` to `m*x ≠ 0`
// and drops the ring-true hyp `0*x = 0` strands the CNF refuter, which
// can close the ORIGINAL goals by paramodulation + refl but has no
// arithmetic to re-derive the consumed bridges.

import (
	"math/big"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// arithRowVocab is the shared num vocabulary of the regression rows.
func arithRowVocab() (m, n, x, zero, mul, lt *ext.TermWrapper) {
	num := ext.NumType
	m = ext.Var("m", num)
	n = ext.Var("n", num)
	x = ext.Var("x", num)
	zero = ext.WrapTerm(ext.MakeNumeral(big.NewInt(0)))
	mul = ext.WrapTerm(dsl.NatStarMeta.Term())
	lt = ext.WrapTerm(dsl.NatLtMeta.Term())
	return
}

// A hyp rewrite that consumes a value-level subterm must emit the consumed
// equation as an extra hyp of the residual:
//
//	(m = 0) ∨ (0 < m), m*x ≠ 0*x ⊢ 0 < m
//
// fires on `m*x ≠ 0*x` → `m*x ≠ 0` (the identity fold 0*x → 0) and must add `0*x = 0`.
func TestArithBridgeEmissionOnHypRewrite(t *testing.T) {
	m, _, x, zero, mul, lt := arithRowVocab()
	goal := prop.MakeProp(
		lt.Apply(zero, m),
		m.Eq(zero).Or(lt.Apply(zero, m)),
		ext.Not(mul.Apply(m, x).Eq(mul.Apply(zero, x))),
	)

	sg := unscopedArithTactic(goal)
	require.NotNil(t, sg, "arith must fire on the B1-rewritable hyp")
	require.Equal(t, 1, sg.Size())
	child := sg.ChildGoal(0)

	bridge := ext.Eq(mul.Apply(zero, x), zero)
	rewritten := Not(ext.Eq(mul.Apply(m, x), zero))
	childHyps := slices.Collect(child.HypIter())
	assert.True(t, slices.ContainsFunc(childHyps, bridge.AlphaEquals),
		"the consumed equation 0*x = 0 must ride along as a bridge hyp")
	assert.True(t, slices.ContainsFunc(childHyps, rewritten.Core().AlphaEquals),
		"the rewritten hyp m*x ≠ 0 must be present")
	// The reconstruct must discharge the bridge — validated eagerly by
	// MakeSubGoals (IsStronger against the parent), so reaching here with
	// the bridge present proves the discharge works.
}

// A hyp the decider proves redundant (⇔ ⊤) by ARITHMETIC must be retained,
// not dropped — both the ring-true equation `0*x = 0` (paramodulation food)
// and the num-totality disjunction `(m = 0) ∨ (0 < m)` (the CNF refuter's
// case-split license). With every candidate retained, arith reports
// no-progress and `auto` falls through to AutoExpand on the ORIGINAL goal.
func TestArithRetainsNonTrivialRedundantHyps(t *testing.T) {
	m, n, x, zero, mul, lt := arithRowVocab()
	goal := prop.MakeProp(
		lt.Apply(zero, m),
		m.Eq(zero).Or(lt.Apply(zero, m)),
		ext.Not(n.Eq(zero)),
		n.Eq(mul.Apply(m, x)),
		mul.Apply(zero, x).Eq(zero),
	)

	sg := unscopedArithTactic(goal)
	if sg == nil {
		return // no fire at all — every redundant hyp retained
	}
	// If arith still fires (e.g. a future decider gets stronger), no
	// retained-class hyp may have been dropped from the child.
	require.Equal(t, 1, sg.Size())
	childHyps := slices.Collect(sg.ChildGoal(0).HypIter())
	for _, kept := range []Term{
		mul.Apply(zero, x).Eq(zero).Core(),
		m.Eq(zero).Or(lt.Apply(zero, m)).Core(),
	} {
		assert.True(t, slices.ContainsFunc(childHyps, kept.AlphaEquals),
			"arith-redundant non-trivial hyp %s must be retained", ext.PrintTerm(kept))
	}
}

// Vacuous redundant hyps are still cleaned up — retention is scoped to
// content a downstream syntactic consumer could actually use. Droppable:
// refl equations (trivially true without arithmetic) and tautological
// clauses whose single witness literal is a non-equality arith truth
// (`X ⇒ (r ≤ r)`). See droppableRedundantHyp.
func TestArithStillDropsVacuousHyps(t *testing.T) {
	m, n, x, zero, _, lt := arithRowVocab()
	le := ext.WrapTerm(dsl.NatLeMeta.Term())
	P := ext.Var("P", MakeFun(ext.NumType, TypeBool))

	for _, tc := range []struct {
		name string
		hyp  *ext.TermWrapper
	}{
		{"refl equation", n.Eq(n)},
		{"guarded refl-≤ (the NaddComplete shape)",
			P.Apply(x).Imply(le.Apply(n, n))},
		{"bare comparison", le.Apply(zero, x)},
	} {
		goal := prop.MakeProp(
			lt.Apply(zero, m),
			tc.hyp,
			ext.Not(m.Eq(zero)),
		)
		sg := unscopedArithTactic(goal)
		require.NotNil(t, sg, "%s: arith must fire", tc.name)
		require.Equal(t, 1, sg.Size())
		childHyps := slices.Collect(sg.ChildGoal(0).HypIter())
		assert.False(t, slices.ContainsFunc(childHyps, tc.hyp.Core().AlphaEquals),
			"%s: a vacuous hyp is dropped", tc.name)
	}
}

// Repeated arith passes must reach a fixpoint: the emitted bridge is itself
// an arith-redundant non-trivial equation, so the retention rule keeps it
// stable (no drop-and-re-emit ping-pong).
func TestArithBridgeEmissionTerminates(t *testing.T) {
	m, _, x, zero, mul, lt := arithRowVocab()
	goal := prop.MakeProp(
		lt.Apply(zero, m),
		m.Eq(zero).Or(lt.Apply(zero, m)),
		ext.Not(mul.Apply(m, x).Eq(mul.Apply(zero, x))),
	)

	var cur Prop = goal
	for range 8 {
		sg := unscopedArithTactic(cur)
		if sg == nil {
			return // fixpoint
		}
		require.Equal(t, 1, sg.Size())
		next := sg.ChildGoal(0)
		require.False(t, next.AlphaEquals(cur), "arith fired without progress")
		cur = next
	}
	t.Fatalf("arith did not reach a fixpoint within 8 passes; last goal: %v", cur)
}

var _ = utils.Assert // keep the utils import if asserts above change
