package refuter

// Regression: the refuter has NO argument-position paramodulation gap for
// derived equations. An equation that only exists inside a
// divide-and-conquer branch (here: from the hyp disjunction's division)
// paramodulates into function-argument positions exactly like an init
// clause — the branch assumption enters the active set and resolves
// normally (divideConquer → merge → per-branch refute).
//
// Pinned because a diagnosis once blamed these exact shapes on a refuter
// limitation; the actual failure was `auto`'s arith preprocessing consuming
// the equational bridges before CNF (see prover/tactic/arith_tactics.go's
// no-hurt contract). Both refuter construction pipelines must keep closing
// the shapes directly.

import (
	"context"
	"math/big"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/ext/dsl"

	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

func assertBothPipelinesRefute(t *testing.T, label string, goal Prop) {
	t.Helper()
	ctx, cancel := context.WithTimeout(t.Context(), 8*time.Second)
	defer cancel()

	raw := CreateRefuter(t.Context(), goal, &cnfNormalizationCache)
	raw.Prove(ctx)
	assert.True(t, raw.Refuted(), "%s: raw pipeline", label)

	cache := &clause.CNFNormalizeCache{
		PreCNF: &clause.PreCNFCache{},
		Tail:   &ext.TermKeyPropMap{},
	}
	pre := CreateRefuterFromPreNormalized(t.Context(), goal, cache)
	pre.Prove(ctx)
	assert.True(t, pre.Refuted(), "%s: prenormalized pipeline", label)
}

func TestDerivedEquationParamodulatesIntoArgumentPosition(t *testing.T) {
	defer goleak.VerifyNone(t)
	num := ext.NumType
	m := Var("m", num)
	n := Var("n", num)
	x := Var("x", num)
	zero := ext.WrapTerm(ext.MakeNumeral(big.NewInt(0)))
	mul := ext.WrapTerm(dsl.NatStarMeta.Term())
	lt := ext.WrapTerm(dsl.NatLtMeta.Term())

	// (m = 0) ∨ (0 < m), m*x ≠ 0*x ⊢ 0 < m: branch m = 0 rewrites under
	// `*` giving 0*x ≠ 0*x, closed by refl.
	assertBothPipelinesRefute(t, "one rewrite under a function symbol", TestProp(
		lt.Apply(zero, m),
		m.Eq(zero).Or(lt.Apply(zero, m)),
		Not(mul.Apply(m, x).Eq(mul.Apply(zero, x))),
	))

	// (m = 0) ∨ (0 < m), n ≠ 0, n = m*x, 0*x = 0 ⊢ 0 < m: branch m = 0
	// chains n = m*x → n = 0*x → n = 0 against n ≠ 0.
	assertBothPipelinesRefute(t, "chained rewrite through an argument position", TestProp(
		lt.Apply(zero, m),
		m.Eq(zero).Or(lt.Apply(zero, m)),
		Not(n.Eq(zero)),
		n.Eq(mul.Apply(m, x)),
		mul.Apply(zero, x).Eq(zero),
	))

	// Abstract-vocabulary control: (m = c) ∨ P(m), f(m) ≠ f(c) ⊢ P(m).
	mc := Var("m", TypeA)
	c := Var("c", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	assertBothPipelinesRefute(t, "abstract vocabulary", TestProp(
		P.Apply(mc),
		mc.Eq(c).Or(P.Apply(mc)),
		Not(f.Apply(mc).Eq(f.Apply(c))),
	))
}
