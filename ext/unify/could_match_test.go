package unify

// Unit tests for the MatchFilter / SpineHeadConst primitive. The
// load-bearing contract — CouldMatch never returns false on a pair the
// βη-unifier would match — is pinned differentially against unifyEq in
// prop.TestCouldMatchNeverBlocksUnifyEq; here we pin the head
// extraction itself, in particular its βη-stability claims (η-variants
// agree on the head; β-redex heads decline rather than guess).

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
)

func TestSpineHeadConst(t *testing.T) {
	a := core.MakeVarType("A")
	b := core.MakeVarType("B")
	cMeta := core.MakeConstMeta("c", core.MakeFun(a, b))
	c := core.MakeConstTerm(cMeta, core.MakeFun(a, b))
	dMeta := core.MakeConstMeta("d", core.MakeFun(a, a, b))
	d := core.MakeConstTerm(dMeta, core.MakeFun(a, a, b))
	x := core.Var("x", a)
	f := core.Var("f", core.MakeFun(a, b))

	// Bare const.
	name, ok := SpineHeadConst(c)
	assert.True(t, ok)
	assert.Equal(t, TermName("c"), name)

	// Applied const: c(x).
	name, ok = SpineHeadConst(core.Apply(c, x))
	assert.True(t, ok)
	assert.Equal(t, TermName("c"), name)

	// Multi-arg spine: d(x)(x).
	name, ok = SpineHeadConst(core.Apply(core.Apply(d, x), x))
	assert.True(t, ok)
	assert.Equal(t, TermName("d"), name)

	// η-expansion agrees with the η-short form: λx.c(x) vs c.
	etaLong, ok := SpineHeadConst(core.Abs(x, core.Apply(c, x)))
	assert.True(t, ok)
	assert.Equal(t, TermName("c"), etaLong)

	// Var head declines.
	_, ok = SpineHeadConst(core.Apply(f, x))
	assert.False(t, ok)

	// λ-bound var head declines: λf. f(x).
	_, ok = SpineHeadConst(core.Abs(f, core.Apply(f, x)))
	assert.False(t, ok)

	// β-redex head declines rather than normalizing: (λf. f(x))(c).
	_, ok = SpineHeadConst(core.Apply(core.Abs(f, core.Apply(f, x)), c))
	assert.False(t, ok)

	// Identity lambda (the set_comprehension shape λp.p): bound-var head declines.
	p := core.Var("p", a)
	_, ok = SpineHeadConst(core.Abs(p, p))
	assert.False(t, ok)
}

func TestMatchFilterCouldMatch(t *testing.T) {
	a := core.MakeVarType("A")
	cMeta := core.MakeConstMeta("c", core.MakeFun(a, core.TypeBool()))
	c := core.MakeConstTerm(cMeta, core.MakeFun(a, core.TypeBool()))
	dMeta := core.MakeConstMeta("d", core.MakeFun(a, core.TypeBool()))
	d := core.MakeConstTerm(dMeta, core.MakeFun(a, core.TypeBool()))
	x := core.Var("x", a)
	g := core.Var("g", core.MakeFun(a, core.TypeBool()))

	cHeaded := MatchFilterFor(core.Abs(x, core.Apply(c, x)))
	assert.True(t, cHeaded.Filtering())

	// Same head — could match (unifier decides).
	assert.True(t, cHeaded.CouldMatch(core.Apply(c, x)))
	// η-short target with the same head.
	assert.True(t, cHeaded.CouldMatch(core.Term(c)))
	// Different rigid const head — excluded.
	assert.False(t, cHeaded.CouldMatch(core.Apply(d, x)))
	// Var-headed target — the var is the target's, excluded.
	assert.False(t, cHeaded.CouldMatch(core.Apply(g, x)))
	// β-redex-headed target — unknown, passes through.
	redex := core.Apply(core.Abs(g, core.Apply(g, x)), c)
	assert.True(t, cHeaded.CouldMatch(redex))

	// Non-filtering rules accept everything: identity lambda (set_comprehension
	// shape), var-headed LHS.
	identity := MatchFilterFor(core.Abs(x, x))
	assert.False(t, identity.Filtering())
	assert.True(t, identity.CouldMatch(core.Apply(d, x)))

	varHead := MatchFilterFor(core.Apply(g, x))
	assert.False(t, varHead.Filtering())
	assert.True(t, varHead.CouldMatch(core.Apply(d, x)))
}
