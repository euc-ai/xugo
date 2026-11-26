package prop

import (
	"math/big"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestContextEq_VariableAgainstNumeralReadsToTheNumeral pins the one
// exception contextEq makes to its bigger-side-on-LHS rule: a bare
// variable against a numeral literal reads variable → numeral. By raw
// size `1` is bit1(_0), two symbols, so the size rule would read
// `p = 1` as `1 → p` — and EqRewrite would then find that tower inside
// `2` = bit0(bit1(_0)) and produce `bit0(p)`, a term the arithmetic
// closer cannot evaluate. Compound terms keep the size rule, towers
// included: the datatype door's tag reasoning rewrites `1` into
// `suc(0)` inside a larger tag on purpose.
func TestContextEq_VariableAgainstNumeralReadsToTheNumeral(t *testing.T) {
	p := Var("p", ext.NumType)
	one := ext.WrapTerm(ext.MakeNumeral(big.NewInt(1)))
	two := ext.WrapTerm(ext.MakeNumeral(big.NewInt(2)))
	f := Var("f", MakeFun(ext.NumType, ext.NumType)) // any num → num symbol
	R := Var("R", MakeFun(ext.NumType, ext.NumType, TypeBool))

	// The tower is what the raw size comparison sees.
	require.Greater(t, one.Size(), p.Size(), "the fixture needs `1` to be spelled larger than a variable")
	require.True(t, ext.IsSub(one, two), "the fixture needs `1`'s tower inside `2`'s")

	// p = 1 keeps the variable on the LHS: the rewrite is p → 1.
	eq := contextEq(p.Eq(one))
	assert.True(t, Lhs(eq).Equals(p), "p = 1 must read p → 1, got %v", eq)
	assert.True(t, Rhs(eq).Equals(one))

	// 1 = p is turned around to the same orientation.
	eq = contextEq(one.Eq(p))
	assert.True(t, Lhs(eq).Equals(p), "1 = p must read p → 1, got %v", eq)

	// A compound term keeps the size rule: f(1) = 2 (three symbols
	// against three) stays as written, f(p) = 1 (two against two) too.
	eq = contextEq(f.Apply(one).Eq(two))
	assert.True(t, Lhs(eq).Equals(f.Apply(one)))
	eq = contextEq(f.Apply(p).Eq(one))
	assert.True(t, Lhs(eq).Equals(f.Apply(p)))

	// Two numerals never swap: the written direction stands.
	eq = contextEq(two.Eq(one))
	assert.True(t, Lhs(eq).Equals(two))

	// The context rewriter as eqSimplify runs it: p = 1 on `R(2, p)`
	// yields `R(2, 1)` — the `2` untouched, the p substituted.
	w := ContextEqRewrite(p.Eq(one), false)(R.Apply(two, p))
	require.NotNil(t, w)
	assert.True(t, Rhs(w).Equals(R.Apply(two, one)), "p = 1 on `R(2, p)` must produce `R(2, 1)`, got %v", Rhs(w))
}
