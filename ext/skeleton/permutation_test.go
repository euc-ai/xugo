package skeleton

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

// Rule-level variants test: COMM and left-comm are permutative (bodies
// equal under a bijective renaming of the λ-peeled pattern vars), ASSOC
// and material-changing rules are not.
func TestPermutativeRulePattern(t *testing.T) {
	A := ext.TypeA
	x := ext.Var("x", A)
	y := ext.Var("y", A)
	z := ext.Var("z", A)
	u := ext.Var("u", ext.MakeFun(A, ext.MakeFun(A, A)))
	v := ext.Var("v", ext.MakeFun(A, ext.MakeFun(A, A)))

	// abs2/abs3 shape the rule sides the way contextAbsEq does:
	// λ-abstractions over the rule's ∀-vars.
	lam := func(vars []*ext.TermWrapper, body *ext.TermWrapper) *ext.TermWrapper {
		for i := len(vars) - 1; i >= 0; i-- {
			body = vars[i].To(body)
		}
		return body
	}

	// COMM: λx.λy.u(x,y) = λx.λy.u(y,x) — variants under x↔y.
	comm := PermutativeRulePattern(
		lam([]*ext.TermWrapper{x, y}, u.Apply(x, y)).Core(),
		lam([]*ext.TermWrapper{x, y}, u.Apply(y, x)).Core())
	assert.True(t, comm, "COMM must be permutative")

	// Left-comm: λx.λy.λz.u(x,u(y,z)) = λx.λy.λz.u(y,u(x,z)) — variants
	// under x↔y, z fixed. Invisible to the instance-level unordered-tree
	// classifier; the whole point of the rule-level test.
	lc := PermutativeRulePattern(
		lam([]*ext.TermWrapper{x, y, z}, u.Apply(x, u.Apply(y, z))).Core(),
		lam([]*ext.TermWrapper{x, y, z}, u.Apply(y, u.Apply(x, z))).Core())
	assert.True(t, lc, "left-comm must be permutative")

	// ASSOC: λx.λy.λz.u(u(x,y),z) = λx.λy.λz.u(x,u(y,z)) — tree rotation,
	// no renaming maps one to the other.
	assoc := PermutativeRulePattern(
		lam([]*ext.TermWrapper{x, y, z}, u.Apply(u.Apply(x, y), z)).Core(),
		lam([]*ext.TermWrapper{x, y, z}, u.Apply(x, u.Apply(y, z))).Core())
	assert.False(t, assoc, "ASSOC must NOT be permutative")

	// Non-bijective collapse: λx.λy.u(x,y) = λx.λy.u(y,y) — y maps to y
	// but x also needs y: not injective.
	collapse := PermutativeRulePattern(
		lam([]*ext.TermWrapper{x, y}, u.Apply(x, y)).Core(),
		lam([]*ext.TermWrapper{x, y}, u.Apply(y, y)).Core())
	assert.False(t, collapse, "variable-collapsing rule must NOT be permutative")

	// Different head consts: λx.λy.u(x,y) = λx.λy.v(y,x) — material changed.
	diffHead := PermutativeRulePattern(
		lam([]*ext.TermWrapper{x, y}, u.Apply(x, y)).Core(),
		lam([]*ext.TermWrapper{x, y}, v.Apply(y, x)).Core())
	assert.False(t, diffHead, "different-head rule must NOT be permutative")

	// Ground equation (no pattern vars): never permutative.
	ground := PermutativeRulePattern(
		u.Apply(x, y).Core(),
		u.Apply(y, x).Core())
	assert.False(t, ground, "ground equation must NOT be rule-level permutative")

	// Pointwise η-form COMM: λs.λt.λw.u(s,t)(w)?? — the SET-typed variant
	// of pointwise (normalized) set lemmas: ∀s t ẋ. un(s,t)(ẋ) ⇔ un(t,s)(ẋ).
	SET := ext.MakeFun(A, ext.TypeBool)
	s := ext.Var("s", SET)
	tt := ext.Var("t", SET)
	w := ext.Var("w", A)
	un := ext.Var("un", ext.MakeFun(SET, ext.MakeFun(SET, SET)))
	pw := PermutativeRulePattern(
		lam([]*ext.TermWrapper{s, tt, w}, un.Apply(s, tt).Apply(w)).Core(),
		lam([]*ext.TermWrapper{s, tt, w}, un.Apply(tt, s).Apply(w)).Core())
	assert.True(t, pw, "pointwise COMM must be permutative")
}
