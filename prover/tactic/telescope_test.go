package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/ext"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A statement in the standard form opens in the order of its
// dependencies: a hypothesis right after the binders it mentions, the
// rest left as a statement.
func TestOpenTelescopeTactic(t *testing.T) {
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	x, y := Var("x", TypeA), Var("y", TypeA)
	A, B, C := P.Apply(x), P.Apply(y), Q.Apply(x, y)
	g := Var("g", MakeFun(TypeA, MakeFun(TypeA, TypeBool))).Apply(x, y)
	h := Var("h", TypeBool)
	// ∀x y. P(x) ∧ P(y) ∧ Q(x, y) ⇒ g(x, y)
	goal := testProp(ext.ForAll(x, y)(A.And(B).And(C).Imply(g)).Core(), h.Core())

	// x, then P(x); y, then P(y): the rest stays a statement.
	sg := OpenTelescopeTactic(goal, []TelescopeItem{
		{Binder: 0}, {Binder: -1, Pieces: []PieceRef{{0, 0}}}, {Binder: 1}, {Binder: -1, Pieces: []PieceRef{{0, 1}}}})
	require.NotNil(t, sg)
	assertPropAlphaEqual(t, sg.ChildGoal(0), testProp(ext.ForAll(x)(A.Imply(ext.ForAll(y)(B.Imply(C.Imply(g))))).Core(), h.Core()))
	assertSubGoals(t, sg, goal)

	// x and P(x); the rest — y and the other two — one block as it was.
	sg = OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 0}, {Binder: -1, Pieces: []PieceRef{{0, 0}}}})
	require.NotNil(t, sg)
	assertPropAlphaEqual(t, sg.ChildGoal(0), testProp(ext.ForAll(x)(A.Imply(ext.ForAll(y)(B.And(C).Imply(g)))).Core(), h.Core()))
	assertSubGoals(t, sg, goal)

	// Both binders, then the pieces in another grouping.
	sg = OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 0}, {Binder: 1},
		{Binder: -1, Pieces: []PieceRef{{0, 0}, {0, 1}}}, {Binder: -1, Pieces: []PieceRef{{0, 2}}}})
	require.NotNil(t, sg)
	assertPropAlphaEqual(t, sg.ChildGoal(0), testProp(ext.ForAll(x, y)(A.And(B).Imply(C.Imply(g))).Core(), h.Core()))
	assertSubGoals(t, sg, goal)

	// The statement as it stands, or nothing opened: nil.
	assert.Nil(t, OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 0}, {Binder: 1}}))
	assert.Nil(t, OpenTelescopeTactic(goal, nil))
	// A hypothesis ahead of a binder it mentions, a binder out of order,
	// a piece taken twice: nil.
	assert.Nil(t, OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 0}, {Binder: -1, Pieces: []PieceRef{{0, 1}}}}))
	assert.Nil(t, OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 1}}))
	assert.Nil(t, OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 0}, {Binder: 1},
		{Binder: -1, Pieces: []PieceRef{{0, 0}}}, {Binder: -1, Pieces: []PieceRef{{0, 0}}}}))
}

// A curried statement is a telescope of blocks: binding into the second
// block before the first's pieces are taken merges the two, the pieces
// left behind conjoined ahead of the rest.
func TestOpenTelescopeTactic_MergesBlocks(t *testing.T) {
	P := Var("P", MakeFun(TypeA, TypeBool))
	x, y := Var("x", TypeA), Var("y", TypeA)
	A, B := P.Apply(x), P.Apply(y)
	g := Var("g", TypeBool)
	// ∀x. P(x) ⇒ ∀y. P(y) ⇒ g
	goal := testProp(ext.ForAll(x)(A.Imply(ext.ForAll(y)(B.Imply(g)))).Core())

	sg := OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 0}, {Binder: 1}})
	require.NotNil(t, sg)
	assertPropAlphaEqual(t, sg.ChildGoal(0), testProp(ext.ForAll(x, y)(A.And(B).Imply(g)).Core()))
	assertSubGoals(t, sg, goal)

	// The first block as it stands: nil.
	assert.Nil(t, OpenTelescopeTactic(goal, []TelescopeItem{{Binder: 0}, {Binder: -1, Pieces: []PieceRef{{0, 0}}}}))
}
