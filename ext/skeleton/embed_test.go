package skeleton

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
)

// Whistle-encoding shapes: full paths, no depth cap, coarse alphabet,
// dedup.
func TestEmbPaths_Shapes(t *testing.T) {
	x := ext.Var("x", ext.TypeA)
	y := ext.Var("y", ext.TypeA)
	f := ext.Var("f", ext.MakeFun(ext.TypeA, ext.TypeBool))

	// Bare variable: single wildcard path.
	assert.Equal(t, []EmbPath{{"*"}}, EmbPaths(x.Core()))

	// Var-headed application: head token *, arg token *.
	assert.Equal(t, []EmbPath{{"*", "*"}}, EmbPaths(f.Apply(x).Core()))

	// Const-headed application with two var args: both arg paths are
	// identical after collapsing vars to *, so they dedup to one.
	assert.Equal(t, []EmbPath{{"C:=", "*"}}, EmbPaths(core.Eq(x.Core(), y.Core())))

	// λ-abstraction: LAM token, then body. Bound and free vars collapse
	// to the same wildcard.
	assert.Equal(t, []EmbPath{{"LAM", "*"}}, EmbPaths(x.To(x).Core()))
}

func TestPathEmbeds_GrowthAndDirection(t *testing.T) {
	x := ext.Var("x", ext.TypeBool)
	n1 := ext.Not(x)
	n2 := ext.Not(n1)

	// x ⊴ ¬x ⊴ ¬¬x: growth chains embed forward...
	assert.True(t, PathEmbeds(EmbPaths(x.Core()), EmbPaths(n1.Core())))
	assert.True(t, PathEmbeds(EmbPaths(n1.Core()), EmbPaths(n2.Core())))
	assert.True(t, PathEmbeds(EmbPaths(x.Core()), EmbPaths(n2.Core())))
	// ...but not backward (paths too long to be subsequences).
	assert.False(t, PathEmbeds(EmbPaths(n2.Core()), EmbPaths(n1.Core())))
}

// Free-variable renaming / argument permutation is invisible to the
// wildcard alphabet: a flip-flop pair has identical path sets, so each
// embeds the other — exactly the loop signal the whistle wants.
func TestPathEmbeds_FlipFlop(t *testing.T) {
	a := ext.Var("a", ext.TypeA).Core()
	b := ext.Var("b", ext.TypeA).Core()
	ab := EmbPaths(core.Eq(a, b))
	ba := EmbPaths(core.Eq(b, a))
	assert.True(t, PathEmbeds(ab, ba))
	assert.True(t, PathEmbeds(ba, ab))
}

// A constant that disappears (definition unfolding to a body not
// containing it) does NOT embed: its C: token has no counterpart.
// The converse direction — all-wildcard paths into constant-bearing
// paths — DOES hold by design (over-approximation: a variable may have
// been instantiated to anything).
func TestPathEmbeds_ConstDischarge(t *testing.T) {
	x := ext.Var("x", ext.TypeA)
	y := ext.Var("y", ext.TypeA)
	g := ext.Var("g", ext.MakeFun(ext.TypeA, ext.TypeBool))

	eq := EmbPaths(core.Eq(x.Core(), y.Core())) // {[C:=, *]}
	gx := EmbPaths(g.Apply(x).Core())           // {[*, *]}

	assert.False(t, PathEmbeds(eq, gx))
	assert.True(t, PathEmbeds(gx, eq))
}

// Every path set embeds itself (repeat states blow the whistle).
func TestPathEmbeds_Reflexive(t *testing.T) {
	x := ext.Var("x", ext.TypeA).Core()
	y := ext.Var("y", ext.TypeA).Core()
	p := EmbPaths(core.Eq(x, y))
	assert.True(t, PathEmbeds(p, p))
}

// TermTrajectory mirrors Trajectory over bare terms: growth embeds,
// a state strictly smaller than every ancestor is spared by the size
// gate, and returning exactly to an ancestor state (a loop) blows.
func TestTermTrajectoryEmbedsAncestor(t *testing.T) {
	x := ext.Var("x", ext.TypeBool)

	var root *TermTrajectory
	n1 := root.Extend(ext.Not(x).Core())
	assert.Equal(t, 1, n1.Depth())
	assert.False(t, n1.EmbedsAncestor())

	n2 := n1.Extend(ext.Not(ext.Not(x)).Core())
	assert.True(t, n2.EmbedsAncestor())

	// Strictly smaller than every ancestor: silent.
	n3 := n2.Extend(x.Core())
	assert.False(t, n3.EmbedsAncestor())

	// Exact repeat of an ancestor: loop, blows.
	n4 := n3.Extend(ext.Not(x).Core())
	assert.True(t, n4.EmbedsAncestor())
}
