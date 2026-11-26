package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A loose reading is cited as its law beside the hypothesis it is read
// under, and a tuple on the reading grounds the law: each component of
// the hypothesis at the binder the law states it at, the witnesses at
// the binders between.

// looseCiteTestEnv is makeReadingTestEnv with two laws carrying the
// index letter B no component fixes. leading states the structure's
// binders first, `∀op e. mon(op, e) ⇒ ∀f:(B → A). ∀y:B. op(e, f(y)) =
// f(y)`. interleaved states them among the others, `∀x op y e f.
// mon(op, e) ⇒ op(e, op(x, f(y))) = op(x, f(y))`, and x shares e's
// type, so no reading of a misplaced tuple by its types puts it right.
// a, c and g are witnesses for x, y and f at B := bool.
type looseCiteTestEnv struct {
	*readingTestEnv
	leading, interleaved Prop
	instance             core.Term
	c, g                 *ext.TermWrapper
}

func makeLooseCiteTestEnv() *looseCiteTestEnv {
	e := makeReadingTestEnv()
	typeB := core.MakeVarType("B")
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	op := Var("op", opA)
	unit := Var("e", core.TypeA())
	x := Var("x", core.TypeA())
	f := Var("f", MakeFun(typeB, core.TypeA()))
	y := Var("y", typeB)
	fy := ext.WrapTerm(f).Apply(y)
	mon := e.ctx.Const("readMon", monA).Apply(op, unit)
	leading := ext.ForAll(op, unit)(mon.Imply(ext.ForAll(f, y)(ext.WrapTerm(op).Apply(unit, fy).Eq(fy)))).Core()
	xfy := ext.WrapTerm(op).Apply(x, fy)
	interleaved := ext.ForAll(x, op, y, unit, f)(mon.Imply(ext.WrapTerm(op).Apply(unit, xfy).Eq(xfy))).Core()
	serveThm(e.ctx, "zz_loose_cite_leading", core.TestThm(leading))
	serveThm(e.ctx, "zz_loose_cite_interleaved", core.TestThm(interleaved))

	monAtInd := e.ctx.Const("readMon", MakeFun(MakeFun(TypeInd, MakeFun(TypeInd, TypeInd)), MakeFun(TypeInd, TypeBool)))
	return &looseCiteTestEnv{
		readingTestEnv: e,
		leading:        prop.MakeProp(leading),
		interleaved:    prop.MakeProp(interleaved),
		instance:       monAtInd.Apply(e.plus, e.zero).Core(),
		c:              ext.WrapTerm(Var("c", TypeBool)),
		g:              ext.WrapTerm(Var("g", MakeFun(TypeBool, TypeInd))),
	}
}

func requireTuple(t *testing.T, got []Term, want ...core.Term) {
	t.Helper()
	require.Len(t, got, len(want))
	for i := range want {
		require.True(t, got[i].AlphaEquals(want[i]), "position %d holds %s, want %s", i, ext.PrintTerm(got[i]), ext.PrintTerm(want[i]))
	}
}

// The tuple runs in the order the law states its binders. Where the
// hypothesis's binders lead, the components open it; where they stand
// among the others, each is placed at its own binder.
func TestLooseCiteTuple_PlacesEachComponentAtItsBinder(t *testing.T) {
	e := makeLooseCiteTestEnv()
	plus, zero, a, c, g := e.plus.Core(), e.zero.Core(), e.a.Core(), e.c.Core(), e.g.Core()

	tuple, err := LooseCiteTuple(e.leading, e.instance, []Term{g, c})
	require.NoError(t, err)
	requireTuple(t, tuple, plus, zero, g, c)
	tuple, err = LooseCiteTuple(e.leading, e.instance, []Term{g})
	require.NoError(t, err)
	requireTuple(t, tuple, plus, zero, g)
	tuple, err = LooseCiteTuple(e.leading, e.instance, nil)
	require.NoError(t, err)
	requireTuple(t, tuple, plus, zero)

	// ∀x op y e f: the components are the second and the fourth.
	tuple, err = LooseCiteTuple(e.interleaved, e.instance, []Term{a, c, g})
	require.NoError(t, err)
	requireTuple(t, tuple, a, plus, c, zero, g)
	given, err := LooseCiteWitnesses(e.interleaved, e.instance, tuple)
	require.NoError(t, err)
	require.Equal(t, []int{0, 2, 4}, given, "the witnesses are read back from between the components")

	// A tuple through y reaches e, the last component, and stops there.
	tuple, err = LooseCiteTuple(e.interleaved, e.instance, []Term{a, c})
	require.NoError(t, err)
	requireTuple(t, tuple, a, plus, c, zero)
	given, err = LooseCiteWitnesses(e.leading, e.instance, []Term{plus, zero, g})
	require.NoError(t, err)
	require.Equal(t, []int{2}, given)
}

// A tuple grounds a prefix of the law's binders. One that stops before
// a binder stated ahead of a component cannot hold that component, and
// is refused naming the binder to give.
func TestLooseCiteTuple_RefusesATupleThatStopsBeforeAComponent(t *testing.T) {
	e := makeLooseCiteTestEnv()
	plus, zero, a, c, g := e.plus.Core(), e.zero.Core(), e.a.Core(), e.c.Core(), e.g.Core()
	_, err := LooseCiteTuple(e.interleaved, e.instance, []Term{a})
	require.ErrorContains(t, err, "the law binds x, op, y, e, f and the hypothesis fixes op, e")
	require.ErrorContains(t, err, "this one stops at y, stated before e — give the reading's binders through y")
	_, err = LooseCiteTuple(e.interleaved, e.instance, nil)
	require.ErrorContains(t, err, "this one stops at x, stated before e — give the reading's binders through y")

	// A recorded tuple that does not hold the components where the law
	// binds them is no record of the expansion.
	_, err = LooseCiteWitnesses(e.interleaved, e.instance, []Term{plus, zero, a, c, g})
	require.ErrorContains(t, err, "position 1 holds")
	_, err = LooseCiteWitnesses(e.interleaved, e.instance, []Term{a, plus, c})
	require.ErrorContains(t, err, "does not reach e")
}

// The By: a tuple on the reading closes the law's instance whichever
// way the law orders its binders, and a tuple the law's order cannot
// hold is refused where the By is built.
func TestRead_LooseCiteInABy(t *testing.T) {
	t.Run("the hypothesis's binders lead", func(t *testing.T) {
		e := makeLooseCiteTestEnv()
		gc := e.g.Apply(e.c)
		sec := e.residentReadingGoal(e.plus.Apply(e.zero, gc).Eq(gc))
		sec.Do(Derive(func(arg *Argument) {
			inst := arg.Assume()
			arg.Show("the law read under the instance, at the index type bool",
				By(Read(depName("zz_loose_cite_leading"), inst).At(e.g, e.c)))
		}))
		require.True(t, sec.Proved())
	})

	interleavedGoal := func(e *looseCiteTestEnv) *GoalStackNode {
		agc := e.plus.Apply(e.a, e.g.Apply(e.c))
		return e.residentReadingGoal(e.plus.Apply(e.zero, agc).Eq(agc))
	}
	t.Run("the hypothesis's binders stand among the others", func(t *testing.T) {
		e := makeLooseCiteTestEnv()
		sec := interleavedGoal(e)
		sec.Do(Derive(func(arg *Argument) {
			inst := arg.Assume()
			arg.Show("the law read under the instance, at the index type bool",
				By(Read(depName("zz_loose_cite_interleaved"), inst).At(e.a, e.c, e.g)))
		}))
		require.True(t, sec.Proved())
	})
	t.Run("a tuple that stops before a component", func(t *testing.T) {
		e := makeLooseCiteTestEnv()
		sec := interleavedGoal(e)
		var refusal string
		func() {
			defer func() { refusal = sprintAny(recover()) }()
			sec.Do(Derive(func(arg *Argument) {
				inst := arg.Assume()
				arg.Show("a tuple that stops at y, stated before e",
					By(Read(depName("zz_loose_cite_interleaved"), inst).At(e.a)))
			}))
		}()
		require.Contains(t, refusal, "is cited as its law beside the hypothesis it is read under")
		require.Contains(t, refusal, "this one stops at y, stated before e — give the reading's binders through y")
	})
}
