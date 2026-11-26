package emit

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/types/known/emptypb"
)

// TestLift_AParameterNameAVariableHoldsMovesTheVariable: the symbol
// walk registers every variable a member's payloads hold — a λ-binder
// of a cited statement among them — and allocates the Go identifier
// `c` to whichever variable named c it meets first. A statement
// binding `c` as its bundle lifts all the same: the parameter is
// named c, and the variable that held the identifier takes another
// (determinant.MultilinearColumnExpansion, whose ring c met a cited
// lemma's set c, rendered with its strips as steps until it did).
func TestLift_AParameterNameAVariableHoldsMovesTheVariable(t *testing.T) {
	ring := ext.MakeType("ring_ops", core.MakeVarType("A"))
	set := core.MakeFun(core.MakeVarType("A"), core.TypeBool())
	binder := ext.Var("c", ring).Core().(core.VarTerm)
	other := ext.Var("c", set).Core().(core.VarTerm)
	skolem := ext.Var("c_0", ring).Core().(core.VarTerm)
	e := &_Emitter{
		varIdent: map[_VarKey]string{
			{other.Name(), other.Type().Key()}:   "c",
			{binder.Name(), binder.Type().Key()}: "c_2",
			{skolem.Name(), skolem.Type().Key()}: "c_0",
		},
		varDecl: map[string]core.VarTerm{"c": other, "c_2": binder, "c_0": skolem},
	}
	root, rest := &msNode{step: &proof.StepProto{}}, &msNode{step: &proof.StepProto{}}
	slots := []liftSlot{{forall: true, binder: "c", typ: ring, skolem: skolem}}

	b := e.liftSlots(root, slots, rest, e.declSet())
	require.True(t, b.bound(), "the binder lifts although a variable holds its name")
	require.Equal(t, rest, b.rest)
	assert.Equal(t, ", c Term", b.signature())

	e.installBinding(b)
	assert.Equal(t, "c", e.varIdent[_VarKey{skolem.Name(), skolem.Type().Key()}], "the Skolem is the parameter")
	moved := e.varIdent[_VarKey{other.Name(), other.Type().Key()}]
	assert.NotEqual(t, "c", moved, "the variable that held the name moved aside")
	assert.True(t, any(other) == any(e.varDecl[moved]))
	_, declared := e.varDecl["c"]
	assert.False(t, declared, "no declaration binds the parameter's name")

	// A name a constant's identifier holds is no variable's to move:
	// the lift declines, and the tree renders from its root.
	e = &_Emitter{
		constIdent: map[_ConstKey]string{{core.TermName("c"), ring.Key()}: "c"},
		varIdent:   map[_VarKey]string{{skolem.Name(), skolem.Type().Key()}: "c_0"},
		varDecl:    map[string]core.VarTerm{"c_0": skolem},
	}
	b = e.liftSlots(root, slots, rest, e.declSet())
	assert.False(t, b.bound())
	assert.Equal(t, root, b.rest)
}

// TestLift_AFactHandleIsNoBindersName: a statement that binds `h` and
// then assumes a premise lifts both — the term parameter keeps the
// binder's name, and the Fact parameter takes the first of h, h2, …
// that no parameter holds. `func(a *Argument, h, x Term, h Fact)` binds
// one Go name twice.
func TestLift_AFactHandleIsNoBindersName(t *testing.T) {
	fun := core.MakeFun(dsl.NumType, dsl.NumType)
	h := ext.Var("h_0", fun).Core().(core.VarTerm)
	x := ext.Var("x_0", dsl.NumType).Core().(core.VarTerm)
	ante := ext.Var("p", core.TypeBool()).Core()
	e := &_Emitter{varIdent: map[_VarKey]string{}, varDecl: map[string]core.VarTerm{}}
	root, rest := &msNode{step: &proof.StepProto{}}, &msNode{step: &proof.StepProto{}}
	slots := []liftSlot{
		{forall: true, binder: "h", typ: fun, skolem: h},
		{forall: true, binder: "x", typ: dsl.NumType, skolem: x},
		{ante: ante},
		{ante: ante},
	}
	b := e.liftSlots(root, slots, rest, e.declSet())
	require.True(t, b.bound())
	assert.Equal(t, ", h *Arrow[Nat, Nat], x *Expr[Nat], h2, h3 Fact", b.signature())
}

// TestBinderComment_TheSuggestedSignatureIsGo: the signature a comment
// suggests above a closure the lift bound nothing for is one a landing
// can paste. A Fact parameter takes no binder's name, the receiver
// steps aside for a binder named a, a subscripted binder is spelled as
// a lifted signature spells it, and the signature stops before a
// binder Go cannot take beside the ones before it.
func TestBinderComment_TheSuggestedSignatureIsGo(t *testing.T) {
	e := &_Emitter{}
	for _, c := range []struct {
		slots []string
		want  string
	}{
		{[]string{"x"}, "func(a *Argument, x Term)"},
		{[]string{"h", "x", ""}, "func(a *Argument, h, x Term, h2 Fact)"},
		{[]string{"h", "a", "u", "v", ""}, "func(arg *Argument, h, a, u, v Term, h2 Fact)"},
		{[]string{"h", "h2", "", ""}, "func(a *Argument, h, h2 Term, h3, h4 Fact)"},
		{[]string{"x₁", "c'", ""}, "func(a *Argument, x1, cPrime Term, h Fact)"},
		{[]string{"x", "", "x", ""}, "func(a *Argument, x Term, h Fact)"},
		{[]string{"x", "func", "y"}, "func(a *Argument, x Term)"},
	} {
		got, ok := e.familyBinderSignature(c.slots)
		require.True(t, ok, "%v", c.slots)
		assert.Equal(t, c.want, got, "%v", c.slots)
	}
	_, ok := e.familyBinderSignature([]string{"type", "x"})
	assert.False(t, ok, "a signature that would bind nothing is no suggestion")
}

// TestLift_ASkolemAnotherSectionMintsKeepsBothSignatures: a lemma
// strips `∀x`, and the theorem strips `∀a` and, under a split, a `∀x`
// of its own, which mints the variable the lemma's strip minted. That
// variable is the lemma's parameter inside the lemma and a variable of
// the script in the theorem; each section's opening strip is still its
// closure's parameter, and the theorem's inner strip the one
// `StripQuant()` left.
func TestLift_ASkolemAnotherSectionMintsKeepsBothSignatures(t *testing.T) {
	env := makeTestEnv(t)
	num := dsl.NumType
	x, a := ext.Var("x", num), ext.Var("a", num)
	x0, a0 := ext.Var("x_0", num), ext.Var("a_0", num)
	strip := func() *proof.StepProto_StripQuant {
		return &proof.StepProto_StripQuant{StripQuant: &proof.HypIndexProto{}}
	}
	closed := func(pb *ext.PoolBuilder, goal core.Prop) *proof.StepProto {
		return &proof.StepProto{Goal: pb.PropRef(goal), Step: &proof.StepProto_TrivialSimplify{}}
	}

	// R is a predicate the statements leave free: a fixture's stand-in
	// for a constant, which keeps them from normalizing to ⊤.
	R := ext.Var("R", core.MakeFun(num, core.TypeBool()))
	lemmaGoal := prop.MakeProp(ext.ForAll(x)(R.Apply(x).Core()).Core())
	lemmaBody := prop.MakeProp(R.Apply(x0).Core())
	pb := ext.NewPoolBuilder()
	lemma := detailed(pb,
		&proof.StepProto{Goal: pb.PropRef(lemmaGoal), SubGoals: []*ext.HolPropProto{pb.PropRef(lemmaBody)}, Step: strip()},
		closed(pb, lemmaBody),
	)

	cited := ext.ForAll(x)(R.Apply(x).Core())
	inner := ext.ForAll(x)(R.Apply(x).And(R.Apply(a0)).Core())
	goal := prop.MakeProp(ext.ForAll(a)(ext.WrapTerm(cited.Core()).And(ext.ForAll(x)(R.Apply(x).And(R.Apply(a)).Core())).Core()).Core())
	opened := prop.MakeProp(ext.WrapTerm(cited.Core()).And(inner).Core())
	left, right := prop.MakeProp(cited.Core()), prop.MakeProp(inner.Core())
	stripped := prop.MakeProp(R.Apply(x0).And(R.Apply(a0)).Core())
	pb = ext.NewPoolBuilder()
	theorem := detailed(pb,
		&proof.StepProto{Goal: pb.PropRef(goal), SubGoals: []*ext.HolPropProto{pb.PropRef(opened)}, Step: strip()},
		&proof.StepProto{
			Goal:     pb.PropRef(opened),
			SubGoals: []*ext.HolPropProto{pb.PropRef(left), pb.PropRef(right)},
			Step:     &proof.StepProto_SplitConj{SplitConj: &emptypb.Empty{}},
		},
		&proof.StepProto{Goal: pb.PropRef(left), Step: &proof.StepProto_KnownThm{
			KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemmaGoal)}}},
		&proof.StepProto{Goal: pb.PropRef(right), SubGoals: []*ext.HolPropProto{pb.PropRef(stripped)}, Step: strip()},
		closed(pb, stripped),
	)

	src := emitMember(t, env, EmitOptions{Family: "nat_num/nat_order", FuncName: "Build_InnerSkolem"}, lemma, theorem).Source
	for _, want := range []string{
		"func(a *Argument, x *Expr[Nat]) {",
		"func(arg *Argument, a *Expr[Nat]) {",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	assert.Equal(t, 1, strings.Count(src, "StripQuant()"), "the theorem's inner strip alone is a step\n--- source: ---\n%s", src)
	assert.NotContains(t, src, "can bind them with", "--- source: ---\n%s", src)
}
