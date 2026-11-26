package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A law stated in the standard form — every binder in front, the
// structure's predicate the first hypothesis — reads at an instance as
// its telescope `∀comps. S(comps) ⇒ ∀xs. …` reads (prop.LawTelescope).

func TestLawTelescope_StandardLawReadsAsItsTelescope(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	op, unit, x := Var("op", opA), Var("e", core.TypeA()), Var("x", core.TypeA())
	mon := e.ctx.Const("readMon", monA).Apply(op, unit)

	// ∀op e x. mon(op, e) ⇒ op(e, x) = x
	alone := ext.ForAll(op, unit, x)(mon.Imply(ext.WrapTerm(op).Apply(unit, x).Eq(x))).Core()
	telescope := prop.LawTelescope(prop.MakeProp(alone))
	require.True(t, telescope.Conclusion().AlphaEquals(e.law.Conclusion()),
		"the telescope of the standard law is the door-form law; got %s", prop.PrintProp(telescope))
	serveThm(e.ctx, "zz_read_std_law", core.TestThm(alone))
	x0 := Var("x", TypeInd)
	got := resolveLemmaTarget("test", e.ctx, Read(depName("zz_read_std_law"), depName("zz_read_inst")))
	require.True(t, got.Conclusion().AlphaEquals(ext.ForAll(x0)(e.plus.Apply(e.zero, x0).Eq(x0)).Core()),
		"reading reads %s", prop.PrintProp(got))

	// ∀op e x. mon(op, e) ∧ op(x, e) = x ⇒ op(e, x) = x: the other
	// hypothesis stays the reading's.
	guarded := ext.ForAll(op, unit, x)(mon.And(ext.WrapTerm(op).Apply(x, unit).Eq(x)).Imply(ext.WrapTerm(op).Apply(unit, x).Eq(x))).Core()
	serveThm(e.ctx, "zz_read_std_guarded", core.TestThm(guarded))
	got = resolveLemmaTarget("test", e.ctx, Read(depName("zz_read_std_guarded"), depName("zz_read_inst")))
	want := ext.ForAll(x0)(e.plus.Apply(x0, e.zero).Eq(x0).Imply(e.plus.Apply(e.zero, x0).Eq(x0))).Core()
	require.True(t, got.Conclusion().AlphaEquals(want), "reading reads %s", prop.PrintProp(got))
	require.Zero(t, got.NumHyps())
}

// A statement whose first hypothesis applies no constant to its leading
// binders is no law: it is returned as it is.
func TestLawTelescope_LeavesOtherStatements(t *testing.T) {
	p, q := Var("p", TypeBool), Var("q", TypeBool)
	stmt := prop.MakeProp(ext.ForAll(p, q)(ext.WrapTerm(p).And(q).Imply(p)).Core())
	require.True(t, prop.LawTelescope(stmt).Conclusion().AlphaEquals(stmt.Conclusion()))
}

// A reading at an instance takes the hypothesis that states the
// instance's predicate wherever it stands among the hypotheses.
func TestLawTelescopeAt_TakesTheInstancesHypothesisWhereverItStands(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	op, unit, x := Var("op", opA), Var("e", core.TypeA()), Var("x", core.TypeA())
	mon := e.ctx.Const("readMon", monA).Apply(op, unit)
	right := ext.WrapTerm(op).Apply(x, unit).Eq(x)
	left := ext.WrapTerm(op).Apply(unit, x).Eq(x)

	// ∀op e x. op(x, e) = x ∧ mon(op, e) ⇒ op(e, x) = x
	law := ext.ForAll(op, unit, x)(right.And(mon).Imply(left)).Core()
	instance := e.ctx.Const("readMon", MakeFun(MakeFun(TypeInd, MakeFun(TypeInd, TypeInd)), MakeFun(TypeInd, TypeBool))).Apply(e.plus, e.zero).Core()
	got := prop.LawTelescopeAt(prop.MakeProp(law), instance)
	want := ext.ForAll(op, unit)(mon.Imply(ext.ForAll(x)(right.Imply(left)))).Core()
	require.True(t, got.Conclusion().AlphaEquals(want), "got %s", prop.PrintProp(got))
}

// A component an earlier reading fixed stays an argument of the
// hypothesis the next reading takes: the hypothesis is no constant
// applied to binders alone, and the instance still picks it.
func TestRead_HypothesisWithAFixedComponent(t *testing.T) {
	e := makeReadingTestEnv()
	u, x := Var("u", TypeInd), Var("x", TypeInd)
	monInd := e.ctx.Const("readMon", MakeFun(MakeFun(TypeInd, MakeFun(TypeInd, TypeInd)), MakeFun(TypeInd, TypeBool)))
	right := e.plus.Apply(x, u).Eq(x)
	left := e.plus.Apply(u, x).Eq(x)
	// ∀u x. mon(plus, u) ∧ plus(x, u) = x ⇒ plus(u, x) = x
	law := ext.ForAll(u, x)(monInd.Apply(e.plus, u).And(right).Imply(left)).Core()
	require.True(t, prop.LawTelescope(prop.MakeProp(law)).Conclusion().AlphaEquals(law),
		"without an instance no hypothesis is a constant applied to binders alone")
	serveThm(e.ctx, "zz_read_fixed_law", core.TestThm(law))
	got := resolveLemmaTarget("test", e.ctx, Read(depName("zz_read_fixed_law"), depName("zz_read_inst")))
	want := ext.ForAll(x)(e.plus.Apply(x, e.zero).Eq(x).Imply(e.plus.Apply(e.zero, x).Eq(x))).Core()
	require.True(t, got.Conclusion().AlphaEquals(want), "reading reads %s", prop.PrintProp(got))
}

// A hypothesis written as a parenthesized conjunction stays one piece
// of the telescope's inner antecedent, wherever it stands.
func TestLawTelescope_ConjunctionPieceStaysWhole(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	op, unit, x := Var("op", opA), Var("e", core.TypeA()), Var("x", core.TypeA())
	mon := e.ctx.Const("readMon", monA).Apply(op, unit)
	right := ext.WrapTerm(op).Apply(x, unit).Eq(x)
	left := ext.WrapTerm(op).Apply(unit, x).Eq(x)
	idem := ext.WrapTerm(op).Apply(unit, unit).Eq(unit)

	// ∀op e x. mon(op, e) ∧ (op(x, e) = x ∧ op(e, x) = x) ∧ op(e, e) = e ⇒ op(e, x) = x
	pair := right.And(left)
	law := ext.ForAll(op, unit, x)(mon.And(pair).And(idem).Imply(left)).Core()
	got := prop.LawTelescope(prop.MakeProp(law))
	want := ext.ForAll(op, unit)(mon.Imply(ext.ForAll(x)(pair.And(idem).Imply(left)))).Core()
	require.True(t, got.Conclusion().AlphaEquals(want), "got %s", prop.PrintProp(got))
}

// A law grounded at a prefix of its binders reads as the telescope at
// that prefix: the hypotheses about the prefix alone ahead, the rest
// behind the remaining binders.
func TestPrefixTelescope(t *testing.T) {
	e := makeReadingTestEnv()
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	op, unit, x := Var("op", opA), Var("e", core.TypeA()), Var("x", core.TypeA())
	mon := e.ctx.Const("readMon", monA).Apply(op, unit)
	right := ext.WrapTerm(op).Apply(x, unit).Eq(x)
	idem := ext.WrapTerm(op).Apply(unit, unit).Eq(unit)
	left := ext.WrapTerm(op).Apply(unit, x).Eq(x)
	// ∀op e x. mon(op, e) ∧ op(x, e) = x ∧ op(e, e) = e ⇒ op(e, x) = x
	law := prop.MakeProp(ext.ForAll(op, unit, x)(mon.And(right).And(idem).Imply(left)).Core())
	got := prop.PrefixTelescope(law, 2)
	want := ext.ForAll(op, unit)(mon.And(idem).Imply(ext.ForAll(x)(right.Imply(left)))).Core()
	require.True(t, got.Conclusion().AlphaEquals(want), "got %s", prop.PrintProp(got))
	// Grounding every binder, or none, reads the law as it is.
	require.True(t, prop.PrefixTelescope(law, 3).Conclusion().AlphaEquals(law.Conclusion()))
	require.True(t, prop.PrefixTelescope(law, 0).Conclusion().AlphaEquals(law.Conclusion()))
}
