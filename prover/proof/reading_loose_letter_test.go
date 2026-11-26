package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// looseLetterTestEnv: a structure `readMon(op, e)` at the letter A and
// a law `∀op e. readMon(op, e) ⇒ ∀s:set(D). ∀F:(D → A). readSum(op, s, F)
// = e` whose index letter D no component fixes — module.ModuleSumIn's
// shape — beside two instances: one on the carrier D → ind, spelling the
// law's loose letter, and one on C → ind.
type looseLetterTestEnv struct {
	ctx          *Script
	law          core.ThmCert
	atD, atC     core.ThmCert
	plusD, zeroD *ext.TermWrapper
}

func makeLooseLetterTestEnv() *looseLetterTestEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	D, C := core.MakeVarType("D"), core.MakeVarType("C")
	opA := MakeFun(core.TypeA(), MakeFun(core.TypeA(), core.TypeA()))
	monA := MakeFun(opA, MakeFun(core.TypeA(), TypeBool))
	sumA := MakeFun(opA, MakeFun(MakeFun(D, TypeBool), MakeFun(MakeFun(D, core.TypeA()), core.TypeA())))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readMon", monA))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readSum", sumA))

	op := Var("op", opA)
	e := Var("e", core.TypeA())
	s := Var("s", MakeFun(D, TypeBool))
	F := Var("F", MakeFun(D, core.TypeA()))
	law := ext.ForAll(op, e)(ctx.Const("readMon", monA).Apply(op, e).Imply(
		ext.ForAll(s, F)(ctx.Const("readSum", sumA).Apply(op, s, F).Eq(e))))

	instance := func(carrier core.HolType, suffix string) (core.ThmCert, *ext.TermWrapper, *ext.TermWrapper) {
		opT := MakeFun(carrier, MakeFun(carrier, carrier))
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readPlus"+suffix, opT))
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("readZero"+suffix, carrier))
		plus := ctx.Const("readPlus"+suffix, opT)
		zero := ctx.Const("readZero"+suffix, carrier)
		mon := ctx.Const("readMon", MakeFun(opT, MakeFun(carrier, TypeBool)))
		return core.TestThm(mon.Apply(plus, zero).Core()), plus, zero
	}
	atD, plusD, zeroD := instance(MakeFun(D, TypeInd), "D")
	atC, _, _ := instance(MakeFun(C, TypeInd), "C")
	t := &looseLetterTestEnv{ctx: ctx, law: core.TestThm(law.Core()), atD: atD, atC: atC, plusD: plusD, zeroD: zeroD}
	serveThm(ctx, "zz_loose_law", t.law)
	serveThm(ctx, "zz_loose_at_d", atD)
	return t
}

// indexLetter reads the reading's leading binder `s:set(X)` and
// returns X, and the letter inside F's codomain `D → ind`.
func indexLetter(t *testing.T, reading Prop) (index, carrier core.VarType) {
	t.Helper()
	first := ext.MatchesFORALL(reading.Conclusion())
	require.False(t, first.IsZero(), "the reading begins at the law's own binders: %s", prop.PrintProp(reading))
	setOf := ext.MatchesFun(first.Var().Type())
	require.Len(t, setOf, 2, "s ranges over sets of a letter, got %s", ext.FormatType(first.Var().Type()))
	index, ok := setOf[0].(core.VarType)
	require.True(t, ok, "s ranges over sets of a letter, got %s", ext.FormatType(first.Var().Type()))
	second := ext.MatchesFORALL(first.Body())
	require.False(t, second.IsZero())
	fParts := ext.MatchesFun(second.Var().Type())
	require.Len(t, fParts, 3, "F's values are functions on the carrier, got %s", ext.FormatType(second.Var().Type()))
	carrier, ok = fParts[1].(core.VarType)
	require.True(t, ok)
	return index, carrier
}

// TestRead_LooseLetterIsKeptApartFromTheInstanceLetter: the law's loose
// index letter D, read at an instance whose carrier is D → ind, is not
// the instance's D. Before the rename the reading read `∀s:set(D).
// ∀F:(D → (D → ind))` with one D, and grounding s at a set of another
// type carried the carrier along.
func TestRead_LooseLetterIsKeptApartFromTheInstanceLetter(t *testing.T) {
	e := makeLooseLetterTestEnv()
	reading, err := readLawAt(e.law, e.atD, nil)
	require.NoError(t, err)
	index, carrier := indexLetter(t, reading)
	require.Equal(t, core.TypeName("D"), carrier.Name(), "the instance's letter is kept")
	require.NotEqual(t, carrier.Name(), index.Name(), "the law's loose letter is held apart from it: %s", prop.PrintProp(reading))

	// The control: an instance spelling no letter of the law's leaves the
	// loose letter as the law states it.
	control, err := readLawAt(e.law, e.atC, nil)
	require.NoError(t, err)
	index, carrier = indexLetter(t, control)
	require.Equal(t, core.TypeName("D"), index.Name())
	require.Equal(t, core.TypeName("C"), carrier.Name())
}

// TestRead_LooseLetterGroundsAtAnotherType: the Go cite — the reading at
// the chains grounded at an index set of another type,
// `module.ModuleSumIn.Read(chains).At(V, T)` — closes.
func TestRead_LooseLetterGroundsAtAnotherType(t *testing.T) {
	e := makeLooseLetterTestEnv()
	D := core.MakeVarType("D")
	V := ext.WrapTerm(Var("V", MakeFun(TypeBool, TypeBool)))
	T := ext.WrapTerm(Var("T", MakeFun(TypeBool, MakeFun(D, TypeInd))))
	sumAtD := e.ctx.Const("readSum", MakeFun(MakeFun(MakeFun(D, TypeInd), MakeFun(MakeFun(D, TypeInd), MakeFun(D, TypeInd))),
		MakeFun(MakeFun(TypeBool, TypeBool), MakeFun(MakeFun(TypeBool, MakeFun(D, TypeInd)), MakeFun(D, TypeInd)))))
	sec := e.ctx.Section(prop.MakeProp(sumAtD.Apply(e.plusD, V, T).Eq(e.zeroD).Core()))
	sec.Do(Derive(func(arg *Argument) {
		arg.Show("the sum law read at the carrier D → ind, at an index set of booleans",
			By(Read(depName("zz_loose_law"), depName("zz_loose_at_d")).At(V, T)))
	}))
	require.True(t, sec.Proved())
}
