package emit

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// An earlier section with a different telescope cannot
// supply the recorded positional witnesses of a later section.
func TestBySectionInstance_PreservesStatedTelescope(t *testing.T) {
	parse := func(text string) core.Prop {
		p := dsl.ParsePropTextInScope(text, nil)
		require.Empty(t, p.Errors)
		return p.Prop
	}
	decoy := parse("∀f:(A → B). ∀P:(B → bool). ∀x:A. (∀y:B. P(y)) ⇒ P(f(x))")
	stated := parse("∀P:(B → bool). ∀f:(A → B). ∀x:A. (∀y:B. P(y)) ⇒ P(f(x))")
	install := core.PropTypeInst(stated,
		core.MakeTypeSubst(core.MakeVarType("A"), core.MakeVarType("B")),
		core.MakeTypeSubst(core.MakeVarType("B"), core.MakeVarType("A")))
	_, sub, _ := atTypesInstance(decoy, install)
	require.False(t, core.PropTypeInst(decoy, sub...).AlphaEquals(install))
	readers := []*ext.PoolReader{{}, {}, {}}
	e := &_Emitter{
		reader: readers[2], printer: &ext.GoTermPrinter{BareNames: true},
		sections: []*_SectionEmit{
			{reader: readers[0], goal: decoy, varName: "differentOrder"},
			{reader: readers[1], goal: stated, varName: "chosen"},
			{reader: readers[2], goal: install, varName: "consumer"},
		},
	}
	numberSections(e)
	expr, _, ok := e.bySectionInstanceExpr(install)
	require.True(t, ok)
	require.Equal(t, "ctx.AtTypeVars(chosen, TypeBinder.BindA[B](), TypeBinder.BindB[A]())", expr)
	require.False(t, e.byPremiseInstallPrinted(&proof.ByPremiseProto{}, install))
	for _, reader := range readers[:2] {
		e.reader = reader
		_, _, ok = e.bySectionInstanceExpr(install)
		require.False(t, ok, "no self or future section may supply the cite")
	}
}

// Explicit identity instances retain the earlier section's stated
// telescope and cannot resolve a self or forward citation.
func TestByIdentityInstance_PreservesStatedTelescope(t *testing.T) {
	parse := func(text string) core.Prop {
		p := dsl.ParsePropTextInScope(text, nil)
		require.Empty(t, p.Errors)
		return p.Prop
	}
	decoy := parse("∀f:(A → B). ∀P:(B → bool). ∀x:A. (∀y:B. P(y)) ⇒ P(f(x))")
	stated := parse("∀P:(B → bool). ∀f:(A → B). ∀x:A. (∀y:B. P(y)) ⇒ P(f(x))")
	consumer := parse("∀P:(B → bool). ∀y:B. P(y) ⇒ P(y)")
	readers := []*ext.PoolReader{{}, {}, {}}
	e := &_Emitter{
		reader: readers[2], printer: &ext.GoTermPrinter{BareNames: true},
		sections: []*_SectionEmit{
			{reader: readers[0], goal: decoy, varName: "differentOrder"},
			{reader: readers[1], goal: stated, varName: "chosen"},
			{reader: readers[2], goal: consumer, varName: "consumer"},
		},
	}
	numberSections(e)
	expr, reference, ok := e.byIdentityInstanceExpr(stated)
	require.True(t, ok)
	require.Equal(t, "ctx.AtTypeVars(chosen, TypeBinder.BindA[A](), TypeBinder.BindB[B]())", expr)
	require.True(t, reference.AlphaEquals(stated))
	for _, reader := range append(readers[:2:2], &ext.PoolReader{}) {
		e.reader = reader
		_, _, ok = e.byIdentityInstanceExpr(stated)
		require.False(t, ok, "only an earlier section of the active member may supply the cite")
	}
	_, ok = identityInstance(parse("∀p:bool. p ⇒ p"), parse("∀p:bool. p ⇒ p"))
	require.False(t, ok, "monomorphic citations cannot use AtTypes")
}

// TestSectionInstance_ALetterWithNoBindingKeepsThePositions: a section
// cited at another type is bound by its statement's letters,
// `ctx.AtTypeVars(lemma1, TypeBinder.BindA[Real]())`, which reads
// without the positional convention. A type variable TypeBinder has no
// method for, or an instance type no phantom spells, has no such
// spelling, and the cite keeps `ctx.AtTypes` and its positions.
func TestSectionInstance_ALetterWithNoBindingKeepsThePositions(t *testing.T) {
	e := &_Emitter{printer: &ext.GoTermPrinter{BareNames: true}}
	a, k := core.MakeVarType("A"), core.MakeVarType("K")
	real := ext.MakeType("real")
	opaque := ext.MakeType("zz_no_phantom")

	require.Equal(t, "ctx.AtTypeVars(lemma1, TypeBinder.BindA[Real]())",
		e.sectionInstExpr("lemma1", []core.TypeSubst{core.MakeTypeSubst(a, real)}))
	require.Equal(t, `ctx.AtTypes(lemma1, MakeType("real"))`,
		e.sectionInstExpr("lemma1", []core.TypeSubst{core.MakeTypeSubst(k, real)}),
		"K is outside the Bind alphabet")
	require.Equal(t, `ctx.AtTypes(lemma1, MakeType("zz_no_phantom"))`,
		e.sectionInstExpr("lemma1", []core.TypeSubst{core.MakeTypeSubst(a, opaque)}),
		"a type with no phantom has no Bind spelling")
}

// numberSections gives hand-built sections their member positions and
// statement keys, as decodeSections does.
func numberSections(e *_Emitter) {
	for i, s := range e.sections {
		s.index, s.outKey = i, s.goal.AlphaKey()
	}
}
