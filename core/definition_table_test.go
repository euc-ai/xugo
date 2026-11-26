package core_test

// A name is defined once, probed from outside: this is an external test
// package, so it holds exactly what any importing package holds.
//
// A constant is identified by its name and a type by its name and
// arity. Two definitions under one name are therefore two axioms about
// one object, and from `c = t₁` and `c = t₂` follows `t₁ = t₂` for any
// two terms of a type. Each test asks a definition door for a name that
// is taken and checks that the door panics, or asks it for the
// definition the name already has and checks that it hands back what
// the first call made.
//
// Definitions form no cycle. A constant or a type is made by hand under
// any name, so a definition's term may mention the name it defines, or
// a name whose own definition leads back to it: `c = ¬c` is such a
// definition, and it proves anything. The tests of the second half make
// such a term and check that the door panics, and that a name mentioned
// before it is defined is still definable where no cycle closes.

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// booleanIdentity and booleanTruth are two closed terms of type
// bool → bool that are not α-equal: λx. x and λx. ⊤, with ⊤ spelled as
// an equation of the identity with itself.
func booleanIdentity() core.Term {
	x := core.Var("x", core.TypeBool())
	return core.Abs(x, x)
}

func booleanTruth() core.Term {
	x := core.Var("x", core.TypeBool())
	return core.Abs(x, core.Refl(booleanIdentity()).Conclusion())
}

// truth is ⊤, spelled as an equation of the identity with itself.
func truth() core.Term { return core.Refl(booleanIdentity()).Conclusion() }

// byHand is a constant of type bool that no definition introduced.
func byHand(name string) core.Term {
	return core.MakeConstTerm(core.MakeConstMeta(name, core.TypeBool()), core.TypeBool())
}

// typeByHand is a type of arity zero that no definition introduced.
func typeByHand(name string) core.HolType {
	return core.MakeCompositeType(core.MakeMetaType(name, 0))
}

// overType is ⊤ spelled over the type t: the identity on t equals
// itself.
func overType(t core.HolType) core.Term {
	y := core.Var("y", t)
	return core.Refl(core.Abs(y, y)).Conclusion()
}

// panicOf is what f panics with, as text.
func panicOf(t *testing.T, f func()) (message string) {
	t.Helper()
	defer func() {
		r := recover()
		require.NotNil(t, r, "no panic")
		message = fmt.Sprint(r)
	}()
	f()
	return ""
}

// inhabited is a source for NewTypeDef: predicate holds of witness, on
// a test's word.
func inhabited(predicate, witness core.Term) core.ThmCert {
	return core.TestThm(core.Apply(predicate, witness))
}

func TestNewConstDefRefusesASecondDefinitionOfAName(t *testing.T) {
	const name = "zz_definition_table_twice"
	core.NewConstDef(booleanIdentity(), name)
	require.Panics(t, func() { core.NewConstDef(booleanTruth(), name) },
		"a second term of the same type")
	require.Panics(t, func() { core.NewConstDef(core.Refl(booleanIdentity()).Conclusion(), name) },
		"a term of another type")
}

func TestNewConstDefOfTheSameTermReturnsTheFirstConstant(t *testing.T) {
	const name = "zz_definition_table_same"
	first := core.NewConstDef(booleanIdentity(), name)
	y := core.Var("y", core.TypeBool())
	second := core.NewConstDef(core.Abs(y, y), name)
	require.True(t, first.Meta() == second.Meta(), "the α-equal definition made a constant of its own")
	require.True(t, first.DefThm().AlphaEquals(second.DefThm()))
}

func TestNewConstDefRefusesTheKernelsOwnConstants(t *testing.T) {
	a := core.TypeA()
	x, y := core.Var("x", a), core.Var("y", a)
	truth := core.Refl(booleanIdentity()).Conclusion()
	require.Panics(t, func() {
		core.NewConstDef(core.Abs(x, core.Abs(y, truth)), core.MetaEq().Name())
	}, "equality")

	p := core.Var("p", core.MakeFun(a, core.TypeBool()))
	require.Panics(t, func() {
		core.NewConstDef(core.Abs(p, core.Hilbert(x, core.Apply(p, x))), core.MetaHilbert().Name())
	}, "ε")
}

func TestNewTypeDefRefusesASecondDefinitionOfAName(t *testing.T) {
	truth := core.Refl(booleanIdentity()).Conclusion()
	everything := booleanTruth()
	x := core.Var("x", core.TypeBool())
	onlyTruth := core.Abs(x, core.Eq(x, truth))

	const typeName, abs, rep = "zz_definition_table_type", "zz_definition_table_abs", "zz_definition_table_rep"
	core.NewTypeDef(inhabited(everything, truth), typeName, abs, rep)

	require.Panics(t, func() {
		core.NewTypeDef(inhabited(onlyTruth, truth), typeName, abs, rep)
	}, "another predicate under the type's name")
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(everything, core.Var("w", core.TypeBool())), typeName, abs, rep)
	}, "another witness under the type's name")
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(everything, truth), typeName, abs+"_2", rep+"_2")
	}, "other constants under the type's name")
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(everything, truth), typeName+"_2", abs, rep+"_2")
	}, "another type under the abs constant's name")
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(everything, truth), typeName+"_2", abs+"_2", rep)
	}, "another type under the rep constant's name")
	require.Panics(t, func() { core.NewConstDef(booleanIdentity(), abs) },
		"a constant definition under the abs constant's name")
	require.Panics(t, func() { core.NewConstDef(booleanIdentity(), rep) },
		"a constant definition under the rep constant's name")
}

func TestNewTypeDefOfTheSameSourceReturnsTheFirstType(t *testing.T) {
	truth := core.Refl(booleanIdentity()).Conclusion()
	const typeName, abs, rep = "zz_definition_table_same_type", "zz_definition_table_same_abs", "zz_definition_table_same_rep"
	firstType, firstAbs, firstRep := core.NewTypeDef(inhabited(booleanTruth(), truth), typeName, abs, rep)
	secondType, secondAbs, secondRep := core.NewTypeDef(inhabited(booleanTruth(), truth), typeName, abs, rep)
	require.True(t, firstType == secondType, "the same source made a type of its own")
	require.True(t, firstAbs.Meta() == secondAbs.Meta(), "the same source made an abs constant of its own")
	require.True(t, firstRep.Meta() == secondRep.Meta(), "the same source made a rep constant of its own")
}

func TestNewTypeDefRefusesNamesInUse(t *testing.T) {
	truth := core.Refl(booleanIdentity()).Conclusion()
	source := inhabited(booleanTruth(), truth)

	for _, own := range []core.MetaType{core.MetaTypeBool(), core.MetaTypeFun()} {
		require.Panics(t, func() {
			core.NewTypeDef(source, own.Name(), "zz_definition_table_own_abs", "zz_definition_table_own_rep")
		}, "the kernel's own type %s", own.Name())
	}

	const defined = "zz_definition_table_defined"
	core.NewConstDef(booleanIdentity(), defined)
	require.Panics(t, func() {
		core.NewTypeDef(source, "zz_definition_table_over_abs", defined, "zz_definition_table_over_abs_rep")
	}, "an abs constant under a defined constant's name")
	require.Panics(t, func() {
		core.NewTypeDef(source, "zz_definition_table_over_rep", "zz_definition_table_over_rep_abs", defined)
	}, "a rep constant under a defined constant's name")
	require.Panics(t, func() {
		core.NewTypeDef(source, "zz_definition_table_over_eq", core.MetaEq().Name(), "zz_definition_table_over_eq_rep")
	}, "an abs constant under equality's name")
	require.Panics(t, func() {
		core.NewTypeDef(source, "zz_definition_table_one_name", "zz_definition_table_both", "zz_definition_table_both")
	}, "one name for both constants")
}

func TestNewConstDefRefusesATermThatMentionsTheNameItDefines(t *testing.T) {
	const name = "zz_definition_cycle_self"
	message := panicOf(t, func() { core.NewConstDef(core.Eq(byHand(name), truth()), name) })
	require.Contains(t, message, `it mentions constant "zz_definition_cycle_self"`)
}

// A refused definition leaves nothing behind: the name is still free.
func TestNewConstDefDefinesANameAfterRefusingIt(t *testing.T) {
	const name = "zz_definition_cycle_then_defined"
	require.Panics(t, func() { core.NewConstDef(core.Eq(byHand(name), truth()), name) })
	defined := core.NewConstDef(truth(), name)
	require.True(t, defined.DefThm().Proved())
}

func TestNewConstDefRefusesADefinitionThatClosesACycle(t *testing.T) {
	const first, second, third = "zz_definition_cycle_1", "zz_definition_cycle_2", "zz_definition_cycle_3"
	core.NewConstDef(core.Eq(byHand(second), truth()), first)
	core.NewConstDef(core.Eq(byHand(third), truth()), second)
	message := panicOf(t, func() { core.NewConstDef(core.Eq(byHand(first), truth()), third) })
	require.Contains(t, message,
		`it mentions constant "zz_definition_cycle_1", whose definition mentions constant "zz_definition_cycle_2", `+
			`whose definition mentions constant "zz_definition_cycle_3"`)
}

func TestNewConstDefAdmitsANameMentionedBeforeItIsDefined(t *testing.T) {
	const earlier, later = "zz_definition_forward_earlier", "zz_definition_forward_later"
	core.NewConstDef(core.Eq(byHand(later), truth()), earlier)
	defined := core.NewConstDef(truth(), later)
	require.True(t, defined.DefThm().Proved())

	// Defining the earlier name again as the same term is still the
	// first constant, though a definition now leads to the name.
	again := core.NewConstDef(truth(), later)
	require.True(t, defined.Meta() == again.Meta())
}

func TestNewTypeDefRefusesAPredicateThatMentionsWhatItDefines(t *testing.T) {
	x := core.Var("x", core.TypeBool())

	const ownType = "zz_definition_cycle_own_type"
	y := core.Var("y", typeByHand(ownType))
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(core.Abs(y, truth()), y), ownType, ownType+"_abs", ownType+"_rep")
	}, "the type in its own predicate")

	const ownAbs = "zz_definition_cycle_own_abs"
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(core.Abs(x, byHand(ownAbs)), truth()), ownAbs+"_type", ownAbs, ownAbs+"_rep")
	}, "the abs constant in the predicate")

	const ownRep = "zz_definition_cycle_own_rep"
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(core.Abs(x, byHand(ownRep)), truth()), ownRep+"_type", ownRep+"_abs", ownRep)
	}, "the rep constant in the predicate")
}

func TestDefinitionsRefuseACycleThroughAType(t *testing.T) {
	x := core.Var("x", core.TypeBool())

	// The type's predicate mentions a constant, whose definition then
	// mentions the type.
	const typeFirst, constantSecond = "zz_definition_cycle_type_first", "zz_definition_cycle_constant_second"
	core.NewTypeDef(inhabited(core.Abs(x, byHand(constantSecond)), truth()), typeFirst, typeFirst+"_abs", typeFirst+"_rep")
	message := panicOf(t, func() { core.NewConstDef(overType(typeByHand(typeFirst)), constantSecond) })
	require.Contains(t, message, `it mentions type "zz_definition_cycle_type_first", whose definition mentions constant "zz_definition_cycle_constant_second"`)

	// The constant's definition mentions a type, whose predicate then
	// mentions the constant.
	const constantFirst, typeSecond = "zz_definition_cycle_constant_first", "zz_definition_cycle_type_second"
	core.NewConstDef(overType(typeByHand(typeSecond)), constantFirst)
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(core.Abs(x, byHand(constantFirst)), truth()), typeSecond, typeSecond+"_abs", typeSecond+"_rep")
	})

	// A constant's definition mentions an abs constant, whose type's
	// predicate then mentions the constant.
	const constantOverAbs, absSecond = "zz_definition_cycle_constant_over_abs", "zz_definition_cycle_abs_second"
	core.NewConstDef(core.Eq(byHand(absSecond), truth()), constantOverAbs)
	require.Panics(t, func() {
		core.NewTypeDef(inhabited(core.Abs(x, byHand(constantOverAbs)), truth()), absSecond+"_type", absSecond, absSecond+"_rep")
	})
}
