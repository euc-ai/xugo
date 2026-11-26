package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// The record reading at the refuter's own instantiations (the By stage's
// RecordParts step; prover/tactic, RecordPartsTactic). A set equation
// stated for every record, `zz_unit(r) = zz_r_carrier(r)`, is installed
// pointwise, so the goal `zz_unit(zz_shift(r)) = zz_r_carrier(r)` is
// closed only by extensionality over the instance at the record
// `zz_shift(r)` builds — an instance the refuter forms on its own, and
// whose projection `zz_r_carrier(zz_shift(r))` is a redex only the
// record equations reduce. The stage hands the refuter the part,
// `zz_r_carrier(zz_shift(r)) = zz_r_carrier(r)`, as an equation of the
// leaf, read through the record equations.

// recordPartsScript is the step-test env with a record `zz_mk_r` packing
// one set, its projection `zz_r_carrier`, a construction `zz_shift(r) =
// zz_mk_r(zz_r_carrier(r))` the projection reads through, and a set
// `zz_unit(r)` defined for every record as its carrier.
func recordPartsScript(t *testing.T) *Script {
	env := makeStepTestEnv()
	setT := core.MakeFun(ext.NumType, core.TypeBool())
	recT := core.MakeFun(ext.NumType, ext.NumType)
	consts := []struct {
		name string
		ty   core.HolType
	}{
		{"zz_mk_r", core.MakeFun(setT, recT)},
		{"zz_r_carrier", core.MakeFun(recT, setT)},
		{"zz_shift", core.MakeFun(recT, recT)},
		{"zz_unit", core.MakeFun(recT, setT)},
	}
	for _, c := range consts {
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(c.name, c.ty))
	}
	ctx := NewScript(env)
	for _, c := range consts {
		ctx.Const(c.name, c.ty)
	}
	projection := core.TestThm(ctx.MakePropText("∀c:(num → bool). zz_r_carrier(zz_mk_r(c)) = c").Conclusion())
	shift := core.TestThm(ctx.MakePropText("∀r:(num → num). zz_shift(r) = zz_mk_r(zz_r_carrier(r))").Conclusion())
	unit := core.TestThm(ctx.MakePropText("∀r:(num → num). zz_unit(r) = zz_r_carrier(r)").Conclusion())
	serveThm(ctx, "zz_r_carrier_mk", projection)
	serveThm(ctx, "zz_shift_def", shift)
	serveThm(ctx, "zz_unit_def", unit)
	tactic.InstallRecordNormal(
		[]tactic.RecordEquation{{Head: "zz_r_carrier", Constructor: "zz_mk_r", Entry: "zz_r_carrier_mk", Statement: projection.AsProp()}},
		[]tactic.RecordEquation{{Head: "zz_shift", Entry: "zz_shift_def", Statement: shift.AsProp()}},
		func(name string) *prop.PropWrapper {
			switch name {
			case "zz_r_carrier_mk":
				return prop.WrapProp(projection)
			case "zz_shift_def":
				return prop.WrapProp(shift)
			}
			panic("recordPartsScript: " + name + " is no record equation")
		})
	t.Cleanup(func() { tactic.InstallRecordNormal(nil, nil, nil) })
	return ctx
}

// The set equation at the built record closes by the refuter once the
// stage has installed the part equation. Without the stage the By is
// refused: the refuter's leaf is the pointwise law and the set equation
// at the built record, and nothing reduces the projection.
func TestRecordParts_SetEquationAtABuiltRecordClosesByTheRefuter(t *testing.T) {
	ctx := recordPartsScript(t)
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀r:(num → num). zz_unit(zz_shift(r)) = zz_r_carrier(r)",
			func(a *Argument, r *ext.Expr[natFun]) {
				a.Show("the unit of the shifted record is its carrier, which is the record's", By(depName("zz_unit_def")))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The tactic alone: a leaf that applies a projection to a bound
// variable gets, for the record value of that variable's type it
// spells, the part equation as one more hypothesis; a leaf that applies
// the projection to no bound variable is left as it is, since no
// instantiation the refuter forms spells the projection of the value.
func TestRecordParts_TacticInstallsThePartWhereALeafQuantifiesOverTheRecord(t *testing.T) {
	ctx := recordPartsScript(t)
	read := func(name string) *prop.PropWrapper { return prop.WrapProp(ctx.Env.LibraryThms[name]) }
	quantified := ctx.MakePropText("∀r:(num → num). ∀x:num. zz_unit(r, x) ⇔ zz_r_carrier(r, x) ⊢ zz_unit(zz_shift(r₀)) = zz_r_carrier(r₀)")
	sub := tactic.RecordPartsTactic(read)(quantified)
	require.NotNil(t, sub, "a leaf quantifying over the record type takes the part equation")
	require.Equal(t, 1, sub.Size())
	child := sub.ChildGoal(0)
	require.True(t, child.HasHyp(ctx.MakePropText("zz_r_carrier(zz_shift(r₀)) = zz_r_carrier(r₀)").Conclusion()),
		"the part equation is a hypothesis of the child:\n%s", prop.PrintProp(child))
	require.Equal(t, quantified.NumHyps()+1, child.NumHyps(), "one equation, for the one value and the one projection")

	unquantified := ctx.MakePropText("zz_unit(zz_shift(r₀)) = zz_r_carrier(zz_shift(r₀)) ⊢ zz_unit(zz_shift(r₀)) = zz_r_carrier(r₀)")
	require.Nil(t, tactic.RecordPartsTactic(read)(unquantified), "no projection of a bound variable: no instantiation spells the projection of the value")
}
