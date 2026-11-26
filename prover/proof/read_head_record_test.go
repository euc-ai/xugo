package proof

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// A law stated at a structure record spells its operations as
// projections applied to the record binder, and a goal at a concrete
// instance spells them by the parts the instance normal form computes:
// `∀R:zz_ops(A). zz_monoid(R) ⇒ ∀x. R.op(R.unit, x) = x` against
// `g(c, a) = a`, where `zz_ind_ops = zz_mk_ops(g, c, le)`. The
// projection applied to the binder has no rigid head of its own; the
// pre-read reads it at the record the structure fact offers, and Read
// pins R from that fact before matching the conclusion read at it.
// The toy record stands for every record the doors install: nothing
// here names a ring.
func TestReadHead_RecordLawReadsAtTheInstanceAFactOffers(t *testing.T) {
	ind, bool_ := TypeInd, core.TypeBool()
	A := core.MakeVarType("A")
	opsMeta := core.MakeMetaType("zz_ops", 1)
	ops := func(t core.HolType) core.HolType { return core.MakeCompositeType(opsMeta, t) }
	op := func(t core.HolType) core.HolType { return core.MakeFun(t, t, t) }
	rel := func(t core.HolType) core.HolType { return core.MakeFun(t, t, bool_) }
	constant := func(name string, abstract core.HolType) func(core.HolType) *ext.TermWrapper {
		meta := core.MakeConstMeta(name, abstract)
		return func(at core.HolType) *ext.TermWrapper { return ext.Const(meta, at) }
	}
	mkOps := constant("zz_mk_ops", core.MakeFun(op(A), A, rel(A), ops(A)))
	opsOp := constant("zz_ops_op", core.MakeFun(ops(A), op(A)))
	opsUnit := constant("zz_ops_unit", core.MakeFun(ops(A), A))
	opsLe := constant("zz_ops_le", core.MakeFun(ops(A), rel(A)))
	monoid := constant("zz_monoid", core.MakeFun(ops(A), bool_))
	indOps := constant("zz_ind_ops", ops(ind))(ops(ind))
	g := constant("zz_g", op(ind))(op(ind))
	h := constant("zz_h", op(ind))(op(ind))
	le := constant("zz_le", rel(ind))(rel(ind))
	c := constant("zz_c", ind)(ind)

	f, e, r := ext.Var("f", op(A)), ext.Var("e", A), ext.Var("r", rel(A))
	packed := mkOps(core.MakeFun(op(A), A, rel(A), ops(A))).Apply(f, e, r)
	projection := func(name string, p *ext.TermWrapper, part *ext.TermWrapper) tactic.RecordEquation {
		return tactic.RecordEquation{Head: name, Constructor: "zz_mk_ops", Entry: "zz." + name,
			Statement: prop.MakeProp(ext.ForAll(f, e, r)(p.Apply(packed).Eq(part)))}
	}
	tactic.InstallRecordNormal([]tactic.RecordEquation{
		projection("zz_ops_op", opsOp(core.MakeFun(ops(A), op(A))), f),
		projection("zz_ops_unit", opsUnit(core.MakeFun(ops(A), A)), e),
		projection("zz_ops_le", opsLe(core.MakeFun(ops(A), rel(A))), r),
	}, []tactic.RecordEquation{{Head: "zz_ind_ops", Entry: "zz.IndOps",
		Statement: prop.MakeProp(indOps.Eq(mkOps(core.MakeFun(op(ind), ind, rel(ind), ops(ind))).Apply(g, c, le)))}}, nil)
	t.Cleanup(func() { tactic.InstallRecordNormal(nil, nil, nil) })

	R, x, a := ext.Var("R", ops(A)), ext.Var("x", A), ext.Var("a", ind)
	isMonoid := monoid(core.MakeFun(ops(A), bool_)).Apply(R)
	unit := opsUnit(core.MakeFun(ops(A), A)).Apply(R)
	law := StatedHeadOf(prop.MakeProp(ext.ForAll(R)(isMonoid.Imply(ext.ForAll(x)(
		opsOp(core.MakeFun(ops(A), op(A))).Apply(R, unit, x).Eq(x))))))
	fact := monoid(core.MakeFun(ops(ind), bool_)).Apply(indOps).Core()
	facts := &FactSource{ByHead: map[core.TermName][]core.Term{"zz_monoid": {fact}}, Structures: map[core.TermName]bool{"zz_monoid": true}}
	goal := prop.MakeProp(g.Apply(c, a).Eq(a))

	atFact := HeadGoalOf(goal, facts)
	require.True(t, law.MayRead(atFact), "the instance the fact offers computes R.op to g and R.unit to c")
	reading, ok := law.Read(atFact)
	require.True(t, ok)
	require.Len(t, reading.Witnesses, 2)
	assert.Equal(t, "R", reading.Witnesses[0].Binder)
	assert.True(t, reading.Witnesses[0].Witness.AlphaEquals(indOps.Core()), "R pinned from the fact: %s", ext.PrintTerm(reading.Witnesses[0].Witness))
	assert.Equal(t, "a", ext.PrintTerm(reading.Witnesses[1].Witness))
	require.Len(t, reading.Premises, 1)
	assert.True(t, reading.Premises[0].Term.AlphaEquals(fact))
	assert.False(t, reading.Premises[0].Resident)

	withHyp := HeadGoalOf(prop.MakeProp(goal.Conclusion(), fact), nil)
	reading, ok = law.Read(withHyp)
	require.True(t, ok, "a resident structure fact offers the record too")
	assert.True(t, reading.Premises[0].Resident)

	assert.False(t, law.MayRead(HeadGoalOf(goal, nil)), "nothing offers a record")

	// At an abstract record the goal spells the projections themselves,
	// and the conclusion as stated meets it.
	S := ext.Var("S", ops(ind))
	atS := func(p func(core.HolType) *ext.TermWrapper, part core.HolType) *ext.TermWrapper {
		return p(core.MakeFun(ops(ind), part)).Apply(S)
	}
	abstract := prop.MakeProp(atS(opsOp, op(ind)).Apply(atS(opsUnit, ind), a).Eq(a).Core(),
		monoid(core.MakeFun(ops(ind), bool_)).Apply(S).Core())
	reading, ok = law.Read(HeadGoalOf(abstract, nil))
	require.True(t, ok)
	assert.Equal(t, "S", ext.PrintTerm(reading.Witnesses[0].Witness))
	assert.True(t, reading.Premises[0].Resident)
	other := HeadGoalOf(prop.MakeProp(h.Apply(c, a).Eq(a)), facts)
	assert.False(t, law.MayRead(other), "the instance computes R.op to g, not h: declined before any instance is built")
	_, ok = law.Read(other)
	assert.False(t, ok)

	// A reading topped by a projection the instance decides is keyed
	// wild — its head is the part's — and reads at the part.
	reflexive := StatedHeadOf(prop.MakeProp(ext.ForAll(R)(isMonoid.Imply(ext.ForAll(x)(
		opsLe(core.MakeFun(ops(A), rel(A))).Apply(R, x, x))))))
	assert.Equal(t, []RigidHead{{}}, reflexive.Rigids())
	reading, ok = reflexive.Read(HeadGoalOf(prop.MakeProp(le.Apply(a, a).Core()), facts))
	require.True(t, ok)
	assert.Equal(t, "a", ext.PrintTerm(reading.Witnesses[1].Witness))
}
