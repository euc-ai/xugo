// records.go — a field's operations and carrier, held in one value.

package field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// FieldOpsData — mk_field packs the ring operations, inverse, division and carrier.
var FieldOpsData = family.DefineData(registry.DataEntry{
	Name: "FieldOps", Type: "field_ops", Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{{
		Name: "mk_field",
		Args: []string{
			"A → A → A",
			"A",
			"A → A",
			"A → A → A",
			"A",
			"A → A → A",
			"A → A",
			"A → A → A",
			"set(A)",
		},
	}},
	Fields: []registry.DataField{
		{Name: "FieldAddDef", Const: "field_add", Field: "add", Symbol: "+"},
		{Name: "FieldZeroDef", Const: "field_zero", Field: "zero"},
		{Name: "FieldNegDef", Const: "field_neg", Field: "neg", Symbol: "-"},
		{Name: "FieldMulDef", Const: "field_mul", Field: "mul", Symbol: "*"},
		{Name: "FieldOneDef", Const: "field_one", Field: "one"},
		{Name: "FieldSubDef", Const: "field_sub", Field: "sub", Symbol: "-"},
		{Name: "FieldInvDef", Const: "field_inv", Field: "inv"},
		{Name: "FieldDivDef", Const: "field_div", Field: "div", Symbol: "/"},
		{Name: "FieldCarrierDef", Const: "field_carrier", Field: "carrier"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "FieldOpsInduction",
		Recursion:      "FieldOpsRecursion",
		Injective:      "MkFieldInjective",
		Extensionality: "FieldOpsEq",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		pairs.PairEq,
		pairs.Fst,
		pairs.Snd,
	},
})

// FieldRingDef — forget a field's inverse and division, retaining its ring.
var FieldRingDef = fieldRingDefThm{family.Define(registry.DefEntry{
	Name: "FieldRingDef",
	Key:  "prop_6409a0bef612b9ac", Const: "field_ring",
	Type: "field_ops(A) → ring_ops(A)",
	Equations: []string{
		"∀F:field_ops(A). field_ring(F) = mk_ring(F.add, F.zero, F.neg, F.mul, F.one, F.sub, F.carrier)",
	},
	Deps: []registry.EntryLike{
		FieldOpsData.Fields[0],
		FieldOpsData.Fields[1],
		FieldOpsData.Fields[2],
		FieldOpsData.Fields[3],
		FieldOpsData.Fields[4],
		FieldOpsData.Fields[5],
		FieldOpsData.Fields[8],
	},
})}

// RestrictFieldDef — keep a field's operations and replace its carrier.
var RestrictFieldDef = restrictFieldDefThm{family.Define(registry.DefEntry{
	Name: "RestrictFieldDef",
	Key:  "prop_67a893811dc7bc7b", Const: "restrict_field",
	Type: "field_ops(A) → set(A) → field_ops(A)",
	Equations: []string{
		"∀F:field_ops(A). ∀S:set(A). " +
			"    restrict_field(F, S) = mk_field(F.add, F.zero, F.neg, F.mul, F.one, F.sub, F.inv, F.div, S)",
	},
	Deps: []registry.EntryLike{
		FieldOpsData.Fields[0],
		FieldOpsData.Fields[1],
		FieldOpsData.Fields[2],
		FieldOpsData.Fields[3],
		FieldOpsData.Fields[4],
		FieldOpsData.Fields[5],
		FieldOpsData.Fields[6],
		FieldOpsData.Fields[7],
		FieldOpsData.Fields[8],
	},
})}

// RestrictFieldRing — restriction commutes with taking a field's ring: the
// ring of F restricted to S is the ring of F's restriction to S, both
// being F's six ring operations packed with S.
var RestrictFieldRing = restrictFieldRingThm{family.Add(registry.ProofEntry{
	Name: "RestrictFieldRing",
	Key:  "prop_9087e9f4296cc268",
	Build: family.Theorem("∀F:field_ops(A). ∀S:set(A). "+
		"    restrict_ring(field_ring(F), S) = field_ring(restrict_field(F, S))",
		func(a *Argument, F *Expr[FieldOps[A]], S *Expr[Set[A]]) {
			a.Show(
				"both sides are F's ring operations packed with S",
				Simp(Fwd(FieldRingDef), Fwd(RestrictFieldDef), Fwd(module_record.RestrictRingDef)),
				Refl())
		}),
})}

// FieldOnRing — a field is the field its ring's operations make with its
// inverse and division: the ring of F keeps F's sum, zero, negation,
// product, one, difference and carrier, so these packed again with F.inv
// and F.div rebuild F itself. It is the field a law over a ring R with an
// inverse and a division reads, at R the ring of F.
var FieldOnRing = fieldOnRingThm{family.Add(registry.ProofEntry{
	Name: "FieldOnRing",
	Key:  "prop_5a542babff267aff",
	Build: FieldOn.Law("field_on(mk_field(field_ring(F).add, "+
		"        field_ring(F).zero, "+
		"        field_ring(F).neg, "+
		"        field_ring(F).mul, "+
		"        field_ring(F).one, "+
		"        field_ring(F).sub, "+
		"        F.inv, "+
		"        F.div, "+
		"        field_ring(F).carrier))",
		func(a *Argument, field FieldFact[on.F]) {
			rebuilt := a.Have(
				"the ring's operations with F's inverse and division rebuild F",
				"mk_field(field_ring(F).add, "+
					"    field_ring(F).zero, "+
					"    field_ring(F).neg, "+
					"    field_ring(F).mul, "+
					"    field_ring(F).one, "+
					"    field_ring(F).sub, "+
					"    F.inv, "+
					"    F.div, "+
					"    field_ring(F).carrier) = "+
					"F",
				Simp(Fwd(FieldOpsData.Ext), Fwd(FieldRingDef)),
				Basic())
			a.Show(
				"so they make the field F",
				rebuilt.Rw(),
				By(field))
		}),
})}

// RestrictFieldRecords — a set read inside the restricted field K is read
// inside M: restricting the ring or the regular module of K to a set gives
// the restriction of M's, since a restriction keeps the operations and only
// replaces the carrier.
var RestrictFieldRecords = restrictFieldRecordsThm{family.Add(registry.ProofEntry{
	Name: "RestrictFieldRecords",
	Key:  "prop_e3939e647e38f17",
	Build: family.Theorem("∀M:field_ops(A). ∀K X:set(A). "+
		"    restrict_ring(field_ring(restrict_field(M, K)), X) = restrict_ring(field_ring(M), X) ∧ "+
		"    restrict_module(regular_module(field_ring(restrict_field(M, K))), X) = "+
		"    restrict_module(regular_module(field_ring(M)), X)",
		func(a *Argument, M *Expr[FieldOps[A]], K, X *Expr[Set[A]]) {
			a.Show(
				"the ring of K is M's ring restricted to K, and both sides are the same record over X",
				Simp(Rev(RestrictFieldRing)),
				Simp(
					Fwd(module_record.RestrictRingTwice),
					Fwd(module_record.RegularModuleDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(module_record.RestrictModuleDef)),
				Basic())
		}),
})}
