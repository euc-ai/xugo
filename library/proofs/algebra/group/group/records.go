// records.go — a group's operations and carrier, held in one value.

package group

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// GroupOpsData — mk_group packs the product, identity, inverse and carrier.
var GroupOpsData = family.DefineData(registry.DataEntry{
	Name: "GroupOps", Type: "group_ops", Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_group", Args: []string{"A → A → A", "A", "A → A", "set(A)"}},
	},
	Fields: []registry.DataField{
		{Name: "GroupMulDef", Const: "group_mul", Field: "mul", Symbol: "*"},
		{Name: "GroupOneDef", Const: "group_one", Field: "one"},
		{Name: "GroupInvDef", Const: "group_inv", Field: "inv"},
		{Name: "GroupCarrierDef", Const: "group_carrier", Field: "carrier"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "GroupOpsInduction",
		Recursion:      "GroupOpsRecursion",
		Injective:      "MkGroupInjective",
		Extensionality: "GroupOpsEq",
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

// RestrictGroupDef — keep a group's operations and replace its carrier.
var RestrictGroupDef = restrictGroupDefThm{family.Define(registry.DefEntry{
	Name: "RestrictGroupDef",
	Key:  "prop_b1fc582e1deb053f", Const: "restrict_group",
	Type: "group_ops(A) → set(A) → group_ops(A)",
	Equations: []string{
		"∀G:group_ops(A). ∀S:set(A). restrict_group(G, S) = mk_group(G.mul, G.one, G.inv, S)",
	},
	Deps: []registry.EntryLike{
		GroupOpsData.Fields[0],
		GroupOpsData.Fields[1],
		GroupOpsData.Fields[2],
		GroupOpsData.Fields[3],
	},
})}
