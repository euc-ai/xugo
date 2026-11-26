// forget.go — the additive group of a ring or a module.

package module_record

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/registry"
)

// AdditiveGroupDef — retain a ring's addition, zero, negation and carrier.
var AdditiveGroupDef = additiveGroupDefThm{family.Define(registry.DefEntry{
	Name: "AdditiveGroupDef",
	Key:  "prop_9b780d89d55b8797", Const: "additive_group", Type: "ring_ops(A) → group_ops(A)",
	Equations: []string{"∀R:ring_ops(A). additive_group(R) = mk_group(R.add,R.zero,R.neg,R.carrier)"},
	Deps:      []registry.EntryLike{RingAddDef, RingZeroDef, RingNegDef, RingCarrierDef},
})}

// ModuleAdditiveGroupDef — retain a module's addition, zero, negation and carrier.
var ModuleAdditiveGroupDef = moduleAdditiveGroupDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleAdditiveGroupDef",
	Key:   "prop_88f0a9c6a252778c",
	Const: "module_additive_group",
	Type:  "module_ops(A,B) → group_ops(B)",
	Equations: []string{
		"∀M:module_ops(A,B). module_additive_group(M) = mk_group(M.add,M.zero,M.neg,M.carrier)",
	},
	Deps: []registry.EntryLike{ModAddDef, ModZeroDef, ModNegDef, ModCarrierDef},
})}
