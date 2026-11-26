// Support closes the nonzero locus inside the space carrier.

package function_support

import (
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

var SupportDef = supportDefThm{family.Define(registry.DefEntry{
	Name:  "SupportDef",
	Key:   "prop_476132642e0c10da",
	Const: "function_support",
	Type:  "set(set(A)) → B → (A → B) → set(A)",
	Reading: "The distinguished value z need not belong to an algebraic structure. " +
		"Values outside the space carrier are ignored. The carrier guard ensures that " +
		"support is a closed subset of the space when T is a topology, even though " +
		"closure of an arbitrary external set need not be. No continuity of f is required.",
	Equations: []string{
		"∀T:set(set(A)). ∀z:B. ∀f:(A → B). " +
			"    function_support(T, z, f) = closure(T, {x:A | x ∈ ⋃T ∧ f(x) ≠ z})",
	},
})}
