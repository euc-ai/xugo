// records.go — the standard resolution as one simplicial set.

package standard_resolution

import "github.com/euc-ai/xugo/library/registry"

// StandardResolutionDef — `standard_resolution(R, S, f)`: the terms of
// the standard resolution of S over R, with its faces and degeneracies.
var StandardResolutionDef = standardResolutionDefThm{family.Define(registry.DefEntry{
	Name:  "StandardResolutionDef",
	Key:   "prop_bd8618c3d4ca63aa",
	Const: "standard_resolution",
	Type:  "ring_ops(A) → ring_ops(B) → (A → B) → simplicial_ops(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). " +
			"    standard_resolution(R, S, f) = " +
			"    mk_simplicial(λn:num. standard_terms(R, S, n), " +
			"        standard_face(R, S, f), " +
			"        standard_degeneracy(R))",
	},
	Deps: []registry.EntryLike{StandardTermsDef, StandardFaceDef, StandardDegeneracyDef},
})}
