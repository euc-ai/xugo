package ideal_class_group

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// InvertibleIdealsDef — `invertible_ideals(R, S)`: the invertible fractional ideals of the subring S of R.
var InvertibleIdealsDef = invertibleIdealsDefThm{family.Define(registry.DefEntry{
	Name:  "InvertibleIdealsDef",
	Key:   "prop_9f8da2c593d12bc1",
	Deps:  []registry.EntryLike{},
	Const: "invertible_ideals",
	Type:  "ring_ops(A) → set(A) → set(set(A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). invertible_ideals(R, S) = {I:set(A) | invertible_fractional(R, S, I)}",
	},
})}

// PrincipalFractionalIdealsDef — `principal_fractional_ideals(R, S)`: the principal fractional ideals aS, one for each nonzero a of R.
var PrincipalFractionalIdealsDef = principalFractionalIdealsDefThm{family.Define(registry.DefEntry{
	Name:  "PrincipalFractionalIdealsDef",
	Key:   "prop_28cf9d5467449097",
	Deps:  []registry.EntryLike{},
	Const: "principal_fractional_ideals",
	Type:  "ring_ops(A) → set(A) → set(set(A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). " +
			"    principal_fractional_ideals(R, S) = {image(R.mul(a), S) | a:A | a ∈ R.carrier ∧ a ≠ R.zero}",
	},
})}

// IdealClassDef — `ideal_class(R, S, I)`: the class I·P of I, its coset modulo the principal fractional ideals P.
var IdealClassDef = idealClassDefThm{family.Define(registry.DefEntry{
	Name:  "IdealClassDef",
	Key:   "prop_fdaf1a9e9d37b4ea",
	Deps:  []registry.EntryLike{PrincipalFractionalIdealsDef},
	Const: "ideal_class",
	Type:  "ring_ops(A) → set(A) → set(A) → set(set(A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S I:set(A). " +
			"    ideal_class(R, S, I) = left_coset(fractional_mul(R, S), I, principal_fractional_ideals(R, S))",
	},
})}

// IdealClassesDef — `ideal_classes(R, S)`: the ideal classes, the cosets of the invertible ideals modulo the principal ones.
var IdealClassesDef = idealClassesDefThm{family.Define(registry.DefEntry{
	Name:  "IdealClassesDef",
	Key:   "prop_f9c6ad1bc5f4eb3d",
	Deps:  []registry.EntryLike{InvertibleIdealsDef, PrincipalFractionalIdealsDef},
	Const: "ideal_classes",
	Type:  "ring_ops(A) → set(A) → set(set(set(A)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). " +
			"    ideal_classes(R, S) = " +
			"    left_cosets(fractional_mul(R, S), invertible_ideals(R, S), principal_fractional_ideals(R, S))",
	},
})}
