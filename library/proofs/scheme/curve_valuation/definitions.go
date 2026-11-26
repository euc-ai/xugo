package curve_valuation

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/closed_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

var poleSpaceDef = poleSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "poleSpaceDef",
	Key:   "prop_6b81eb4f8f10e806",
	Const: "elliptic_pole_space",
	Type:  "field_ops(A) → set(A) → A → A → num → module_ops(A, A)",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀n:num. " +
			"    elliptic_pole_space(R, k, x, y, n) = " +
			"    lattice_pair_h0(regular_module(field_ring(R)), " +
			"        monoid_pow((λM:prod(set(A), set(A)). λN:prod(set(A), set(A)). " +
			"                lattice_pair_mul(field_ring(R), " +
			"                    weierstrass_chart_zero(field_ring(R), k, x, y), " +
			"                    weierstrass_chart_one(R, k, x, y), " +
			"                    M, " +
			"                    N)), " +
			"            (weierstrass_chart_zero(field_ring(R), k, x, y), " +
			"                weierstrass_chart_one(R, k, x, y)), " +
			"            lattice_pair_inverse(field_ring(R), " +
			"                weierstrass_chart_zero(field_ring(R), k, x, y), " +
			"                weierstrass_chart_one(R, k, x, y), " +
			"                weierstrass_origin(R, k, x, y)), " +
			"            n))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "",
})}

var poleOrderDef = poleOrderDefThm{family.Define(registry.DefEntry{
	Name:  "poleOrderDef",
	Key:   "prop_1581656d663bb9a",
	Const: "elliptic_pole_order",
	Type:  "field_ops(A) → set(A) → A → A → A → num",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀g:A. " +
			"    elliptic_pole_order(R, k, x, y, g) = " +
			"    COND(g = R.zero, " +
			"        0, " +
			"        εn:num. " +
			"            g ∈ elliptic_pole_space(R, k, x, y, n).carrier ∧ " +
			"            (∀m:num. g ∈ elliptic_pole_space(R, k, x, y, m).carrier ⇒ n ≤ m))",
	},
	Deps: []registry.EntryLike{poleSpaceDef},
	Reading: "The least-index choice is determined for nonzero " +
		"affine functions by StructureRingHasPoleAtOrigin. A nonzero input " +
		"outside all pole spaces has no prescribed pole-order behavior.",
})}

var poleOrderBasisDef = poleOrderBasisDefThm{family.Define(registry.DefEntry{
	Name:  "poleOrderBasisDef",
	Key:   "prop_d4c3435fe8b32484",
	Const: "elliptic_pole_basis",
	Type:  "field_ops(A) → set(A) → A → A → num → set(A) → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀n:num. ∀S:set(A). " +
			"    elliptic_pole_basis(R, k, x, y, n, S) ⇔ " +
			"    finite(S) ∧ " +
			"    module_basis(restrict_ring(field_ring(R), k), elliptic_pole_space(R, k, x, y, n), S) ∧ " +
			"    (∀u v:A. " +
			"        u ∈ S ∧ " +
			"        v ∈ S ∧ " +
			"        elliptic_pole_order(R, k, x, y, u) = elliptic_pole_order(R, k, x, y, v) ⇒ " +
			"        u = v)",
	},
	Deps:    []registry.EntryLike{poleSpaceDef, poleOrderDef},
	Reading: "",
})}
