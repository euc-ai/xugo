package closed_point

import (
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/registry"
)

var ClosedPointDef = closedPointDefThm{family.Define(registry.DefEntry{
	Name:  "ClosedPointDef",
	Key:   "prop_853bb43106321ed3",
	Const: "elliptic_closed_point",
	Type:  "field_ops(A) → set(A) → A → A → prod(set(A), set(A)) → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀P:prod(set(A), set(A)). " +
			"    elliptic_closed_point(R, k, x, y, P) ⇔ " +
			"    P = weierstrass_origin(R, k, x, y) ∨ " +
			"    (maximal_ideal( " +
			"            restrict_ring(field_ring(R), weierstrass_chart_zero(field_ring(R), k, x, y)), " +
			"            fst(P)) ∧ " +
			"        snd(P) = " +
			"        weierstrass_chart_one(R, k, x, y) ∩ " +
			"        ideal_span(restrict_ring(field_ring(R), " +
			"                ring_away(field_ring(R), weierstrass_chart_zero(field_ring(R), k, x, y), x)), " +
			"            fst(P)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "A closed point is one ideal pair. The origin has its existing " +
		"pair; an affine maximal ideal is paired with its extension to the " +
		"overlap contracted to chart one. No rationality restriction is imposed.",
})}

var PointDegreeDef = pointDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "PointDegreeDef",
	Key:   "prop_5d63d8651804054",
	Const: "elliptic_point_degree",
	Type:  "field_ops(A) → set(A) → A → A → prod(set(A), set(A)) → num",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀P:prod(set(A), set(A)). " +
			"    elliptic_point_degree(R, k, x, y, P) = " +
			"    COND(P = weierstrass_origin(R, k, x, y), " +
			"        1, " +
			"        module_dim(restrict_ring(field_ring(R), k), " +
			"            quotient_module(restrict_module(regular_module(field_ring(R)), " +
			"                    weierstrass_chart_zero(field_ring(R), k, x, y)), " +
			"                fst(P))))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Degree is the k-dimension of the affine residue field, and one at the " +
		"origin. Its positivity and finite dimensionality require the closed-point hypothesis.",
})}

// ResidueFieldDef — `elliptic_residue_field(R, k, x, y, P)`: the
// residue at the point P as a field record: the quotient of the chart
// ring holding P by P's ideal, with the inverse and division of cosets.
var ResidueFieldDef = residueFieldDefThm{family.Define(registry.DefEntry{
	Name:  "ResidueFieldDef",
	Key:   "prop_b5b78f0de59ce86d",
	Const: "elliptic_residue_field",
	Type:  "field_ops(A) → set(A) → A → A → prod(set(A), set(A)) → field_ops(set(A))",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀P:prod(set(A), set(A)). " +
			"    elliptic_residue_field(R, k, x, y, P) = " +
			"    ideal_quotient_field(COND(P = weierstrass_origin(R, k, x, y), " +
			"            restrict_ring(field_ring(R), weierstrass_chart_one(R, k, x, y)), " +
			"            restrict_ring(field_ring(R), weierstrass_chart_zero(field_ring(R), k, x, y))), " +
			"        COND(P = weierstrass_origin(R, k, x, y), snd(P), fst(P)))",
	},
})}

var FrobeniusCountDef = frobeniusCountDefThm{family.Define(registry.DefEntry{
	Name:  "FrobeniusCountDef",
	Key:   "prop_36fb762b6de8d42f",
	Const: "elliptic_frobenius_count",
	Type:  "field_ops(A) → set(A) → A → A → num → num",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. ∀m:num. " +
			"    elliptic_frobenius_count(R, k, x, y, m) = " +
			"    COND(m = 0, " +
			"        0, " +
			"        nat_sum({P:prod(set(A), set(A)) | " +
			"                elliptic_closed_point(R, k, x, y, P) ∧ " +
			"                elliptic_point_degree(R, k, x, y, P) ∣ m}, " +
			"            λP:prod(set(A), set(A)). elliptic_point_degree(R, k, x, y, P)))",
	},
	Deps: []registry.EntryLike{ClosedPointDef, PointDegreeDef},
	Reading: "Only positive m is the geometric count. At m=0 the " +
		"definition fixes zero and makes no extension-field assertion.",
})}

var PointCountDef = pointCountDefThm{family.Define(registry.DefEntry{
	Name:  "PointCountDef",
	Key:   "prop_9c29431220ecfd2b",
	Const: "elliptic_point_count",
	Type:  "field_ops(A) → set(A) → A → A → num",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀x:A. ∀y:A. " +
			"    elliptic_point_count(R, k, x, y) = " +
			"    card({P:prod(set(A), set(A)) | " +
			"            biaffine_rational_point(restrict_ring(field_ring(R), " +
			"                    ring_away(field_ring(R), " +
			"                        weierstrass_chart_zero(field_ring(R), k, x, y), " +
			"                        x)), " +
			"                k, " +
			"                weierstrass_chart_zero(field_ring(R), k, x, y), " +
			"                weierstrass_chart_one(R, k, x, y), " +
			"                P)})",
	},
	Deps: []registry.EntryLike{},
	Reading: "This counts existing rational ideal pairs. PointCountAffine identifies it with " +
		"one plus the affine coordinate count, independently of the chosen function-field model.",
})}

var AffineSolutionCountDef = affineSolutionCountDefThm{family.Define(registry.DefEntry{
	Name:  "AffineSolutionCountDef",
	Key:   "prop_46f6eee526bcd9a8",
	Const: "affine_solution_count",
	Type:  "ring_ops(A) → A → A → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀a b:A. " +
			"    affine_solution_count(R, a, b) = " +
			"    card({z:prod(A, A) | " +
			"            fst(z) ∈ R.carrier ∧ " +
			"            snd(z) ∈ R.carrier ∧ " +
			"            R.mul(snd(z), snd(z)) = " +
			"            R.add(R.add(R.mul(fst(z), R.mul(fst(z), fst(z))), R.mul(a, fst(z))), b)})",
	},
	Deps: []registry.EntryLike{},
	Reading: "Only the coefficient field and two coefficients occur. No " +
		"function-field model, closed point, or twist is part of this definition.",
})}
