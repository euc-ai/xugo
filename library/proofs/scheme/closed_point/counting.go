package closed_point

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

var ResidueFieldSize = residueFieldSizeThm{family.Add(registry.ProofEntry{
	Name: "ResidueFieldSize",
	Key:  "prop_8ace421058eec6b3",
	Deps: []registry.EntryLike{
		ClosedPointDef,
		PointDegreeDef,
		ResidueFieldDef,
		ClosedPointDegreePositive,
		finite_field.FiniteDimensionalSpaceSize,
		quotient_ring.QuotientFieldOn,
		elliptic_curve.OriginMaximal,
	},
	Reading: "At the origin the residue quotient is taken on " +
		"chart one. At affine points it is taken on chart zero.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
			"elliptic_closed_point(L, k, x, y, P)",
		},
		Conclusion: "finite_field(elliptic_residue_field(L, k, x, y, P)) ∧ " +
			"has_size(elliptic_residue_field(L, k, x, y, P).carrier, " +
			"    card(k) ^ elliptic_point_degree(L, k, x, y, P))",
	},
		"A maximal-ideal quotient is a field. Its finite k-dimension is point_degree, so "+
			"FiniteDimensionalSpaceSize counts its elements; the origin has residue k and degree one."),
})}

var PointCountAffine = pointCountAffineThm{family.Add(registry.ProofEntry{
	Name: "PointCountAffine",
	Key:  "prop_54c0109fadf58e1c",
	Deps: []registry.EntryLike{
		PointCountDef,
		AffineSolutionCountDef,
		elliptic_curve.RationalPointsOfWeierstrass,
		cardinality.CardImageInj,
	},
	Reading: "This is the sole model-to-coordinate count bridge. It holds for every " +
		"Weierstrass model over the same finite coefficient field and does not mention twisting.",
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "elliptic_point_count(L, k, x, y) = " +
			"1 + affine_solution_count(restrict_ring(field_ring(L), k), a, b)",
	},
		"RationalPointsOfWeierstrass gives the disjoint bijection between rational ideal pairs and the "+
			"origin together with affine coordinate solutions. The finite coordinate set makes its "+
			"cardinality one plus affine_solution_count; no smoothness or characteristic condition is needed."),
})}
